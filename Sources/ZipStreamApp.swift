import SwiftUI
import WebKit

let browserUA = "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1"

// MARK: - Errores

enum ZipError: LocalizedError {
    case invalid(String), unsupported(String), unsafePath(String), inflate

    var errorDescription: String? {
        switch self {
        case .invalid(let s): return "ZIP inválido: \(s)"
        case .unsupported(let s): return "No soportado: \(s)"
        case .unsafePath(let s): return "Ruta insegura: \(s)"
        case .inflate: return "Error al descomprimir"
        }
    }
}

// MARK: - Inflater (deflate crudo con zlib del sistema)

final class Inflater {
    private var strm = z_stream()
    private let cap = 1 << 16
    private let out: UnsafeMutablePointer<UInt8>
    private var ready = false

    init() throws {
        out = UnsafeMutablePointer<UInt8>.allocate(capacity: 1 << 16)
        let rc = inflateInit2_(&strm, -15, ZLIB_VERSION, Int32(MemoryLayout<z_stream>.size))
        guard rc == Z_OK else { throw ZipError.inflate }
        ready = true
    }

    deinit {
        if ready { inflateEnd(&strm) }
        out.deallocate()
    }

    /// Devuelve cuántos bytes de entrada consumió (exacto) y si el flujo deflate terminó.
    func process(_ src: UnsafePointer<UInt8>, _ count: Int,
                 sink: (UnsafePointer<UInt8>, Int) throws -> Void) throws -> (consumed: Int, ended: Bool) {
        strm.next_in = UnsafeMutablePointer(mutating: src)
        strm.avail_in = uInt(count)
        while true {
            strm.next_out = out
            strm.avail_out = uInt(cap)
            let rc = inflate(&strm, Z_NO_FLUSH)
            let produced = cap - Int(strm.avail_out)
            if produced > 0 { try sink(out, produced) }
            if rc == Z_STREAM_END { return (count - Int(strm.avail_in), true) }
            if rc != Z_OK && rc != Z_BUF_ERROR { throw ZipError.inflate }
            if strm.avail_in == 0 && strm.avail_out > 0 { return (count, false) }
        }
    }
}

// MARK: - Extractor ZIP en streaming

/// Lee el ZIP byte a byte a medida que llega, extrae cada archivo y descarta lo ya procesado.
/// Soporta: stored y deflate, ZIP64, data descriptors (con deflate). No soporta cifrado.
final class ZipStreamExtractor {
    private enum State { case header, data, descriptor, done }

    private var state = State.header
    private var buf = [UInt8]()
    private var pos = 0
    private let root: URL
    private var file: FileHandle?
    private var inflater: Inflater?
    private var method: UInt16 = 0
    private var hasDescriptor = false
    private var zip64 = false
    private var remaining: UInt64 = 0
    private var compSize: UInt64 = 0

    private(set) var filesDone = 0
    private(set) var bytesWritten: UInt64 = 0
    private(set) var currentName = ""
    var isComplete: Bool { state == .done }

    init(root: URL) throws {
        self.root = root
        try FileManager.default.createDirectory(at: root, withIntermediateDirectories: true)
    }

    func abort() {
        try? file?.close()
        file = nil
        inflater = nil
    }

    func feed(_ data: Data) throws {
        buf.append(contentsOf: data)
        try run()
        if pos > (1 << 20) {   // compacta lo ya consumido
            buf.removeFirst(pos)
            pos = 0
        }
    }

    // Lectores little-endian (índice absoluto en buf)
    private func r16(_ i: Int) -> UInt16 { UInt16(buf[i]) | UInt16(buf[i + 1]) << 8 }
    private func r32(_ i: Int) -> UInt32 { UInt32(r16(i)) | UInt32(r16(i + 2)) << 16 }
    private func r64(_ i: Int) -> UInt64 { UInt64(r32(i)) | UInt64(r32(i + 4)) << 32 }
    private var avail: Int { buf.count - pos }

    private func run() throws {
        while true {
            switch state {
            case .done:
                pos = buf.count
                return

            case .header:
                guard avail >= 4 else { return }
                let sig = r32(pos)
                if sig == 0x04034b50 {
                    guard avail >= 30 else { return }
                    let nameLen = Int(r16(pos + 26))
                    let extraLen = Int(r16(pos + 28))
                    guard avail >= 30 + nameLen + extraLen else { return }
                    try startEntry(nameLen: nameLen, extraLen: extraLen)
                } else if sig == 0x02014b50 || sig == 0x06054b50 || sig == 0x06064b50 {
                    state = .done   // llegó el directorio central: ya está todo
                } else {
                    let head = buf[pos..<min(pos + 80, buf.count)]
                    let text = String(decoding: head, as: UTF8.self).filter { !$0.isNewline && $0.isASCII }
                    throw ZipError.invalid("firma inesperada. Tras \(currentName) empieza con: \(text.prefix(60))")
                }

            case .data:
                if method == 0 {
                    if remaining == 0 { try finishEntry(); continue }
                    guard avail > 0 else { return }
                    let n = Int(min(UInt64(avail), remaining))
                    let start = pos
                    try buf.withUnsafeBufferPointer { p in
                        try self.write(p.baseAddress! + start, n)
                    }
                    pos += n
                    remaining -= UInt64(n)
                } else {
                    guard avail > 0 else { return }
                    let n = avail
                    let start = pos
                    let r = try buf.withUnsafeBufferPointer { p in
                        try self.inflater!.process(p.baseAddress! + start, n) { ptr, len in
                            try self.write(ptr, len)
                        }
                    }
                    pos += r.consumed
                    compSize += UInt64(r.consumed)
                    if r.ended { try finishEntry() }
                }

            case .descriptor:
                guard avail >= 4 else { return }
                let sigLen = (r32(pos) == 0x08074b50) ? 4 : 0
                guard avail >= sigLen + 4 + 16 else { return }
                let c = pos + sigLen + 4
                let is32 = UInt64(r32(c)) == compSize
                let is64 = r64(c) == compSize
                let big: Bool
                if is32 && is64 { big = zip64 }
                else if is32 { big = false }
                else if is64 { big = true }
                else { big = zip64 }
                pos += sigLen + 4 + (big ? 16 : 8)
                state = .header
            }
        }
    }

    private func startEntry(nameLen: Int, extraLen: Int) throws {
        let flags = r16(pos + 6)
        method = r16(pos + 8)
        var csize = UInt64(r32(pos + 18))
        var usize = UInt64(r32(pos + 22))
        let nameStart = pos + 30
        var name = String(decoding: buf[nameStart..<(nameStart + nameLen)], as: UTF8.self)
        name = name.replacingOccurrences(of: "\\", with: "/")

        // Campo extra ZIP64 (0x0001)
        zip64 = false
        var e = nameStart + nameLen
        let eEnd = e + extraLen
        while e + 4 <= eEnd {
            let id = r16(e)
            let sz = Int(r16(e + 2))
            if id == 0x0001 {
                zip64 = true
                var o = e + 4
                if usize == 0xFFFF_FFFF, o + 8 <= eEnd { usize = r64(o); o += 8 }
                if csize == 0xFFFF_FFFF, o + 8 <= eEnd { csize = r64(o); o += 8 }
            }
            e += 4 + sz
        }

        if flags & 0x01 != 0 { throw ZipError.unsupported("zip cifrado") }
        guard method == 0 || method == 8 else { throw ZipError.unsupported("método de compresión \(method)") }
        hasDescriptor = flags & 0x08 != 0
        pos += 30 + nameLen + extraLen
        currentName = name

        compSize = 0
        let skip = name.hasPrefix("__MACOSX/") || name.hasSuffix(".DS_Store")
        if name.hasSuffix("/") {
            if !skip {
                try FileManager.default.createDirectory(at: try safeURL(name), withIntermediateDirectories: true)
            }
            state = hasDescriptor ? .descriptor : .header
            return
        }
        if method == 0 && hasDescriptor && csize == 0 {
            throw ZipError.unsupported("archivo sin comprimir con data descriptor")
        }
        if !skip {
            let dest = try safeURL(name)
            try FileManager.default.createDirectory(at: dest.deletingLastPathComponent(), withIntermediateDirectories: true)
            FileManager.default.createFile(atPath: dest.path, contents: nil)
            file = try FileHandle(forWritingTo: dest)
        }
        if method == 8 { inflater = try Inflater() }
        remaining = csize
        state = .data
    }

    private func finishEntry() throws {
        try file?.close()
        file = nil
        inflater = nil
        filesDone += 1
        state = hasDescriptor ? .descriptor : .header
    }

    private func write(_ p: UnsafePointer<UInt8>, _ n: Int) throws {
        guard let f = file else { return }
        try f.write(contentsOf: Data(bytes: p, count: n))
        bytesWritten += UInt64(n)
    }

    private func safeURL(_ name: String) throws -> URL {
        let parts = name.split(separator: "/", omittingEmptySubsequences: true)
        if name.hasPrefix("/") || parts.contains("..") { throw ZipError.unsafePath(name) }
        return parts.reduce(root) { $0.appendingPathComponent(String($1)) }
    }
}

// MARK: - Descarga

final class StreamDownloader: NSObject, URLSessionDataDelegate {
    var onProgress: ((Int64, Int64, Int, String, UInt64) -> Void)?
    var onFinish: ((Error?) -> Void)?

    private var extractor: ZipStreamExtractor?
    private var session: URLSession?
    private var received: Int64 = 0
    private var total: Int64 = 0
    private var failure: Error?
    private var lastReport = Date.distantPast

    func start(url: URL, dest: URL, cookie: String? = nil, referer: String? = nil) throws {
        extractor = try ZipStreamExtractor(root: dest)
        let queue = OperationQueue()
        queue.maxConcurrentOperationCount = 1
        let cfg = URLSessionConfiguration.ephemeral
        cfg.timeoutIntervalForRequest = 60
        cfg.timeoutIntervalForResource = 60 * 60 * 24
        cfg.httpShouldSetCookies = false
        session = URLSession(configuration: cfg, delegate: self, delegateQueue: queue)
        var req = URLRequest(url: url)
        req.setValue(browserUA, forHTTPHeaderField: "User-Agent")
        if let c = cookie, !c.isEmpty { req.setValue(c, forHTTPHeaderField: "Cookie") }
        if let r = referer { req.setValue(r, forHTTPHeaderField: "Referer") }
        session!.dataTask(with: req).resume()
    }

    func cancel() { session?.invalidateAndCancel() }

    func urlSession(_ session: URLSession, dataTask: URLSessionDataTask, didReceive response: URLResponse,
                    completionHandler: @escaping (URLSession.ResponseDisposition) -> Void) {
        if let h = response as? HTTPURLResponse, !(200..<300).contains(h.statusCode) {
            failure = ZipError.invalid("el servidor respondió HTTP \(h.statusCode)")
            completionHandler(.cancel)
            return
        }
        if let mime = response.mimeType?.lowercased(), mime.contains("html") || mime.contains("json") {
            failure = ZipError.invalid("el servidor devolvió una página (\(mime)), no un zip. Puede requerir sesión o cookies")
            completionHandler(.cancel)
            return
        }
        total = response.expectedContentLength
        completionHandler(.allow)
    }

    func urlSession(_ session: URLSession, dataTask: URLSessionDataTask, didReceive data: Data) {
        guard failure == nil else { return }
        do {
            try extractor?.feed(data)
            received += Int64(data.count)
            report()
        } catch {
            failure = error
            dataTask.cancel()
        }
    }

    func urlSession(_ session: URLSession, task: URLSessionTask, didCompleteWithError error: Error?) {
        extractor?.abort()
        var err: Error? = failure ?? error
        if err == nil, extractor?.isComplete != true { err = ZipError.invalid("descarga incompleta") }
        report(force: true)
        onFinish?(err)
        session.finishTasksAndInvalidate()
    }

    private func report(force: Bool = false) {
        let now = Date()
        guard force || now.timeIntervalSince(lastReport) > 0.25 else { return }
        lastReport = now
        onProgress?(received, total, extractor?.filesDone ?? 0,
                    extractor?.currentName ?? "", extractor?.bytesWritten ?? 0)
    }
}

// MARK: - Modelo y vista

final class Model: ObservableObject {
    @Published var urlText = ""
    @Published var progress = 0.0
    @Published var status = "Listo"
    @Published var detail = ""
    @Published var running = false
    @Published var showDownload = false
    private var worker: StreamDownloader?

    private func fmt(_ n: Int64) -> String {
        ByteCountFormatter.string(fromByteCount: n, countStyle: .file)
    }

    func start() {
        let text = urlText.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let url = URL(string: text), url.scheme?.hasPrefix("http") == true else {
            status = "URL inválida"
            return
        }
        start(url: url, cookie: nil, referer: nil)
    }

    func start(url: URL, cookie: String?, referer: String?) {
        guard !running else { return }
        showDownload = true
        let docs = FileManager.default.urls(for: .documentDirectory, in: .userDomainMask)[0]
        let dest = docs.appendingPathComponent("Extraido", isDirectory: true)

        let w = StreamDownloader()
        w.onProgress = { [weak self] rec, tot, files, name, written in
            DispatchQueue.main.async {
                guard let self = self else { return }
                self.progress = tot > 0 ? Double(rec) / Double(tot) : 0
                self.status = tot > 0 ? "Descargado \(self.fmt(rec)) de \(self.fmt(tot))" : "Descargado \(self.fmt(rec))"
                self.detail = "\(files) archivos · escrito \(self.fmt(Int64(written)))\n\(name)"
            }
        }
        w.onFinish = { [weak self] err in
            DispatchQueue.main.async {
                guard let self = self else { return }
                self.running = false
                UIApplication.shared.isIdleTimerDisabled = false
                if let err = err {
                    if (err as? URLError)?.code == .cancelled {
                        self.status = "Cancelado"
                    } else {
                        self.status = "Error: \(err.localizedDescription)"
                    }
                } else {
                    self.progress = 1
                    self.status = "Listo. Archivos › ZipStream › Extraido"
                }
            }
        }
        do {
            try w.start(url: url, dest: dest, cookie: cookie, referer: referer)
            worker = w
            running = true
            progress = 0
            status = "Conectando…"
            detail = ""
            UIApplication.shared.isIdleTimerDisabled = true   // mantener la pantalla encendida
        } catch {
            status = "Error: \(error.localizedDescription)"
        }
    }

    func cancel() { worker?.cancel() }
}

// MARK: - Navegador integrado

final class Browser: NSObject, ObservableObject, WKNavigationDelegate, WKUIDelegate {
    let webView: WKWebView
    @Published var address = ""
    @Published var canGoBack = false
    var onDownload: ((URL, String?, String?) -> Void)?

    override init() {
        webView = WKWebView(frame: .zero, configuration: WKWebViewConfiguration())
        super.init()
        webView.customUserAgent = browserUA
        webView.navigationDelegate = self
        webView.uiDelegate = self
        webView.allowsBackForwardNavigationGestures = true
    }

    func go(_ text: String) {
        let t = text.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !t.isEmpty else { return }
        var s = t
        if !t.contains("://") {
            if t.contains(".") && !t.contains(" ") {
                s = "https://" + t
            } else {
                let q = t.addingPercentEncoding(withAllowedCharacters: .urlQueryAllowed) ?? t
                s = "https://www.google.com/search?q=" + q
            }
        }
        if let u = URL(string: s) { webView.load(URLRequest(url: u)) }
    }

    // Enlace de descarga directa (clic en un botón "download")
    func webView(_ webView: WKWebView, decidePolicyFor navigationAction: WKNavigationAction,
                 decisionHandler: @escaping (WKNavigationActionPolicy) -> Void) {
        if navigationAction.shouldPerformDownload, let url = navigationAction.request.url {
            decisionHandler(.cancel)
            capture(url)
            return
        }
        decisionHandler(.allow)
    }

    // Respuesta que es un archivo (zip, octet-stream, attachment…)
    func webView(_ webView: WKWebView, decidePolicyFor navigationResponse: WKNavigationResponse,
                 decisionHandler: @escaping (WKNavigationResponsePolicy) -> Void) {
        var isFile = !navigationResponse.canShowMIMEType
        if let h = navigationResponse.response as? HTTPURLResponse,
           let cd = h.value(forHTTPHeaderField: "Content-Disposition")?.lowercased(),
           cd.contains("attachment") { isFile = true }
        if isFile, let url = navigationResponse.response.url {
            decisionHandler(.cancel)
            capture(url)
        } else {
            decisionHandler(.allow)
        }
    }

    func webView(_ webView: WKWebView, createWebViewWith configuration: WKWebViewConfiguration,
                 for navigationAction: WKNavigationAction, windowFeatures: WKWindowFeatures) -> WKWebView? {
        if navigationAction.targetFrame == nil { webView.load(navigationAction.request) }
        return nil
    }

    func webView(_ webView: WKWebView, didCommit navigation: WKNavigation!) {
        address = webView.url?.absoluteString ?? address
        canGoBack = webView.canGoBack
    }

    func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
        address = webView.url?.absoluteString ?? address
        canGoBack = webView.canGoBack
    }

    private func capture(_ url: URL) {
        let referer = webView.url?.absoluteString
        webView.configuration.websiteDataStore.httpCookieStore.getAllCookies { [weak self] cookies in
            let host = url.host ?? ""
            let mine = cookies.filter { c in
                let d = c.domain.hasPrefix(".") ? String(c.domain.dropFirst()) : c.domain
                return host == d || host.hasSuffix("." + d)
            }
            let header = HTTPCookie.requestHeaderFields(with: mine)["Cookie"]
            DispatchQueue.main.async { self?.onDownload?(url, header, referer) }
        }
    }
}

struct WebContainer: UIViewRepresentable {
    let webView: WKWebView
    func makeUIView(context: Context) -> WKWebView { webView }
    func updateUIView(_ uiView: WKWebView, context: Context) {}
}

// MARK: - Vistas

struct ContentView: View {
    @StateObject private var m = Model()
    @StateObject private var b = Browser()

    var body: some View {
        VStack(spacing: 0) {
            Picker("", selection: $m.showDownload) {
                Text("Navegador").tag(false)
                Text("Descarga").tag(true)
            }
            .pickerStyle(.segmented)
            .padding(8)

            if m.showDownload { downloadView } else { browserView }
        }
        .onAppear {
            b.onDownload = { url, cookie, ref in m.start(url: url, cookie: cookie, referer: ref) }
            if b.webView.url == nil { b.go("https://www.google.com") }
        }
    }

    var browserView: some View {
        VStack(spacing: 0) {
            HStack(spacing: 8) {
                Button { b.webView.goBack() } label: { Image(systemName: "chevron.left") }
                    .disabled(!b.canGoBack)
                TextField("Buscar o escribir URL", text: $b.address)
                    .textFieldStyle(.roundedBorder)
                    .keyboardType(.webSearch)
                    .submitLabel(.go)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled(true)
                    .onSubmit { b.go(b.address) }
            }
            .padding(.horizontal, 8)
            .padding(.bottom, 6)
            WebContainer(webView: b.webView)
        }
    }

    var downloadView: some View {
        VStack(alignment: .leading, spacing: 16) {
            Text("ZipStream").font(.largeTitle.bold())
            Text("Navega hasta el archivo y toca su botón de descarga: la app detecta el enlace y empieza sola. Deja la app abierta mientras trabaja.")
                .font(.subheadline).foregroundColor(.secondary)
            TextField("…o pega una URL directa", text: $m.urlText)
                .textFieldStyle(.roundedBorder)
                .keyboardType(.URL)
                .textInputAutocapitalization(.never)
                .autocorrectionDisabled(true)
                .disabled(m.running)
            ProgressView(value: m.progress)
            Text(m.status).font(.callout)
            Text(m.detail).font(.footnote).foregroundColor(.secondary)
            Button(m.running ? "Cancelar" : "Descargar y extraer") {
                if m.running { m.cancel() } else { m.start() }
            }
            .buttonStyle(.borderedProminent)
            Spacer()
        }
        .padding()
    }
}

@main
struct ZipStreamApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}
