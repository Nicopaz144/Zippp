import SwiftUI
import WebKit
import AVFoundation
import UserNotifications

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

    private(set) var filesDone: Int
    private(set) var bytesWritten: UInt64
    private let base: UInt64
    private var dropped: UInt64 = 0
    private(set) var boundary: UInt64
    private(set) var boundaryFiles: Int
    private(set) var boundaryBytes: UInt64
    private(set) var currentName = ""
    var isComplete: Bool { state == .done }

    init(root: URL, baseOffset: UInt64 = 0, filesDone: Int = 0, bytesWritten: UInt64 = 0) throws {
        self.root = root
        self.base = baseOffset
        self.filesDone = filesDone
        self.bytesWritten = bytesWritten
        self.boundary = baseOffset
        self.boundaryFiles = filesDone
        self.boundaryBytes = bytesWritten
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
            dropped += UInt64(pos)
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
                boundary = base + dropped + UInt64(pos)   // aquí no hay estado: punto de reanudación
                boundaryFiles = filesDone
                boundaryBytes = bytesWritten
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

// MARK: - Utilidades

func fmtBytes(_ n: Int64) -> String {
    ByteCountFormatter.string(fromByteCount: n, countStyle: .file)
}

func fmtTime(_ sec: Double) -> String {
    guard sec.isFinite, sec >= 0 else { return "—" }
    let t = Int(sec), h = t / 3600, m = (t % 3600) / 60, s = t % 60
    if h > 0 { return "\(h) h \(m) min" }
    if m > 0 { return "\(m) min \(s) s" }
    return "\(s) s"
}

func freeSpace() -> Int64 {
    let u = URL(fileURLWithPath: NSHomeDirectory())
    let v = try? u.resourceValues(forKeys: [.volumeAvailableCapacityForImportantUsageKey])
    return v?.volumeAvailableCapacityForImportantUsage ?? 0
}

// MARK: - Punto de reanudación

/// Se guarda en un límite entre archivos del zip: ahí el parser no tiene estado,
/// así que reanudar solo necesita el offset del flujo.
struct Checkpoint: Codable {
    var url: String
    var cookie: String?
    var referer: String?
    var offset: UInt64
    var files: Int
    var written: UInt64
    var total: Int64
    var name: String

    static let key = "zipstream.checkpoint"
    static func load() -> Checkpoint? {
        guard let d = UserDefaults.standard.data(forKey: key) else { return nil }
        return try? JSONDecoder().decode(Checkpoint.self, from: d)
    }
    func save() {
        if let d = try? JSONEncoder().encode(self) { UserDefaults.standard.set(d, forKey: Checkpoint.key) }
    }
    static func clear() { UserDefaults.standard.removeObject(forKey: key) }
}

struct Snap {
    var received: Int64      // bytes del zip procesados (posición absoluta en el flujo)
    var total: Int64
    var files: Int
    var written: UInt64
    var name: String
    var skipping: Bool
}

// MARK: - Segundo plano (audio silencioso) y avisos

final class KeepAlive {
    static let shared = KeepAlive()
    private let engine = AVAudioEngine()
    private let player = AVAudioPlayerNode()
    private var active = false

    func start() {
        guard !active else { return }
        do {
            let session = AVAudioSession.sharedInstance()
            try session.setCategory(.playback, mode: .default, options: [.mixWithOthers])
            try session.setActive(true)
            let format = AVAudioFormat(standardFormatWithSampleRate: 44100, channels: 1)!
            let buffer = AVAudioPCMBuffer(pcmFormat: format, frameCapacity: 44100)!
            buffer.frameLength = 44100
            memset(buffer.floatChannelData![0], 0, Int(buffer.frameLength) * MemoryLayout<Float>.size)
            engine.attach(player)
            engine.connect(player, to: engine.mainMixerNode, format: format)
            try engine.start()
            player.scheduleBuffer(buffer, at: nil, options: .loops, completionHandler: nil)
            player.play()
            NotificationCenter.default.addObserver(self, selector: #selector(interrupted(_:)),
                                                   name: AVAudioSession.interruptionNotification, object: nil)
            active = true
        } catch {
            print("KeepAlive error: \(error)")
        }
    }

    @objc private func interrupted(_ n: Notification) {
        guard let raw = n.userInfo?[AVAudioSessionInterruptionTypeKey] as? UInt,
              AVAudioSession.InterruptionType(rawValue: raw) == .ended else { return }
        try? AVAudioSession.sharedInstance().setActive(true)
        if !engine.isRunning { try? engine.start() }
        player.play()
    }

    func stop() {
        guard active else { return }
        player.stop()
        engine.stop()
        engine.detach(player)
        NotificationCenter.default.removeObserver(self)
        try? AVAudioSession.sharedInstance().setActive(false, options: .notifyOthersOnDeactivation)
        active = false
    }
}

enum Notifier {
    static func requestAuth() {
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound]) { _, _ in }
    }
    static func post(_ title: String, _ body: String) {
        let c = UNMutableNotificationContent()
        c.title = title
        c.body = body
        c.sound = .default
        UNUserNotificationCenter.current().add(UNNotificationRequest(identifier: UUID().uuidString, content: c, trigger: nil))
    }
}

// MARK: - Descarga (con reanudación)

final class StreamDownloader: NSObject, URLSessionDataDelegate {
    var onProgress: ((Snap) -> Void)?
    var onFinish: ((Error?) -> Void)?

    private var cp: Checkpoint
    private let dest: URL
    private var extractor: ZipStreamExtractor?
    private var session: URLSession?
    private var skipRemaining: UInt64 = 0
    private var received: Int64 = 0
    private var total: Int64 = 0
    private var failure: Error?
    private var lastReport = Date.distantPast
    private var lastSave = Date.distantPast

    init(checkpoint: Checkpoint, dest: URL) {
        self.cp = checkpoint
        self.dest = dest
        super.init()
    }

    func start() throws {
        guard let url = URL(string: cp.url) else { throw ZipError.invalid("URL inválida") }
        extractor = try ZipStreamExtractor(root: dest, baseOffset: cp.offset,
                                           filesDone: cp.files, bytesWritten: cp.written)
        let queue = OperationQueue()
        queue.maxConcurrentOperationCount = 1
        let cfg = URLSessionConfiguration.ephemeral
        cfg.timeoutIntervalForRequest = 60
        cfg.timeoutIntervalForResource = 60 * 60 * 24 * 3
        cfg.httpShouldSetCookies = false
        session = URLSession(configuration: cfg, delegate: self, delegateQueue: queue)

        var req = URLRequest(url: url)
        req.setValue(browserUA, forHTTPHeaderField: "User-Agent")
        if let c = cp.cookie, !c.isEmpty { req.setValue(c, forHTTPHeaderField: "Cookie") }
        if let r = cp.referer { req.setValue(r, forHTTPHeaderField: "Referer") }
        if cp.offset > 0 { req.setValue("bytes=\(cp.offset)-", forHTTPHeaderField: "Range") }
        session!.dataTask(with: req).resume()
    }

    func cancel() { session?.invalidateAndCancel() }

    func urlSession(_ session: URLSession, dataTask: URLSessionDataTask, didReceive response: URLResponse,
                    completionHandler: @escaping (URLSession.ResponseDisposition) -> Void) {
        func fail(_ msg: String) {
            failure = ZipError.invalid(msg)
            completionHandler(.cancel)
        }
        guard let h = response as? HTTPURLResponse else { return fail("respuesta no válida") }
        if [401, 403, 404, 410].contains(h.statusCode) {
            return fail("HTTP \(h.statusCode): el enlace caducó o requiere sesión. Ve al navegador y toca descargar otra vez: continuará donde quedó")
        }
        if let mime = response.mimeType?.lowercased(), mime.contains("html") || mime.contains("json") {
            return fail("el servidor devolvió una página (\(mime)), no un zip. Ve al navegador y toca descargar otra vez")
        }
        if h.statusCode == 206 {
            let cr = (h.value(forHTTPHeaderField: "Content-Range") ?? "").replacingOccurrences(of: "bytes ", with: "")
            let start = cr.split(separator: "-").first.flatMap { UInt64($0) }
            guard start == cp.offset else { return fail("el servidor devolvió otro rango") }
            if let slash = cr.lastIndex(of: "/"), let t = Int64(cr[cr.index(after: slash)...]) { total = t } else { total = cp.total }
            received = Int64(cp.offset)
            skipRemaining = 0
        } else if h.statusCode == 200 {
            // El servidor ignoró Range: se vuelve a bajar y se descarta lo ya extraído
            total = response.expectedContentLength
            received = 0
            skipRemaining = cp.offset
        } else {
            return fail("HTTP \(h.statusCode)")
        }
        if cp.offset > 0, cp.total > 0, total > 0, total != cp.total {
            return fail("el archivo cambió en el servidor")
        }
        cp.total = total
        completionHandler(.allow)
    }

    func urlSession(_ session: URLSession, dataTask: URLSessionDataTask, didReceive data: Data) {
        guard failure == nil else { return }
        var d = data
        if skipRemaining > 0 {
            let n = min(UInt64(d.count), skipRemaining)
            skipRemaining -= n
            received += Int64(n)
            d = d.dropFirst(Int(n))
            if d.isEmpty { report(); return }
        }
        do {
            try extractor?.feed(d)
            received += Int64(d.count)
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
        guard force || now.timeIntervalSince(lastReport) > 0.5, let ex = extractor else { return }
        lastReport = now
        onProgress?(Snap(received: received, total: total, files: ex.filesDone,
                         written: ex.bytesWritten, name: ex.currentName, skipping: skipRemaining > 0))
        if force || now.timeIntervalSince(lastSave) > 2 {
            var c = cp
            c.offset = ex.boundary
            c.files = ex.boundaryFiles
            c.written = ex.boundaryBytes
            c.total = total
            c.save()
            lastSave = now
        }
    }
}

// MARK: - Modelo

final class Model: ObservableObject {
    struct Row: Identifiable { let id: String; let value: String }

    @Published var urlText = ""
    @Published var progress = 0.0
    @Published var status = "Listo"
    @Published var rows: [Row] = []
    @Published var running = false
    @Published var showDownload = false
    @Published var pending: Checkpoint?

    private var worker: StreamDownloader?
    private var userPaused = false
    private var attempts = 0
    private var startDate = Date()
    private var lastTime: Date?
    private var lastReceived: Int64 = 0
    private var speed = 0.0

    init() {
        pending = Checkpoint.load()
        showDownload = pending != nil
        if let p = pending { status = "Descarga pendiente: \(p.name)" }
    }

    private var destination: URL {
        FileManager.default.urls(for: .documentDirectory, in: .userDomainMask)[0]
            .appendingPathComponent("Extraido", isDirectory: true)
    }

    // URL pegada a mano
    func start() {
        let text = urlText.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let url = URL(string: text), url.scheme?.hasPrefix("http") == true else {
            status = "URL inválida"
            return
        }
        start(url: url, cookie: nil, referer: nil)
    }

    // Enlace capturado por el navegador: si coincide con una descarga pendiente, continúa donde quedó
    func start(url: URL, cookie: String?, referer: String?) {
        guard !running else { return }
        showDownload = true
        var cp = Checkpoint(url: url.absoluteString, cookie: cookie, referer: referer,
                            offset: 0, files: 0, written: 0, total: 0, name: url.lastPathComponent)
        if let old = Checkpoint.load(), old.name == cp.name {
            cp.offset = old.offset; cp.files = old.files; cp.written = old.written; cp.total = old.total
        }
        attempts = 0
        begin(cp)
    }

    func resume() {
        guard !running, let p = pending else { return }
        attempts = 0
        begin(p)
    }

    func discard() {
        Checkpoint.clear()
        pending = nil
        rows = []
        progress = 0
        status = "Listo"
    }

    func cancel() {
        userPaused = true
        if let w = worker {
            w.cancel()
        } else {
            running = false
            KeepAlive.shared.stop()
            pending = Checkpoint.load()
            status = "Pausado"
        }
    }

    private func begin(_ cp: Checkpoint) {
        userPaused = false
        let w = StreamDownloader(checkpoint: cp, dest: destination)
        w.onProgress = { [weak self] s in DispatchQueue.main.async { self?.update(s) } }
        w.onFinish = { [weak self] err in DispatchQueue.main.async { self?.finished(err) } }
        do {
            try w.start()
            worker = w
            running = true
            pending = nil
            status = cp.offset > 0 ? "Reanudando…" : "Conectando…"
            startDate = Date()
            lastTime = nil
            speed = 0
            KeepAlive.shared.start()
            if attempts == 0 { Notifier.requestAuth() }
        } catch {
            status = "Error: \(error.localizedDescription)"
        }
    }

    private func update(_ s: Snap) {
        let now = Date()
        if let lt = lastTime {
            let dt = now.timeIntervalSince(lt)
            if dt > 0.05 {
                let inst = Double(s.received - lastReceived) / dt
                speed = speed == 0 ? inst : speed * 0.85 + inst * 0.15
                lastTime = now
                lastReceived = s.received
            }
        } else {
            lastTime = now
            lastReceived = s.received
        }

        progress = s.total > 0 ? Double(s.received) / Double(s.total) : 0
        status = s.skipping ? "Reanudando: saltando lo ya extraído…" : "Descargando \(Int(progress * 100)) %"

        let written = Int64(clamping: s.written)
        var est: Int64 = 0
        if !s.skipping, s.total > 0, s.received > 50_000_000 {
            est = Int64(Double(s.written) / Double(s.received) * Double(s.total))
        }
        let eta = (speed > 1000 && s.total > 0) ? fmtTime(Double(max(0, s.total - s.received)) / speed) : "calculando…"

        var r: [Row] = [
            Row(id: "Velocidad", value: "\(fmtBytes(Int64(max(0, speed))))/s"),
            Row(id: "Tiempo restante", value: eta),
            Row(id: "Transcurrido", value: fmtTime(now.timeIntervalSince(startDate))),
            Row(id: "Descargado", value: s.total > 0 ? "\(fmtBytes(s.received)) de \(fmtBytes(s.total))" : fmtBytes(s.received)),
            Row(id: "Extraído", value: est > 0 ? "\(fmtBytes(written)) de ≈\(fmtBytes(est))" : fmtBytes(written)),
        ]
        if est > written { r.append(Row(id: "Falta por extraer", value: "≈\(fmtBytes(est - written))")) }
        r.append(Row(id: "Archivos extraídos", value: "\(s.files)"))
        r.append(Row(id: "Espacio libre", value: fmtBytes(freeSpace())))
        r.append(Row(id: "Archivo actual", value: s.name))
        rows = r
    }

    private func finished(_ err: Error?) {
        worker = nil
        if err == nil {
            Checkpoint.clear()
            pending = nil
            running = false
            progress = 1
            status = "✅ Completado en \(fmtTime(Date().timeIntervalSince(startDate)))"
            KeepAlive.shared.stop()
            Notifier.post("ZipStream", "Descarga y extracción completas")
            return
        }
        let urlErr = err as? URLError
        if userPaused || urlErr?.code == .cancelled {
            running = false
            KeepAlive.shared.stop()
            pending = Checkpoint.load()
            status = "Pausado"
            return
        }
        if urlErr != nil, attempts < 30 {
            attempts += 1
            status = "Sin conexión. Reintentando (\(attempts)/30)…"
            DispatchQueue.main.asyncAfter(deadline: .now() + 5) { [weak self] in
                guard let self = self, self.running, !self.userPaused, self.worker == nil,
                      let cp = Checkpoint.load() else { return }
                self.begin(cp)
            }
            return
        }
        running = false
        KeepAlive.shared.stop()
        pending = Checkpoint.load()
        status = "Error: \(err!.localizedDescription)"
        Notifier.post("ZipStream", "La descarga se detuvo. Ábrela para reanudar.")
    }
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
        ScrollView {
            VStack(alignment: .leading, spacing: 14) {
                Text("ZipStream").font(.largeTitle.bold())

                if let p = m.pending, !m.running {
                    VStack(alignment: .leading, spacing: 8) {
                        Text("Descarga pendiente").font(.headline)
                        Text("\(p.name)\n\(p.files) archivos extraídos · continúa desde \(fmtBytes(Int64(clamping: p.offset)))")
                            .font(.footnote).foregroundColor(.secondary)
                        HStack {
                            Button("Reanudar") { m.resume() }.buttonStyle(.borderedProminent)
                            Button("Descartar", role: .destructive) { m.discard() }.buttonStyle(.bordered)
                        }
                    }
                    .padding()
                    .frame(maxWidth: .infinity, alignment: .leading)
                    .background(Color.gray.opacity(0.15))
                    .cornerRadius(12)
                }

                Text("Navega hasta el archivo y toca su botón de descarga. Sigue en segundo plano y se reanuda solo si se corta.")
                    .font(.subheadline).foregroundColor(.secondary)
                TextField("…o pega una URL directa", text: $m.urlText)
                    .textFieldStyle(.roundedBorder)
                    .keyboardType(.URL)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled(true)
                    .disabled(m.running)

                ProgressView(value: m.progress)
                Text(m.status).font(.headline)

                ForEach(m.rows) { r in
                    HStack(alignment: .top) {
                        Text(r.id).foregroundColor(.secondary)
                        Spacer(minLength: 12)
                        Text(r.value).multilineTextAlignment(.trailing)
                    }
                    .font(.footnote)
                }

                Button(m.running ? "Pausar" : "Descargar y extraer") {
                    if m.running { m.cancel() } else { m.start() }
                }
                .buttonStyle(.borderedProminent)
            }
            .padding()
        }
    }
}

@main
struct ZipStreamApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}
