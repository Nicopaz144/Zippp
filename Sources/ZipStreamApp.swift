import SwiftUI
import Compression

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

// MARK: - Inflater (deflate crudo con Compression framework)

final class Inflater {
    private var stream: compression_stream
    private let cap = 1 << 16
    private let out: UnsafeMutablePointer<UInt8>

    init() throws {
        out = UnsafeMutablePointer<UInt8>.allocate(capacity: 1 << 16)
        stream = compression_stream(
            dst_ptr: UnsafeMutablePointer<UInt8>(bitPattern: 1)!,
            dst_size: 0,
            src_ptr: UnsafePointer<UInt8>(bitPattern: 1)!,
            src_size: 0,
            state: nil)
        guard compression_stream_init(&stream, COMPRESSION_STREAM_DECODE, COMPRESSION_ZLIB) == COMPRESSION_STATUS_OK else {
            throw ZipError.inflate
        }
    }

    deinit {
        compression_stream_destroy(&stream)
        out.deallocate()
    }

    /// Devuelve cuántos bytes de entrada consumió y si el flujo deflate terminó.
    func process(_ src: UnsafePointer<UInt8>, _ count: Int,
                 sink: (UnsafePointer<UInt8>, Int) throws -> Void) throws -> (consumed: Int, ended: Bool) {
        stream.src_ptr = src
        stream.src_size = count
        while true {
            stream.dst_ptr = out
            stream.dst_size = cap
            let status = compression_stream_process(&stream, 0)
            let produced = cap - stream.dst_size
            if produced > 0 { try sink(out, produced) }
            if status == COMPRESSION_STATUS_END { return (count - stream.src_size, true) }
            if status == COMPRESSION_STATUS_ERROR { throw ZipError.inflate }
            if stream.src_size == 0 && stream.dst_size > 0 { return (count, false) }
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
                    throw ZipError.invalid("firma inesperada")
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
                    if r.ended { try finishEntry() }
                }

            case .descriptor:
                guard avail >= 4 else { return }
                let sigLen = (r32(pos) == 0x08074b50) ? 4 : 0
                let total = sigLen + 4 + (zip64 ? 16 : 8)
                guard avail >= total else { return }
                pos += total
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

        let dest = try safeURL(name)
        if name.hasSuffix("/") {
            try FileManager.default.createDirectory(at: dest, withIntermediateDirectories: true)
            state = .header
            return
        }
        if method == 0 && hasDescriptor && csize == 0 {
            throw ZipError.unsupported("archivo sin comprimir con data descriptor")
        }
        try FileManager.default.createDirectory(at: dest.deletingLastPathComponent(), withIntermediateDirectories: true)
        FileManager.default.createFile(atPath: dest.path, contents: nil)
        file = try FileHandle(forWritingTo: dest)
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
        try file?.write(contentsOf: Data(bytes: p, count: n))
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

    func start(url: URL, dest: URL) throws {
        extractor = try ZipStreamExtractor(root: dest)
        let queue = OperationQueue()
        queue.maxConcurrentOperationCount = 1
        let cfg = URLSessionConfiguration.ephemeral
        cfg.timeoutIntervalForRequest = 60
        cfg.timeoutIntervalForResource = 60 * 60 * 24
        session = URLSession(configuration: cfg, delegate: self, delegateQueue: queue)
        session!.dataTask(with: url).resume()
    }

    func cancel() { session?.invalidateAndCancel() }

    func urlSession(_ session: URLSession, dataTask: URLSessionDataTask, didReceive response: URLResponse,
                    completionHandler: @escaping (URLSession.ResponseDisposition) -> Void) {
        if let h = response as? HTTPURLResponse, !(200..<300).contains(h.statusCode) {
            failure = ZipError.invalid("el servidor respondió HTTP \(h.statusCode)")
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
            try w.start(url: url, dest: dest)
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

struct ContentView: View {
    @StateObject private var m = Model()

    var body: some View {
        VStack(alignment: .leading, spacing: 16) {
            Text("ZipStream").font(.largeTitle.bold())
            Text("Descarga un .zip y lo extrae sobre la marcha, sin guardar el zip. Deja la app abierta mientras trabaja.")
                .font(.subheadline).foregroundColor(.secondary)
            TextField("https://…/archivo.zip", text: $m.urlText)
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
