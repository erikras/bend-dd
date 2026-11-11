import SwiftUI
import WebKit

// The web app (web/src, built by tools/web.sh into ios/web) in a WKWebView. Its
// files are served from the app bundle under app://local/, so that the page, its
// module workers and the solver's WebAssembly load as they do over https.
struct SolverView: UIViewRepresentable {
    func makeUIView(context: Context) -> WKWebView {
        let config = WKWebViewConfiguration()
        config.setURLSchemeHandler(BundleSchemeHandler(), forURLScheme: BundleSchemeHandler.scheme)
        config.userContentController.addUserScript(WKUserScript(
            source: "window.ddNative = { maxWorkers: \(Self.maxWorkers()) };",
            injectionTime: .atDocumentStart, forMainFrameOnly: true))
        let view = WKWebView(frame: .zero, configuration: config)
        view.isOpaque = false
        view.backgroundColor = Self.paper
        view.scrollView.backgroundColor = Self.paper
        view.scrollView.contentInsetAdjustmentBehavior = .automatic
        view.allowsBackForwardNavigationGestures = false
        view.navigationDelegate = context.coordinator
        #if DEBUG
        view.isInspectable = true
        #endif
        // DD_PAGE (simctl launch with SIMCTL_CHILD_DD_PAGE) opens another page of the
        // bundle, for checks like the one in tools/ios.sh.
        let page = ProcessInfo.processInfo.environment["DD_PAGE"] ?? "index.html"
        view.load(URLRequest(url: URL(string: "\(BundleSchemeHandler.scheme)://local/\(page)")!))
        return view
    }

    // The page's background, --bg in web/src/style.css.
    static let paper = UIColor(red: 0xf6 / 255.0, green: 0xf4 / 255.0, blue: 0xef / 255.0, alpha: 1)

    func updateUIView(_ view: WKWebView, context: Context) {}

    func makeCoordinator() -> Coordinator { Coordinator() }

    // Each solver worker holds its own WebAssembly memory of about 530 MB, and WebKit
    // caps what a page's memories add up to (5 of them in the simulator; less on a
    // phone, where 8 workers in Safari ended the page). So the app runs 2 workers on
    // a phone with less than 7 GB, 3 on a larger phone, and 4 on an iPad with 12 GB
    // or more. The page uses at least 2.
    static func maxWorkers() -> Int {
        let gb = Double(ProcessInfo.processInfo.physicalMemory) / 1_073_741_824
        let cores = ProcessInfo.processInfo.activeProcessorCount
        let pad = UIDevice.current.userInterfaceIdiom == .pad
        let byMemory = gb < 7 ? 2 : (pad && gb >= 11) ? 4 : 3
        return max(2, min(byMemory, cores - 1))
    }

    final class Coordinator: NSObject, WKNavigationDelegate {
        #if DEBUG
        // DD_EVAL (SIMCTL_CHILD_DD_EVAL) runs a script once the page has loaded, to
        // drive it in the simulator without taps.
        func webView(_ webView: WKWebView, didFinish navigation: WKNavigation!) {
            if let script = ProcessInfo.processInfo.environment["DD_EVAL"] {
                webView.evaluateJavaScript(script)
            }
        }
        #endif

        // Links out of the app open in Safari.
        func webView(_ webView: WKWebView, decidePolicyFor action: WKNavigationAction,
                     decisionHandler: @escaping (WKNavigationActionPolicy) -> Void) {
            if let url = action.request.url, url.scheme == "http" || url.scheme == "https" {
                UIApplication.shared.open(url)
                decisionHandler(.cancel)
            } else {
                decisionHandler(.allow)
            }
        }

        // iOS may end the page's process to reclaim memory, most likely mid-simulation.
        // Reload rather than leave a blank screen.
        func webViewWebContentProcessDidTerminate(_ webView: WKWebView) {
            webView.reload()
        }
    }
}

final class BundleSchemeHandler: NSObject, WKURLSchemeHandler {
    static let scheme = "app"
    private let root = Bundle.main.resourceURL!.appendingPathComponent("web")

    func webView(_ webView: WKWebView, start task: WKURLSchemeTask) {
        guard let url = task.request.url else { return }
        var path = url.path
        if path.isEmpty || path == "/" { path = "/index.html" }
        let file = root.appendingPathComponent(String(path.dropFirst())).standardizedFileURL
        guard file.path.hasPrefix(root.standardizedFileURL.path),
              let data = try? Data(contentsOf: file) else {
            task.didReceive(HTTPURLResponse(url: url, statusCode: 404, httpVersion: "HTTP/1.1", headerFields: [:])!)
            task.didFinish()
            return
        }
        let headers = [
            "Content-Type": Self.mime(file.pathExtension),
            "Content-Length": String(data.count),
            "Cache-Control": "no-cache",
        ]
        task.didReceive(HTTPURLResponse(url: url, statusCode: 200, httpVersion: "HTTP/1.1", headerFields: headers)!)
        task.didReceive(data)
        task.didFinish()
    }

    func webView(_ webView: WKWebView, stop task: WKURLSchemeTask) {}

    static func mime(_ ext: String) -> String {
        switch ext {
        case "html": return "text/html; charset=utf-8"
        case "js", "mjs": return "text/javascript; charset=utf-8"
        case "css": return "text/css; charset=utf-8"
        case "wasm": return "application/wasm"
        case "json": return "application/json"
        case "png": return "image/png"
        case "svg": return "image/svg+xml"
        default: return "application/octet-stream"
        }
    }
}
