// Draws the app icon, four suits on a green table: swift tools/icon.swift out.png.
// The PNG has an alpha channel, which the App Store refuses in an icon; tools/ios.sh
// flattens it with sips.
import AppKit

let size = 1024.0
let rep = NSBitmapImageRep(bitmapDataPlanes: nil, pixelsWide: 1024, pixelsHigh: 1024, bitsPerSample: 8,
                           samplesPerPixel: 4, hasAlpha: true, isPlanar: false, colorSpaceName: .deviceRGB,
                           bytesPerRow: 0, bitsPerPixel: 0)!
NSGraphicsContext.current = NSGraphicsContext(bitmapImageRep: rep)
NSColor(calibratedRed: 0.05, green: 0.42, blue: 0.24, alpha: 1).setFill()
NSRect(x: 0, y: 0, width: size, height: size).fill()
let card = NSRect(x: 182, y: 152, width: 660, height: 720)
NSColor.white.setFill()
NSBezierPath(roundedRect: card, xRadius: 70, yRadius: 70).fill()
let suits: [(String, NSColor, CGFloat, CGFloat)] = [
    ("♠", .black, 352, 512), ("♥", NSColor(calibratedRed: 0.8, green: 0.1, blue: 0.12, alpha: 1), 672, 512),
    ("♦", NSColor(calibratedRed: 0.8, green: 0.1, blue: 0.12, alpha: 1), 352, 192), ("♣", .black, 672, 192),
]
for (s, color, cx, y) in suits {
    let attrs: [NSAttributedString.Key: Any] = [.font: NSFont.systemFont(ofSize: 300), .foregroundColor: color]
    let str = NSAttributedString(string: s, attributes: attrs)
    let w = str.size().width
    str.draw(at: NSPoint(x: cx - w / 2, y: y))
}
NSGraphicsContext.current?.flushGraphics()
try! rep.representation(using: .png, properties: [:])!.write(to: URL(fileURLWithPath: CommandLine.arguments[1]))
