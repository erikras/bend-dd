import SwiftUI

@main
struct DoubleDummyApp: App {
    var body: some Scene {
        WindowGroup {
            SolverView()
                .ignoresSafeArea(.container, edges: .bottom)
                .background(Color(SolverView.paper).ignoresSafeArea())
                .preferredColorScheme(.light)
        }
    }
}
