#!/bin/sh
# tools/ios.sh: the iOS app (ios/), the web app in a WKWebView, for iPhone and iPad.
#
#   tools/ios.sh web       build the page (tools/web.sh build), copy it to ios/web, and
#                          regenerate the Xcode project
#   tools/ios.sh sim [device]  web, then build and run the app in a simulator
#                          ("iPhone 18 Pro" by default)
#   tools/ios.sh archive   web, then archive a signed Release build to ios/build
#   tools/ios.sh upload    archive, then upload it to App Store Connect for TestFlight
#
# Needs Xcode, xcodegen (brew install xcodegen) and what tools/web.sh needs. Signing is
# automatic, for the team in ios/project.yml, with the Apple ID signed in to Xcode.
# Each solver worker reserves a 512 MB heap, most of it for the runtime's lanes, and
# iOS ends the page's process when they add up to too much, so the app caps the
# number of workers by the device's memory (ios/DoubleDummy/SolverView.swift).
# Each upload needs a new build number: CURRENT_PROJECT_VERSION, which this sets to
# the time of the build unless BUILD is given.

set -e
cd "$(dirname "$0")/.."
PATH="$HOME/.bend/bin:$PATH"

W=ios/web
BUILD=${BUILD:-$(date -u +%Y%m%d.%H%M)}

web() {
  tools/web.sh build
  rm -rf $W && cp -R web/dist $W
  (cd ios && xcodegen generate --quiet)
}

case "$1" in
  web)
    web
    ;;
  sim)
    web
    device=${2:-iPhone 18 Pro}
    xcodebuild -project ios/DoubleDummy.xcodeproj -scheme DoubleDummy -configuration Debug \
      -destination "platform=iOS Simulator,name=$device" -derivedDataPath ios/build/sim -quiet build
    xcrun simctl boot "$device" 2>/dev/null || true
    open "$(xcode-select -p)/Applications/Simulator.app" 2>/dev/null || true
    xcrun simctl install "$device" "ios/build/sim/Build/Products/Debug-iphonesimulator/Double Dummy.app"
    xcrun simctl launch "$device" co.formnerd.doubledummy
    ;;
  archive|upload)
    web
    xcodebuild -project ios/DoubleDummy.xcodeproj -scheme DoubleDummy -configuration Release \
      -destination "generic/platform=iOS" -archivePath ios/build/DoubleDummy.xcarchive \
      -allowProvisioningUpdates CURRENT_PROJECT_VERSION=$BUILD -quiet archive
    echo "archived build $BUILD: ios/build/DoubleDummy.xcarchive"
    if [ "$1" = upload ]; then
      xcodebuild -exportArchive -archivePath ios/build/DoubleDummy.xcarchive \
        -exportOptionsPlist ios/ExportOptions.plist -exportPath ios/build/export \
        -allowProvisioningUpdates
      echo "uploaded build $BUILD; it shows in TestFlight once App Store Connect has processed it"
    fi
    ;;
  *)
    sed -n '2,16p' "$0" | sed 's/^# \{0,1\}//'
    exit 1
    ;;
esac
