import VersoSlides
import Deck

open VersoSlides

def staticDir : System.FilePath := "/root/presentations/static"

def main : IO UInt32 := do
  let config : Config :=
    { theme := "white", slideNumber := true, transition := "none", center := false, margin := 0 }
  let rc ← slidesMain (config := config) (doc := %doc Deck)
  let outputDir := config.outputDir
  let cssContents ← IO.FS.readFile (staticDir / "custom.css")
  let overrideContents ← IO.FS.readFile "overrides.css"
  IO.FS.writeFile (outputDir / "custom.css") (cssContents ++ "\n" ++ overrideContents)
  for name in #["lean-logo.png", "lean-logo-large.png"] do
    let bytes ← IO.FS.readBinFile (staticDir / name)
    IO.FS.writeBinFile (outputDir / name) bytes
  let htmlPath := outputDir / "index.html"
  let html ← IO.FS.readFile htmlPath
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\">\n    </head>"
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  let titleSlideOld := "<section>\n          <h2>\n            Instance Assignment Failures</h2>\n          <p>\n            Paul Reichert</p>\n          <p>\n            2026-08-26</p>"
  let titleSlideNew := "<section class=\"title-slide\">\n          <div class=\"top-area\"><img class=\"logo\" src=\"lean-logo-large.png\" alt=\"Lean Logo\"></div>\n          <div class=\"blue-band\"><h1>Instance Assignment Failures</h1>\n          <div class=\"subtitle\">Ten failure modes from Mathlib</div>\n          <div class=\"meta\"><strong>Paul Reichert</strong><br>Lean FRO</div>\n          <div class=\"date\">2026-08-26</div>\n          </div>"
  let html := html.replace titleSlideOld titleSlideNew
  let slideHeader := "<div class=\"slide-header\"><img src=\"lean-logo.png\" alt=\"Lean\"></div>"
  let html := html.replace "<section>\n" s!"<section>\n          {slideHeader}\n"
  let html := html.replace "<section data-transition=\"fade\">\n"
    s!"<section data-transition=\"fade\">\n          {slideHeader}\n"
  IO.FS.writeFile htmlPath html
  return rc
