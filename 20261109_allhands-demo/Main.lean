import VersoSlides
import Slides

open VersoSlides

def main : IO UInt32 := do
  let config : Config := { center := false, margin := 0, theme := "white", slideNumber := true }
  let rc ← slidesMain (config := config) (doc := %doc Slides)
  let outputDir := config.outputDir
  let cssContents ← IO.FS.readFile "../static/custom.css"
  IO.FS.writeFile (outputDir / "custom.css") cssContents
  let logoBytes ← IO.FS.readBinFile "../static/lean-logo.png"
  IO.FS.writeBinFile (outputDir / "lean-logo.png") logoBytes
  let logoLargeBytes ← IO.FS.readBinFile "../static/lean-logo-large.png"
  IO.FS.writeBinFile (outputDir / "lean-logo-large.png") logoLargeBytes
  let htmlPath := outputDir / "index.html"
  let html ← IO.FS.readFile htmlPath
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\">\n    </head>"
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  let titleSlideOld := "<section><h2>Coherence of Type Classes in Lean</h2><p>Paul Reichert, Lean FRO</p><p>Lean FRO All-Hands, November 9, 2026</p></section>"
  let titleSlideNew := "<section class=\"title-slide\"><div class=\"top-area\"><img class=\"logo\" src=\"lean-logo-large.png\" alt=\"Lean Logo\"></div><div class=\"blue-band\"><h1>Coherence of Type Classes in Lean</h1><div class=\"meta\"><strong>Paul Reichert</strong><br>Lean FRO</div><div class=\"date\">Lean FRO All-Hands | November 9, 2026</div></div></section>"
  let html := html.replace titleSlideOld titleSlideNew
  let slideHeader := "<div class=\"slide-header\"><img src=\"lean-logo.png\" alt=\"Lean\"></div>"
  let html := html.replace "<section>" s!"<section>{slideHeader}"
  let html := html.replace "<section data-transition=\"fade\">" s!"<section data-transition=\"fade\">{slideHeader}"
  IO.FS.writeFile htmlPath html
  return rc
