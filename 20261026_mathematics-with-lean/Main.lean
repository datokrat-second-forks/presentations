import VersoSlides
import Slides

open VersoSlides

def staticDir : System.FilePath := "../static"

/-- Images referenced from raw `html` blocks, which verso-slides does not copy by itself. -/
def puzzleImages : Array String :=
  #["puzzle-1-in-isolation.webp", "puzzle-2-in-the-bigger-picture.webp",
    "puzzle-3-where-it-belongs.webp"]

def main : IO UInt32 := do
  let config : Config :=
    { theme := "white", slideNumber := true, transition := "none", center := false, margin := 0 }
  let rc ← slidesMain (config := config) (doc := %doc Slides)
  let outputDir := config.outputDir
  let cssContents ← IO.FS.readFile (staticDir / "custom.css")
  let overrideContents ← IO.FS.readFile "overrides.css"
  IO.FS.writeFile (outputDir / "custom.css") (cssContents ++ "\n" ++ overrideContents)
  for name in #["lean-logo.png", "lean-logo-large.png"] do
    let bytes ← IO.FS.readBinFile (staticDir / name)
    IO.FS.writeBinFile (outputDir / name) bytes
  IO.FS.createDirAll (outputDir / "images")
  for name in puzzleImages do
    let bytes ← IO.FS.readBinFile ("static/images" / name)
    IO.FS.writeBinFile (outputDir / "images" / name) bytes
  let htmlPath := outputDir / "index.html"
  let html ← IO.FS.readFile htmlPath
  let html := html.replace "</head>" "<link rel=\"stylesheet\" href=\"custom.css\">\n    </head>"
  -- Fetch the puzzle images when the deck opens, so that they do not first appear as a blank
  -- stage when their fragments are shown.
  let preloads := puzzleImages.foldl (init := "") fun acc name =>
    acc ++ s!"<link rel=\"preload\" as=\"image\" href=\"images/{name}\">\n    "
  let html := html.replace "</head>" (preloads ++ "</head>")
  let html := html.replace "Reveal.initialize({" "Reveal.initialize({\n        disableLayout: true,"
  let titleSlideOld := "<section><h2>Mathematics with Lean</h2><p>Paul Reichert</p>"
  let titleSlideNew := "<section class=\"title-slide\"><div class=\"top-area\"><img class=\"logo\" src=\"lean-logo-large.png\" alt=\"Lean Logo\"></div><div class=\"blue-band\"><h1>Mathematics with Lean</h1><div class=\"subtitle\">Proof Mechanization as a Research Tool</div><div class=\"meta\"><strong>Paul Reichert</strong><br>Research Software Engineer, Lean FRO</div></div>"
  unless html.contains titleSlideOld do
    throw <| IO.userError "title slide markup changed; update `titleSlideOld` in Main.lean"
  let html := html.replace titleSlideOld titleSlideNew
  -- Add the logo header to every slide except the title slide.
  let slideHeader := "<div class=\"slide-header\"><img src=\"lean-logo.png\" alt=\"Lean\"></div>"
  let html := match html.splitOn "<section" with
    | [] => html
    | first :: rest => rest.foldl (init := first) fun acc part =>
      match part.splitOn ">" with
      | attrs :: body =>
        if attrs.contains "title-slide" then acc ++ "<section" ++ part
        else acc ++ "<section" ++ attrs ++ ">" ++ slideHeader ++ ">".intercalate body
      | [] => acc ++ "<section" ++ part
  IO.FS.writeFile htmlPath html
  return rc
