/-
Eleventy emitter: replaces Verso's final page layer.

Verso's `emitHtmlMulti` walks the traversed document and writes one
complete HTML page per part, wrapping each in a fixed skeleton
(`VersoManual.Html.page`: header, ToC sidebar, main). That skeleton is
not parameterized, so a site with its own chrome cannot reuse it.

This module mirrors the walk (`emitHtmlMulti.emitContent` / `emitPart`,
Verso v4.32.0) but writes the pieces an Eleventy consumer assembles:

  <out>/pages/<path>.html   one HTML fragment per page (no skeleton)
  <out>/pages.json          one record per page: url, title, section
                            number, local ToC, prev/next, fragment path
  <out>/toc.json            the book's table of contents as a tree
  <out>/assets.json         which files under verso-data/ each page loads
  <out>/verso-data/         Verso's feature files (KaTeX, tippy, popper)
  <out>/verso-vars.css      Verso's CSS variables (fonts, colours)
  <out>/verso-inline.css    the CSS Verso would inline in every <head>
  <out>/verso-inline.js     the JS Verso would inline in every <head>
  <out>/verso-docs.json     hover docstrings, fetched by verso-inline.js

Links inside the fragments are root-absolute (`/The-Result/Axioms/#id`),
as Verso produces them; the consumer serves the pages at those paths.
-/
import VersoManual

open Lean (Name NameMap Json ToJson)
open Verso.FS
open Verso.Doc
open Verso.Multi (Path AllRemotes updateRemotes)
open Verso.Code (LinkTargets)
open Verso.Code.Hover (Dedup State)
open Verso.Output (Html)
open Verso.Output.Html
open Verso.Genre (Manual)
open Verso.Genre.Manual
open Verso.Genre.Manual.Html (Toc)

set_option autoImplicit false

namespace ApodicticDoc.Emit

/-- The monad Verso's `GenreHtml Manual` instance renders in, plus the
hover-docstring dedup state. Same stack as `emitHtmlMulti.emitContent`. -/
abbrev EleventyM := StateT (State Html) (ReaderT AllRemotes (ReaderT ExtensionImpls (Verso.BuildLogT IO)))

/-- Plain text of an HTML fragment (tags stripped), for titles. -/
partial def htmlText : Html → String
  | .text _ s => s
  | .seq es => String.join (es.toList.map htmlText)
  | .tag _ _ e => htmlText e

def render (html : Html) : String := html.asString (breakLines := false)

partial def tocJson : Toc → Json
  | { title, shortTitle, path, id, sectionNum, children } =>
    Json.mkObj [
      ("title", Json.str (render title)),
      ("titleText", Json.str (htmlText title)),
      ("shortTitle", shortTitle.map (Json.str ∘ render) |>.getD Json.null),
      ("path", Json.arr (path.map Json.str)),
      ("url", Json.str (path.link)),
      ("id", id.map Json.str |>.getD Json.null),
      ("sectionNum", sectionNum.map (Json.str ∘ sectionNumberString) |>.getD Json.null),
      ("children", Json.arr (children.toArray.map tocJson))
    ]

def localItemJson (item : LocalContentItem) : Json :=
  have := item.linkTexts_nonempty
  Json.mkObj [
    ("dest", Json.str item.dest),
    ("html", Json.str (render item.linkTexts[0].2)),
    ("level", item.header?.map (fun h => Json.num h.level) |>.getD Json.null),
    ("numbering", item.header?.bind (·.numbering) |>.map Json.str |>.getD Json.null)
  ]

/-- Drop ToC entries that have no page of their own (Verso's
`Toc.onlyPages`, which is not exported). -/
partial def onlyPages (toc : Toc) : Toc :=
  {toc with children := toc.children.filter (·.path.size > toc.path.size) |>.map onlyPages}

/-- prev/next pages in reading order, from the book ToC. -/
def neighbours (bookToc : Toc) (path : Path) : Option Toc × Option Toc :=
  let z := Toc.Zipper.followPath (onlyPages bookToc) path
  (z.bind Toc.Zipper.prev |>.map (·.focus), z.bind Toc.Zipper.next |>.map (·.focus))

def neighbourJson : Option Toc → Json
  | none => Json.null
  | some t =>
    Json.mkObj [
      ("url", Json.str (t.path.link t.id)),
      ("title", Json.str (render t.title)),
      ("titleText", Json.str (htmlText t.title)),
      ("sectionNum", t.sectionNum.map (Json.str ∘ sectionNumberString) |>.getD Json.null)
    ]

/-- The list of files each page must load, relative to `verso-data/`.
Mirrors the head of `VersoManual.Html.page`. -/
def assetsJson (state : TraverseState) : Json :=
  let extraJsFiles :=
    sortJs (state.extraJsFiles.toArray.map (false, ·.toStaticJsFile))
      |>.map fun (_, f) => (f.filename, f.defer)
  let featureJs := state.features.toArray.flatMap (·.jsFilePaths)
  let css :=
    state.extraCssFiles.toArray.map (·.filename) ++
    state.features.toArray.flatMap (·.cssFilePaths)
  Json.mkObj [
    ("css", Json.arr (css.map Json.str)),
    ("js", Json.arr ((featureJs ++ extraJsFiles).map fun (src, defer) =>
      Json.mkObj [("src", Json.str src), ("defer", Json.bool defer)]))
  ]

/-- Emit one part's page (and its children's, while `depth` allows),
returning the page records in reading order. Mirrors `emitPart`. -/
partial def emitPart (out : System.FilePath) (config : Config) (state : TraverseState)
    (bookToc : Toc) (authors : List String) (authorshipNote : Option String)
    (opts : Verso.Doc.Html.Options) (ctxt : TraverseContext)
    (definitionIds : NameMap String) (linkTargets : LinkTargets TraverseContext)
    (root : Bool) (depth : Nat) (part : Part Manual) : EleventyM (Array Json) := do
  let toHtml {α} [Verso.Doc.Html.ToHtml Manual (ReaderT AllRemotes (ReaderT ExtensionImpls (Verso.BuildLogT IO))) α]
      (opts : Verso.Doc.Html.Options) (ctxt : TraverseContext) (x : α) : EleventyM Html :=
    Manual.toHtml opts ctxt state definitionIds linkTargets {} x
  -- `sectionHtml` yields a lone space at the root (empty number + " ").
  let sectionNum : Html := match sectionString ctxt with
    | some s => if s.isEmpty then .empty else .text true (s ++ " ")
    | none => .empty
  let pageTitleHtml := sectionNum ++ (← Html.seq <$> part.title.mapM (toHtml opts ctxt))
  let titleHtml :=
    pageTitleHtml ++
    if let some id := part.metadata.bind (·.id) then permalink id state else .empty
  let introHtml ← Html.seq <$> part.content.mapM (toHtml opts ctxt)
  let leaf := depth == 0 || part.htmlSplit == .never
  let contents ←
    if leaf then
      Html.seq <$> part.subParts.mapM (fun p => toHtml {opts with headerLevel := 2} (ctxt.inPart p) p)
    else pure .empty
  let includeSubparts := if leaf then .all else .depth 0
  let localItems : Array LocalContentItem ← do
    let (errs, items) ← localContents opts ctxt state (includeTitle := false) (includeSubparts := includeSubparts) part
    for e in errs do Verso.reportError e
    pure items
  -- Same fallback as Verso: a local ToC with only headers is dropped.
  let localItems := if localItems.filter (·.header?.isNone) |>.isEmpty then #[] else localItems
  let subToc ← part.subParts.mapM (fun p => toc depth opts (ctxt.inPart p) state definitionIds linkTargets p)
  let pageContent : Html :=
    if root then
      let subTocHtml := if subToc.size > 0 then {{
          <section>
          <h2>"Contents"</h2>
          <ol class="section-toc">{{subToc.map (·.html config.rootTocDepth)}}</ol>
          </section>
        }}
      else .empty
      {{<section>{{Html.titlePage titleHtml authors authorshipNote introHtml ++ contents}} {{subTocHtml}}</section>}}
    else
      let subTocHtml :=
        if (depth > 0 && part.htmlSplit != .never) && subToc.size > 0 && part.htmlToc then
          {{<ol class="section-toc">{{subToc.map (·.html config.sectionTocDepth)}}</ol>}}
        else .empty
      {{<section><h1>{{titleHtml}}</h1> {{introHtml}} {{contents}} {{subTocHtml}}</section>}}

  let fragment : System.FilePath :=
    if ctxt.path.isEmpty then "pages/index.html"
    else "pages" / (String.intercalate "/" ctxt.path.toList ++ ".html")
  if let some dir := (out / fragment).parent then IO.FS.createDirAll dir
  IO.FS.writeFile (out / fragment) (render pageContent)

  let (prev, next) := neighbours bookToc ctxt.path
  let record := Json.mkObj [
    ("path", Json.arr (ctxt.path.map Json.str)),
    ("url", Json.str ctxt.path.link),
    ("id", part.metadata.bind (·.id) |>.bind (state.externalTags[·]?) |>.map (Json.str ∘ toString ∘ (·.htmlId)) |>.getD Json.null),
    ("title", Json.str (render pageTitleHtml)),
    ("titleText", Json.str part.titleString),
    ("sectionNum", sectionString ctxt |>.map Json.str |>.getD Json.null),
    ("depth", Json.num ctxt.path.size),
    ("fragment", Json.str fragment.toString),
    ("localToc", Json.arr (localItems.map localItemJson)),
    ("prev", neighbourJson prev),
    ("next", neighbourJson next)
  ]

  let mut records := #[record]
  if depth > 0 ∧ part.htmlSplit != .never then
    for p in part.subParts do
      let nextFile := p.metadata.bind (·.file) |>.getD (p.titleString.sluggify.toString)
      let ctxt' := {ctxt with path := ctxt.path.push nextFile}.inPart p
      records := records ++ (← emitPart out config state bookToc authors authorshipNote opts ctxt' definitionIds linkTargets false (depth - 1) p)
  return records

/-- Rewrite the one root-relative URL Verso's inline JS hardcodes. The
consumer sets `window.VERSO_ROOT` (e.g. `"/verso/"`) before loading it. -/
def patchInlineJs (js : String) : String :=
  js.replace "fetch(\"-verso-docs.json\")" "fetch(window.VERSO_ROOT + \"verso-docs.json\")"

def emitAll (out : System.FilePath) (config : Config) (text : Part Manual) (state : TraverseState) : EleventyM Unit := do
  let «meta» : Option PartMetadata := text.metadata
  let authors := meta.map (·.authors) |>.getD []
  let authorshipNote := meta.bind (·.authorshipNote)
  let opts : Verso.Doc.Html.Options := {}
  let ctxt : TraverseContext := {}
  let definitionIds := state.definitionIds ctxt
  let linkTargets := state.localTargets ++ (← readThe AllRemotes).remoteTargets
  let chapters ← text.subParts.toList.mapM fun p =>
    toc config.htmlDepth opts (ctxt.inPart p) state definitionIds linkTargets p
  let titleHtml ← Html.seq <$> text.title.mapM (Manual.toHtml opts ctxt state definitionIds linkTargets {} ·)
  let bookToc : Toc := { title := titleHtml, path := #[], id := none, sectionNum := some #[], children := chapters }

  ensureDir out
  state.writeFiles (out / "verso-data")
  -- Source maps are not served; keep the committed tree small.
  for f in (← System.FilePath.walkDir (out / "verso-data")) do
    if f.extension == some "map" then IO.FS.removeFile f
  IO.FS.writeFile (out / "verso-vars.css") Verso.Output.Html.«verso-vars.css»
  let css := state.extraCss.toArray.map (·.css) |>.qsort (· < ·)
  IO.FS.writeFile (out / "verso-inline.css") (String.intercalate "\n" css.toList)
  let js := state.extraJs.toArray.map (·.js) |>.qsort (· < ·)
  IO.FS.writeFile (out / "verso-inline.js") (patchInlineJs (String.intercalate "\n" js.toList))
  IO.FS.writeFile (out / "assets.json") (assetsJson state).pretty
  IO.FS.writeFile (out / "toc.json") (Json.mkObj [
    ("title", Json.str (render titleHtml)),
    ("titleText", Json.str text.titleString),
    ("authors", Json.arr (authors.toArray.map Json.str)),
    ("children", Json.arr (chapters.toArray.map tocJson))
  ]).pretty

  let pages ← emitPart out config state bookToc authors authorshipNote opts ctxt definitionIds linkTargets true config.htmlDepth text
  IO.FS.writeFile (out / "pages.json") (Json.arr pages).pretty

/-- Traverse the document once and write the Eleventy input tree. The
replacement for `manualMain`: Verso's own page emitters do not run. -/
def eleventyMain (text : Part Manual) (impls : ExtensionImpls) (out : System.FilePath)
    (config : Config := {}) : IO UInt32 :=
  Verso.runWithLogger <| flip ReaderT.run impls do
    let (text', state) ← traverse text config
    let remotes ← updateRemotes false config.remoteConfigFile (fun _ => pure ())
    let ((), htmlState) ← emitAll out config text' state |>.run .empty |>.run remotes
    IO.FS.writeFile (out / "verso-docs.json") (toString htmlState.dedup.docJson)

end ApodicticDoc.Emit
