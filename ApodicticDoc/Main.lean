import VersoManual
import ApodicticDoc
import ApodicticDoc.Emit.Eleventy

open Verso.Genre.Manual

/-- `generate-doc [--output DIR]` writes the Eleventy input tree for the
document (default `_out/eleventy`). Verso's own HTML is not produced;
the site under `site/` assembles the pages. -/
def main (args : List String) : IO UInt32 := do
  let out ← match args with
    | [] => pure "_out/eleventy"
    | ["--output", dir] => pure dir
    | _ =>
      IO.eprintln "usage: generate-doc [--output DIR]"
      return 1
  -- No math in the document and no Verso search on the site, so neither
  -- KaTeX (1.4 MB of fonts) nor the search assets are emitted.
  ApodicticDoc.Emit.eleventyMain (%doc ApodicticDoc) extension_impls% out
    (config := { features := .empty })
