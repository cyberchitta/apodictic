# The document's prose — what is specific here

The `document-prose` skill holds the rules for any page and its two
reads. This file is what this document adds. It also holds what goes in
the placeholders of the skill's briefs.

## Where things are

- The document is `ApodicticDoc/ApodicticDoc/Result.lean`. A part runs
  from its `# ` heading to the next one.
- A part's generated page is
  `site/verso/pages/The-Result/<Part>.html`; the front page is
  `site/verso/pages/The-Result.html`.
- The source editions are in the lab notebook. The session's private
  instructions say where, and how to search the extraction. A brief's
  `<SOURCES>` is filled from those.
- Before any `lake` command: `export PATH="$HOME/.elan/bin:$PATH"`,
  and run it from the package's own directory.

## The gate

`/opt/homebrew/bin/bash ApodicticDoc/doc-gate.sh`

It builds the library with its lint, the draft library, the isolation
check and the draft again, then the document. It regenerates
`site/verso`, checks quotations and builds the site. It ends
`GATE fail=0` and lists the pages whose visible text differs from
`HEAD`. `Classical.choice` outside the consistency ledger fails it.
Read what the library step prints: a warning there does not change
the exit status.

## Wording

- A premise is a *claim* (a universal claim about action) or a
  *condition* (a situational hypothesis). The page says which. Each is
  named in prose with its Lean name in brackets.
- "Claim" has that sense only. The lender's instrument is a "promise".
- Preference is ordinal in the wording too: "preferred to", never
  "worth more".
- The sources are Mises and Rothbard. The running example is theirs
  where they give one.
- `bun run verify` in `site/` bans some retired terms. A fix can
  reintroduce one.

## Markup

- Bold is `*x*`, not `**x**`. A literal `[` is written `\[`.
- Flat bullets only. No nested lists and no numbered lists.
- A part is linked with `{ref "tag"}[text]`. A part gets a tag with a
  `%%% tag %%%` block; `rg -n '%%%'` on the document lists them. Adding
  a tag changes heading anchors, not page URLs.
- The common terms (library, docstring, signature, linter, frame,
  vocabulary) are defined under *Terms* on *The Result*, the front
  page.

## Fixed through a rewrite

The `{docstring X}` directives and their order, and the `lean` and
`leanOutput` blocks.

## A changed title

It changes the page's URL. The published article deep-links page URLs,
so its links are updated. `generate-doc` does not delete the old page.

## The model page

Not chosen yet.

## The record

One line a part in the worklist, with what was read and what was taken
on an agent's word. The human's items go to an ask. Polish left for a
part's next pass goes in the lab notebook.

## For the briefs

- `<RESERVED>`: what the root `CLAUDE.md` reserves to the human, and
  its rule for `Praxeology.lean`.

- `<WHAT-THE-DOCUMENT-IS>`: a document that audits Austrian economics
  (Mises, Rothbard) with a proof assistant.
- `<COMMON-TERMS>`: Terms such as library, docstring, signature,
  linter, frame and vocabulary are defined once on the front page
  (*The Result*, under *Terms*).
