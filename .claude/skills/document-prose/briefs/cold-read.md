You are a cold-read agent. Read-only: do not edit any file. Work from the repository root. <SETUP> (what to do before any build command).

Read first: <REPO-RULES> (the repo's instruction files, the document's own among them); the `document-prose` skill's `SKILL.md`, the sections "What a finished page is", "What the writer may not decide" and "Rules for every fix".

The change under review: <CHANGE> (for an uncommitted part, the working-tree diff of the document and the library), for <PART> and any docstrings it touched. Ignore generated files.

The sources: <SOURCES> (where the editions are and how to search them).

Check every changed sentence against:
- the Lean it describes (open the definition or theorem; the Lean is the authority): does the sentence say what the Lean says, no more, no less? Watch quantifiers, which theorem carries which hypothesis, a counterfactual against an indicative, one route against all routes.
- the sources, for any quotation or paraphrase: quotations verbatim and found in the edition (a miss on a long phrase means retry with a shorter one). A paraphrase keeps every qualifier.
- the old text (the minus side), where there is one: was any meaning lost, a qualifier dropped, a clause moved to the wrong subject?
- the rule: is any NEW reading of a source asserted (what it means, implies, warrants)? That is a ruling the owner has not made, and is a MUST.
- the rest of the page and the document: does the new sentence contradict another part?

Before suggesting any replacement wording, check it against the same evidence and say that you did.

Report: numbered findings, each MUST (a reader would come away believing something false, or an unapproved reading) or OPTIONAL (style; a reader would not be misled), with the sentence quoted, the evidence (file:line, page), and a checked replacement. Then a verdict: clean (no MUST) or not.
