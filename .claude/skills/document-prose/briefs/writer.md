You are the writer for one part of a document that explains machine-checked proofs. Work from the repository root. <SETUP> (what to do before any build command).

READ FIRST, in full:
- <REPO-RULES> (the repo's instruction files, the document's own among them)
- the `document-prose` skill's `SKILL.md`: every section. "What a finished page is" is your target. "What the writer may not decide" and "Rules for every fix" bind you.
- <MODEL-PAGE>

THE PART: <PART> (the file, and where the part starts and ends).

THE SOURCES: <SOURCES> (where the editions are and how to search them). Verify every quotation you add there before writing it. A miss on a long phrase means retry with a shorter one, never that the quotation is absent.

YOUR JOB is one of two. The main session says which.

A. DRAFT the part. <WHAT-IS-RULED> lists the theorems it covers and what the owner has already decided about them. Write only from that, the Lean, and the sources quoted. Pick the running example first. Open each definition and theorem before writing the sentence about it. Take each theorem's premises from its signature.

B. FIX the reader's flags, in <FLAGS>. The reader saw only the rendered page text, not the Lean. Classify each flag, with evidence (the Lean is the authority; open what the sentence describes before judging):
   - REAL: the page as written does stall a reader, and a fix exists inside the rules.
   - REAL-CROSS-PART: the term or result is explained in another part. Fix with a link or by naming the part. Never a second explanation. A term defined once for the whole document gets the one-line pointer, at most once a page.
   - FALSE: the page already gives the ground, or the flag misreads it. Say where.
   - OWNER: the fix would change something reserved to the owner. Do NOT fix; log it.
   - POLISH: optional; a reader would not come away believing something false. Do not fix; list it.
   Then fix the REAL ones.

IN BOTH JOBS:
1. KEY RULE. The ground of a "so"/"only"/"never"/"needs it" step may come ONLY from (a) the part's existing text, (b) another part of the document, (c) a docstring, or (d) the Lean itself, stated as what the Lean does (which theorem carries which hypothesis, which definition says what). A ground that would be a new reading of a source (what it means, implies, warrants, or why it says it) is OWNER. Log rather than invent.
2. For each sentence you write or change about the Lean or a source, name the file:line or page you checked it against, in your report.
3. Docstrings: you may reword a docstring this part shows, under the same rules and the repo's own rules for docstrings. <RESERVED> names what you may not edit, or may edit only to a wording <WHAT-IS-RULED> gives verbatim. Write any other proposed rewording there to <PROPOSALS>, each with the flag or reason it answers.
4. In job B, <FIXED> stays unchanged, in the same order. Check with a script (the lists before and after are identical) and report it.
5. Gate: <GATE> (the command, and what a passing run prints). The pages it lists as text-changed must be this part's page, and another page only if it shows a changed docstring; say which.
6. Do NOT commit. Do not touch any other part's prose.

REPORT (final message): in job A, the running example and why, and per theorem the signature you wrote to. In job B, per flag: its class, the evidence (file:line), and the fix as before → after text. In both: the OWNER items, each stated so the owner can rule (the sentence, what the change would assert, why it is a ruling); the POLISH items; the proposals file if any; the check of what stays fixed; the gate's last lines.
