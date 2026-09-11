#!/usr/bin/env python3
"""Report repeated eight-word runs across the emitted doc-site pages.

The ruling this serves is the human's: no duplication of text across pages.
The trouble is that a naive n-gram check over the emitted HTML reports mostly
noise, and the noise buries the signal. Measured 2026-09-11, the site had 181
repeated eight-word runs across pages, of which only 43 were text anyone
wrote twice.  See _notes/2026-09-11-duplication-is-structural.md.

So this script sorts every repeat into three buckets and reports them apart:

  SIGNATURES   emitted Lean identifiers -- "praxis actionframe agent praxis
               agent time praxis time stock" and the like.  Repeats wherever
               the same {docstring} renders.  Not text.  Not fixable.  The
               printed output of a command (`#manifest`, rendered as a
               `lean-output` block) is filed the same way: the compiler
               wrote it, and two theorems' manifests share their furniture.

  QUOTATIONS   words of Mises or Rothbard.  A summary page and a claim's
               pedigree BOTH have to cite the sentence they are about; a rule
               that forbade this would forbid the document from quoting its
               own subject.  Not fixable, and should not be.

  OURS         our own phrasing, written twice.  This is the only bucket that
               is a defect, and the only one whose count should be driven to
               zero.

Two mechanics are load-bearing and were each got wrong once:

  - Docstrings render as NESTED divs, so carving them out with a non-greedy
    regex silently mis-attributes a whole docstring as prose -- which reported
    the document's largest overlap as our-prose-vs-our-prose when it was
    prose-vs-docstring.  The walker below tracks depth.
  - The renderer splits words across <span> elements, so stripping tags and
    searching the resulting STRING misses matches that are really there.
    Compare word streams, never strings.

Known limitation, found by red-testing this script: a run is filed under
SIGNATURES when it contains no stopword at all, so a duplicated run of our own
prose made entirely of content words ("zebra mango trellis quorum vellum
kestrel obsidian parapet") is misfiled and not reported.  English prose with
eight consecutive content words is rare enough to accept; if the OURS count
ever looks implausibly low, check the SIGNATURES bucket by eye.

Usage:  python3 site/check-duplication.py [--show ours|quotations|signatures]

Exits 1 if the OURS bucket is non-empty, 0 otherwise.  Signatures and
quotations never fail the build.
"""

import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PAGES = os.path.join(ROOT, "site", "verso", "pages")
N = 8

# Sources that authored the prose and the docstrings.  Quoted spans are
# lifted from these rather than from the HTML, because quotation marks are
# what mark a quotation and the emitted page does not preserve them reliably.
AUTHORED = [
    "ApodicticDoc/ApodicticDoc/Result.lean",
    "Apodictic/Apodictic/Praxeology.lean",
    "Apodictic/Apodictic/MarginalUtility.lean",
    "Apodictic/Apodictic/Urgency.lean",
    "Apodictic/Apodictic/Allocation.lean",
    "Apodictic/Apodictic/Mises.lean",
    "Apodictic/Apodictic/Action.lean",
    "Apodictic/Apodictic/Contrast.lean",
    "Apodictic/Apodictic/Consistency.lean",
]

# Runs the human has ruled may stand in more than one place.  Each entry is a
# phrase plus the reason it is exempt; keep the reason, because an exemption
# list with no reasons becomes a place to hide duplication.  Matching is on
# words, so punctuation and case here do not matter.
ALLOWED = [
    (
        "the warrant for the premise is the conclusion",
        "Human ruling, 2026-09-11.  The sharpest statement of the central "
        "finding, and both surfaces need it: SwapDominant's docstring must "
        "stand alone for a reader who opens the library and never the essay, "
        "and The finding must land its own hinge.  Revisit if an equally "
        "good alternative phrasing turns up.",
    ),
]

# A run with none of these is identifiers, not English.
STOP = set(
    "the of a an is are was to that he his it in and not for by with which "
    "as no be on at from this there".split()
)

TAG = re.compile(r"<(/?)(\w+)[^>]*?(/?)>")
WORD = re.compile(r"[A-Za-z0-9’']+")
OPENS_DOCSTRING = re.compile(
    r'class="namedocs"|hl lean block|hl lean lean-output|class="signature'
)


def words(text):
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"&[a-z#0-9]+;", " ", text)
    return WORD.findall(text.lower())


def split_page(path):
    """Return (our prose, rendered docstrings and code) as two word streams.

    Walks tags tracking depth, so a nested </div> inside a docstring does not
    end it early.
    """
    html = open(path, encoding="utf-8").read()
    html = re.sub(r"<(script|style)[^>]*>.*?</\1>", " ", html, flags=re.S)
    prose, doc, depth, pos = [], [], 0, 0
    for m in TAG.finditer(html):
        (doc if depth else prose).append(html[pos:m.start()])
        pos = m.end()
        close, name, selfclose = m.groups()
        if depth:
            if name in ("div", "code", "pre") and not selfclose:
                depth += -1 if close else 1
        elif not close and not selfclose and OPENS_DOCSTRING.search(m.group(0)):
            depth = 1
    (doc if depth else prose).append(html[pos:])
    return words(" ".join(prose)), words(" ".join(doc))


def grams(stream, n=N):
    return {tuple(stream[i:i + n]) for i in range(len(stream) - n + 1)}


def quoted_grams():
    """Five-grams appearing inside a quotation in the authored sources.

    Five rather than eight so that a run only PARTLY inside a quotation still
    counts as quotation -- a summary that embeds a quoted clause mid-sentence
    should not be charged for the join.  String literals that are code rather
    than English are filtered by requiring stopwords.
    """
    out = set()
    for rel in AUTHORED:
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8").read()
        spans = re.findall(r'"([^"]{20,400})"', text, flags=re.S)
        spans += [
            m.group(0).replace(">", " ")
            for m in re.finditer(r"(?:^> .*\n)+", text, flags=re.M)
        ]
        for span in spans:
            w = words(span)
            if sum(1 for x in w if x in STOP) >= max(2, len(w) // 8):
                out |= grams(w, 5)
    return out


def allowed_grams():
    """Exact word-strings of the ruled-exempt phrases.

    Matching is STRICT -- a run is exempt only when it sits entirely inside an
    allowed phrase.  A looser test (any five words in common) would excuse
    runs that merely brush the phrase and carry our own words on either side,
    which is how an exemption list quietly becomes a loophole.
    """
    return [" ".join(words(phrase)) for phrase, _reason in ALLOWED]


def classify(run, quoted, allowed):
    if not any(x in STOP for x in run):
        return "signatures"
    if any(" ".join(run) in phrase for phrase in allowed):
        return "allowed"
    if any(tuple(run[i:i + 5]) in quoted for i in range(len(run) - 4)):
        return "quotations"
    return "ours"


def stitch(runs):
    """Join overlapping n-grams back into the longest readable runs."""
    remaining, out = set(runs), []
    for run in sorted(remaining):
        if run not in remaining:
            continue
        remaining.discard(run)
        text, cur = list(run), run
        while True:
            nxt = [r for r in remaining if r[:-1] == cur[1:]]
            if not nxt:
                break
            cur = nxt[0]
            remaining.discard(cur)
            text.append(cur[-1])
        out.append(" ".join(text))
    return sorted(out, key=len, reverse=True)


def main():
    show = None
    if "--show" in sys.argv:
        i = sys.argv.index("--show")
        if i + 1 < len(sys.argv):
            show = sys.argv[i + 1]

    files = sorted(glob.glob(os.path.join(PAGES, "**", "*.html"), recursive=True))
    if not files:
        print("no emitted pages under site/verso/pages -- run generate-doc first")
        return 0

    quoted = quoted_grams()
    allowed = allowed_grams()
    prose, docs = {}, {}
    for f in files:
        p, d = split_page(f)
        prose[f], docs[f] = grams(p), grams(d)

    buckets = {"signatures": {}, "quotations": {}, "allowed": {}, "ours": {}}
    for a in files:
        for b in files:
            if a == b:
                continue
            for run in prose[a] & docs[b]:
                buckets[classify(run, quoted, allowed)].setdefault(
                    (os.path.basename(a) + " prose", os.path.basename(b) + " docstring"), set()
                ).add(run)
    for i, a in enumerate(files):
        for b in files[i + 1:]:
            for run in prose[a] & prose[b]:
                buckets[classify(run, quoted, allowed)].setdefault(
                    (os.path.basename(a) + " prose", os.path.basename(b) + " prose"), set()
                ).add(run)

    total = {k: sum(len(v) for v in d.values()) for k, d in buckets.items()}
    print(f"repeated {N}-word runs across pages:")
    print(f"  signatures  {total['signatures']:4}   emitted identifiers; not text")
    print(f"  quotations  {total['quotations']:4}   Mises or Rothbard; both pages must cite him")
    print(f"  allowed     {total['allowed']:4}   ruled to stand twice; see ALLOWED in this file")
    print(f"  OURS        {total['ours']:4}   written twice -- the only defect")

    for name in ("ours", "allowed", "quotations", "signatures"):
        if show and show != name:
            continue
        if not show and name != "ours":
            continue
        if not buckets[name]:
            continue
        print(f"\n{name}:")
        for (a, b), runs in sorted(buckets[name].items(), key=lambda kv: -len(kv[1])):
            print(f"  {a}  <->  {b}   ({len(runs)})")
            for line in stitch(runs):
                print(f"      {line}")

    return 1 if total["ours"] else 0


if __name__ == "__main__":
    sys.exit(main())
