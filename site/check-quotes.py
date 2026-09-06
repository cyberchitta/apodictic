#!/usr/bin/env python3
"""Check every quotation in the library and document against the source texts.

The failure this exists to catch is named in _notes/intent.md: "a pedigree is
the one thing Lean cannot check and a misquotation survives every build." It
has bitten once — MarginalUtility.lean's module docstring quoted "the greater
the supply, the lower the marginal utility" when Rothbard wrote "The greater
the supply OF A GOOD, the lower the marginal utility". Two words dropped
inside quotation marks, under the headline theorem, found 2026-09-06 by an
ad-hoc version of this script and by nothing else.

Usage:  python3 site/check-quotes.py        (from the repo root or anywhere)

Sources live in _notes/sources/*.txt and are GITIGNORED — they are copyrighted
editions. Without them the script cannot do its job and says so, exiting 0, so
that a clone without sources is not a failing build. That exit is a skip, not
a pass; read the message.

Matching is deliberately forgiving about presentation and strict about words:

  - page furniture (running footers, "=== PDF PAGE n ===") is removed, since a
    quotation may straddle a page break — the misquotation above was found only
    after this, because "...axiom of human / [footer] / action" hid the phrase
  - end-of-line hyphenation is rejoined ("eco-\\nnomics" -> "economics")
  - whitespace collapses, curly quotes and dashes normalise, markdown emphasis
    inside a quotation is stripped
  - an elision ("..." or "…") splits the quotation; each fragment must appear
  - case is ignored, because embedding a quotation mid-sentence legitimately
    lowercases its first letter

Two buckets, because not every quoted string is a citation:

  FAIL  a quotation with a page citation near it that is NOT in the sources.
        Exits 1. This is the bug the script is for.
  NOTE  a quoted phrase with no citation nearby and no match — almost always
        our own coinage in scare quotes ("the whole point", "does not say").
        Listed for eyeballing; does not fail.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCES = ROOT / "_notes" / "sources"
TARGETS = [
    *sorted((ROOT / "Apodictic" / "Apodictic").glob("*.lean")),
    ROOT / "ApodicticDoc" / "ApodicticDoc.lean",
    ROOT / "ApodicticDoc" / "ApodicticDoc" / "Result.lean",
    ROOT / "README.md",
]

# A citation must follow the closing quote almost immediately -- "...' (*MES*
# p. 25)" -- not merely appear somewhere later in the same docstring. A loose
# window mislabels our own scare quotes as citations, which is the difference
# between a report worth reading and one that cries wolf.
CITE_AFTER = re.compile(
    r"^[\s,;.)]{0,6}\(?\s*(\*?MES\*?|\*?Human Action\*?|pp?\.\s*\d|ch\.\s*[IVX])"
)
# A citation may also PRECEDE its quotation -- "(Rothbard, *MES*, ch. 1, p. 27):
# \"The greater the supply...\"" -- and the one misquotation this script has ever
# caught sat under a heading of exactly that shape. Checking only forwards would
# have classified it as an uncited phrase and let it through as a NOTE.
CITE_BEFORE = re.compile(
    r"(\*?MES\*?|\*?Human Action\*?|pp?\.\s*\d+|ch\.\s*[IVX]+)[^\"]{0,48}$"
)

FURNITURE = [
    re.compile(r"(?m)^=== PDF PAGE \d+ ===$"),
    re.compile(r"(?m)^\d+ Man, Economy, and State.*$"),
    re.compile(r"(?m)^Fundamentals of Human Action \d+$"),
]


def normalise(text):
    for pat in FURNITURE:
        text = pat.sub("", text)
    text = re.sub(r"-\n", "", text)          # rejoin end-of-line hyphenation
    text = text.replace("’", "'").replace("‘", "'")
    text = text.replace("“", '"').replace("”", '"')
    text = text.replace("—", "-").replace("–", "-")
    text = re.sub(r"[*_]", "", text)         # markdown emphasis
    return re.sub(r"\s+", " ", text).lower()


def load_sources():
    if not SOURCES.is_dir():
        return None
    texts = {}
    for path in sorted(SOURCES.glob("*.txt")):
        texts[path.name] = normalise(path.read_text(encoding="utf-8"))
    return texts or None


def quotations(text):
    """Yield (quote, has_citation) for every double-quoted run of >=4 words."""
    for m in re.finditer(r'"([^"\n]{16,400})"', text):
        body = m.group(1)
        if len(body.split()) < 4:
            continue
        if body.lstrip().startswith(("lean", "http", "--")):
            continue
        # A real quotation opens on a word. Anything opening on punctuation is
        # the gap between two adjacent quotations, mis-paired by the scanner.
        if not re.match(r"[A-Za-z]", body.strip()):
            continue
        after = text[m.end():m.end() + 40]
        before = text[max(0, m.start() - 90):m.start()]
        cited = bool(CITE_AFTER.match(after)) or bool(CITE_BEFORE.search(before))
        yield body, cited


def main():
    sources = load_sources()
    if sources is None:
        print("check-quotes: SKIPPED — no _notes/sources/*.txt (they are "
              "gitignored copyrighted editions). Nothing was checked.")
        return 0

    fails, notes, checked = [], [], 0
    for path in TARGETS:
        if not path.exists():
            continue
        raw = path.read_text(encoding="utf-8")
        # a docstring wraps quotations across lines; flatten before extracting
        flat = re.sub(r"\s*\n\s*", " ", raw)
        for quote, cited in quotations(flat):
            fragments = [f for f in re.split(r"\.\.\.|…", quote) if f.strip()]
            needles = [normalise(f).strip() for f in fragments]
            checked += 1
            if all(any(n in body for body in sources.values()) for n in needles):
                continue
            where = f"{path.relative_to(ROOT)}"
            (fails if cited else notes).append((where, quote))

    for where, quote in notes:
        print(f"NOTE  {where}: no source match, no citation nearby — "
              f'"{quote[:80]}"')
    if notes:
        print()

    if not fails:
        print(f"check-quotes: clean ({checked} quotations, "
              f"{len(sources)} source texts)")
        return 0

    print(f"check-quotes: {len(fails)} CITED quotation(s) not found in sources\n",
          file=sys.stderr)
    for where, quote in fails:
        print(f'  {where}\n    "{quote}"\n', file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
