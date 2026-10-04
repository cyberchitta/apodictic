#!/usr/bin/env bash
# Check that the draft library (ApodicticDraft) is isolated from the
# trusted library and the document (CLAUDE.md, "ApodicticDraft"):
#   1. no module of the library or the document imports it;
#   2. it is not a default target of either lake package;
#   3. a plain `lake build` does not build it — checked by deleting the
#      draft's build products, running the plain build, and failing if
#      any came back (and if the build log names the draft).
# Exits non-zero, loudly, on any failure. Run from anywhere:
#   /opt/homebrew/bin/bash Apodictic/check-draft-isolation.sh
# Step 3 runs `lake build`; with a warm cache it takes seconds.
set -u
export PATH="$HOME/.elan/bin:$PATH"

PKG="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$PKG")"
DOC="$REPO/ApodicticDoc"
fail=0
bad() { echo "FAIL: $*" >&2; fail=1; }

# 1. imports
hits="$(rg -n --glob '*.lean' --glob '!.lake/**' --glob '!_out/**' \
  '^\s*import\s+.*\bApodicticDraft\b' \
  "$PKG/Apodictic.lean" "$PKG/Apodictic" "$DOC" 2>/dev/null)"
if [ -n "$hits" ]; then
  bad "the library or the document imports ApodicticDraft:"
  echo "$hits" >&2
else
  echo "ok: nothing in Apodictic/ or ApodicticDoc/ imports ApodicticDraft"
fi

# 2. default targets
for lf in "$PKG/lakefile.toml" "$DOC/lakefile.toml"; do
  if rg -q '^\s*defaultTargets\s*=.*ApodicticDraft' "$lf"; then
    bad "ApodicticDraft is a default target in $lf"
  else
    echo "ok: not a default target in ${lf#$REPO/}"
  fi
done
if rg -q 'ApodicticDraft' "$DOC/lakefile.toml" "$DOC/lake-manifest.json"; then
  bad "the document's lake config names ApodicticDraft"
else
  echo "ok: the document's lakefile and manifest do not name ApodicticDraft"
fi

# 3. a plain build does not build the draft
find "$PKG/.lake/build" -maxdepth 3 -name 'ApodicticDraft*' -exec rm -rf {} +
log="$(cd "$PKG" && lake build 2>&1)"
status=$?
if [ $status -ne 0 ]; then
  bad "plain lake build failed (exit $status)"
  echo "$log" | tail -20 >&2
fi
if echo "$log" | rg -q 'ApodicticDraft'; then
  bad "plain lake build log mentions ApodicticDraft:"
  echo "$log" | rg 'ApodicticDraft' >&2
fi
left="$(find "$PKG/.lake/build" -maxdepth 3 -name 'ApodicticDraft*')"
if [ -n "$left" ]; then
  bad "plain lake build produced draft build products:"
  echo "$left" >&2
else
  echo "ok: plain lake build produced no ApodicticDraft build products"
fi
echo "$log" | tail -1

if [ $fail -ne 0 ]; then
  echo "DRAFT ISOLATION CHECK FAILED" >&2
  exit 1
fi
echo "draft isolation: all checks passed"
