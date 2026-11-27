#!/usr/bin/env bash
# The gate for a change to document prose or to a docstring: library build
# (with its lint), draft library, draft isolation, draft again (the isolation
# check leaves it unbuilt), document build, site tree regenerated, quotations,
# site build. Then the generated pages whose visible text differs from HEAD.
# It regenerates site/verso from the working tree: that is the check, so there
# is no dry run. Ends "GATE fail=0" or "GATE fail=1", and exits with that.
# Usage: /opt/homebrew/bin/bash ApodicticDoc/doc-gate.sh
if ((BASH_VERSINFO[0] < 5)); then
  echo "needs bash 5+, found $BASH_VERSION" >&2
  exit 1
fi
set -euo pipefail

if (($# != 0)); then
  echo "usage: doc-gate.sh (no arguments)" >&2
  exit 2
fi

export PATH="$HOME/.elan/bin:$PATH"
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
logs=$(mktemp -d)
trap 'rm -rf "${logs:?}"' EXIT
fail=0

# step <name> <directory under the root> <command…>
step() {
  local name=$1 dir=$2
  shift 2
  printf '== %s\n' "$name"
  if ! (cd "$root/$dir" && "$@") >"$logs/$name.log" 2>&1; then
    fail=1
    tail -n 40 "$logs/$name.log"
  fi
}

# Appends each line that starts with whitespace to the line before it.
join_wrapped() {
  awk '
    /^[[:space:]]/ && NR > 1 { line = line $0; next }
    NR > 1 { print line }
    { line = $0 }
    END { if (NR > 0) print line }'
}

strip_tags() {
  sed 's/<[^>]*>//g'
}

text_changed() {
  local page=$1 before after
  before=$(git -C "$root" show "HEAD:$page" | strip_tags)
  after=$(strip_tags <"$root/$page")
  [[ $before != "$after" ]]
}

step library Apodictic lake build
# The lint and the axiom lines are in the build's output. Read what prints here:
# a warning is a failure the build's exit status does not carry.
grep -E 'error|warning' "$logs/library.log" | grep -v 'Found 0 errors' || true
# Classical.choice outside the consistency ledger fails the gate. A long axiom
# list wraps, and only its first line names the file, so wrapped lines are
# joined before the ledger's are filtered out.
if join_wrapped <"$logs/library.log" | grep 'Classical.choice' | grep -v Consistency; then
  fail=1
fi

step draft Apodictic lake build ApodicticDraft
step isolation Apodictic /opt/homebrew/bin/bash check-draft-isolation.sh
step draft-again Apodictic lake build ApodicticDraft
step document ApodicticDoc lake build
step generate ApodicticDoc lake exe generate-doc --output ../site/verso
step quotes site bun run check-quotes
step verify site bun run verify

printf '== visible text against HEAD\n'
while IFS= read -r page; do
  if text_changed "$page"; then
    printf '  text changed: %s\n' "$page"
  fi
done < <(git -C "$root" diff --name-only --diff-filter=M -- site/verso/)
git -C "$root" ls-files --others --exclude-standard -- site/verso/ | sed 's/^/  new file: /'

printf 'GATE fail=%s\n' "$fail"
exit "$fail"
