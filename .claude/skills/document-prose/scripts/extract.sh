#!/usr/bin/env bash
# Prints one generated page as the text a reader sees. Code listings become
# "[code listing]": the follow-the-page reader must not lean on them.
# Usage: extract.sh site/verso/pages/The-Result/<Part>.html > <file outside the repo>
if ((BASH_VERSINFO[0] < 5)); then
  echo "needs bash 5+, found $BASH_VERSION" >&2
  exit 1
fi
set -euo pipefail

if (($# != 1)); then
  echo "usage: extract.sh <page.html>" >&2
  exit 2
fi

perl -0pe '
  s/<pre\b.*?<\/pre>/\n[code listing]\n/gs;
  s/<code class="hl lean block".*?<\/code>/\n[code listing]\n/gs;
  s/<\/(p|li|h[1-6]|div)>/\n/g;
  s/<li[^>]*>/- /g;
  s/<[^>]+>//g;
  s/&quot;/"/g; s/&#x27;|&#39;/\x27/g; s/&amp;/&/g; s/&lt;/</g; s/&gt;/>/g;
  s/\n\s*\n+/\n\n/g' -- "$1"
