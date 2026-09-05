// The document, as emitted by `lake exe generate-doc --output ../site/verso`
// (ApodicticDoc/ApodicticDoc/Emit/Eleventy.lean). Pages carry their
// rendered fragment; the layout and the verso-page element read from here.
import { readFileSync } from 'fs';
import { fileURLToPath } from 'url';
import { dirname, join } from 'path';

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = join(__dirname, '..', 'verso');
const read = (f) => JSON.parse(readFileSync(join(root, f), 'utf8'));

const pages = read('pages.json').map((p) => ({
  ...p,
  html: readFileSync(join(root, p.fragment), 'utf8'),
}));
const byUrl = Object.fromEntries(pages.map((p) => [p.url, p]));

export default {
  root: '/verso/',
  toc: read('toc.json'),
  assets: read('assets.json'),
  pages,
  byUrl,
};
