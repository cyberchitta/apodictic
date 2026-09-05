import path from 'path';
import { fileURLToPath } from 'url';
import ejsPlugin from '@11ty/eleventy-plugin-ejs';
import sgPlugin, {
  helpers as sgHelpers,
  createCustomElementRenderer,
} from '@cyberchitta/supramental-gold/eleventy';
import verso from './_data/verso.js';
import site from './_data/site.json' with { type: 'json' };

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const sgRoot = path.dirname(
  fileURLToPath(import.meta.resolve('@cyberchitta/supramental-gold/package.json')),
);
const sgEleventy = path.join(sgRoot, 'eleventy');
const includesDir = path.join(__dirname, '_includes');

export default function (eleventyConfig) {
  // Consumer `_includes` first so local files shadow SG defaults.
  eleventyConfig.addPlugin(ejsPlugin, { views: [includesDir, sgEleventy] });
  eleventyConfig.addPlugin(sgPlugin);

  eleventyConfig.addGlobalData('layout', 'layouts/base.ejs');
  eleventyConfig.addGlobalData('helpers', sgHelpers);

  // One page per Verso part: doc.md paginates over verso.pages and
  // declares `<showcase type="verso-page" url="..." />`; the element
  // template prints that page's fragment.
  const renderCustomElements = createCustomElementRenderer(
    { showcase: { 'verso-page': 'showcase/verso-page.ejs' } },
    includesDir,
    { data: { verso, site }, helpers: sgHelpers },
  );
  eleventyConfig.addTransform('renderCustomElements', async function (content) {
    if (!this.page.outputPath || !this.page.outputPath.endsWith('.html')) return content;
    return await renderCustomElements(content);
  });

  // Verso's runtime files, served under /verso/ (window.VERSO_ROOT).
  eleventyConfig.addPassthroughCopy({ 'verso/verso-data': 'verso/verso-data' });
  eleventyConfig.addPassthroughCopy({ 'verso/verso-vars.css': 'verso/verso-vars.css' });
  eleventyConfig.addPassthroughCopy({ 'verso/verso-inline.css': 'verso/verso-inline.css' });
  eleventyConfig.addPassthroughCopy({ 'verso/verso-inline.js': 'verso/verso-inline.js' });
  eleventyConfig.addPassthroughCopy({ 'verso/verso-docs.json': 'verso/verso-docs.json' });
  eleventyConfig.addPassthroughCopy('assets');

  eleventyConfig.ignores.add('verso/**');
  eleventyConfig.ignores.add('README.md');

  return {
    dir: { input: '.', output: '_site', includes: '_includes', data: '_data' },
    markdownTemplateEngine: 'ejs',
    htmlTemplateEngine: 'ejs',
    templateFormats: ['md', 'ejs'],
  };
}
