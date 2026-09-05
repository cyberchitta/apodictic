---
pagination:
  data: verso.pages
  size: 1
  alias: p
permalink: "<%= p.url %>index.html"
layout: layouts/verso-page.ejs
eleventyComputed:
  title: "<%= p.titleText %>"
---
<showcase type="verso-page" url="<%= p.url %>" />
