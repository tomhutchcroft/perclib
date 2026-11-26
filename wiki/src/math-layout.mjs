import { createHash } from "node:crypto";

const digest = (value) => createHash("sha256").update(value).digest("hex").slice(0, 12);
// Only KaTeX's numeric layout declarations qualify. Authored colours, URLs,
// arbitrary CSS and MathML attributes retain their original inline form.
const geometry = /^(?:(?:height|vertical-align|top|bottom|left|right|width|min-width|margin-left|margin-right|padding-left|padding-right|border-bottom-width):-?(?:\d+(?:\.\d*)?|\.\d+)(?:em|ex|px|%)?;)+$/;
const tokens = /<!--[\s\S]*?-->|<(?:script|style|pre|code)\b[^>]*>[\s\S]*?<\/(?:script|style|pre|code)>|<(?:[^>"']|"[^"]*"|'[^']*')*>/g;

function visitLayout(html, visit) {
  let main = false, depth = 0;
  return html.replace(tokens, (tag) => {
    if (/^<main\b/.test(tag) && /\bid="main-content"/.test(tag)) main = true;
    if (/^<\/main\b/.test(tag)) { main = false; depth = 0; }
    if (!main) return tag;
    if (/^<\/span\b/.test(tag)) { if (depth) depth--; return tag; }
    if (!/^<span\b/.test(tag)) return tag;
    const classes = / class="([^"]*)"/.exec(tag);
    if (!depth && !classes?.[1].split(/\s+/).includes("katex")) return tag;
    depth++;
    // KaTeX puts style last. Keeping that restriction makes the transformation
    // exactly reversible, including the original attribute order.
    const style = / style="([^"]*)">$/.exec(tag);
    return style && geometry.test(style[1]) ? visit(tag, style[1], classes) : tag;
  });
}

export function compactMathLayout(files) {
  const entries = new Map(), names = new Map();
  const replacement = (tag, style, classes, name) => {
    const without = tag.slice(0, -(` style="${style}">`.length)) + ">";
    return classes
      ? without.replace(classes[0], ` class="${classes[1]} ${name}"`)
      : without.slice(0, -1) + ` class="${name}">`;
  };
  const rule = ({name, style}) => `#main-content .katex .${name}{${style}}\n`;
  for (const [file, html] of files) {
    if (!file.endsWith(".html")) continue;
    visitLayout(html, (tag, style, classes) => {
      const name = `km-${digest(style)}`;
      if (names.has(name) && names.get(name) !== style) throw Error("Math layout style hash collision");
      names.set(name, style);
      const saving = tag.length - replacement(tag, style, classes, name).length;
      if (saving > 0) {
        const entry = entries.get(style) ?? {name, style, saving: 0};
        entry.saving += saving;
        entries.set(style, entry);
      }
      return tag;
    });
  }
  const candidates = new Map([...entries].filter(([,entry]) => entry.saving > rule(entry).length));
  const changed = new Map(), used = new Map();
  // The fingerprint has fixed width, so its eventual value does not affect
  // whether adding the stylesheet would make an individual page smaller.
  const linkSize = '<link rel="stylesheet" href="/assets/math-layout.000000000000.css">'.length;
  for (const [file, html] of files) {
    if (!file.endsWith(".html") || !html.includes("</head>")) continue;
    const pageUsed = new Map();
    const compact = visitLayout(html, (tag, style, classes) => {
      const entry = candidates.get(style);
      if (!entry) return tag;
      const next = replacement(tag, style, classes, entry.name);
      if (next.length >= tag.length) return tag;
      pageUsed.set(style, entry);
      return next;
    });
    if (html.length - compact.length > linkSize) {
      changed.set(file, compact);
      for (const [style, entry] of pageUsed) used.set(style, entry);
    }
  }
  if (!changed.size) return {pages: 0, styles: 0, bytesSaved: 0};
  // The main-content scope outranks the pinned KaTeX class selectors. Avoid
  // !important, so reader styles can still override these layout declarations.
  const css = [...used.values()].sort((a,b) => a.style < b.style ? -1 : a.style > b.style ? 1 : 0).map(rule).join("");
  const asset = `assets/math-layout.${digest(css)}.css`;
  const link = `<link rel="stylesheet" href="/${asset}">`;
  let bytesSaved = -Buffer.byteLength(css);
  const output = new Map();
  for (const [file, compact] of changed) {
    const html = compact.replace("</head>", link + "</head>");
    bytesSaved += Buffer.byteLength(files.get(file)) - Buffer.byteLength(html);
    output.set(file, html);
  }
  if (bytesSaved <= 0) return {pages: 0, styles: 0, bytesSaved: 0};
  if (files.has(asset) && files.get(asset) !== css) throw Error("Math layout stylesheet hash collision");
  for (const [file, html] of output) files.set(file, html);
  files.set(asset, css);
  return {pages: changed.size, styles: used.size, bytesSaved, asset};
}
