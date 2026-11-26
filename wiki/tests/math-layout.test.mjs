import test from "node:test";
import assert from "node:assert/strict";
import { compactMathLayout } from "../src/math-layout.mjs";
import { renderMath } from "../src/render.mjs";

const page = (body) => `<html><head></head><body><main id="main-content">${body}</main></body></html>`;
function restore(html, css) {
  const styles = new Map([...css.matchAll(/\.([\w-]+)\{([^{}]+)\}/g)].map(m => [m[1],m[2]]));
  return html.replace(/<link rel="stylesheet" href="\/assets\/math-layout\.[a-f0-9]+\.css">/, "")
    .replace(/<span\b[^>]*>/g, tag => tag.replace(/ class="([^"]*)"/, (attr, value) => {
      const names = value.split(" "), name = names.find(n => styles.has(n));
      if (!name) return attr;
      const rest = names.filter(n => n !== name).join(" ");
      return (rest ? ` class="${rest}"` : "") + ` style="${styles.get(name)}"`;
    }));
}

test("shared math geometry restores the exact KaTeX markup, including accessible MathML", () => {
  const formula = String.raw`$$\begin{aligned}\frac{x_i^2}{\sqrt{1+y}}&=\sum_{n=0}^\infty a_n\\ \widehat f(x)&=\int_{-\infty}^{\infty}f(t)e^{itx}\,dt\end{aligned}$$`;
  const original = page(renderMath(formula.repeat(30)));
  const files = new Map([["index.html",original]]);
  const result = compactMathLayout(files);
  assert.ok(result.bytesSaved > 1000);
  assert.equal(restore(files.get("index.html"), files.get(result.asset)), original);
  assert.equal((files.get("index.html").match(/class="katex-mathml"/g)||[]).length, 30);
  const reversed = new Map([["other.html",original],["index.html",original]]);
  const forward = new Map([...reversed].reverse());
  assert.deepEqual(compactMathLayout(reversed),compactMathLayout(forward));
  assert.deepEqual([...reversed].sort(),[...forward].sort());
});

test("math compaction leaves other markup, code, unsafe styles and unprofitable pages unchanged", () => {
  const geometry = '<span class="katex"><span class="base" style="height:1em;vertical-align:-0.25em;"></span></span>';
  const excluded = '<span style="height:1em;vertical-align:-0.25em;">outside math</span>' +
    `<pre>${geometry}</pre><code>${geometry}</code><script>const sample='${geometry}';</script><!--${geometry}-->` +
    '<span class="katex"><span style="color:red;">x</span><span style="height:1em;}body{color:red;">y</span></span>';
  const files = new Map([["index.html",page(geometry.repeat(30)+excluded)], ["tiny.html",page(geometry)], ["fragment.html",geometry.repeat(30)]]);
  const originals = new Map(files);
  const result = compactMathLayout(files);
  assert.equal(result.pages,1);
  assert.ok(files.get("index.html").includes(excluded));
  assert.equal(files.get("tiny.html"),originals.get("tiny.html"));
  assert.equal(files.get("fragment.html"),originals.get("fragment.html"));
  assert.equal(restore(files.get("index.html"),files.get(result.asset)),originals.get("index.html"));
});
