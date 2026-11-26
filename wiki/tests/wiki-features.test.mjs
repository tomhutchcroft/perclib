import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { readArticles, assertionsIn } from "../scripts/articles.mjs";
import { renderMath, plain } from "../src/render.mjs";
import {
  expandCollapsibles,
  resolveWanted,
  prepareSection,
  linkGraph,
  assertNoDeadLinks,
  linkReport,
  linkReportText,
  tableOfContents,
  citationList,
  annotatePreviews,
  previewData,
  previewScript,
} from "../src/wiki-features.mjs";

const here = path.dirname(fileURLToPath(import.meta.url));
const real = await readArticles();
const [fixture] = await readArticles(path.join(here, "fixtures"));
const baseline = JSON.parse(await fs.readFile(path.join(here, "../migration-baseline.json"), "utf8"));
const assertions = assertionsIn(real);

function setup(change = (html) => html) {
  const articles = [...real, structuredClone(fixture)];
  const pages = new Map(articles.map((p) => [p.id, p]));
  const bodies = new Map(),
    wanted = [],
    resolved = [];
  for (const p of articles)
    bodies.set(
      p.id,
      p.sections.map((s) => {
        const html = p.id === fixture.id ? change(s.html, s.id) : s.html;
        const r = prepareSection(html, pages, `${p.id}/${s.id}`);
        wanted.push(...r.wanted.map((w) => ({ ...w, article: p.id, section: s.id })));
        resolved.push(...r.resolved.map((w) => ({ ...w, article: p.id, section: s.id })));
        return { id: s.id, title: s.title, html: r.html };
      }),
    );
  const graph = linkGraph(articles, bodies, assertions, baseline);
  return { articles, pages, bodies, wanted, resolved, graph };
}

test("collapsible blocks render as nested details with mathematics inside and a mandatory summary", () => {
  const proof = fixture.sections.find((s) => s.id === "proof").html;
  const html = expandCollapsibles(proof);
  assert.equal(html.match(/<details class="collapsible">/g).length, 2);
  assert.match(html, /<summary>Proof of the bound \$\\chi_q\(v\)\\le 1\/\(1-m\)\$<\/summary>/);
  assert.match(html, /<summary>Verification of \(3\)<\/summary><div class="collapsible-body">\n<p><span id="step-3">/);
  // The inner block closes before the outer block's remaining text.
  assert.ok(html.indexOf("</div></details>") < html.indexOf("End of the proof"));
  const rendered = renderMath(html);
  const summary = /<summary>([\s\S]*?)<\/summary>/.exec(rendered)[1];
  assert.match(summary, /class="katex"/);
  assert.match(rendered.slice(rendered.indexOf("Verification")), /katex-display/);
  assert.ok(!/(^|\n):::/.test(rendered));

  assert.throws(() => expandCollapsibles(":::details\n<p>x</p>\n:::"), /needs a summary line/);
  assert.throws(() => expandCollapsibles(":::details   \n<p>x</p>\n:::"), /needs a summary line/);
  assert.throws(() => expandCollapsibles(":::details Proof\n<p>x</p>"), /not closed/);
  assert.throws(() => expandCollapsibles("<p>x</p>\n:::"), /matches no open block/);
  assert.throws(() => expandCollapsibles(":::details A\n:::details B\n:::\n:::"), /fewer colons/);
  assert.throws(() => expandCollapsibles(":::proof A\n:::"), /unknown block directive/);
  assert.throws(() => expandCollapsibles("<details><p>no summary</p></details>"), /must begin with a <summary>/);
  assert.equal(expandCollapsibles("<details><summary>Kept</summary>x</details>"), "<details><summary>Kept</summary>x</details>");
  // Text that merely contains colons is not a directive.
  assert.equal(expandCollapsibles("<p>ratio a:::b</p>"), "<p>ratio a:::b</p>");
});

test("existing articles contain no directive collisions and all hand-written blocks have summaries", () => {
  for (const p of real)
    for (const s of p.sections) assert.doesNotThrow(() => expandCollapsibles(s.html, `${p.id}/${s.id}`));
});

test("search text of an article includes the text of its collapsed blocks", () => {
  const { bodies } = setup();
  const text = bodies.get(fixture.id).map((s) => s.title + " " + plain(s.html)).join(" ");
  assert.match(text, /quokka estimate/);
  assert.match(text, /Verification of \(3\)/);
  assert.ok(!text.includes(":::"));
});

test("backlinks are generated per article and per assertion", () => {
  const { graph, pages } = setup();
  assert.ok(graph.incoming.get("connectivity").some((x) => x.article === fixture.id && x.section === "statement"));
  assert.ok(graph.incoming.get("product-model").some((x) => x.article === fixture.id));
  assert.ok(graph.citing.get("53Z9").some((x) => x.article === fixture.id && x.section === "statement"));
  // A same-page fragment link is not an incoming link of the article itself.
  assert.ok(!graph.incoming.get(fixture.id).some((x) => x.article === fixture.id));
  const own = assertions.filter((a) => a.tag === "53Z9");
  const title = (id, section) => pages.get(id).sections.find((s) => s.id === section).title;
  const html = citationList(own, graph, pages, title);
  assert.match(html, /<li id="cites-53Z9"><a href="\/tag\/53Z9\/">/);
  assert.match(html, /href="\/articles\/collapsible-fixture\/#section-statement">Collapsible fixture: Statement<\/a>/);
  assert.match(citationList([{ tag: "ZZZZ", title: "None" }], graph, pages, title), /Not linked from any article/);
});

test("a dead internal link in an article fails with its location; valid links pass", () => {
  assert.doesNotThrow(() => assertNoDeadLinks(setup().graph));
  const { graph } = setup((html, id) =>
    id === "statement"
      ? html +
        '<a href="/articles/no-such-article/">a</a><a href="/articles/connectivity/#no-such-anchor">b</a>' +
        '<a href="/tag/ZZZZ/">c</a><a href="#missing-step">d</a><a href="#/connectivity?section=absent">e</a>'
      : html,
  );
  assert.equal(graph.dead.length, 5);
  assert.throws(() => assertNoDeadLinks(graph), (error) => {
    for (const piece of [
      "collapsible-fixture#section-statement: /articles/no-such-article/ (no such article)",
      "#no-such-anchor in connectivity",
      "/tag/ZZZZ/ (no such active assertion)",
      "#missing-step in collapsible-fixture",
      "Missing section",
    ])
      assert.ok(error.message.includes(piece), piece);
    return true;
  });
  // External, source and errata links are outside the article graph.
  const ok = setup((html, id) =>
    id === "statement" ? html + '<a href="https://arxiv.org/abs/1">x</a><a href="/sources/hutchcroft-book/">y</a>' : html,
  );
  assert.equal(ok.graph.dead.length, 0);
});

test("the link report lists articles without inline links, unlinked concepts and wanted pages without failing", () => {
  const { articles, bodies, graph, wanted } = setup();
  const report = linkReport(articles, bodies, graph, wanted);
  assert.ok(!report.noInlineLinks.includes(fixture.id));
  assert.deepEqual(
    report.unlinkedMentions.filter((u) => u.article === fixture.id),
    [{ article: fixture.id, section: "proof", term: "geometric series", target: "subcritical-bound" }],
  );
  assert.deepEqual(report.wantedPages.find((w) => w.slug === "random-cluster-model"), {
    slug: "random-cluster-model",
    phrases: ["random-cluster model"],
    from: [{ article: fixture.id, section: "statement" }],
  });
  const text = linkReportText(report);
  assert.match(text, /random-cluster-model \(random-cluster model\) from collapsible-fixture#section-statement/);
  assert.match(text, /collapsible-fixture#section-proof: "geometric series" -> subcritical-bound/);

  const bare = setup((html) => html.replace(/<a\b[^>]*>([\s\S]*?)<\/a>/g, "$1"));
  const r2 = linkReport(bare.articles, bare.bodies, bare.graph, bare.wanted);
  assert.ok(r2.noInlineLinks.includes(fixture.id));
  assert.ok(r2.unlinkedMentions.some((u) => u.article === fixture.id && u.section === "statement" && u.target === "product-model"));
});

test("wanted links render without a destination and become ordinary links once the article exists", () => {
  const pages = new Map([["connectivity", {}]]);
  const a = resolveWanted('<a data-wanted="lace-expansion">lace</a> and <a data-wanted="connectivity">clusters</a>', pages);
  assert.match(a.html, /<a class="wanted-link" data-wanted="lace-expansion" title="Wanted page: no article yet">lace<\/a>/);
  assert.match(a.html, /<a href="\/articles\/connectivity\/">clusters<\/a>/);
  assert.deepEqual(a.wanted, [{ slug: "lace-expansion", phrase: "lace" }]);
  assert.deepEqual(a.resolved, [{ slug: "connectivity", phrase: "clusters" }]);
  assert.throws(() => resolveWanted('<a data-wanted="x" href="/y/">z</a>', pages), /no href/);
  assert.throws(() => resolveWanted('<a data-wanted="Bad Slug">z</a>', pages), /invalid wanted page id/);
});

test("the table of contents lists every section, sub-headings with ids and the generated panels", () => {
  const html = tableOfContents(
    [...fixture.sections, { id: "sub", title: "With $x$", html: '<h3 id="part-a">Part A</h3><h3>No id</h3>' }],
    [["connections", "Connections"]],
  );
  assert.match(html, /^<nav class="article-toc" id="toc"/);
  for (const href of ["#section-statement", "#section-proof", "#section-sub", "#part-a", "#connections"])
    assert.ok(html.includes(`href="${href}"`), href);
  assert.ok(!html.includes("No id"));
  assert.match(renderMath(html), /class="katex"/);
});

test("hover previews annotate internal links and carry pre-rendered, script-safe data", () => {
  const { pages, bodies } = setup();
  const statement = bodies.get(fixture.id)[0].html;
  const { html, used } = annotatePreviews(statement, fixture.id, pages, assertions, baseline);
  assert.deepEqual([...used].sort(), ["a:connectivity", "a:product-model", "t:53Z9"]);
  assert.match(html, /href="\/articles\/connectivity\/" data-preview="a:connectivity"/);
  assert.match(html, /href="#step-3">/); // same-page links get no preview
  const data = previewData(used, pages, assertions);
  assert.equal(data["t:53Z9"].k, "Theorem 53Z9");
  assert.match(data["t:53Z9"].s, /In A small-parameter susceptibility bound/);
  const script = previewScript({ x: { k: "</script>", t: " ", s: "" } });
  assert.ok(!script.slice(0, -"</script>".length).includes("</script"));
  assert.ok(!script.includes(" "));
  assert.equal(previewScript({}), "");
});

test("built article pages carry the contents, tools, script, previews, backlinks and searchable collapsed text", async () => {
  const { build } = await import("../src/build.mjs");
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-features-"));
  try {
    const files = await build(path.join(dir, "out"));
    const page = files.get("articles/green-free-triangle/index.html");
    assert.match(page, /<nav class="article-toc" id="toc"/);
    assert.match(page, /<div class="article-tools" hidden>.*data-details-action="expand".*data-details-action="collapse"/);
    assert.match(page, /<script defer src="\/assets\/article\.js"><\/script>/);
    const data = JSON.parse(/<script type="application\/json" id="link-preview-data">([\s\S]*?)<\/script>/.exec(page)[1]);
    for (const key of page.matchAll(/data-preview="([^"]+)"/g)) assert.ok(data[key[1]], key[1]);
    assert.match(page, /<li id="cites-[0-9A-Z]{4}">/);
    // A page without collapsed blocks has no expand/collapse tools.
    const plainPage = [...files].find(([f, h]) => f.startsWith("articles/") && f.endsWith("/index.html") && h.includes('id="toc"') && !h.includes("<details"));
    assert.ok(plainPage && !plainPage[1].includes('class="article-tools"'));
    // Collapsed text is searchable: the summary and body of a hand-written block.
    const source = real.find((p) => p.id === "green-free-triangle").sections.map((s) => s.html).join("");
    const inside = plain(/<details>([\s\S]*?)<\/details>/.exec(source)[1].replace(/\$[^$]*\$/g, " ")).split(" ").slice(0, 6).join(" ");
    const index = JSON.parse(files.get("search-index.json"));
    assert.ok(index.find((r) => r.url === "/articles/green-free-triangle/").text.includes(inside), inside);
    assert.match(files.get("link-report.txt"), /^Wiki link report/);
    const report = JSON.parse(files.get("link-report.json"));
    assert.ok(Array.isArray(report.noInlineLinks) && Array.isArray(report.unlinkedMentions) && Array.isArray(report.wantedPages));
    // Print styles open every block.
    assert.match(files.get("assets/details.css"), /@media print\{[^}]*details:not\(\[open\]\)::details-content\{content-visibility:visible;display:block\}/);
    // What links here now follows every link form, not only legacy hash links.
    const connectivity = files.get("articles/connectivity/index.html");
    const start = connectivity.indexOf("<h3>What links here</h3>");
    const whatLinksHere = connectivity.slice(start, connectivity.indexOf("</section>", start));
    assert.ok((whatLinksHere.match(/class="rail-link"/g) ?? []).length > 3);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
});
