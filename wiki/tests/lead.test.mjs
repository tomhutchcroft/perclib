import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import {
  wikiRoot,
  readArticles,
  assertionsIn,
  parseLead,
  leadHtml,
} from "../scripts/articles.mjs";
import { checkArticles } from "../scripts/check-articles.mjs";
import { transform } from "../src/render.mjs";
import {
  linkGraph,
  assertNoDeadLinks,
  linkReport,
  linkReportText,
  citationList,
} from "../src/wiki-features.mjs";
import {
  prepareBodies,
  articleOpening,
  articleSearchText,
  bodyTitle,
} from "../src/build.mjs";

const here = path.dirname(fileURLToPath(import.meta.url));
const real = await readArticles();
const [fixture] = await readArticles(path.join(here, "fixtures/lead"));
const baseline = JSON.parse(
  await fs.readFile(path.join(wikiRoot, "migration-baseline.json"), "utf8"),
);
const assertions = assertionsIn(real);
const sha = (text) => createHash("sha256").update(text).digest("hex");
const { sources } = JSON.parse(await fs.readFile(path.join(wikiRoot, "src/content/catalog.json"), "utf8"));
const front = (await fs.readFile(path.join(here, "fixtures/lead/articles/lead-fixture.md"), "utf8")).split("\n---\n\n")[0] + "\n---\n\n";
const frontLines = front.split("\n").length; // file line of the first body line

function setup(lead = fixture.lead) {
  const copy = { ...structuredClone(fixture), lead };
  const articles = [...real, copy];
  const pages = new Map(articles.map((p) => [p.id, p]));
  const { bodies, wanted, resolvedWanted } = prepareBodies(articles, pages, sources);
  const graph = linkGraph(articles, bodies, assertions, baseline);
  return { articles, pages, bodies, wanted, resolvedWanted, graph };
}

test("the parser keeps the lead apart from the sections", () => {
  assert.equal(fixture.sections[0].id, "statement");
  assert.equal(fixture.sections.length, 2);
  assert.match(fixture.lead, /^<p>Under a row sum/);
  assert.match(fixture.lead, /product percolation in the theory\.<\/p>$/);
  // Bare-text paragraphs are wrapped; HTML paragraphs are kept as written.
  const html = leadHtml(fixture.lead);
  assert.equal(html.match(/<p\b/g).length, 3);
  assert.match(html, /\n<p>The comparison with walks gives the wombat estimate/);
});

test("a lead renders before the contents box, with mathematics and links", () => {
  const { pages, bodies } = setup();
  const sections = bodies.get(fixture.id);
  assert.equal(sections[0].id, "lead");
  const html = transform(articleOpening(fixture, sections, [["connections", "Connections"]]), pages, baseline);
  const lead = html.indexOf('id="section-lead"'),
    context = html.indexOf('class="running-context"'),
    toc = html.indexOf('id="toc"');
  assert.ok(lead >= 0 && lead < context && context < toc, "lead, then running context, then contents");
  assert.match(html.slice(lead, context), /class="katex"/);
  assert.match(html.slice(lead, context), /href="\/articles\/connectivity\/"/);
  assert.match(html.slice(lead, context), /class="wanted-link" data-wanted="lead-wanted-page"/);
  // The contents box lists sections, never the lead.
  assert.ok(!html.slice(toc).includes("#section-lead"));
  assert.match(html.slice(toc), /href="#section-statement"/);
  // Collapse tools still follow from the sections.
  assert.match(html, /data-details-action="expand"/);
  // Without a lead the opening starts with the running context, as before.
  const plainOpening = articleOpening(fixture, sections.filter((s) => !s.lead), []);
  assert.ok(plainOpening.startsWith('<div class="running-context">'));
});

test("the lead is searchable and indexed like section text", () => {
  const { bodies } = setup();
  const text = articleSearchText(fixture, bodies.get(fixture.id), []);
  assert.match(text, /wombat estimate/);
  assert.match(text, /uniform row-sum bound/);
  assert.match(text, /Collapsed proof text/);
  // Section entries index exactly as before: title, a space, the plain text.
  assert.match(text, /Statement The statement section has no link\./);
});

test("backlinks, citations, the link check and the link report cover the lead", () => {
  const { pages, bodies, wanted, graph } = setup();
  assertNoDeadLinks(graph);
  assert.ok(graph.incoming.get("connectivity").some((x) => x.article === fixture.id && x.section === "lead"));
  assert.ok(graph.citing.get("53Z9").some((x) => x.article === fixture.id && x.section === "lead"));
  const html = citationList(
    assertions.filter((a) => a.tag === "53Z9"),
    graph,
    pages,
    (id, section) => bodyTitle(pages.get(id), section),
  );
  assert.match(html, /href="\/articles\/lead-fixture\/#section-lead">Lead fixture: Introduction<\/a>/);
  const report = linkReport([...real, pages.get(fixture.id)], bodies, graph, wanted);
  // Only the lead links out: the lead counts as body for the inline-link report.
  assert.ok(!report.noInlineLinks.includes(fixture.id));
  assert.deepEqual(
    report.unlinkedMentions.filter((u) => u.article === fixture.id),
    [{ article: fixture.id, section: "lead", term: "product percolation", target: "product-model" }],
  );
  assert.deepEqual(report.wantedPages.find((w) => w.slug === "lead-wanted-page")?.from, [
    { article: fixture.id, section: "lead" },
  ]);
  assert.match(linkReportText(report), /lead-fixture#section-lead: "product percolation" -> product-model/);
  // Without the lead's links the article has no inline link at all.
  const bare = setup("<p>No links here.</p>");
  assert.ok(linkReport(bare.articles, bare.bodies, bare.graph, bare.wanted).noInlineLinks.includes(fixture.id));
  // A dead link in the lead fails, naming the article and the lead.
  const dead = setup('<p>See <a href="/articles/no-such-article/">nothing</a>.</p>');
  assert.throws(() => assertNoDeadLinks(dead.graph), /lead-fixture#section-lead: \/articles\/no-such-article\/ \(no such article\)/);
});

async function readOne(body) {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-lead-"));
  try {
    await fs.mkdir(path.join(dir, "articles"));
    await fs.writeFile(path.join(dir, "articles/lead-fixture.md"), front + body);
    return await readArticles(dir);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
}
const tail = "## Statement {#section-statement}\n\n<p>Text.</p>\n";

test("a lead may not contain an assertion anchor, a heading or a collapsible block", async () => {
  const at = (n) => `lead-fixture\\.md:${frontLines + n}: `;
  await assert.rejects(
    readOne(`<p>Intro.</p>\n\n<p>More.</p>\n<a id="tag-53Z9" data-assertion="theorem" data-title="X"></a><p>Stated.</p>\n\n${tail}`),
    new RegExp(at(3) + "an assertion anchor may not stand in the lead"),
  );
  await assert.rejects(
    readOne(`<p>Intro.</p>\n\n### A heading\n\n${tail}`),
    new RegExp(at(2) + "a heading may not stand in the lead"),
  );
  await assert.rejects(
    readOne(`<p>Intro.</p>\n<h3 id="x">A heading</h3>\n\n${tail}`),
    new RegExp(at(1) + "a heading may not stand in the lead"),
  );
  await assert.rejects(
    readOne(`<p>Intro.</p>\n\n:::details Proof\n<p>Hidden.</p>\n:::\n\n${tail}`),
    new RegExp(at(2) + "a collapsible block may not stand in the lead"),
  );
  await assert.rejects(
    readOne(`<p>Intro.</p>\n<details><summary>Proof</summary><p>Hidden.</p></details>\n\n${tail}`),
    new RegExp(at(1) + "a collapsible block may not stand in the lead"),
  );
});

test("a lead has at most three paragraphs and only paragraphs", async () => {
  await assert.rejects(readOne(`<p>1</p><p>2</p>\n\n3\n\n<p>4</p>\n\n${tail}`), /the lead has 4 paragraphs; at most 3/);
  await assert.rejects(readOne(`<div class="math-display">$$x$$</div>\n\n${tail}`), /paragraphs only/);
  await assert.rejects(readOne(`<p>Intro.</p>\n${tail}`), /separated from the first section heading by one blank line/);
  await assert.rejects(
    readOne(`<p>Intro.</p>\n\n## Lead {#section-lead}\n\n<p>Text.</p>\n\n${tail}`),
    /section id "lead" is reserved/,
  );
  await assert.rejects(readOne(`<p>Only an anchor</p>\n\n`), /expected section headings/);
  const [ok] = await readOne(`One.\n\n<p>Two.</p><p>Three.</p>\n\n${tail}`);
  assert.equal(ok.lead, "One.\n\n<p>Two.</p><p>Three.</p>");
  assert.equal(parseLead("x.md", ""), null);
});

test("frozen digests: a frozen article has a lead digest exactly when it has a lead", async () => {
  assert.equal(real.length >= 142, true);
  // The current tree validates against the migration baseline.
  await assert.doesNotReject(checkArticles());
  for (const id of Object.keys(baseline.articles)) {
    const { sections, lead, ...metadata } = real.find((p) => p.id === id);
    assert.equal(sha(JSON.stringify(metadata)), baseline.articles[id].metadataSha256, id);
    if (lead === undefined) assert.equal(baseline.articles[id].lead, undefined, id);
    else assert.equal(baseline.articles[id].lead?.sha256, sha(lead), id);
  }
});

test("adding a lead to a frozen article changes exactly one digest, `lead`", async () => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-lead-frozen-"));
  try {
    await fs.cp(path.join(wikiRoot, "articles"), path.join(dir, "articles"), { recursive: true });
    await fs.copyFile(path.join(wikiRoot, "tags.json"), path.join(dir, "tags.json"));
    const id = Object.keys(baseline.articles)[0];
    const file = path.join(dir, "articles", `${id}.md`);
    const text = await fs.readFile(file, "utf8");
    const at = text.indexOf("\n---\n\n") + "\n---\n\n".length;
    const lead = '<p>A lead with a <a href="/articles/connectivity/">link</a>.</p>';
    await fs.writeFile(file, text.slice(0, at) + lead + "\n\n" + text.slice(at));
    const frozen = structuredClone(baseline);
    await fs.writeFile(path.join(dir, "migration-baseline.json"), JSON.stringify(frozen));
    await assert.rejects(checkArticles(dir), new RegExp(`${id}/lead: exposition changed from migration baseline`));
    frozen.articles[id].lead = { sha256: sha(lead) };
    await fs.writeFile(path.join(dir, "migration-baseline.json"), JSON.stringify(frozen));
    await assert.doesNotReject(checkArticles(dir));
    // Exactly one digest was added; metadata and section digests are untouched.
    const { lead: added, ...rest } = frozen.articles[id];
    assert.deepEqual(rest, baseline.articles[id]);
    assert.deepEqual(added, { sha256: sha(lead) });
    // Editing the lead later is caught by that digest alone.
    await fs.writeFile(file, text.slice(0, at) + "<p>Another lead.</p>\n\n" + text.slice(at));
    await assert.rejects(checkArticles(dir), new RegExp(`${id}/lead: exposition changed`));
    // Removing the lead while the baseline records one is caught too.
    await fs.writeFile(file, text);
    await assert.rejects(checkArticles(dir), new RegExp(`${id}/lead: exposition changed`));
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
});
