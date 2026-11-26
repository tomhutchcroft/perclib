import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { wikiRoot, readArticles, assertionsIn, leadHtml } from "../scripts/articles.mjs";
import { prepareSection, linkGraph, assertNoDeadLinks } from "../src/wiki-features.mjs";
import { prepareBodies, aboutPage, applyBasePath, bodyTitle } from "../src/build.mjs";
import { transform, document } from "../src/render.mjs";
import {
  catalogue,
  expandCitations,
  newCitationState,
  parseCitation,
  referencesList,
  bibliographyPage,
  plainCitations,
  plainCitationsText,
  assertNoPlainCitations,
  failOnPlainCitations,
  outboundLinks,
} from "../src/citations.mjs";

const here = path.dirname(fileURLToPath(import.meta.url));
const { sources } = JSON.parse(await fs.readFile(path.join(wikiRoot, "src/content/catalog.json"), "utf8"));
const byKey = catalogue(sources);
const real = await readArticles();
const [fixture] = await readArticles(path.join(here, "fixtures/citations"));
const baseline = JSON.parse(await fs.readFile(path.join(wikiRoot, "migration-baseline.json"), "utf8"));
const assertions = assertionsIn(real);

function setup() {
  const articles = [...real, fixture];
  const pages = new Map(articles.map((p) => [p.id, p]));
  return { articles, pages, ...prepareBodies(articles, pages, sources) };
}
const sectionHtml = (bodies, id) => bodies.get(fixture.id).find((s) => s.id === id).html;

test("markup: [@key] and [@key, locator], several keys per bracket", () => {
  assert.deepEqual(parseCitation("dct-sharpness"), [{ key: "dct-sharpness", locator: undefined }]);
  assert.deepEqual(parseCitation("grimmett, §3; @dct-sharpness"), [
    { key: "grimmett", locator: "§3" },
    { key: "dct-sharpness", locator: undefined },
  ]);
  assert.throws(() => parseCitation("grimmett,  "), /empty locator/);
  assert.throws(() => parseCitation("grimmett; dct"), /malformed citation/);
  // Every citation in an existing article parses and names a catalogue work.
  for (const p of real)
    for (const s of [p.lead ?? "", ...p.sections.map((x) => x.html)])
      for (const [, inner] of s.matchAll(/\[@([^\]]*)\]/g))
        for (const { key } of parseCitation(inner, p.id)) assert.ok(byKey.has(key), `${p.id}: ${key}`);
});

test("a citation key missing from the catalogue fails with a clear message", () => {
  assert.throws(
    () => expandCitations("<p>[@no-such-work, Theorem 2]</p>", byKey, "fixture/statement"),
    /fixture\/statement: citation key "no-such-work" is not in the source catalogue/,
  );
  const broken = { ...structuredClone(fixture), id: "broken" };
  broken.sections[0].html = "<p>[@no-such-work]</p>";
  assert.throws(() => prepareBodies([broken], new Map([["broken", broken]]), sources), /broken\/statement: citation key "no-such-work"/);
});

test("rendering keeps the locator in the visible text and links to #ref-<key>", () => {
  const { bodies } = setup();
  const lead = sectionHtml(bodies, "lead");
  assert.match(
    lead,
    /\[<a class="citation" id="cite-dct-sharpness-1" href="#ref-dct-sharpness">Duminil-Copin–Tassion, Theorem 1\.1<\/a>\]/,
  );
  // Mathematics before the citation is untouched; "<" inside it is not a tag.
  assert.match(lead, /\$p<p_c\$ was proved by \[<a class="citation"/);
  const statement = sectionHtml(bodies, "statement");
  assert.match(statement, /\[<a [^>]*id="cite-grimmett-1" href="#ref-grimmett">Grimmett, §3<\/a>; <a [^>]*id="cite-dct-sharpness-2"[^>]*>Duminil-Copin–Tassion<\/a>\]/);
  assert.match(statement, /<code>\[@not-a-key\]<\/code>/);
});

test("the book in preparation: a reference like any other, no link and no locator", () => {
  const { bodies } = setup();
  assert.match(sectionHtml(bodies, "lead"), />T\. Hutchcroft, book in preparation<\/a>\]/);
  const entry = /<li id="ref-hutchcroft-book">[\s\S]*?<\/li>/.exec(sectionHtml(bodies, "references"))[0];
  assert.doesNotMatch(entry, /href="http/);
  assert.deepEqual(outboundLinks(byKey.get("hutchcroft-book")), []);
  assert.throws(() => expandCitations("[@hutchcroft-book, Chapter 2]", byKey, "x"), /without locators \(ruling 6\)/);
});

test("References: only the works cited on the page, with backlinks to every citation", () => {
  const { bodies } = setup();
  const entries = bodies.get(fixture.id);
  const refs = entries.at(-1);
  assert.equal(refs.id, "references");
  assert.equal(bodyTitle(fixture, "references"), "References");
  const ids = [...refs.html.matchAll(/<li id="ref-([^"]+)"/g)].map((m) => m[1]);
  assert.deepEqual(ids.sort(), ["dct-sharpness", "grimmett", "hutchcroft-book"]);
  const dct = /<li id="ref-dct-sharpness">[\s\S]*?<\/li>/.exec(refs.html)[0];
  assert.deepEqual([...dct.matchAll(/href="#(cite-[^"]+)"/g)].map((m) => m[1]), [
    "cite-dct-sharpness-1",
    "cite-dct-sharpness-2",
    "cite-dct-sharpness-3",
  ]);
  assert.match(dct, /Hugo Duminil-Copin and Vincent Tassion/);
  assert.match(dct, /<a class="ref-arxiv" href="https:\/\/arxiv\.org\/abs\/1502\.03050v3">arXiv:1502\.03050<\/a>/);
  assert.match(refs.html, /<a class="ref-doi" href="https:\/\/doi\.org\/10\.1007\/978-3-662-03981-6">/);
  // Every backlink target and every #ref- target exists: no dead links.
  const all = entries.map((s) => s.html).join("\n");
  for (const m of all.matchAll(/href="#((?:cite|ref)-[^"]+)"/g)) assert.ok(all.includes(`id="${m[1]}"`), m[1]);
  const { articles, bodies: b } = setup();
  const graph = linkGraph(articles, b, assertions, baseline);
  assert.deepEqual(graph.dead.filter((d) => d.article === fixture.id), []);
  assertNoDeadLinks(graph);
  // An article that already has a References section gets the list appended to it.
  const own = { ...structuredClone(fixture), id: "own-refs" };
  own.sections.push({ id: "references", title: "References", html: "<p>Hand-written.</p>" });
  const ob = prepareBodies([own], new Map([["own-refs", own]]), sources).bodies.get("own-refs");
  assert.equal(ob.filter((s) => s.id === "references").length, 1);
  assert.match(ob.at(-1).html, /^<p>Hand-written\.<\/p>\n<ol class="references">/);
});

test("collapsed blocks: a citation inside <details> carries the id its backlink targets", () => {
  const { bodies } = setup();
  const proof = sectionHtml(bodies, "proof");
  const details = /<details\b[\s\S]*?<\/details>/.exec(proof)[0];
  assert.match(details, /id="cite-dct-sharpness-3" href="#ref-dct-sharpness">Duminil-Copin–Tassion, Lemma 2\.1</);
  assert.match(sectionHtml(bodies, "references"), /href="#cite-dct-sharpness-3"/);
  // article.js opens every <details> enclosing the target of a same-page
  // fragment link (tested in article-script.test.mjs); citation ids are ordinary ids.
});

test("plain-text citations are reported, not failed, until the switch is set", () => {
  assert.equal(failOnPlainCitations, false);
  const bodies = new Map([
    [
      "x",
      [
        {
          id: "s",
          html: '<p>By Hutchcroft (2022) and [DCT16, Theorem 1.1], arXiv:2106.06400, and the book in preparation. Linked: <a href="https://arxiv.org/abs/1">arXiv:1904.05804</a>. $f(2015)$</p>' +
            referencesList({ counts: new Map([["grimmett", 1]]), order: ["grimmett"] }, byKey),
        },
      ],
    ],
  ]);
  const found = plainCitations([{ id: "x" }], bodies);
  assert.deepEqual(found.map((f) => f.text), ["Hutchcroft (2022)", "[DCT16, Theorem 1.1]", "arXiv:2106.06400", "book in preparation"]);
  assert.match(plainCitationsText(found), /Plain-text citations not written as \[@key\] \(advisory\): 4/);
  assert.doesNotThrow(() => assertNoPlainCitations(found));
  assert.throws(() => assertNoPlainCitations(found, true), /4 plain-text citations/);
  // Expanded citations are links and are not reported.
  const { articles, bodies: b } = setup();
  assert.deepEqual(plainCitations([fixture], b).filter((f) => f.article === fixture.id), []);
  assert.ok(plainCitations(articles, b).length > 0, "the existing backlog is reported");
});

test("site bibliography lists every catalogue entry with its citing articles, under /perclib/", () => {
  const { citedBy } = setup();
  assert.deepEqual(citedBy.get("dct-sharpness"), [{ article: fixture.id, title: fixture.title }]);
  const page = bibliographyPage(sources, citedBy);
  assert.equal(page.match(/<li id="ref-/g).length, sources.length);
  assert.match(page, /<li id="ref-dct-sharpness">[\s\S]*?Cited in <a href="\/articles\/citation-fixture\/#cite-dct-sharpness-1">Citation fixture<\/a>/);
  assert.match(page, /<li id="ref-mathlib">[\s\S]*?Not yet cited inline\./);
  const about = aboutPage({ commit: null, date: "today" }, { provenance: null }, { articles: 1, assertions: 1, proved: null });
  assert.match(about, /href="\/bibliography\/"/);
  const site = applyBasePath(
    new Map([
      ["bibliography/index.html", document("Bibliography", page, { collections: [] })],
      ["about/index.html", document("About", about, { collections: [] })],
    ]),
    "/perclib/",
  );
  const bib = site.get("bibliography/index.html");
  assert.match(bib, /href="\/perclib\/articles\/citation-fixture\/#cite-dct-sharpness-1"/);
  assert.match(bib, /href="\/perclib\/sources\/dct-sharpness\/"/);
  assert.match(bib, /href="https:\/\/arxiv\.org\/abs\/1502\.03050v3"/);
  assert.doesNotMatch(bib, /href="\/(?!perclib\/)/);
  assert.match(site.get("about/index.html"), /href="\/perclib\/bibliography\/"/);
  // Same-page fragments are not prefixed.
  const art = applyBasePath(new Map([["a/index.html", `<p> ${sectionHtml(setup().bodies, "lead")}</p>`]]), "/perclib/");
  assert.match(art.get("a/index.html"), /href="#ref-dct-sharpness"/);
});

test("existing articles without citation markup are unchanged", () => {
  const { bodies } = setup();
  const pages = new Map(real.map((p) => [p.id, p]));
  for (const id of ["bk-inequality", "triangle-condition"]) {
    const p = pages.get(id);
    const expected = [
      ...(p.lead === undefined ? [] : [{ id: "lead", html: leadHtml(p.lead) }]),
      ...p.sections,
    ].map((s) => ({ id: s.id, html: prepareSection(s.html, pages, `${id}/${s.id}`).html }));
    const got = bodies.get(id);
    assert.deepEqual(got.map((s) => s.id), expected.map((s) => s.id), id);
    got.forEach((s, i) => {
      assert.equal(s.html, expected[i].html, `${id}/${s.id}`);
      assert.equal(transform(s.html, pages, baseline), transform(expected[i].html, pages, baseline));
    });
  }
});
