import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createRequire } from "node:module";
import { execFileSync } from "node:child_process";
import { checkArticles, checkHistory } from "../scripts/check-articles.mjs";
import { validateOccurrences, concordancePanel } from "./concordance.mjs";
import { collectHistory, historyPage, recordedReferenceHistory } from "./history.mjs";
import { coveragePage, readingMapPage } from "./coverage.mjs";
import { historyCsv, dailyHistoryCsv, fileHistoryCsv } from "./history-csv.mjs";
import { validateProofUses, frontierPage } from "./frontier.mjs";
import { loadEvidence, evidencePanel, statusFor } from "./manifest.mjs";
import { readRegistry, leadId, leadHtml } from "../scripts/articles.mjs";
import { loadRecords } from "./records.mjs";
import { compactMathLayout } from "./math-layout.mjs";
import {
  prepareSection,
  linkGraph,
  assertNoDeadLinks,
  linkReport,
  linkReportText,
  tableOfContents,
  hasCollapsibles,
  collapseTools,
  citationList,
  annotatePreviews,
  previewData,
  previewScript,
} from "./wiki-features.mjs";
import {
  catalogue,
  expandCitations,
  newCitationState,
  withReferences,
  bibliographyPage,
  plainCitations,
  plainCitationsText,
  assertNoPlainCitations,
  failOnPlainCitations,
  referencesSectionId,
  referencesTitle,
} from "./citations.mjs";
import { loadErrata, errataPage, articleErrata, errataIndex, errataResolutionText, errataVersionText } from "./errata.mjs";
import {
  esc,
  decode,
  plain,
  articleUrl,
  transform,
  heading,
  item,
  railBlock,
  document,
  leadSection,
  unfinishedNotice,
} from "./render.mjs";
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
// Collapsible blocks and wanted links are expanded once; every later use of
// an article body (pages, search, link graph) sees the same HTML. The lead,
// when present, is the first body entry, with id `lead` and an empty title, so
// backlinks, the link checks and the link report treat it as body text.
// Citations [@key] (src/citations.mjs) are expanded against the source
// catalogue `sources`; an article citing any work gets a References list.
// `citedBy` maps each cited catalogue key to the articles citing it.
export function prepareBodies(articles, pages, sources = []) {
  const bodies = new Map(),
    wanted = [],
    resolvedWanted = [],
    citedBy = new Map(),
    byKey = catalogue(sources);
  for (const p of articles) {
    const citations = newCitationState();
    const entries = [
        ...(p.lead === undefined
          ? []
          : [{ id: leadId, title: "", html: leadHtml(p.lead), lead: true }]),
        ...p.sections,
      ].map((s) => {
        const where = `${p.id}/${s.id}`;
        const r = prepareSection(s.html, pages, where);
        const at = (w) => ({ ...w, article: p.id, section: s.id });
        wanted.push(...r.wanted.map(at));
        resolvedWanted.push(...r.resolved.map(at));
        const html = expandCitations(r.html, byKey, where, citations).html;
        return s.lead
          ? { id: s.id, title: s.title, html, lead: true }
          : { id: s.id, title: s.title, html };
      });
    bodies.set(p.id, withReferences(entries, citations, byKey));
    for (const key of citations.order)
      citedBy.set(key, [...(citedBy.get(key) ?? []), { article: p.id, title: p.title }]);
  }
  return { bodies, wanted, resolvedWanted, citedBy };
}
// Title of a body entry in backlink lists.
export const bodyTitle = (page, section) =>
  section === leadId
    ? "Introduction"
    : (page.sections.find((s) => s.id === section)?.title ??
      (section === referencesSectionId ? referencesTitle : undefined));
// The opening of an article page after its header: lead, running context,
// contents box (sections only) and the collapse tools.
export function articleOpening(p, sections, extra) {
  const lead = sections.find((s) => s.lead),
    rest = sections.filter((s) => !s.lead);
  return (
    (lead ? leadSection(lead.html) : "") +
    `<div class="running-context"><h2>Running context</h2><ul>${p.context.map((c) => `<li>${c}</li>`).join("")}</ul></div>` +
    tableOfContents(rest, extra) +
    (hasCollapsibles(sections) ? collapseTools() : "")
  );
}
// Search text of an article: metadata, every body entry (lead, sections and
// collapsed blocks) and its assertion titles.
export const articleSearchText = (p, body, assertions) =>
  [
    p.title,
    p.summary,
    ...p.aliases,
    ...p.context,
    ...body.map((s) => (s.title ? s.title + " " : "") + plain(s.html)),
    ...assertions
      .filter((a) => a.article === p.id)
      .map((a) => a.tag + " " + a.title),
  ].join(" ");
export function validateLinks(files) {
  for (const [file, html] of files) {
    if (!file.endsWith(".html")) continue;
    for (const m of html.matchAll(/(?:href|src)="([^"]+)"/g)) {
      const href = decode(m[1]);
      if (/^(https?:|mailto:|data:)/.test(href)) continue;
      const url = new URL(href, `https://wiki.invalid/${file}`);
      let target = decodeURIComponent(url.pathname).slice(1);
      if (!target || target.endsWith("/")) target += "index.html";
      if (!files.has(target))
        throw Error(`${file}: missing destination ${href}`);
      if (
        url.hash &&
        target.endsWith(".html") &&
        !files
          .get(target)
          .includes(`id="${decodeURIComponent(url.hash.slice(1))}"`)
      )
        throw Error(`${file}: missing anchor ${href}`);
    }
  }
}
// The site may be served under a path prefix (GitHub Pages serves this
// repository at /perclib/). Pages are generated with root-relative URLs and
// checked as such; applyBasePath then prefixes every one of them. The value is
// "/" or "/a/b/" made of URL-safe path segments; anything else is refused.
export function normalizeBasePath(value) {
  if (value === undefined || value === null || value === "" || value === "/")
    return "/";
  const segments = String(value).replace(/^\/|\/$/g, "").split("/");
  if (
    !segments.every(
      (s) => /^[A-Za-z0-9._~-]+$/.test(s) && s !== "." && s !== "..",
    )
  )
    throw Error(`Invalid base path: ${JSON.stringify(value)}`);
  return `/${segments.join("/")}/`;
}
// Prefix every root-relative URL of the generated site with the base path: the
// href, src and action attributes and refresh redirects of every page, the
// search index, and (through data-base on <html>) the search script's fetch.
export function applyBasePath(files, base) {
  if (base === "/") return files;
  const prefix = (url) =>
    url.startsWith("/") && !url.startsWith("//") ? base + url.slice(1) : url;
  const result = new Map();
  for (const [file, content] of files) {
    if (file.endsWith(".html"))
      result.set(
        file,
        content
          .replace(
            /(\s)(href|src|action)="([^"]*)"/g,
            (_, space, attr, url) => `${space}${attr}="${prefix(url)}"`,
          )
          .replace(
            /content="0;url=([^"]*)"/g,
            (_, url) => `content="0;url=${prefix(url)}"`,
          )
          .replace(/^<!doctype html><html lang="en"/, `$&` + ` data-base="${base}"`),
      );
    else if (file === "search-index.json")
      result.set(
        file,
        JSON.stringify(
          JSON.parse(content).map((row) => ({ ...row, url: prefix(row.url) })),
        ) + "\n",
      );
    else result.set(file, content);
  }
  return result;
}
// Articles that have been through the critic and restructuring carry no draft
// marker. The list is src/passed-articles.json (wiki/README.md, "Deployment").
export async function loadPassedArticles(
  file = path.join(root, "src/passed-articles.json"),
  articles,
) {
  const ids = JSON.parse(await fs.readFile(file, "utf8"));
  if (!Array.isArray(ids) || !ids.every((id) => typeof id === "string"))
    throw Error("passed-articles.json must be an array of article ids");
  if (new Set(ids).size !== ids.length)
    throw Error("passed-articles.json lists an article twice");
  const known = new Set(articles.map((p) => p.id));
  for (const id of ids)
    if (!known.has(id)) throw Error(`passed-articles.json: unknown article ${id}`);
  return new Set(ids);
}
export const draftMarker = (id, passed) =>
  passed.has(id)
    ? ""
    : '<p class="draft-marker"><span class="draft-label">Draft</span>Not yet through review and restructuring; see <a href="/about/">About</a>.</p>';
const count = (n) => n.toLocaleString("en-US");
// The lead of the home page: the banner's message in one sentence, with the
// counts of this build. `proved` is null when no manifest was supplied.
export const homeStatus = ({ articles, assertions, proved }) =>
  `<p class="home-status">This wiki is unfinished and under active construction, so articles may be incomplete and statements and proofs may contain errors; ${
    proved === null
      ? `it has ${count(articles)} articles and ${count(assertions)} assertions, and formal status is not shown in this build`
      : `of its ${count(articles)} articles and ${count(assertions)} assertions, only the ${count(proved)} marked 'proved' have been checked in Lean`
  } (see <a href="/about/">About</a>).</p>`;
// Commit and date of this build, for the About page.
export function buildInfo({ buildCommit, buildDate } = {}) {
  let commit = buildCommit ?? process.env.WIKI_BUILD_COMMIT ?? null;
  if (!commit)
    try {
      commit = execFileSync("git", ["rev-parse", "HEAD"], {
        cwd: root,
        encoding: "utf8",
        stdio: ["ignore", "pipe", "ignore"],
      }).trim();
    } catch {
      commit = null;
    }
  if (commit !== null && !/^[a-f0-9]{40}$/.test(commit))
    throw Error(`Invalid build commit: ${commit}`);
  const date = buildDate ?? new Date();
  return {
    commit,
    date: date.toISOString().slice(0, 16).replace("T", " ") + " UTC",
  };
}
const repositoryUrl = "https://github.com/tomhutchcroft/perclib";
// The About page (not an article; it carries no assertion tags).
export function aboutPage(info, evidence, counts) {
  const formal = evidence.provenance
    ? `Formal status on this site comes from the Lean manifest compiled at commit <code>${esc(evidence.provenance.commit)}</code> (<a href="${esc(evidence.provenance.runUrl)}">${esc(evidence.provenance.runLabel ?? "successful CI run")}</a>): ${count(counts.proved)} of ${count(counts.assertions)} assertions are proved in Lean.`
    : "This build shows no formal status: no compiled Lean manifest was supplied.";
  const section = (id, title, html) =>
    `<section class="article-section" id="about-${id}"><h2>${title}</h2>${html}</section>`;
  return (
    heading("About this wiki") +
    section(
      "project",
      "What this is",
      "<p>The Percolation Library is a mathematical reference on percolation theory, arranged like an encyclopedia but with complete proofs, developed together with PercLib, a library of formal proofs in Lean 4 and mathlib. Each citable assertion has a permanent tag; a citation identifies an assertion and does not by itself certify a proof. Where a Lean statement carries the same tag, its formal status is shown with the assertion.</p>",
    ) +
    section(
      "progress",
      "Work in progress",
      `<p>${esc(unfinishedNotice.replace(/; see About\.$/, "."))} Articles marked “Draft” have not yet been through critical review and restructuring.</p>`,
    ) +
    section(
      "status",
      "What the formal statuses mean",
      "<ul><li><strong>proved</strong>: Lean has checked a proof of the tagged Lean statement, using only the standard axioms (propext, Classical.choice, Quot.sound).</li><li><strong>proved-modulo</strong>: Lean has checked a proof that assumes named results from the literature; those inputs are listed with the assertion and are not proved here.</li><li><strong>stated</strong>: a Lean statement exists and has been reviewed as matching the prose, but it has no proof yet.</li><li><strong>Compiled statement; correspondence pending</strong>: a Lean statement exists, but nobody has yet checked that it says what the prose says.</li><li><strong>unformalised</strong>: no Lean statement is attached to the assertion.</li></ul><p>Only assertions marked “proved” have been checked in Lean. A prose proof without the “proved” mark has not been machine-checked, however complete it looks. Whether a Lean statement matches the prose is reviewed separately, and that review is shown next to the status.</p>",
    ) +
    section(
      "errata",
      "Errata",
      '<p>The <a href="/errata/">source errata</a> record problems found in the published literature while this wiki was written, with proposed corrections. Every entry is provisional until Tom Hutchcroft confirms it; confirmed entries say so.</p>',
    ) +
    section(
      "bibliography",
      "Bibliography",
      '<p>Articles cite published works by a link to a References list at the foot of the page. The <a href="/bibliography/">bibliography</a> lists every work in the source catalogue with the articles that cite it.</p>',
    ) +
    section(
      "authorship",
      "How the text was written",
      "<p>Much of the text was drafted with AI assistance and is being reviewed.</p>",
    ) +
    section(
      "contact",
      "Responsibility and reporting errors",
      `<p>Tom Hutchcroft is responsible for this wiki. To report an error, open an issue in the <a href="${repositoryUrl}/issues/new/choose">perclib repository</a> with one of its issue templates: “Mathematical gap” for a statement that is false, vacuous or missing a hypothesis, or a proof that does not work; “Question” for anything else. Please name the article and the assertion tag.</p>`,
    ) +
    section(
      "licence",
      "Licence",
      `<p>The Lean code and the tooling that builds this site are licensed under the Apache License, Version 2.0. The wiki prose is © Tom Hutchcroft and the PercLib contributors, licensed under <a href="https://creativecommons.org/licenses/by/4.0/">Creative Commons Attribution 4.0 International (CC BY 4.0)</a>; see <a href="${repositoryUrl}/blob/main/wiki/NOTICE">NOTICE</a>. Statements quoted from published papers remain their authors'. Suggested attribution: “PercLib wiki, T. Hutchcroft and contributors, https://tomhutchcroft.github.io/perclib/, CC BY 4.0”. Mathematics is typeset with KaTeX (MIT licence).</p>`,
    ) +
    section(
      "build",
      "This build",
      `<p>Built from ${
        info.commit
          ? `commit <a href="${repositoryUrl}/commit/${info.commit}"><code>${info.commit}</code></a>`
          : "an unrecorded commit"
      } on ${esc(info.date)}. ${formal}</p><p>Every page is rendered before publication, and search runs in your browser over a static index.</p>`,
    )
  );
}
export async function build(
  output = path.join(root, "dist"),
  evidenceOptions = {},
) {
  const basePath = normalizeBasePath(
    evidenceOptions.basePath ?? process.env.WIKI_BASE_PATH,
  );
  const { articles, assertions, baseline } = await checkArticles();
  // The tag-history base: an explicit option or WIKI_HISTORY_BASE (the Pages
  // workflow, whose manual runs have no push base), else checkHistory's default.
  await checkHistory(
    undefined,
    evidenceOptions.historyBase ?? (process.env.WIKI_HISTORY_BASE || undefined),
  );
  const registry = await readRegistry();
  const evidence = await loadEvidence(assertions, {
    reviewsPath: path.join(root, "reviews/correspondence.json"),
    ...evidenceOptions,
  });
  const records = await loadRecords(root, articles, assertions);
  const passed = await loadPassedArticles(
    evidenceOptions.passedArticlesPath,
    articles,
  );
  const counts = {
    articles: articles.length,
    assertions: assertions.length,
    proved: evidence.entries
      ? [...evidence.entries.values()].filter((e) => e.proof_status === "proved")
          .length
      : null,
  };
  const proofUses = validateProofUses(
    evidenceOptions.proofUsesPath
      ? JSON.parse(await fs.readFile(evidenceOptions.proofUsesPath, "utf8"))
      : records.proofUses,
    assertions,
  );
  const evidenceCounts = evidence.entries
    ? [...evidence.entries.values()].reduce(
        (counts, entry) => {
          const result = statusFor(entry, evidence.reviews);
          const status =
            result.status ?? "Compiled statement; correspondence pending";
          counts.status[status] = (counts.status[status] ?? 0) + 1;
          if (entry.proof_status !== "unformalised")
            counts.review[result.reviewState] =
              (counts.review[result.reviewState] ?? 0) + 1;
          return counts;
        },
        { status: {}, review: {} },
      )
    : null;
  const evidenceSummary = evidenceCounts
    ? "<h2>Compiled evidence snapshot</h2><p>This is one supplied snapshot, not a historical series. Proof status and prose correspondence are separate counts.</p>" +
      Object.entries(evidenceCounts)
        .map(
          ([axis, counts]) =>
            "<h3>" +
            (axis === "status"
              ? "Assertion status"
              : "Correspondence of compiled statements") +
            "</h3><ul>" +
            Object.entries(counts)
              .map(
                ([label, count]) =>
                  "<li>" + esc(label) + ": " + count + "</li>",
              )
              .join("") +
            "</ul>",
        )
        .join("")
    : "";
  const history = collectHistory(root, evidenceOptions.historyRef);
  const pages = new Map(articles.map((p) => [p.id, p]));
  const { bodies, wanted, resolvedWanted, citedBy } = prepareBodies(
    articles,
    pages,
    records.sources,
  );
  const graph = linkGraph(articles, bodies, assertions, baseline);
  assertNoDeadLinks(graph);
  const report = linkReport(articles, bodies, graph, wanted);
  const strictCitations = evidenceOptions.strictCitations ?? failOnPlainCitations;
  const unlinkedCitations = plainCitations(articles, bodies);
  assertNoPlainCitations(unlinkedCitations, strictCitations);
  const sectionTitle = (id, section) => bodyTitle(pages.get(id), section);
  const read = async (file) =>
    JSON.parse(await fs.readFile(path.join(root, "src/content", file), "utf8"));
  const { collections, sources } = records;
  const errata = await loadErrata(root, sources, assertions);
  const occurrences = validateOccurrences(
    evidenceOptions.occurrencesPath
      ? JSON.parse(await fs.readFile(evidenceOptions.occurrencesPath, "utf8"))
      : records.occursIn,
    sources,
    assertions,
  );
  const concordance = (rows) =>
    concordancePanel(rows, sources, assertions, evidence);
  const reuse = await read("reuse-audit.json");
  const files = new Map();
  const format = (html) => transform(html, pages, baseline);
  const add = (
    route,
    title,
    body,
    rail = "",
    description = "",
    extraHead = "",
  ) => {
    const file = route ? `${route}/index.html` : "index.html";
    if (files.has(file)) throw Error(`Duplicate route: ${route}`);
    files.set(
      file,
      document(title, format(body), {
        collections,
        rail: format(rail),
        description,
        extraHead,
      }),
    );
  };
  const links = (ids) =>
    ids
      .map((id) => {
        if (!pages.has(id)) throw Error(`Missing article ${id}`);
        return `<a class="rail-link" href="${articleUrl(id)}">${esc(pages.get(id).title)}</a>`;
      })
      .join("");
  const occurrence = (o) => {
    if (!pages.has(o.pageId))
      throw Error(`Missing occurrence article ${o.pageId}`);
    if (
      o.sectionId &&
      !pages.get(o.pageId).sections.some((s) => s.id === o.sectionId)
    )
      throw Error(`Missing occurrence section ${o.sectionId}`);
    return `<div class="article-section"><h3><a href="${articleUrl(o.pageId)}${o.sectionId ? "#section-" + o.sectionId : ""}">${esc(o.label)}</a></h3><p>${esc(o.locator)}</p><p>${esc(o.relationship)} · ${esc(o.status)}</p><p>${esc(o.note)}</p></div>`;
  };
  for (const p of articles) {
    const own = assertions.filter((a) => a.article === p.id);
    const incoming = [
      ...new Set(graph.incoming.get(p.id).map((x) => x.article)),
    ].sort((a, b) => pages.get(a).title.localeCompare(pages.get(b).title));
    const previewKeys = new Set();
    const sections = bodies.get(p.id).map((s) => {
      const r = annotatePreviews(s.html, p.id, pages, assertions, baseline);
      r.used.forEach((k) => previewKeys.add(k));
      return { ...s, html: r.html };
    });
    const body =
      heading(p.title, p.subtitle || p.summary, p.kind) +
      draftMarker(p.id, passed) +
      articleErrata(p.id, errata, assertions) +
      articleOpening(p, sections, [
        ["connections", "Connections"],
        ["sources", "Sources"],
        ["citations", "Assertion citations"],
        ["formal-evidence", "Formal evidence"],
      ]) +
      sections
        .filter((s) => !s.lead)
        .map(
          (s) =>
            `<section class="article-section" id="section-${s.id}"><h2>${esc(s.title)}</h2>${s.html}</section>`,
        )
        .join("") +
      `<section class="article-section" id="connections"><h2>Connections</h2><p>These are editorial reading links, not dependencies extracted from Lean.</p><h3>Prerequisites</h3>${links(p.prototypeUses)}<h3>Related articles</h3>${links(p.related)}<h3>What links here</h3>${links(incoming)}</section>` +
      `<section class="article-section" id="sources"><h2>Sources</h2><ul>${p.sourceIds
        .map((id) => {
          const source = sources.find((s) => s.id === id);
          if (!source) throw Error(`Missing source ${id}`);
          return `<li><a href="/sources/${id}/">${esc(source.shortName)}</a></li>`;
        })
        .join(
          "",
        )}</ul>${sources.flatMap((s) => s.occurrences.filter((o) => o.pageId === p.id).map((o) => `<h3><a href="/sources/${s.id}/">${esc(s.shortName)}</a></h3>${occurrence(o)}`)).join("")}</section>` +
      `<section class="article-section" id="citations"><h2>Assertion citations</h2><p>Each assertion with the article sections that link to it.</p>${citationList(own, graph, pages, sectionTitle)}</section>` +
      evidencePanel(own, evidence) +
      concordance(occurrences.filter((o) => own.some((a) => a.tag === o.tag)));
    const rail =
      railBlock(
        "On this page",
        sections
          .filter((s) => !s.lead)
          .map((s) => `<a href="#section-${s.id}">${esc(s.title)}</a>`)
          .join("") +
          '<a href="#connections">Connections</a><a href="#sources">Sources</a>',
      ) +
      railBlock(
        "Cite an assertion",
        `<div class="tag-citations">${own.map((a) => `<a href="/tag/${a.tag}/" title="${esc(a.title)}">${a.tag}</a>`).join("")}</div>`,
      ) +
      railBlock("Related reading", links(p.related));
    add(
      `articles/${p.id}`,
      p.title,
      body,
      rail,
      p.summary,
      '<script defer src="/assets/article.js"></script>' +
        previewScript(previewData(previewKeys, pages, assertions)),
    );
    add(
      p.id,
      p.title,
      `<p>This article is at <a href="${articleUrl(p.id)}">${esc(p.title)}</a>.</p>`,
      "",
      "",
      `<meta http-equiv="refresh" content="0;url=${articleUrl(p.id)}">`,
    );
  }
  add(
    "articles",
    "Article index",
    heading("Article index", "Browse the mathematical reference.") +
      articles.map(item).join(""),
  );
  add(
    "",
    "Library overview",
    heading(
      "A connected theory of percolation.",
      "A mathematical encyclopedia of models, results, and proofs.",
      "The mathematical library",
    ) +
      homeStatus(counts) +
      `<div class="collection-grid">${collections
        .map(
          (c) =>
            `<section class="collection"><h2 class="collection-heading"><a href="/collections/${c.id}/">${esc(c.title)}</a><small>${c.pages.length} pages</small></h2><p>${esc(c.description)}</p>${c.pages
              .slice(0, 3)
              .map((id) => item(pages.get(id)))
              .join("")}</section>`,
        )
        .join(
          "",
        )}</div><section class="featured-theorem"><p class="eyebrow">One complete argument to explore</p><h2><a href="${articleUrl("subcritical-bound")}">From a row-sum bound to finite clusters</a></h2><p>Count simple paths, sum walk weights, and bound susceptibility.</p></section>`,
  );
  add(
    "subjects",
    "Subject index",
    heading("Subjects") +
      collections
        .map(
          (c) =>
            `<section class="article-section"><h2><a href="/collections/${c.id}/">${esc(c.title)}</a></h2><p>${esc(c.description)}</p></section>`,
        )
        .join(""),
  );
  for (const c of collections)
    add(
      `collections/${c.id}`,
      c.title,
      heading(c.title, c.description) +
        c.pages
          .map((id) => {
            if (!pages.has(id)) throw Error(`Missing article ${id}`);
            return item(pages.get(id));
          })
          .join(""),
    );
  add(
    "sources",
    "Source concordance",
    heading(
      "Source concordance",
      "Bibliographic records and recorded article correspondences.",
    ) +
      `<p><a href="/errata/">Source errata and provisional corrections</a></p>` +
      '<p><a href="/coverage/">Source coverage worklist</a> — inventoried source texts and reading maps, including gaps.</p>' +
      concordance(occurrences) +
      sources
        .map(
          (s) =>
            `<section class="article-section"><h2><a href="/sources/${s.id}/">${esc(s.title)}</a></h2><p>${[s.author, s.year].filter((v) => v != null).map(esc).join(" · ")}</p><p>${esc(s.description)}</p></section>`,
        )
        .join(""),
  );
  const inventories = new Map();
  const inventoryRoot = evidenceOptions.readingMapsPath ?? path.join(root, "sources");
  let inventoryFiles;
  try { inventoryFiles = await fs.readdir(inventoryRoot, { withFileTypes: true }); }
  catch (error) { if (error.code !== "ENOENT") throw error; inventoryFiles = []; }
  for (const file of inventoryFiles.sort((a, b) => a.name.localeCompare(b.name))) {
    if (!file.name.endsWith(".md")) continue;
    if (!file.isFile() || !/^[A-Za-z0-9]+(?:[.-][A-Za-z0-9]+)*\.md$/.test(file.name))
      throw Error(`Invalid reading map file: ${file.name}`);
    const markdown = (await fs.readFile(path.join(inventoryRoot, file.name), "utf8")).replace(/\r\n/g, "\n");
    const title = /^# ([^\n]+)\n/.exec(markdown)?.[1];
    if (!title) throw Error(`Reading map needs a title: ${file.name}`);
    inventories.set(file.name.slice(0, -3), { title, markdown });
  }
  add("coverage", "Source coverage worklist",
    coveragePage(await fs.readFile(evidenceOptions.coveragePath ?? path.join(root, "COVERAGE.md"), "utf8"), pages, inventories));
  for (const [id, record] of inventories)
    add(`coverage/sources/${id}`, record.title, readingMapPage(record, pages, inventories));
  for (const s of sources)
    add(
      `sources/${s.id}`,
      s.shortName,
      heading(s.title, s.description) +
        (errata.some((e) => e.source === s.id) ? `<p><a href="/errata/${s.id}/">Source errata and provisional corrections</a></p>` : "") +
        concordance(occurrences.filter((o) => o.source === s.id)) +
        `<p>${[s.author, s.year, s.edition].filter((v) => v != null).map(esc).join(" · ")}</p>${s.url ? `<p><a href="${esc(s.url)}">Source</a></p>` : ""}<p>${esc(s.coverageNote)}</p>` +
        s.occurrences.map(occurrence).join(""),
    );
  add("errata", "Source errata", errataIndex(errata, sources), "", "",
    '<script defer src="/assets/errata-filter.js"></script>');
  for (const data of errata) {
    const source = sources.find((s) => s.id === data.source);
    add(`errata/${source.id}`, `${source.shortName}: errata`, errataPage(data, source, assertions, evidence));
  }
  // Preserve every field of the dated provenance records without implying current status.
  const record = (value) => {
    if (value === null) return "Not recorded";
    if (Array.isArray(value))
      return `<ul>${value.map((v) => `<li>${record(v)}</li>`).join("")}</ul>`;
    if (typeof value === "object")
      return `<dl class="record">${Object.entries(value)
        .map(([k, v]) => `<dt>${esc(k)}</dt><dd>${record(v)}</dd>`)
        .join("")}</dl>`;
    if (typeof value === "string" && /^https:\/\//.test(value))
      return `<a href="${esc(value)}">${esc(value)}</a>`;
    return esc(value);
  };
  add(
    "provenance",
    "Lean & provenance",
    heading("Reused foundations and provenance") +
      "<p>These records describe their cited revisions, not the current state of the repository or the formal status of an article.</p>" +
      record(reuse),
  );
  add(
    "frontier",
    "Proof frontier",
    frontierPage(assertions, evidence, proofUses),
  );
  files.set("metrics/history.json", JSON.stringify(history, null, 2) + "\n");
  const csv = historyCsv(history);
  if (csv !== null) files.set("metrics/history.csv", csv);
  const dailyCsv = dailyHistoryCsv(history);
  if (dailyCsv !== null) files.set("metrics/history-daily.csv", dailyCsv);
  const fileCsv = fileHistoryCsv(history);
  if (fileCsv !== null) files.set("metrics/history-files.csv", fileCsv);
  add(
    "metrics/library",
    "Formalization library growth",
    historyPage(history, "library"),
  );
  add("metrics/wiki", "Wiki growth", historyPage(history, "wiki"));
  add("metrics/errata", "Errata history", historyPage(history, "errata"));
  const referenceHistory = recordedReferenceHistory(history);
  files.set("metrics/reference/history.json", JSON.stringify(referenceHistory, null, 2) + "\n");
  const referenceCsv = historyCsv(referenceHistory);
  if (referenceCsv !== null) files.set("metrics/reference/history.csv", referenceCsv);
  const referenceDailyCsv = dailyHistoryCsv(referenceHistory);
  if (referenceDailyCsv !== null) files.set("metrics/reference/history-daily.csv", referenceDailyCsv);
  add("metrics/reference/library", "Recorded reference: library growth",
    historyPage(history, "library", {reference: true}));
  add("metrics/reference/wiki", "Recorded reference: wiki growth",
    historyPage(history, "wiki", {reference: true}));
  add("metrics/reference/errata", "Recorded reference: errata history",
    historyPage(history, "errata", {reference: true}));
  add(
    "metrics",
    "Project metrics",
    heading("Project metrics") +
      evidenceSummary +
      '<p>Selected revision: <a href="/metrics/library/">Library growth</a> · <a href="/metrics/wiki/">Wiki growth</a> · <a href="/metrics/errata/">Errata history</a></p><p>Recorded reference: <a href="/metrics/reference/library/">Library growth</a> · <a href="/metrics/reference/wiki/">Wiki growth</a> · <a href="/metrics/reference/errata/">Errata history</a></p><p>The reference pages follow their own recorded history, normally the fetched main branch. Growth pages show source counts. Verified status comes only from the separately supplied compiled evidence.</p>' +
      `<p>This site contains ${articles.length} articles and ${assertions.length} active assertion tags. These counts describe this site build, not the number of Lean proofs.</p>` +
      (evidence.provenance
        ? `<p>Formal evidence comes from <a href="${evidence.provenance.runUrl}">${evidence.provenance.runLabel ? "the " + esc(evidence.provenance.runLabel.toLowerCase()) : "this successful CI run"}</a>, compiled commit <code>${evidence.provenance.commit}</code>.</p>`
        : "<p>No compiled manifest is supplied.</p>"),
  );
  add(
    "bibliography",
    "Bibliography",
    heading(
      "Bibliography",
      "Every work in the source catalogue and the articles that cite it.",
    ) + bibliographyPage(sources, citedBy),
  );
  add(
    "about",
    "About",
    aboutPage(buildInfo(evidenceOptions), evidence, counts),
  );
  add(
    "search",
    "Search",
    heading("Search the library") +
      '<form id="search-form" action="/search/" class="catalog-filter"><label class="catalog-query"><span>Title, concept, source, or tag</span><input type="search" name="q" autocomplete="off"></label><button class="button button-primary">Search</button></form><p id="search-status" role="status">Type to search. JavaScript is needed for filtering; the full article index is below.</p><div id="search-results">' +
      articles.map(item).join("") +
      "</div>",
  );
  const index = articles.map((p) => ({
    title: p.title,
    summary: p.summary,
    url: articleUrl(p.id),
    // Collapsed blocks and the lead are part of the body and are indexed with it.
    text: articleSearchText(p, bodies.get(p.id), assertions),
  }));
  index.push(
    ...[...inventories].map(([id, record]) => ({
      title: record.title,
      summary: "Version-specific source reading map; coverage remains to be checked.",
      url: `/coverage/sources/${id}/`,
      text: record.markdown,
    })),
    ...assertions.map((a) => ({
      title: `${a.tag} · ${a.title}`,
      summary: pages.get(a.article).title,
      url: `/tag/${a.tag}/`,
      text: `${a.tag} ${a.title}`,
    })),
    ...sources.map((s) => ({
      title: s.title,
      summary: s.description,
      url: `/sources/${s.id}/`,
      text: [
        s.title,
        s.author,
        s.shortName,
        ...s.occurrences.map((o) => o.label + " " + o.locator),
      ].join(" "),
    })),
  );
  index.push(...errata.flatMap((data) => data.entries.map((entry) => ({
    title: `${entry.title} (${entry.status})`, summary: entry.status === "withdrawn" ? entry.withdrawalReason : `${errataResolutionText(entry)} ${entry.problem}`,
    url: `/errata/${data.source}/#${entry.id}`,
    text: [entry.title, entry.status, entry.locator, errataVersionText(data), ...(entry.status === "withdrawn" ? [entry.withdrawalReason] : [errataResolutionText(entry), entry.claim, entry.problem, entry.correction, entry.leanImpact]), ...entry.tags].join(" "),
  }))));
  files.set("search-index.json", JSON.stringify(index) + "\n");
  files.set(
    "link-report.json",
    JSON.stringify({ ...report, resolvedWanted, unlinkedCitations }, null, 2) + "\n",
  );
  files.set(
    "link-report.txt",
    linkReportText(report, resolvedWanted) +
      plainCitationsText(unlinkedCitations, strictCitations),
  );
  for (const entry of registry.tags) {
    const a = assertions.find((a) => a.tag === entry.tag),
      target = a ? `${articleUrl(a.article)}#${a.anchor}` : null;
    add(
      `tag/${entry.tag}`,
      `Assertion ${entry.tag}`,
      heading(`Assertion ${entry.tag}`) +
        (target
          ? `<p><a href="${target}">${esc(a.title)}</a></p>`
          : `<p>This identity is ${entry.state === "withdrawn" ? "withdrawn" : "reserved but not yet attached to an assertion"}. It will never be reused.</p>`),
      "",
      "",
      target
        ? `<link rel="canonical" href="${target}"><meta http-equiv="refresh" content="0;url=${target}">`
        : "",
    );
  }
  for (const name of await fs.readdir(path.join(root, "src/assets")))
    files.set(
      `assets/${name}`,
      await fs.readFile(path.join(root, "src/assets", name), "utf8"),
    );
  let katexRoot;
  try {
    katexRoot = path.dirname(
      createRequire(import.meta.url).resolve("katex/package.json"),
    );
  } catch {
    katexRoot = path.dirname(
      createRequire(
        new URL("../prototype/package.json", import.meta.url),
      ).resolve("katex/package.json"),
    );
  }
  files.set(
    "assets/katex/katex.min.css",
    await fs.readFile(path.join(katexRoot, "dist/katex.min.css"), "utf8"),
  );
  const mathLayout = compactMathLayout(files);
  validateLinks(files);
  const site = applyBasePath(files, basePath);
  // Replace only generated output, after input and link validation succeed.
  await fs.rm(output, { recursive: true, force: true });
  for (const [file, content] of site) {
    await fs.mkdir(path.dirname(path.join(output, file)), { recursive: true });
    await fs.writeFile(path.join(output, file), content);
  }
  await fs.cp(
    path.join(katexRoot, "dist/fonts"),
    path.join(output, "assets/katex/fonts"),
    { recursive: true },
  );
  await fs.copyFile(
    path.join(katexRoot, "LICENSE"),
    path.join(output, "assets/katex/LICENSE"),
  );
  console.log(
    `Built ${articles.length} static articles, ${assertions.length} assertion redirects, ${registry.tags.filter((t) => t.state === "withdrawn").length} tombstones; all local links and mathematics validated.`,
  );
  console.log(
    `Link report (advisory): ${report.noInlineLinks.length} articles without inline links, ${report.unlinkedMentions.length} unlinked concept mentions, ${report.wantedPages.length} wanted pages, ${unlinkedCitations.length} plain-text citations; see dist/link-report.txt.`,
  );
  if (mathLayout.pages) console.log(`Shared ${mathLayout.styles} math layout styles across ${mathLayout.pages} pages; saved ${mathLayout.bytesSaved} bytes.`);
  if (basePath !== "/") console.log(`All site URLs are under the base path ${basePath}.`);
  return site;
}
// Command line: node src/build.mjs [--base-path /perclib/] [output directory].
// WIKI_BASE_PATH sets the base path when the option is absent.
export function parseArguments(argv) {
  const options = {};
  let output;
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === "--base-path") {
      if (i + 1 >= argv.length) throw Error("--base-path needs a value");
      options.basePath = argv[++i];
    } else if (arg.startsWith("--base-path=")) options.basePath = arg.slice(12);
    else if (arg.startsWith("-") || output !== undefined)
      throw Error(`Unexpected argument: ${arg}`);
    else output = path.resolve(arg);
  }
  return { output, options };
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const { output, options } = parseArguments(process.argv.slice(2));
  await build(output, options);
}
