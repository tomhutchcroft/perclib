// Inline citations of works in the source catalogue (src/content/catalog.json):
// author markup, its rendering as links to a per-article References section,
// the site bibliography, and the report of plain-text citations left unlinked.
// Pure functions; the build composes them and tests run them on fixtures.
//
// Author syntax (wiki/STYLE.md, "Citations"):
//   [@key]                     one work, no locator
//   [@key, Theorem 1.1]        one work with a locator, kept in the visible text
//   [@key1, §3; @key2]         several works in one bracket
// `key` is the `id` of a catalogue entry.
import { esc, plain, articleUrl } from "./render.mjs";

// Plain-text citation patterns left unlinked are reported by the link report.
// The single switch: set to true once the backlog is cleared, and the build
// fails on them instead (a build option `strictCitations` overrides it).
export const failOnPlainCitations = false;

const keyPattern = /^[A-Za-z0-9][A-Za-z0-9._-]*$/;
// Code, tags and formulas are skipped as in renderMath: a formula's "<" is not
// the start of a tag, and "[@" inside mathematics is not a citation.
const citationMarkup =
  /<pre\b[^>]*>[\s\S]*?<\/pre>|<code\b[^>]*>[\s\S]*?<\/code>|\$\$(?:(?!<\/)[\s\S])*?\$\$|\$(?:(?!<\/)[^$])+?\$|<(?:[^>"']|"[^"]*"|'[^']*')*>|\[@([^\]]*)\]/g;

// An unpublished work (the book in preparation, ruling 6): no link, no locator.
export const isUnpublished = (source) =>
  !source.url && !source.doi && !source.arxiv && /preparation/i.test(source.edition ?? "");

export const catalogue = (sources) => new Map(sources.map((s) => [s.id, s]));

// Parse the inside of one `[@…]` bracket into [{key, locator}].
export function parseCitation(inner, where = "article") {
  return ("@" + inner).split(";").map((part) => {
    const m = /^\s*@([^\s,;]+)\s*(?:,\s*([\s\S]*?))?\s*$/.exec(part);
    if (!m || !keyPattern.test(m[1]))
      throw Error(`${where}: malformed citation "[@${inner}]": write [@key] or [@key, locator], several separated by ";"`);
    if (m[2] !== undefined && !m[2].trim())
      throw Error(`${where}: empty locator in citation "[@${inner}]"`);
    return { key: m[1], locator: m[2] };
  });
}

// Visible text of a citation: the catalogue's short label, then the locator.
export const citationText = (source, locator) =>
  esc(source.shortName) + (locator ? ", " + locator : "");

// Replace every citation in an HTML fragment. `state` is shared by the
// sections of one article: `counts` numbers the citations of each key, and
// `order` records the keys in order of first citation.
export function expandCitations(html, sources, where = "article", state = newCitationState()) {
  const out = html.replace(citationMarkup, (match, inner) => {
    if (inner === undefined) return match;
    const parts = parseCitation(inner, where);
    return (
      "[" +
      parts
        .map(({ key, locator }) => {
          const source = sources.get(key);
          if (!source)
            throw Error(`${where}: citation key "${key}" is not in the source catalogue (src/content/catalog.json)`);
          if (locator !== undefined && isUnpublished(source))
            throw Error(`${where}: the unpublished work "${key}" is cited without locators (ruling 6): "[@${inner}]"`);
          const n = (state.counts.get(key) ?? 0) + 1;
          state.counts.set(key, n);
          if (n === 1) state.order.push(key);
          return `<a class="citation" id="${citeId(key, n)}" href="#${refId(key)}">${citationText(source, locator)}</a>`;
        })
        .join("; ") +
      "]"
    );
  });
  return { html: out, state };
}
export const newCitationState = () => ({ counts: new Map(), order: [] });
export const refId = (key) => `ref-${key}`;
export const citeId = (key, n) => `cite-${key}-${n}`;

const arxivOf = (s) =>
  s.arxiv ?? /^https?:\/\/arxiv\.org\/(?:abs|pdf)\/([^?#]+?)(?:\.pdf)?$/.exec(s.url ?? "")?.[1] ?? null;
const doiOf = (s) =>
  s.doi ??
  /^https?:\/\/(?:dx\.)?doi\.org\/(10\.[^?#]+)$/.exec(s.url ?? "")?.[1] ??
  /^https?:\/\/[^/]+\/(?:[^?#]*\/)?(10\.\d{4,9}\/[^?#]+)$/.exec(s.url ?? "")?.[1] ??
  null;

// Outbound links of an entry: DOI, arXiv, otherwise the catalogue URL.
export function outboundLinks(source) {
  if (isUnpublished(source)) return [];
  const doi = doiOf(source),
    arxiv = arxivOf(source),
    links = [];
  if (doi) links.push(`<a class="ref-doi" href="https://doi.org/${esc(doi)}">doi:${esc(doi)}</a>`);
  if (arxiv)
    links.push(
      `<a class="ref-arxiv" href="https://arxiv.org/abs/${esc(arxiv)}">arXiv:${esc(arxiv.replace(/v\d+$/, ""))}</a>`,
    );
  if (!links.length && source.url) links.push(`<a class="ref-url" href="${esc(source.url)}">online</a>`);
  return links;
}

// One bibliographic entry: authors, title, journal volume (year) or the
// edition of an unpublished work, then its outbound links.
export function referenceEntry(source) {
  const venue = [source.journal, source.volume].filter((v) => v != null).map(esc).join(" ");
  const year = source.year != null ? String(source.year) : null;
  const where = isUnpublished(source)
    ? /preparation/i.test(source.title)
      ? ""
      : esc(source.edition.toLowerCase())
    : venue
      ? venue + (year ? ` (${esc(year)})` : "") + (source.pages ? `, ${esc(source.pages)}` : "")
      : year
        ? esc(year)
        : "";
  const links = outboundLinks(source);
  return (
    `<span class="ref-authors">${esc(source.author)}</span>, ` +
    `<span class="ref-title">${esc(source.title)}</span>` +
    (where ? `, ${where}` : "") +
    "." +
    (links.length ? " " + links.join(" · ") : "")
  );
}

const sortKey = (s) => s.shortName.toLocaleLowerCase("en");
const bySource = (sources) => (a, b) =>
  sortKey(sources.get(a)).localeCompare(sortKey(sources.get(b)), "en") || a.localeCompare(b);

// The References list of one article: only the works it cites, each with
// backlinks to every citation of it on the page.
export function referencesList(state, sources) {
  const keys = [...state.order].sort(bySource(sources));
  return `<ol class="references">${keys
    .map((key) => {
      const n = state.counts.get(key);
      const back = Array.from({ length: n }, (_, i) =>
        `<a href="#${citeId(key, i + 1)}" aria-label="Back to citation ${i + 1}">${n === 1 ? "^" : backLabel(i)}</a>`,
      ).join(" ");
      return `<li id="${refId(key)}"><span class="ref-backlinks">${n === 1 ? back : "^ " + back}</span> ${referenceEntry(sources.get(key))}</li>`;
    })
    .join("")}</ol>`;
}
const backLabel = (i) =>
  i < 26 ? String.fromCharCode(97 + i) : backLabel(Math.floor(i / 26) - 1) + String.fromCharCode(97 + (i % 26));

export const referencesTitle = "References";
export const referencesSectionId = "references";

// Add the References list to an article's prepared body entries: appended to
// its own "references" section if it has one, otherwise as a new last section.
export function withReferences(entries, state, sources) {
  if (!state.order.length) return entries;
  const list = referencesList(state, sources);
  const own = entries.findIndex((s) => s.id === referencesSectionId);
  if (own === -1) return [...entries, { id: referencesSectionId, title: referencesTitle, html: list, generated: true }];
  return entries.map((s, i) => (i === own ? { ...s, html: s.html + "\n" + list } : s));
}

// The site bibliography: every catalogue entry with the articles citing it.
// `citedBy` maps key to [{article, title}] (article order).
export function bibliographyPage(sourceList, citedBy) {
  const sources = catalogue(sourceList);
  const keys = sourceList.map((s) => s.id).sort(bySource(sources));
  const cited = keys.filter((k) => citedBy.get(k)?.length).length;
  return (
    `<p>Every work in the source catalogue, with the articles that cite it inline. ${cited} of ${keys.length} works are cited inline so far. Each article lists the works it cites in its own References section.</p>` +
    `<ol class="references bibliography">${keys
      .map((key) => {
        const list = citedBy.get(key) ?? [];
        return `<li id="${refId(key)}">${referenceEntry(sources.get(key))} <a class="ref-source" href="/sources/${esc(key)}/">Source record</a><span class="ref-cited-by">${
          list.length
            ? " Cited in " + list.map((c) => `<a href="${articleUrl(c.article)}#${citeId(key, 1)}">${esc(c.title)}</a>`).join(", ") + "."
            : " Not yet cited inline."
        }</span></li>`;
      })
      .join("")}</ol>`
  );
}

// Plain-text citations in visible body text, outside links and generated
// reference lists: "Hutchcroft (2022)", "[DCT16, Theorem 1.1]",
// "arXiv:2106.06400", "book in preparation".
const plainPatterns = [
  ["author-year", /\b[A-Z][\p{L}'’-]+(?:(?:,| and| &)\s+[A-Z][\p{L}'’-]+)*(?:\s+et al\.)?\s+\((?:1[89]|20)\d{2}[a-z]?\)/gu],
  ["bracket key", /\[[A-Z][A-Za-z+-]*\d{2}[a-z]?(?:,[^\]]*)?\]/g],
  ["arXiv identifier", /\barXiv:\s?\d{4}\.\d{4,5}(?:v\d+)?/g],
  ["book in preparation", /\bbook in preparation\b/gi],
];
export function visibleCitationText(html) {
  return plain(
    html
      .replace(/<ol class="references[^"]*">[\s\S]*?<\/ol>/g, " ")
      .replace(/<(pre|code|a)\b[^>]*>[\s\S]*?<\/\1>/g, " ")
      .replace(/\$\$[\s\S]*?\$\$|\$[^$]*\$/g, " "),
  );
}
export function plainCitations(articles, bodies) {
  const found = [];
  for (const p of articles)
    for (const s of bodies.get(p.id) ?? []) {
      const text = visibleCitationText(s.html);
      for (const [kind, pattern] of plainPatterns)
        for (const m of text.matchAll(pattern)) found.push({ article: p.id, section: s.id, kind, text: m[0] });
    }
  return found;
}
export function plainCitationsText(found, strict = failOnPlainCitations) {
  return (
    [
      "",
      `Plain-text citations not written as [@key] (${strict ? "these fail the build" : "advisory"}): ${found.length}`,
      ...found.map((f) => `  ${f.article}#section-${f.section}: ${f.kind}: "${f.text}"`),
    ].join("\n") + "\n"
  );
}
export function assertNoPlainCitations(found, strict = failOnPlainCitations) {
  if (!strict || !found.length) return;
  throw Error(
    `${found.length} plain-text citations are not written as [@key]:\n` +
      found.slice(0, 20).map((f) => `  ${f.article}#section-${f.section}: "${f.text}"`).join("\n"),
  );
}
