// Article reading aids: collapsible blocks, wanted links, the internal link
// graph (backlinks, dead-link check, editorial link report), tables of
// contents and hover-preview data. Pure functions over parsed articles; the
// build composes them, and the tests run them on fixture articles.
import { esc, decode, plain, articleUrl, legacyUrl, renderMath } from "./render.mjs";

const fence = /^(:{3,})[ \t]*([A-Za-z]*)(?:[ \t]+(.*?))?[ \t]*$/;

// Author syntax (wiki/README.md, "Collapsible blocks"):
//   :::details Summary line, which is mandatory
//   body (HTML; mathematics allowed)
//   :::
// A block nests inside another whose fence has more colons.
export function expandCollapsibles(html, where = "article") {
  const lines = html.split("\n"),
    out = [],
    stack = [];
  lines.forEach((line, i) => {
    const m = fence.exec(line);
    if (!m) return out.push(line);
    const [, colons, word, summary] = m;
    if (word === "") {
      if (!stack.length || stack.at(-1).colons !== colons)
        throw Error(`${where}: line ${i + 1}: closing fence ${colons} matches no open block`);
      stack.pop();
      return out.push("</div></details>");
    }
    if (word !== "details")
      throw Error(`${where}: line ${i + 1}: unknown block directive "${word}"`);
    if (!summary?.trim())
      throw Error(`${where}: line ${i + 1}: a collapsible block needs a summary line`);
    if (stack.length && colons.length >= stack.at(-1).colons.length)
      throw Error(`${where}: line ${i + 1}: a nested block needs fewer colons than its parent`);
    stack.push({ colons, line: i + 1 });
    out.push(
      `<details class="collapsible"><summary>${summary.trim()}</summary><div class="collapsible-body">`,
    );
  });
  if (stack.length)
    throw Error(`${where}: line ${stack.at(-1).line}: collapsible block is not closed`);
  const result = out.join("\n");
  // Hand-written blocks follow the same rule: a summary saying what is inside.
  for (const m of result.matchAll(/<details\b[^>]*>(\s*)(<summary\b)?/g))
    if (!m[2]) throw Error(`${where}: <details> must begin with a <summary> line`);
  return result;
}

const wantedTag = /<a\b([^>]*?)\bdata-wanted="([^"]*)"([^>]*)>([\s\S]*?)<\/a>/g;
// <a data-wanted="slug">phrase</a> marks a phrase whose article does not exist yet.
export function resolveWanted(html, pages, where = "article") {
  const wanted = [],
    resolved = [];
  const out = html.replace(wantedTag, (all, before, slug, after, phrase) => {
    if (/\bhref\s*=/.test(before + after))
      throw Error(`${where}: a wanted link has no href: ${all}`);
    if (!/^[a-z0-9]+(?:-[a-z0-9]+)*$/.test(slug))
      throw Error(`${where}: invalid wanted page id "${slug}"`);
    if (pages.has(slug)) {
      resolved.push({ slug, phrase: plain(phrase) });
      return `<a href="${articleUrl(slug)}">${phrase}</a>`;
    }
    wanted.push({ slug, phrase: plain(phrase) });
    return `<a class="wanted-link" data-wanted="${slug}" title="Wanted page: no article yet">${phrase}</a>`;
  });
  return { html: out, wanted, resolved };
}

export const prepareSection = (html, pages, where) =>
  resolveWanted(expandCollapsibles(html, where), pages, where);

// Resolve an href written in an article body to its place in the site.
// Returns null for links outside the article graph (external, sources, errata…).
export function resolveHref(href, from, pages, assertions, baseline) {
  let raw = decode(href);
  if (/^[a-z][a-z0-9+.-]*:/i.test(raw)) return null;
  if (raw.startsWith("#/")) raw = legacyUrl(raw, pages, baseline);
  const url = new URL(raw, `https://wiki.invalid${articleUrl(from)}`);
  const fragment = url.hash ? decodeURIComponent(url.hash.slice(1)) : "";
  const parts = decodeURIComponent(url.pathname).split("/").filter(Boolean);
  const tag = (t) => {
    const a = assertions.find((x) => x.tag === t);
    return { kind: "assertion", tag: t, article: a?.article ?? null, fragment: `tag-${t}`, exists: !!a };
  };
  if (parts[0] === "tag" && parts.length <= 3 && /^[0-9A-Z]{4}$/.test(parts[1] ?? ""))
    return tag(parts[1]);
  let article = null;
  if (parts[0] === "articles" && parts.length >= 2) article = parts[1];
  else if (parts.length === 1 && pages.has(parts[0])) article = parts[0];
  else if (parts[0] === "articles" && parts.length === 1) return null;
  if (!article) return null;
  const t = /^tag-([0-9A-Z]{4})$/.exec(fragment);
  if (t && pages.has(article)) {
    const r = tag(t[1]);
    return { ...r, exists: r.exists && r.article === article, article };
  }
  return { kind: "article", article, fragment, exists: pages.has(article) };
}

const generatedIds = ["toc", "connections", "sources", "citations", "formal-evidence"];
const idsOf = (p) =>
  new Set([
    ...generatedIds,
    ...p.sections.map((s) => `section-${s.id}`),
    ...p.sections.flatMap((s) => [...s.html.matchAll(/(?<![\w-])id="([^"]+)"/g)].map((m) => m[1])),
  ]);

// The link graph of the article bodies. `bodies` maps article id to its
// prepared sections ({id, title, html}).
export function linkGraph(articles, bodies, assertions, baseline) {
  const pages = new Map(articles.map((p) => [p.id, p]));
  const ids = new Map(articles.map((p) => [p.id, idsOf({ sections: bodies.get(p.id) })]));
  const incoming = new Map(articles.map((p) => [p.id, []]));
  const citing = new Map(assertions.map((a) => [a.tag, []]));
  const outgoing = new Map(),
    dead = [],
    inline = new Map();
  for (const p of articles) {
    const out = [];
    let count = 0;
    for (const s of bodies.get(p.id)) {
      for (const m of s.html.matchAll(/<a\b[^>]*?\bhref\s*=\s*(["'])(.*?)\1/g)) {
        let target;
        try {
          target = resolveHref(m[2], p.id, pages, assertions, baseline);
        } catch (error) {
          dead.push({ article: p.id, section: s.id, href: m[2], reason: error.message });
          continue;
        }
        if (!target) continue;
        const where = { article: p.id, section: s.id, href: m[2] };
        if (!target.exists) {
          dead.push({ ...where, reason: target.kind === "assertion" ? "no such active assertion" : "no such article" });
          continue;
        }
        if (target.fragment && !ids.get(target.article).has(target.fragment)) {
          dead.push({ ...where, reason: `no anchor #${target.fragment} in ${target.article}` });
          continue;
        }
        out.push({ ...target, section: s.id });
        if (target.article !== p.id) {
          if (!/^see also$/i.test(s.title)) count++;
          const list = incoming.get(target.article);
          if (!list.some((x) => x.article === p.id && x.section === s.id))
            list.push({ article: p.id, section: s.id });
        }
        if (target.kind === "assertion") {
          const list = citing.get(target.tag);
          if (!list.some((x) => x.article === p.id && x.section === s.id))
            list.push({ article: p.id, section: s.id });
        }
      }
    }
    outgoing.set(p.id, out);
    inline.set(p.id, count);
  }
  return { incoming, citing, outgoing, dead, inline };
}

export function assertNoDeadLinks(graph) {
  if (!graph.dead.length) return;
  throw Error(
    `Dead internal links in articles:\n` +
      graph.dead.map((d) => `  ${d.article}#section-${d.section}: ${d.href} (${d.reason})`).join("\n"),
  );
}

const words = (text) =>
  text
    .normalize("NFKC")
    .toLowerCase()
    .split(/[^\p{L}\p{N}]+/u)
    .filter(Boolean);
const visibleWords = (html) =>
  words(
    plain(
      html
        .replace(/<a\b[\s\S]*?<\/a>/g, " | ")
        .replace(/<(pre|code|script|style|summary|h[1-6])\b[\s\S]*?<\/\1>/g, " | ")
        .replace(/\$\$[\s\S]*?\$\$/g, " | ")
        .replace(/\$[^$]*\$/g, " | "),
    ),
  );
// Concept names of an article, as normalised word sequences: its title and
// its aliases of two or more words (single-word aliases such as "cluster" are
// search keys, too generic to demand a link). No mathematics, at least four letters.
const termsOf = (p) =>
  [
    plain(String(p.title)),
    ...(p.aliases ?? []).map((t) => plain(String(t))).filter((t) => words(t).length >= 2),
  ]
    .filter((t) => !t.includes("$"))
    .map((t) => words(t).join(" "))
    .filter((t) => t.replace(/ /g, "").length >= 4);

// Editorial report; never fails the build.
export function linkReport(articles, bodies, graph, wanted) {
  const noInline = articles.filter((p) => !graph.inline.get(p.id)).map((p) => p.id);
  const unlinked = [];
  const owners = new Map();
  let longest = 1;
  for (const p of articles)
    for (const t of termsOf(p)) {
      owners.set(t, [...(owners.get(t) ?? []), p.id]);
      longest = Math.max(longest, t.split(" ").length);
    }
  for (const p of articles) {
    const own = new Set(termsOf(p));
    for (const s of bodies.get(p.id)) {
      const w = visibleWords(s.html);
      const linked = new Set(
        graph.outgoing.get(p.id).filter((o) => o.section === s.id).map((o) => o.article),
      );
      const found = new Map();
      for (let i = 0; i < w.length; i++)
        for (let n = 1; n <= longest && i + n <= w.length; n++) {
          const term = w.slice(i, i + n).join(" ");
          if (own.has(term)) continue;
          for (const id of owners.get(term) ?? [])
            if (id !== p.id && !linked.has(id) && !found.has(id)) found.set(id, term);
        }
      for (const [target, term] of found)
        unlinked.push({ article: p.id, section: s.id, term, target });
    }
  }
  const pages = new Map();
  for (const w of wanted) {
    const entry = pages.get(w.slug) ?? { slug: w.slug, phrases: [], from: [] };
    if (!entry.phrases.includes(w.phrase)) entry.phrases.push(w.phrase);
    if (!entry.from.some((f) => f.article === w.article && f.section === w.section))
      entry.from.push({ article: w.article, section: w.section });
    pages.set(w.slug, entry);
  }
  const wantedPages = [...pages.values()].sort(
    (a, b) => b.from.length - a.from.length || a.slug.localeCompare(b.slug),
  );
  return { noInlineLinks: noInline, unlinkedMentions: unlinked, wantedPages };
}

export function linkReportText(report, resolvedWanted = []) {
  const lines = [
    "Wiki link report (advisory; the build does not fail on these)",
    "",
    `Articles with no inline link to another article in their body: ${report.noInlineLinks.length}`,
    ...report.noInlineLinks.map((id) => `  ${id}`),
    "",
    `Concepts mentioned without a link although an article exists: ${report.unlinkedMentions.length}`,
    ...report.unlinkedMentions.map(
      (u) => `  ${u.article}#section-${u.section}: "${u.term}" -> ${u.target}`,
    ),
    "",
    `Wanted pages (for the wiki queue): ${report.wantedPages.length}`,
    ...report.wantedPages.map(
      (w) => `  ${w.slug} (${w.phrases.join("; ")}) from ${w.from.map((f) => `${f.article}#section-${f.section}`).join(", ")}`,
    ),
  ];
  if (resolvedWanted.length)
    lines.push(
      "",
      `Wanted links whose article now exists (rendered as ordinary links; replace them): ${resolvedWanted.length}`,
      ...resolvedWanted.map((w) => `  ${w.article}#section-${w.section}: ${w.slug}`),
    );
  return lines.join("\n") + "\n";
}

// Wikipedia-style contents box, placed before the first section.
export function tableOfContents(sections, extra) {
  const item = (href, title, children = "") =>
    `<li><a href="#${href}">${title}</a>${children}</li>`;
  const sub = (s) => {
    const h3 = [...s.html.matchAll(/<h3\b[^>]*\bid="([^"]+)"[^>]*>([\s\S]*?)<\/h3>/g)];
    return h3.length ? `<ul>${h3.map((m) => item(m[1], m[2])).join("")}</ul>` : "";
  };
  return `<nav class="article-toc" id="toc" aria-labelledby="toc-title"><h2 id="toc-title">Contents</h2><ul>${sections
    .map((s) => item(`section-${s.id}`, esc(s.title), sub(s)))
    .join("")}${extra.map(([id, title]) => item(id, esc(title))).join("")}</ul></nav>`;
}

export const hasCollapsibles = (sections) => sections.some((s) => /<details\b/.test(s.html));
export const collapseTools = () =>
  '<div class="article-tools" hidden><button type="button" class="button" data-details-action="expand">Expand all</button><button type="button" class="button" data-details-action="collapse">Collapse all</button></div>';

export function citationList(own, graph, pages, sectionTitle) {
  const from = (list) =>
    list
      .map(
        (c) =>
          `<a href="${articleUrl(c.article)}#section-${c.section}">${esc(pages.get(c.article).title)}: ${esc(sectionTitle(c.article, c.section))}</a>`,
      )
      .join(", ");
  return `<ul class="assertion-backlinks">${own
    .map((a) => {
      const list = graph.citing.get(a.tag) ?? [];
      return `<li id="cites-${a.tag}"><a href="/tag/${a.tag}/">${a.tag} · ${esc(a.title)}</a><span class="backlinks">${list.length ? ` Linked from ${from(list)}.` : " Not linked from any article."}</span></li>`;
    })
    .join("")}</ul>`;
}

// Hover previews: each internal link in a body names its target in
// data-preview, and the page carries the (pre-rendered) preview text of exactly
// those targets, so previews also work in the offline export.
export function annotatePreviews(html, from, pages, assertions, baseline) {
  const used = new Set();
  const out = html.replace(/<a\b([^>]*?)\bhref\s*=\s*(["'])(.*?)\2([^>]*)>/g, (all, before, q, href, after) => {
    if (/data-preview=/.test(before + after)) return all;
    let target;
    try {
      target = resolveHref(href, from, pages, assertions, baseline);
    } catch {
      return all;
    }
    if (!target?.exists) return all;
    const key = target.kind === "assertion" ? `t:${target.tag}` : target.article === from ? null : `a:${target.article}`;
    if (!key) return all;
    used.add(key);
    return `<a${before}href=${q}${href}${q}${after} data-preview="${key}">`;
  });
  return { html: out, used };
}

export function previewData(keys, pages, assertions) {
  const data = {};
  const html = (text) => renderMath(esc(text));
  for (const key of [...keys].sort()) {
    const [kind, id] = [key.slice(0, 1), key.slice(2)];
    if (kind === "a") {
      const p = pages.get(id);
      data[key] = { k: "Article", t: html(p.title), s: html(p.summary ?? p.subtitle ?? "") };
    } else {
      const a = assertions.find((x) => x.tag === id);
      data[key] = {
        k: `${a.kind[0].toUpperCase()}${a.kind.slice(1)} ${a.tag}`,
        t: html(a.title),
        s: html(`In ${pages.get(a.article).title}`),
      };
    }
  }
  return data;
}

export const previewScript = (data) =>
  Object.keys(data).length
    ? `<script type="application/json" id="link-preview-data">${JSON.stringify(data)
        .replace(/</g, "\\u003c")
        .replace(/\u2028/g, "\\u2028")
        .replace(/\u2029/g, "\\u2029")}</script>`
    : "";
