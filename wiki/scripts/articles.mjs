import fs from 'node:fs/promises';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

export const wikiRoot = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
export const tagPattern = /^[0-9A-Z]{4}$/;
// Invisible citation anchors leave the original exposition and layout intact.
export const anchorPattern = /<a id="tag-([0-9A-Z]{4})" data-assertion="(definition|proposition|theorem|corollary)" data-title="([^"<>]+)"><\/a>/g;
export const stripAnchors = text => text.replace(anchorPattern, '');

export async function readArticles(root = wikiRoot) {
  const names = (await fs.readdir(path.join(root, 'articles'))).filter(n => n.endsWith('.md')).sort();
  return Promise.all(names.map(async name => {
    const text = await fs.readFile(path.join(root, 'articles', name), 'utf8');
    const front = /^---\n([\s\S]*?)\n---\n\n/.exec(text);
    if (!front) throw Error(`${name}: missing JSON front matter (a YAML subset)`);
    const metadata = JSON.parse(front[1]);
    if (metadata.id !== name.slice(0, -3)) throw Error(`${name}: article ID must match filename`);
    if ('tag' in metadata || 'status' in metadata || 'sections' in metadata) throw Error(`${name}: assertion tags/statuses are not article metadata`);
    const body = text.slice(front[0].length);
    const headings = [...body.matchAll(/^## (.+) \{#section-([a-z0-9-]+)\}\n\n/gm)];
    if (!headings.length) throw Error(`${name}: expected section headings`);
    const lead = parseLead(name, body.slice(0, headings[0].index), front[0].split('\n').length);
    const sections = headings.map((h, i) => {
      if (h[2] === leadId) throw Error(`${name}: section id "${leadId}" is reserved for the lead`);
      const raw = body.slice(h.index + h[0].length, headings[i+1]?.index ?? body.length);
      const suffix = i === headings.length - 1 ? '\n' : '\n\n';
      if (!raw.endsWith(suffix)) throw Error(`${name}/${h[2]}: missing section separator`);
      return {id:h[2], title:h[1], html:raw.slice(0, -suffix.length)};
    });
    return lead === null ? {...metadata, sections} : {...metadata, lead, sections};
  }));
}

// The lead: up to three paragraphs between the front matter and the first
// section heading (wiki/README.md, "Lead"). A paragraph is an HTML block of
// <p> elements or a bare-text (Markdown) paragraph; paragraphs are separated by
// a blank line, and the lead by a blank line from the first heading. The lead
// holds no assertion anchor, heading or collapsible block; errors name the
// article and its file line. Returns the authored text, or null without a lead.
export const leadId = 'lead';
export const maxLeadParagraphs = 3;
const blockTag = /^<\/?(?:address|article|aside|blockquote|details|dialog|div|dl|fieldset|figcaption|figure|footer|form|h[1-6]|header|hr|li|main|nav|ol|pre|section|summary|table|ul)\b/i;
const htmlParagraph = /^<p\b[^>]*>[\s\S]*<\/p>$/;
export function parseLead(name, raw, firstLine = 1) {
  if (raw === '') return null;
  const fail = (offset, message) =>
    Error(`${name}:${firstLine + raw.slice(0, offset).split('\n').length - 1}: ${message}`);
  if (!raw.endsWith('\n\n') || raw.endsWith('\n\n\n')) throw fail(raw.length - 1, 'the lead must be separated from the first section heading by one blank line');
  const text = raw.slice(0, -2);
  const checks = [
    [/data-assertion/, 'an assertion anchor may not stand in the lead (assertions belong in sections)'],
    [/^#{1,6}(?:[ \t]|$)|<h[1-6]\b/im, 'a heading may not stand in the lead'],
    [/^[ \t]*:{3,}|<details\b/im, 'a collapsible block may not stand in the lead'],
  ];
  for (const [pattern, message] of checks) {
    const m = pattern.exec(text);
    if (m) throw fail(m.index, message);
  }
  if (/^\s/.test(text)) throw fail(0, 'the lead may not begin with a blank line or indentation');
  let paragraphs = 0, offset = 0;
  for (const block of text.split(/\n[ \t]*\n/)) {
    const at = text.indexOf(block, offset);
    offset = at + block.length;
    const trimmed = block.trim();
    if (!trimmed) throw fail(at, 'paragraphs in the lead are separated by exactly one blank line');
    if (/^<p\b/i.test(trimmed)) {
      if (!htmlParagraph.test(trimmed)) throw fail(at, 'an HTML paragraph in the lead must be a block of complete <p> elements');
      paragraphs += trimmed.match(/<p\b/gi).length;
    } else if (blockTag.test(trimmed)) throw fail(at, 'the lead holds paragraphs only, not other block elements');
    else paragraphs++;
  }
  if (paragraphs > maxLeadParagraphs) throw fail(0, `the lead has ${paragraphs} paragraphs; at most ${maxLeadParagraphs} are allowed`);
  return text;
}

// HTML of a parsed lead: bare-text paragraphs are wrapped in <p>; HTML
// paragraphs are kept as written.
export const leadHtml = text =>
  text.split(/\n[ \t]*\n/).map(b => b.trim()).map(b => /^<p\b/i.test(b) ? b : `<p>${b}</p>`).join('\n');

export function assertionsIn(articles) {
  return articles.flatMap(article => article.sections.flatMap(section =>
    [...section.html.matchAll(anchorPattern)].map(m => ({tag:m[1], kind:m[2], title:m[3], article:article.id, section:section.id, anchor:`tag-${m[1]}`}))));
}

export async function readRegistry(root = wikiRoot) {
  return JSON.parse(await fs.readFile(path.join(root, 'tags.json'), 'utf8'));
}

export function validateTags(articles, registry, previous = null, previousAssertions = []) {
  if (registry.version !== 1 || !Array.isArray(registry.tags)) throw Error('Invalid tag ledger');
  const reserved = new Map();
  for (const entry of registry.tags) {
    if (typeof entry.tag !== 'string' || !tagPattern.test(entry.tag) || !['allocated','withdrawn'].includes(entry.state)) throw Error(`Malformed ledger entry: ${JSON.stringify(entry)}`);
    if (reserved.has(entry.tag)) throw Error(`Duplicate ledger tag: ${entry.tag}`);
    reserved.set(entry.tag, entry.state);
  }
  const assertions = assertionsIn(articles);
  const used = new Set();
  for (const a of assertions) {
    if (used.has(a.tag)) throw Error(`Duplicate assertion tag: ${a.tag}`);
    if (reserved.get(a.tag) !== 'allocated') throw Error(`Unallocated or withdrawn assertion tag: ${a.tag}`);
    used.add(a.tag);
  }
  for (const article of articles) {
    if (article.lead !== undefined && /\b(?:Lrp|PercLib|Mathlib)\.[A-Za-z_]/.test(article.lead)) throw Error(`${article.id}: Lean declaration name in article content`);
    for (const section of article.sections) {
      const stripped = stripAnchors(section.html);
      if (/data-assertion|id\s*=\s*["']tag-/.test(stripped)) throw Error(`${article.id}/${section.id}: malformed assertion anchor`);
      if (/\b(?:Lrp|PercLib|Mathlib)\.[A-Za-z_]/.test(stripped)) throw Error(`${article.id}: Lean declaration name in article content`);
    }
  }
  if (previous) {
    for (const entry of previous.tags) {
      if (!reserved.has(entry.tag)) throw Error(`Reserved tag removed: ${entry.tag}`);
      if (entry.state === 'withdrawn' && reserved.get(entry.tag) !== 'withdrawn') throw Error(`Tombstone resurrected: ${entry.tag}`);
    }
    for (const {tag} of previousAssertions) {
      if (!used.has(tag) && reserved.get(tag) !== 'withdrawn') throw Error(`Removed assertion needs a tombstone: ${tag}`);
    }
  }
  return assertions;
}
