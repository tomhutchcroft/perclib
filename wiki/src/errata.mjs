import fs from "node:fs/promises";
import path from "node:path";
import {esc, heading} from "./render.mjs";
import {statusFor} from "./manifest.mjs";

const slug = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const repairLabels = {found: "Fix found", partial: "Partial fix", workaround: "Workaround found", open: "No fix yet", unassessed: "Not assessed"};
const scaleLabels = {notation: "Notation / typo", local: "Local correction", substantial: "Substantial proof change", statement: "Statement / scope change", unknown: "Not yet determined"};
const repairKey = (row) => row.resolution?.status ?? "unassessed";
const comparisonLabels = {pending: "Version comparison pending", compared: "Version comparison recorded"};
const nonempty = (value) => typeof value === "string" && value.trim();
const https = (value) => {
  try { const u = new URL(value); return u.protocol === "https:" && !u.username && !u.password; }
  catch { return false; }
};
export function validateErrata(data, sources, assertions) {
  if (data?.schema !== "perclib-source-errata-v1" ||
      !sources.some((s) => s.id === data.source) || !Array.isArray(data.entries))
    throw Error("Errata: unknown source or invalid schema");
  if (data.versionAudit !== undefined) {
    const audit = data.versionAudit;
    if (!audit || typeof audit !== "object" || Array.isArray(audit) ||
        !["checkedVersion", "method", "scope"].every((k) => nonempty(audit[k])) ||
        !https(audit.checkedUrl) || !Array.isArray(audit.comparisons) ||
        Object.keys(audit).some((k) => !["checkedVersion", "checkedUrl", "method", "scope", "comparisons"].includes(k)))
      throw Error("Errata: invalid source-version audit");
    const versions = new Set([audit.checkedUrl]);
    for (const comparison of audit.comparisons) {
      if (!comparison || typeof comparison !== "object" || Array.isArray(comparison) ||
          !["version", "findings"].every((k) => nonempty(comparison[k])) ||
          !https(comparison.url) || versions.has(comparison.url) ||
          !["pending", "compared"].includes(comparison.status) ||
          Object.keys(comparison).some((k) => !["version", "url", "status", "findings"].includes(k)))
        throw Error("Errata: invalid source-version comparison");
      versions.add(comparison.url);
    }
  }
  const tags = new Map(assertions.map((a) => [a.tag, a.article]));
  const seen = new Set();
  for (const row of data.entries) {
    if (typeof row.id !== "string" || !slug.test(row.id) || seen.has(row.id) ||
        !["provisional", "confirmed", "withdrawn"].includes(row.status) ||
        !["title", "locator", "claim", "problem", "correction", "leanImpact"].every((k) => typeof row[k] === "string" && row[k].trim()) ||
        Object.keys(row).some((k) => !["id", "title", "status", "locator", "claim", "problem", "correction", "leanImpact", "tags", "issues", "confirmationUrl", "withdrawalReason", "withdrawalUrl", "resolution"].includes(k)) ||
        !Array.isArray(row.tags) || !row.tags.length || row.tags.some((t) => !tags.has(t)) ||
        new Set(row.tags).size !== row.tags.length ||
        !Array.isArray(row.issues) || row.issues.some((u) => !https(u)))
      throw Error("Errata: invalid entry, tag or issue");
    if (row.resolution !== undefined) {
      const r = row.resolution;
      if (!r || typeof r !== "object" || Array.isArray(r) ||
          !["found", "partial", "workaround", "open"].includes(r.status) ||
          typeof r.scale !== "string" || !Object.hasOwn(scaleLabels, r.scale) ||
          !["summary", "impact"].every((k) => typeof r[k] === "string" && r[k].trim()) ||
          Object.keys(r).some((k) => !["status", "summary", "scale", "impact"].includes(k)))
        throw Error("Errata: invalid repair assessment");
    }
    if (row.status === "confirmed" && !https(row.confirmationUrl))
      throw Error("Errata: confirmation requires Tom's recorded confirmation");
    if (row.status === "withdrawn" &&
        (!row.withdrawalReason?.trim() || !https(row.withdrawalUrl)))
      throw Error("Errata: withdrawal requires a reason and record");
    seen.add(row.id);
  }
  return data;
}
export async function loadErrata(root, sources, assertions) {
  const directory = path.join(root, "errata");
  let names;
  try { names = (await fs.readdir(directory)).filter((n) => n.endsWith(".json")).sort(); }
  catch (error) { if (error.code === "ENOENT") return []; throw error; }
  return Promise.all(names.map(async (name) => {
    const data = validateErrata(JSON.parse(await fs.readFile(path.join(directory, name), "utf8")), sources, assertions);
    if (name !== `${data.source}.json`) throw Error("Errata: filename must match source");
    return data;
  }));
}
export const erratumUrl = (source, id) => `/errata/${source}/#${id}`;
export const errataNotice = "Provisional entries are reported source discrepancies awaiting Tom Hutchcroft's confirmation. Their editorial status is separate from formal proof status. An unresolved correction is not a completed theorem.";
const repairNotice = "Repair status assesses the specific reported issue. A fix may correct a formula, replace an argument, or change a statement; it does not certify the rest of the paper. Tom's confirmation and Lean proof status are recorded separately.";
const versionNotice = "Reports apply to the source version actually checked. A discrepancy in a preprint does not establish a discrepancy in the published article.";
export function errataVersionText(data) {
  const audit = data.versionAudit;
  if (!audit) return "Source-version audit not recorded here; consult the individual locators.";
  return [`Checked version: ${audit.checkedVersion}.`, audit.method, audit.scope,
    ...audit.comparisons.map((c) => `${comparisonLabels[c.status]}: ${c.version}. ${c.findings}`)].join(" ");
}
function versionPanel(data) {
  const audit = data.versionAudit;
  if (!audit) return `<p class="errata-version-audit">${errataVersionText(data)}</p>`;
  return `<div class="errata-version-audit"><p><strong>Checked version:</strong> <a href="${esc(audit.checkedUrl)}">${esc(audit.checkedVersion)}</a>.</p>` +
    `<p><strong>Audit method:</strong> ${esc(audit.method)}</p><p><strong>Scope:</strong> ${esc(audit.scope)}</p>` +
    (audit.comparisons.length ? `<ul>${audit.comparisons.map((c) => `<li><strong>${comparisonLabels[c.status]}:</strong> <a href="${esc(c.url)}">${esc(c.version)}</a>. ${esc(c.findings)}</li>`).join("")}</ul>` : "") + "</div>";
}
function resolutionBadges(row) {
  if (row.status === "withdrawn") return "";
  return `<span class="errata-badge errata-${repairKey(row)}">${repairLabels[repairKey(row)]}</span> <span class="errata-badge">Changes: ${scaleLabels[row.resolution?.scale ?? "unknown"]}</span>`;
}
function resolutionPanel(row) {
  return `<div class="errata-resolution"><p class="errata-badges">${resolutionBadges(row)}</p>` +
    (row.resolution ? `<p>${esc(row.resolution.summary)}</p><p><strong>Impact:</strong> ${esc(row.resolution.impact)}</p>`
      : "<p>The repair and extent of the required changes have not yet been assessed.</p>") + "</div>";
}
export function errataResolutionText(row) {
  if (row.status === "withdrawn") return "";
  return [repairLabels[repairKey(row)], scaleLabels[row.resolution?.scale ?? "unknown"], row.resolution?.summary, row.resolution?.impact].filter(Boolean).join(". ");
}
export function errataIndex(errata, sources) {
  const rows = errata.flatMap((data) => data.entries.map((entry) => ({...entry, source: data.source})));
  const active = rows.filter((row) => row.status !== "withdrawn");
  const incomplete = active.filter((row) => repairKey(row) !== "found");
  const sourceById = new Map(sources.map((source) => [source.id, source]));
  const counts = Object.entries(repairLabels).map(([key, label]) => [label, active.filter((row) => repairKey(row) === key).length]);
  const options = (labels) => Object.entries(labels).map(([value, label]) => `<option value="${esc(value)}">${esc(label)}</option>`).join("");
  const filters = '<form id="errata-filter" class="catalog-filter errata-filter" hidden aria-label="Filter errata">' +
    '<label><span>Repair availability</span><select name="repair"><option value="">All repairs</option>' + options(repairLabels) +
    (rows.length > active.length ? '<option value="withdrawn">Withdrawn entries</option>' : '') + '</select></label>' +
    '<label><span>Significance of changes</span><select name="significance"><option value="">All changes</option>' + options(scaleLabels) + '</select></label>' +
    '<label><span>Source</span><select name="source"><option value="">All sources</option>' +
    errata.map((data) => `<option value="${esc(data.source)}">${esc(sourceById.get(data.source).shortName)}</option>`).join("") + '</select></label>' +
    '<button type="reset" class="button button-secondary">Clear filters</button></form>' +
    '<p id="errata-filter-status" role="status" aria-live="polite" aria-atomic="true"></p>' +
    '<noscript><p>All entries are shown below. Enable JavaScript to filter this list.</p></noscript>';
  return heading("Source errata", errataNotice) + `<p>${repairNotice}</p><p>${versionNotice}</p>` +
    `<dl class="errata-counts">${counts.filter(([, count], i) => count || i < 4).map(([label, count]) => `<div><dt>${label}</dt><dd>${count}</dd></div>`).join("")}</dl>` +
    `<p>${active.length} active source entries${rows.length > active.length ? `; ${rows.length - active.length} withdrawn` : ""}. An issue recorded in several sources is counted once per source.</p>` +
    '<details class="errata-key"><summary>How to read repair status and significance</summary>' +
    '<p><strong>Fix found:</strong> a concrete repair of the reported issue is available. <strong>Partial fix:</strong> part of the issue remains unresolved. <strong>Workaround found:</strong> a different or restricted result is available, but the intended claim remains unsettled. <strong>No fix yet:</strong> no sufficient repair is known here.</p>' +
    '<p><strong>Notation / typo:</strong> a display or convention correction. <strong>Local correction:</strong> a bounded change to a calculation or proof step. <strong>Substantial proof change:</strong> a new argument or significant estimate. <strong>Statement / scope change:</strong> hypotheses, conclusions, constants or the model must change; the impact paragraph explains how. <strong>Not yet determined:</strong> the extent of a sufficient repair is unknown.</p>' +
    '<p>Significance describes changes to the source mathematics, not the effort needed to formalize it in Lean. A short statement correction can still matter mathematically.</p></details>' +
    filters +
    (incomplete.length ? '<section class="article-section" id="errata-pending"><h2>Still incomplete</h2><ul class="errata-pending">' + incomplete.map((row) =>
      `<li><a href="${erratumUrl(row.source, row.id)}">${esc(sourceById.get(row.source).shortName)}: ${esc(row.title)}</a><p class="errata-badges">${resolutionBadges(row)}</p><p>${esc(row.resolution?.summary ?? "Repair not yet assessed.")}</p></li>`).join("") + '</ul></section>' : "") +
    errata.map((data) => {
      const source = sourceById.get(data.source);
      return `<section class="article-section" data-errata-group="${esc(source.id)}"><h2><a href="/errata/${source.id}/">${esc(source.shortName)}</a></h2><p>${data.entries.length} recorded entries · ${esc(source.edition)}</p>` + versionPanel(data) + '<ul class="errata-list">' + data.entries.map((row) =>
        `<li data-errata-row data-repair="${row.status === "withdrawn" ? "withdrawn" : repairKey(row)}" data-scale="${row.status === "withdrawn" ? "" : row.resolution?.scale ?? "unknown"}"><h3><a href="${erratumUrl(source.id, row.id)}">${esc(row.title)}</a></h3>` +
        (row.status === "withdrawn" ? `<p>Withdrawn: ${esc(row.withdrawalReason)}</p>` : resolutionPanel(row)) +
        `<p class="errata-editorial">Editorial status: ${row.status}${row.status === "provisional" ? "; awaiting Tom's confirmation" : ""}.</p></li>`).join("") + '</ul></section>';
    }).join("");
}
export function errataPage(data, source, assertions, evidence) {
  const byTag = new Map(assertions.map((a) => [a.tag, a]));
  const snapshot = evidence.provenance
    ? `<p>Compiled snapshot: <a href="https://github.com/${esc(evidence.provenance.repository)}/commit/${esc(evidence.provenance.commit)}"><code>${esc(evidence.provenance.commit)}</code></a> · <a href="${esc(evidence.provenance.runUrl)}">${esc(evidence.provenance.runLabel ?? "Successful CI run")}</a>. Proof status describes the compiled statement; its correspondence to the wiki is reviewed separately.</p>`
    : "<p>No compiled manifest is supplied with this edition. Formal status is unavailable; issue resolutions and prose proofs do not supply compiled evidence.</p>";
  const formal = (tag) => {
    const assertion = byTag.get(tag);
    const entry = evidence.entries?.get(tag);
    const result = entry ? statusFor(entry, evidence.reviews) : null;
    const review = result && entry.proof_status !== "unformalised"
      ? ` Wiki/Lean correspondence review: ${esc(result.reviewState)}.` : "";
    return `<li><a href="/tag/${tag}/">${tag} · ${esc(assertion.title)}</a><p>Formal status: ${esc(result ? (result.status ?? "Compiled statement; correspondence pending") : "unavailable")}.${review} <a href="/articles/${assertion.article}/#${entry ? `formal-${tag}` : "formal-evidence"}">Statement and Lean evidence</a>.</p>` +
      (entry?.proof_status === "proved-modulo"
        ? `<p>Named inputs still to discharge:</p><ul>${entry.inputs.map((input) => `<li><code>${esc(input)}</code></li>`).join("")}</ul>` : "") + "</li>";
  };
  return heading(`${source.shortName}: errata`, errataNotice) +
    `<p>${repairNotice} <a href="/errata/">All errata and classification key</a>.</p>` +
    `<p><a href="${esc(source.url)}">${esc(source.title)}</a> · ${esc(source.edition)}</p>` +
    `<p>${versionNotice}</p>` + versionPanel(data) +
    snapshot +
    data.entries.map((row) => {
      const start = `<section class="article-section" id="${row.id}"><h2>${esc(row.title)}</h2><p><strong>Editorial status: ${row.status}.</strong></p>`;
      if (row.status === "withdrawn") return start + `<p>This entry has been withdrawn. ${esc(row.withdrawalReason)}</p><p><a href="${esc(row.withdrawalUrl)}">Withdrawal record</a></p></section>`;
      return start +
        resolutionPanel(row) +
        `<p><strong>Source locator:</strong> ${esc(row.locator)}</p>` +
        `<h3>Source claim</h3><p>${esc(row.claim)}</p><h3>Reported problem</h3><p>${esc(row.problem)}</p>` +
        `<h3>Correction and remaining scope</h3><p>${esc(row.correction)}</p>` +
        `<h3>Consequences for Lean</h3><p>${esc(row.leanImpact)}</p>` +
        `<ul>${row.tags.map(formal).join("")}</ul>` +
        `<p>${[...row.issues.map((u, i) => `<a href="${esc(u)}">Issue record${row.issues.length > 1 ? ` ${i + 1}` : ""}</a>`),
          row.status === "confirmed" ? `<a href="${esc(row.confirmationUrl)}">Tom's confirmation</a>` : "Awaiting Tom's confirmation"].join(" · ")}` +
        "</p></section>";
    }).join("");
}
export function articleErrata(article, errata, assertions) {
  const owned = new Set(assertions.filter((a) => a.article === article).map((a) => a.tag));
  const rows = errata.flatMap((source) => source.entries.filter((row) => row.tags.some((t) => owned.has(t))).map((row) => ({source: source.source, ...row})));
  if (!rows.length) return "";
  return '<section class="running-context"><h2>Source errata</h2><p>These source diagnoses have the editorial status shown below; this does not certify a formal proof.</p><ul>' +
    rows.map((row) => `<li><a href="${erratumUrl(row.source, row.id)}">${esc(row.title)}</a> — ${row.status}${row.status === "provisional" ? "; awaiting Tom's confirmation" : ""}.${row.status === "withdrawn" ? "" : `<p class="errata-badges">${resolutionBadges(row)}</p>`}</li>`).join("") + "</ul></section>";
}
