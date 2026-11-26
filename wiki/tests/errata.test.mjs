import test from "node:test";
import assert from "node:assert/strict";
import {validateErrata, errataPage, articleErrata, errataIndex, errataResolutionText, errataVersionText} from "../src/errata.mjs";
const source = {id: "fixture-src", shortName: "Fixture", title: "Fixture", edition: "Fixture edition", url: "https://example.org/fixture-src"};
const assertions = [{tag: "AAAA", article: "alpha", title: "Affected assertion"}];
const absent = {entries: null, reviews: [], provenance: null};
const fixture = () => ({schema: "perclib-source-errata-v1", source: "fixture-src", entries: [{
  id: "sign", title: "A sign", status: "provisional", locator: "Lemma 1",
  claim: "<script>source</script>", problem: "A missing sign.", correction: "Still unresolved.", leanImpact: "Keep <scope> explicit.",
  tags: ["AAAA"], issues: ["https://github.com/example/repo/issues/1"]}]});
test("provisional source diagnoses stay provisional on source and article pages", () => {
  const data = validateErrata(fixture(), [source], assertions);
  const html = errataPage(data, source, assertions, absent);
  assert.ok(html.includes("Editorial status: provisional"));
  assert.ok(html.includes("Awaiting Tom's confirmation"));
  assert.ok(html.includes("&lt;script&gt;source&lt;/script&gt;"));
  assert.ok(!html.includes("<script>"));
  assert.ok(articleErrata("alpha", [data], assertions).includes("/errata/fixture-src/#sign"));
  assert.equal(articleErrata("beta", [data], assertions), "");
});
test("confirmation, withdrawal, and assertion references require explicit records", () => {
  const data = fixture(); data.entries[0].status = "confirmed";
  assert.throws(() => validateErrata(data, [source], assertions), /confirmation/);
  data.entries[0].confirmationUrl = "https://github.com/example/repo/issues/1#issuecomment-2";
  assert.ok(errataPage(validateErrata(data, [source], assertions), source, assertions, absent).includes("Tom's confirmation"));
  data.entries[0].status = "withdrawn";
  assert.throws(() => validateErrata(data, [source], assertions), /withdrawal/);
  Object.assign(data.entries[0], {withdrawalReason: "No fault.", withdrawalUrl: source.url});
  const html = errataPage(validateErrata(data, [source], assertions), source, assertions, absent);
  assert.ok(html.includes('id="sign"'));
  assert.ok(html.includes("This entry has been withdrawn"));
  assert.ok(!html.includes("Reported problem"));
  data.entries[0].tags = ["ZZZZ"];
  assert.throws(() => validateErrata(data, [source], assertions), /tag/);
});
test("errata distinguish absent evidence, statement review, proof debts and source confirmation", () => {
  const data = validateErrata(fixture(), [source], assertions);
  const noManifest = errataPage(data, source, assertions, absent);
  assert.ok(noManifest.includes("Formal status: unavailable"));
  assert.ok(!noManifest.includes("Formal status: unformalised"));
  assert.ok(noManifest.includes("&lt;scope&gt;"));
  assert.ok(noManifest.includes('/articles/alpha/#formal-evidence'));
  const fingerprint = {schema: "perclib-statement-v1", sha256: "a".repeat(64)};
  const entry = {tag: "AAAA", proof_status: "statement-only", fingerprint, inputs: []};
  const evidence = {entries: new Map([["AAAA", entry]]), reviews: [], provenance: {
    repository: "tomhutchcroft/perclib", commit: "b".repeat(40),
    runUrl: "https://github.com/tomhutchcroft/perclib/actions/runs/123"
  }};
  let html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Compiled statement; correspondence pending"));
  assert.ok(html.includes("Wiki/Lean correspondence review: missing"));
  assert.ok(html.includes('/articles/alpha/#formal-AAAA'));
  assert.ok(html.includes(evidence.provenance.commit));
  assert.ok(html.includes(evidence.provenance.runUrl));
  evidence.reviews.push({tag: "AAAA", fingerprint: {...fingerprint}});
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Formal status: stated"));
  assert.ok(html.includes("Editorial status: provisional"));
  entry.fingerprint = {...fingerprint, sha256: "c".repeat(64)};
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Wiki/Lean correspondence review: stale"));
  assert.ok(!html.includes("Formal status: stated"));
  data.entries[0].status = "confirmed";
  data.entries[0].confirmationUrl = source.url;
  entry.proof_status = "proved-modulo";
  entry.inputs = ["Synthetic.<Input>"];
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Editorial status: confirmed"));
  assert.ok(html.includes("Formal status: proved-modulo"));
  assert.ok(html.includes("Named inputs still to discharge"));
  assert.ok(html.includes("Synthetic.&lt;Input&gt;"));
  assert.ok(html.includes("Wiki/Lean correspondence review: stale"));
  entry.proof_status = "proved"; entry.inputs = [];
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Formal status: proved."));
  assert.ok(html.includes("Wiki/Lean correspondence review: stale"));
  data.entries[0].status = "withdrawn";
  data.entries[0].withdrawalReason = "No fault.";
  data.entries[0].withdrawalUrl = source.url;
  html = errataPage(data, source, assertions, evidence);
  assert.ok(!html.includes("Consequences for Lean"));
  assert.ok(!html.includes("Formal status: proved"));
});
test("authored formal statuses and missing formalisation consequences fail closed", () => {
  const data = fixture();
  data.entries[0].formalStatus = "proved";
  assert.throws(() => validateErrata(data, [source], assertions), /invalid entry/);
  delete data.entries[0].formalStatus;
  delete data.entries[0].leanImpact;
  assert.throws(() => validateErrata(data, [source], assertions), /invalid entry/);
});

const repair = () => ({status: "found", summary: "Restore <factor>.", scale: "local", impact: "The conclusion is unchanged."});
test("repair availability is independent of confirmation and compiled evidence", () => {
  const data = fixture(), row = data.entries[0];
  row.resolution = repair();
  validateErrata(data, [source], assertions);
  let html = errataPage(data, source, assertions, absent);
  assert.match(html, /Fix found/);
  assert.match(html, /Changes: Local correction/);
  assert.match(html, /Restore &lt;factor&gt;/);
  assert.match(html, /Editorial status: provisional/);
  assert.match(html, /Formal status: unavailable/);
  assert.match(articleErrata("alpha", [data], assertions), /Fix found/);
  assert.match(errataResolutionText(row), /Local correction.*Restore <factor>/);
  row.status = "confirmed"; row.confirmationUrl = source.url;
  row.resolution = {...repair(), status: "open", scale: "unknown", summary: "Still open."};
  html = errataPage(validateErrata(data, [source], assertions), source, assertions, absent);
  assert.match(html, /Editorial status: confirmed/);
  assert.match(html, /No fix yet/);
  assert.match(html, /Not yet determined/);
  assert.match(html, /Formal status: unavailable/);
});
test("legacy entries are unassessed, while incomplete and withdrawn entries remain distinct", () => {
  const data = fixture();
  data.entries[0].correction = "A correction exists in prose, without an assessment.";
  const legacy = errataPage(data, source, assertions, absent);
  assert.match(legacy, /Not assessed/);
  assert.doesNotMatch(legacy, /class="errata-badge errata-found"/);
  const base = data.entries[0];
  for (const status of ["found", "partial", "workaround", "open"])
    data.entries.push({...base, id: status, title: status, resolution: {...repair(), status}});
  data.entries.push({...base, id: "withdrawn", title: "Withdrawn fix", status: "withdrawn", withdrawalUrl: source.url, withdrawalReason: "Not an error.", resolution: repair()});
  validateErrata(data, [source], assertions);
  const html = errataIndex([data], [source]);
  for (const label of ["Fix found", "Partial fix", "Workaround found", "No fix yet", "Not assessed"])
    assert.ok(html.includes(`<dt>${label}</dt><dd>1</dd>`));
  assert.match(html, /5 active source entries; 1 withdrawn/);
  const pending = html.split('<h2>Still incomplete</h2>')[1].split('</section>')[0];
  for (const id of ["sign", "partial", "workaround", "open"])
    assert.ok(pending.includes(`/errata/fixture-src/#${id}`));
  assert.ok(!pending.includes('/errata/fixture-src/#found'));
  assert.ok(!pending.includes('/errata/fixture-src/#withdrawn'));
  const withdrawn = errataPage(data, source, assertions, absent).split('id="withdrawn"')[1];
  assert.doesNotMatch(withdrawn, /Fix found|Impact:|Formal status/);
  assert.equal(errataResolutionText(data.entries.at(-1)), "");
  assert.match(html, /Restore &lt;factor&gt;/);
});
test("repair assessments require a known status, a scale, and concrete repair and impact text", () => {
  for (const invalid of [null, [], {}, {...repair(), status: "proved"}, {...repair(), scale: "constructor"},
    {...repair(), scale: ["local"]}, {...repair(), summary: " "}, {...repair(), impact: ""}, {...repair(), formalStatus: "proved"}]) {
    const data = fixture(); data.entries[0].resolution = invalid;
    assert.throws(() => validateErrata(data, [source], assertions), /repair assessment/);
  }
});

const audit = () => ({checkedVersion: "Preprint v1", checkedUrl: "https://example.org/v1",
  method: "HTML and extracted PDF text; no visual check.", scope: "Lemma <1> only.",
  comparisons: [{version: "Published <article>", url: "https://example.org/published", status: "pending",
    findings: "Publication metadata read; formulas not compared."}]});
test("checked editions and pending comparisons stay separate from fixes and proof status", () => {
  const data = fixture(); data.versionAudit = audit(); data.entries[0].resolution = repair();
  const original = structuredClone(data.entries);
  validateErrata(data, [source], assertions);
  for (const html of [errataIndex([data], [source]), errataPage(data, source, assertions, absent)]) {
    assert.match(html, /Checked version:.*Preprint v1/);
    assert.match(html, /Version comparison pending/);
    assert.match(html, /Publication metadata read; formulas not compared/);
    assert.match(html, /Lemma &lt;1&gt;/);
    assert.match(html, /Published &lt;article&gt;/);
    assert.match(html, /Fix found/);
    assert.match(html, /Editorial status: provisional/);
    assert.doesNotMatch(html, /Version comparison recorded|Editorial status: confirmed|Formal status: proved/);
  }
  assert.match(errataVersionText(data), /Preprint v1.*Version comparison pending.*formulas not compared/);
  assert.deepEqual(data.entries, original);
  data.versionAudit.comparisons[0] = {...audit().comparisons[0], status: "compared", findings: "Lemma 1 has the same sign; other passages not checked."};
  const html = errataPage(validateErrata(data, [source], assertions), source, assertions, absent);
  assert.match(html, /Version comparison recorded/);
  assert.match(html, /other passages not checked/);
  assert.match(html, /Editorial status: provisional/);
  assert.match(html, /Formal status: unavailable/);
});
test("absent shared audit does not infer that source passages were never read", () => {
  const data = fixture();
  for (const text of [errataIndex([data], [source]), errataPage(data, source, assertions, absent), errataVersionText(data)]) {
    assert.match(text, /Source-version audit not recorded here; consult the individual locators/);
    assert.doesNotMatch(text, /Version comparison pending|Version comparison recorded|Checked version:/);
  }
});
test("source-version audits reject missing scope, unsafe links, duplicate editions and invented statuses", () => {
  for (const invalid of [null, [], {}, {...audit(), checkedVersion: " "}, {...audit(), checkedUrl: "javascript:alert(1)"},
    {...audit(), checkedUrl: "https://user:secret@example.org/v1"}, {...audit(), method: []}, {...audit(), scope: ""},
    {...audit(), comparisons: null}, {...audit(), formalStatus: "proved"}]) {
    const data = fixture(); data.versionAudit = invalid;
    assert.throws(() => validateErrata(data, [source], assertions), /source-version audit/);
  }
  const comparison = audit().comparisons[0];
  for (const invalid of [null, [], {}, {...comparison, version: " "}, {...comparison, url: "http://example.org/v2"},
    {...comparison, status: "confirmed"}, {...comparison, findings: " "}, {...comparison, formalStatus: "proved"},
    {...comparison, url: audit().checkedUrl}]) {
    const data = fixture(); data.versionAudit = {...audit(), comparisons: [invalid]};
    assert.throws(() => validateErrata(data, [source], assertions), /source-version comparison/);
  }
  const data = fixture(); data.versionAudit = {...audit(), comparisons: [comparison, comparison]};
  assert.throws(() => validateErrata(data, [source], assertions), /source-version comparison/);
});
