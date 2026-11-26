import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {execFileSync} from "node:child_process";
import {collectHistory, historyPage, summarizeDays, errataCountFields} from "../src/history.mjs";
import {historyCsv, dailyHistoryCsv, fileHistoryCsv} from "../src/history-csv.mjs";

const csv = text => {
  const [header, ...rows] = text.trimEnd().split("\r\n").map(line => line.split(","));
  return rows.map(row => Object.fromEntries(header.map((key, i) => [key, row[i]])));
};
async function fixture(run) {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-errata-history-"));
  const git = (...args) => execFileSync("git", args, {cwd: root, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"]}).trim();
  const record = (source, entries) => fs.writeFile(path.join(root, `wiki/errata/${source}.json`),
    JSON.stringify({schema: "perclib-source-errata-v1", source, entries}));
  const commit = message => {git("add", "."); git("commit", "-m", message); return git("rev-parse", "HEAD");};
  try {
    git("init"); git("config", "user.name", "Fixture"); git("config", "user.email", "fixture@example.invalid");
    await fs.mkdir(path.join(root, "wiki/errata/nested"), {recursive: true});
    await fs.mkdir(path.join(root, "wiki/articles"));
    await fs.writeFile(path.join(root, "wiki/articles/a.md"), "Baseline article");
    commit("Baseline");
    await run({root, git, record, commit});
  } finally {await fs.rm(root, {recursive: true, force: true});}
}

test("errata-only commits retain status transitions, tombstones, deletions and separate reference history", async () => fixture(async ({root, record, commit}) => {
  const a = {id: "first", status: "provisional"}, b = {id: "second", status: "provisional"};
  await record("paper", [a,b]);
  await fs.writeFile(path.join(root, "wiki/errata/nested/ignored.json"), "not an errata source");
  await fs.writeFile(path.join(root, "wiki/errata/ignored.txt"), "not JSON");
  const reference = commit("Report two entries");
  await record("paper", [{...a,status:"confirmed"},b]); commit("Confirm one");
  await record("paper", [{...a,status:"confirmed"},{...b,status:"withdrawn"}]); commit("Withdraw one");
  await record("other", [{id:"third",status:"provisional"}]); commit("Add source");
  await fs.rm(path.join(root, "wiki/errata/paper.json")); commit("Remove source");
  await record("other", [{id:"third",status:"confirmed"}]); // Dirty status must not enter history.
  const h = collectHistory(root, "HEAD", reference);
  assert.deepEqual(h.snapshots.map(r => errataCountFields.map(k => r[k])), [
    [0,0,0,0,0], [1,2,2,0,0], [1,2,1,1,0], [1,2,0,1,1], [2,3,1,1,1], [1,1,1,0,0],
  ]);
  assert.ok(h.snapshots.every(r => r.articles === 1));
  assert.equal(h.comparison.history.snapshots.length, 2);
  assert.equal(h.comparison.snapshot.errataEntries, 2);
  for (const [files, snapshot] of [[h.files,h.snapshots.at(-1)],[h.comparison.files,h.comparison.snapshot]])
    for (const key of errataCountFields)
      assert.equal(files.reduce((n,f) => n+(f.counts[key]||0),0),snapshot[key]);
  for (const key of errataCountFields)
    assert.equal(summarizeDays(h.snapshots).reduce((n,d) => n+d.changes[key],0),h.snapshots.at(-1)[key]);
  const page = historyPage(h,"errata");
  assert.match(page,/Errata history/); assert.match(page,/not an inferred withdrawal/);
  assert.match(page,/paper\.json<\/code><\/th><td>Removed/);
  assert.match(page,/2 → 0 \(-2\)/);
  assert.doesNotMatch(page,/NaN|undefined|ignored\.json|ignored\.txt/);
  assert.match(historyPage(h,"wiki"),/href="\/metrics\/errata\/"/);
  assert.doesNotMatch(historyPage(h,"wiki"),/paper\.json<\/code>/);
  assert.match(historyPage(h,"errata",{reference:true}),/2 recorded snapshots/);
  assert.match(historyPage(h,"errata",{reference:true}),/\/metrics\/reference\/history.csv/);
  const rows=csv(historyCsv(h));
  assert.equal(rows[2].errataEntriesDelta,"0");
  assert.equal(rows[2].errataConfirmedDelta,"1");
  assert.equal(rows[3].errataWithdrawnDelta,"1");
  assert.equal(rows[5].errataWithdrawnDelta,"-1");
  const files=csv(fileHistoryCsv(h));
  const removed=files.find(r=>r.path==="wiki/errata/paper.json");
  assert.equal(removed.kind,"errata"); assert.equal(removed.errataEntriesDelta,"-2");
}));

test("unknown historical errata formats leave entry counters unavailable while other counts survive", async () => fixture(async ({root,record,commit}) => {
  const file=path.join(root,"wiki/errata/paper.json");
  await fs.writeFile(file,"{broken"); const unreadable=commit("Unreadable historical JSON");
  await record("paper",[{id:"entry",status:"future-status"}]); commit("Unknown status");
  await record("paper",[{id:"entry",status:"provisional"},{id:"entry",status:"provisional"}]); commit("Duplicate identity");
  await record("paper",[{id:"entry",status:"provisional"}]); commit("Known record");
  const h=collectHistory(root);
  assert.deepEqual(h.snapshots.map(r=>r.errataSources),[0,1,1,1,1]);
  assert.deepEqual(h.snapshots.map(r=>r.errataEntries),[0,null,null,null,1]);
  assert.ok(h.snapshots.every(r=>r.articles===1));
  const page=historyPage(h,"errata");
  assert.match(page,/Some errata counters are unavailable/);
  assert.doesNotMatch(page,/NaN|undefined/);
  const rows=csv(historyCsv(h));
  assert.equal(rows[1].errataEntries,""); assert.equal(rows[1].errataEntriesDelta,"");
  assert.equal(rows[4].errataEntries,"1"); assert.equal(rows[4].errataEntriesDelta,"");
  // Unknown transitions cannot become zero or be inferred across the gap.
  assert.ok(csv(dailyHistoryCsv(h)).some(r=>r.errataEntriesDelta===""));
  const comparison=collectHistory(root,"HEAD",unreadable);
  const fileRow=csv(fileHistoryCsv(comparison)).find(r=>r.path==="wiki/errata/paper.json");
  assert.equal(fileRow.errataEntriesReference,"");
  assert.equal(fileRow.errataEntriesSelected,"1");
  assert.equal(fileRow.errataEntriesDelta,"");
  assert.equal(fileRow.errataSourcesDelta,"0");
}));

test("older saved histories do not invent errata counters or a reference series", () => {
  const h={available:true,tip:"old",snapshots:[{commit:"old",date:"2026-11-17T00:00:00Z",articles:2}]};
  const page=historyPage(h,"errata");
  assert.match(page,/Some errata counters are unavailable/);
  assert.doesNotMatch(page,/class="history-point"|NaN|undefined/);
  const row=csv(historyCsv(h))[0],day=csv(dailyHistoryCsv(h))[0];
  for(const key of errataCountFields){assert.equal(row[key],"");assert.equal(row[key+"Delta"],"");assert.equal(day[key+"Delta"],"");}
  assert.match(historyPage(h,"errata",{reference:true}),/Reference history is unavailable/);
});
