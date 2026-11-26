import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { collectHistory, recordedReferenceHistory, historyPage } from "../src/history.mjs";
import { historyCsv, dailyHistoryCsv } from "../src/history-csv.mjs";

const csvRows = (csv) => {
  const [keys, ...rows] = csv.trimEnd().split("\r\n").map(line => line.split(","));
  return rows.map(row => Object.fromEntries(keys.map((key, i) => [key, row[i]])));
};

test("reference history follows its own merge chain without absorbing draft commits", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-reference-series-"));
  const git = (...args) => execFileSync("git", args, {
    cwd: root, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"],
  }).trim();
  const write = (file, text) => fs.writeFile(path.join(root, file), text);
  const commit = (message) => {
    git("add", "."); git("commit", "-m", message);
    return git("rev-parse", "HEAD");
  };
  try {
    git("init", "-b", "main");
    git("config", "user.name", "Fixture");
    git("config", "user.email", "fixture@example.invalid");
    await fs.mkdir(path.join(root, "PercLib"));
    await fs.mkdir(path.join(root, "wiki/articles"), {recursive: true});
    await write("PercLib/Basic.lean", "-- baseline\n");
    await write("wiki/articles/base.md", "Merged baseline\n");
    const base = commit("Baseline");
    git("checkout", "-b", "draft");
    await write("wiki/articles/draft.md", "Unmerged article\n");
    const draft = commit("Wiki continuation");
    git("checkout", "main");
    await write("PercLib/Second.lean", "-- second\n");
    const added = commit("Library grows on main");
    git("checkout", "-b", "prover");
    await write("PercLib/Third.lean", "-- third\n");
    const side = commit("Library work before integration");
    git("checkout", "main");
    git("merge", "--no-ff", "prover", "-m", "Integrate library work");
    const merge = git("rev-parse", "HEAD");
    await write("README", "Only metadata changes\n");
    const reference = commit("Record metadata at the reference tip");
    await write("PercLib/Dirty.lean", "-- not committed\n");

    const h = collectHistory(root, draft, "main");
    const r = recordedReferenceHistory(h);
    assert.equal(h.comparison.relationship, "diverged");
    assert.deepEqual(h.snapshots.map(s => s.commit), [base, draft]);
    assert.deepEqual(h.snapshots.map(s => s.articles), [1, 2]);
    assert.deepEqual(r.snapshots.map(s => s.commit), [base, added, merge, reference]);
    assert.ok(!r.snapshots.some(s => [side, draft].includes(s.commit)));
    assert.deepEqual(r.snapshots.map(s => s.leanFiles), [1, 2, 3, 3]);
    assert.ok(r.snapshots.every(s => s.articles === 1));
    assert.deepEqual(r.snapshots.at(-1), h.comparison.snapshot);
    assert.equal(r.tip, reference);
    assert.equal(r.buildTip, draft);
    assert.equal(r.reference, "main");
    assert.equal(r.shallow, false);

    const page = historyPage(h, "library", {reference: true});
    assert.match(page, /Recorded reference <code>main<\/code>/);
    assert.match(page, /reference’s own first-parent chain/);
    assert.match(page, /not a live check of GitHub/);
    assert.match(page, /3 at the reference tip/);
    assert.ok(page.includes(`/compare/${added}...${merge}`));
    assert.ok(!page.includes(`/commit/${draft}`));
    assert.match(page, /href="\/metrics\/reference\/history.json"/);
    assert.match(page, /href="\/metrics\/reference\/history.csv" download="perclib-reference-history.csv"/);
    assert.match(page, /href="\/metrics\/reference\/history-daily.csv"/);
    assert.doesNotMatch(page, /href="\/metrics\/history(?:-daily)?\.csv"/);
    assert.match(historyPage(h, "wiki"), /href="\/metrics\/reference\/wiki\/"/);

    const rows = csvRows(historyCsv(r));
    assert.deepEqual(rows.map(row => row.commit), [base, added, merge, reference]);
    assert.ok(rows.every(row => row.selectedTip === reference && row.shallow === "false"));
    assert.deepEqual(rows.map(row => row.leanFilesDelta), ["", "1", "1", "0"]);
    assert.ok(rows.every(row => row.articles === "1"));
    const daily = csvRows(dailyHistoryCsv(r));
    assert.ok(daily.every(row => row.selectedTip === reference));
    assert.equal(daily.reduce((sum, row) => sum + Number(row.leanFilesDelta), 0), 2);

    const same = collectHistory(root, reference, reference);
    assert.deepEqual(recordedReferenceHistory(same).snapshots, same.snapshots);
    const missing = collectHistory(root, draft, "missing-reference");
    assert.equal(missing.available, true);
    assert.equal(recordedReferenceHistory(missing).available, false);
    assert.equal(historyCsv(recordedReferenceHistory(missing)), null);
  } finally {
    await fs.rm(root, {recursive: true, force: true});
  }
});

test("a saved comparison point does not invent a reference series, and shallow history stays visible", () => {
  const snapshot = {commit: "a".repeat(40), date: "2026-11-16T00:00:00Z", leanFiles: 1, leanLines: 2};
  const legacy = {available: true, tip: "b".repeat(40), snapshots: [snapshot],
    comparison: {available: true, reference: "refs/remotes/origin/main", referenceCommit: snapshot.commit, snapshot}};
  assert.equal(recordedReferenceHistory(legacy).available, false);
  const absent = historyPage(legacy, "library", {reference: true});
  assert.match(absent, /Reference history is unavailable/);
  assert.doesNotMatch(absent, /history-chart|history.csv|NaN|undefined/);
  legacy.comparison.history = {available: true, reference: "refs/remotes/origin/main",
    tip: snapshot.commit, shallow: true, selection: "Fixture", snapshots: [snapshot]};
  const page = historyPage(legacy, "library", {reference: true});
  assert.match(page, /checkout is shallow/);
  assert.match(page, /Baseline — no earlier snapshot/);
  assert.doesNotMatch(page, /\/compare\/|NaN|undefined/);
});
