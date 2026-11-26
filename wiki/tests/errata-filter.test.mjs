import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import vm from "node:vm";
import {errataIndex} from "../src/errata.mjs";

const script = await fs.readFile(new URL("../src/assets/errata-filter.js", import.meta.url), "utf8");
function start(search = "", historyThrows = false) {
  const row = (repair, scale) => ({dataset: {repair, scale}, hidden: false});
  const rows = [row("found", "local"), row("partial", "substantial"), row("found", "substantial"),
    row("open", "statement"), row("unassessed", "unknown"), row("withdrawn", "")];
  const group = (source, selected) => ({dataset: {errataGroup: source}, hidden: false, querySelectorAll: () => selected});
  const groups = [group("alpha", rows.slice(0, 2)), group("beta", rows.slice(2))];
  const choices = {repair: ["", "found", "partial", "workaround", "open", "unassessed", "withdrawn"],
    significance: ["", "notation", "local", "substantial", "statement", "unknown"], source: ["", "alpha", "beta"]};
  const fields = Object.fromEntries(Object.entries(choices).map(([key, values]) => [key,
    {value: "", options: values.map(value => ({value}))}]));
  const events = {}, windowEvents = {}, writes = [];
  const form = {hidden: true, elements: {namedItem: key => fields[key]}, addEventListener: (name, fn) => { events[name] = fn; }};
  const status = {}, pending = {hidden: false};
  const location = {search, pathname: "/errata/index.html", hash: "#main-content"};
  vm.runInNewContext(script, {
    document: {querySelector: selector => ({"#errata-filter": form, "#errata-filter-status": status, "#errata-pending": pending})[selector], querySelectorAll: () => groups},
    window: {addEventListener: (name, fn) => { windowEvents[name] = fn; }}, location, URLSearchParams,
    history: {replaceState: (_state, _title, url) => {
      if (historyThrows) throw Error("History changes forbidden");
      writes.push(url); location.search = new URL(url, "https://wiki.test").search;
    }},
  });
  return {rows, groups, fields, events, windowEvents, writes, location, form, status, pending,
    visible: () => rows.map((row, i) => row.hidden ? null : i).filter(i => i !== null)};
}

test("errata filters intersect repair, significance and source without counting the incomplete summary twice", () => {
  const app = start("?repair=found&significance=substantial&source=beta");
  assert.deepEqual(app.visible(), [2]);
  assert.equal(app.status.textContent, "Showing 1 of 5 active entries; 0 of 1 withdrawn entries.");
  assert.equal(app.groups[0].hidden, true);
  assert.equal(app.groups[1].hidden, false);
  assert.equal(app.pending.hidden, true);
  assert.equal(app.form.hidden, false);
  assert.deepEqual(app.writes, []);
  app.fields.source.value = "alpha"; app.events.change();
  assert.deepEqual(app.visible(), []);
  assert.match(app.status.textContent, /No entries match these filters/);
  assert.ok(app.groups.every(group => group.hidden));
});

test("clear filters restores all entries and preserves unrelated query parameters and anchors", () => {
  const app = start("?repair=open&significance=statement&source=beta&context=reading");
  let prevented = false;
  app.events.reset({preventDefault() { prevented = true; }});
  assert.equal(prevented, true);
  assert.deepEqual(app.visible(), [0, 1, 2, 3, 4, 5]);
  assert.equal(app.status.textContent, "Showing 5 of 5 active entries; 1 of 1 withdrawn entries.");
  assert.equal(app.pending.hidden, false);
  assert.equal(app.writes.at(-1), "/errata/index.html?context=reading#main-content");
  app.fields.repair.value = "unassessed"; app.events.change();
  assert.deepEqual(app.visible(), [4]);
  app.fields.repair.value = "withdrawn"; app.events.change();
  assert.deepEqual(app.visible(), [5]);
  assert.match(app.status.textContent, /0 of 5 active entries; 1 of 1 withdrawn/);
  app.fields.significance.value = "unknown"; app.events.change();
  assert.deepEqual(app.visible(), []); // Withdrawal has no repair significance.
});

test("invalid URL values are ignored and history navigation restores valid selections", () => {
  const app = start("?repair=proved&significance=constructor&source=%22%3E%3Cscript%3E");
  assert.deepEqual(app.visible(), [0, 1, 2, 3, 4, 5]);
  assert.ok(Object.values(app.fields).every(field => field.value === ""));
  app.location.search = "?repair=open&source=beta"; app.windowEvents.popstate();
  assert.deepEqual(app.visible(), [3]);
  assert.equal(app.fields.repair.value, "open");
  assert.equal(app.fields.source.value, "beta");
  assert.deepEqual(app.writes, []);
});

test("downloaded copies keep filtering if the browser forbids History API changes", () => {
  const app = start("", true);
  app.fields.repair.value = "partial";
  let prevented = false;
  app.events.submit({preventDefault() { prevented = true; }});
  assert.equal(prevented, true);
  assert.deepEqual(app.visible(), [1]);
  assert.match(app.status.textContent, /Showing 1 of 5 active entries/);
  app.events.reset({preventDefault() {}});
  assert.deepEqual(app.visible(), [0, 1, 2, 3, 4, 5]);
});

test("the static errata index retains every entry and its audit when filtering is unavailable", () => {
  const sources = [{id: "alpha", shortName: "A < B", edition: "v1"}];
  const entries = [{id: "unassessed", title: "Legacy entry", status: "provisional"},
    {id: "fixed", title: "Repaired entry", status: "provisional", resolution: {status: "found", scale: "substantial", summary: "A repair", impact: "A new proof"}},
    {id: "retired", title: "Retired entry", status: "withdrawn", withdrawalReason: "No fault"}];
  const html = errataIndex([{source: "alpha", entries}], sources);
  assert.match(html, /id="errata-filter"[^>]*hidden/);
  assert.match(html, /Enable JavaScript to filter this list/);
  assert.match(html, /<option value="alpha">A &lt; B<\/option>/);
  assert.match(html, /<option value="withdrawn">Withdrawn entries<\/option>/);
  assert.match(html, /data-repair="unassessed" data-scale="unknown"/);
  assert.match(html, /data-repair="withdrawn" data-scale=""/);
  assert.match(html, /data-repair="found" data-scale="substantial"/);
  for (const entry of entries) assert.ok(html.includes(`/errata/alpha/#${entry.id}`));
  assert.match(html, /Source-version audit not recorded here/);
  assert.doesNotMatch(html, /<li[^>]*hidden|data-errata-group="alpha"[^>]*hidden/);
});
