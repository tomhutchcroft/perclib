import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import vm from "node:vm";

const script = await fs.readFile(new URL("../src/assets/site.js", import.meta.url), "utf8");
function element() {
  return {
    events: {}, attributes: {}, children: [],
    addEventListener(name, fn) { this.events[name] = fn; },
    setAttribute(name, value) { this.attributes[name] = value; },
    getAttribute(name) { return this.attributes[name]; },
    append(...children) { this.children.push(...children); },
    replaceChildren(...children) { this.children = children; },
    focus() {},
  };
}
async function start({offline, ok = true, historyThrows = false} = {}) {
  const nodes = Object.fromEntries(["menu-toggle", "sidebar", "mobile-overlay", "search-form", "search-results", "search-status"].map(name => [name, element()]));
  const input = element();
  nodes["search-form"].elements = {q: input};
  let fetched = 0;
  const rows = [{url: "../tag/ABCD/index.html", title: "Lémma", text: "Lémma proof", summary: "A result"}];
  const context = {
    document: {
      querySelector(selector) { return nodes[selector.slice(1)] ?? null; },
      body: {classList: {toggle() {}}},
      addEventListener() {},
      createElement() { return element(); },
    },
    matchMedia() { return {matches: false, addEventListener() {}}; },
    location: {search: "?q=lemma"},
    history: {replaceState() { if (historyThrows) throw Error("file origin"); }},
    URLSearchParams,
    fetch: async url => {
      fetched++;
      assert.equal(url, "/search-index.json");
      if (offline) throw Error("Offline search must not fetch");
      return {ok, json: async () => rows};
    },
  };
  if (offline) context.PERCLIB_OFFLINE_SEARCH = rows;
  vm.runInNewContext(script, context);
  await new Promise(resolve => setImmediate(resolve));
  return {nodes, input, get fetched() { return fetched; }};
}

test("offline search uses bundled data and keeps working when file origins forbid history changes", async () => {
  const app = await start({offline: true, historyThrows: true});
  assert.equal(app.fetched, 0);
  assert.equal(app.nodes["search-status"].textContent, "1 results");
  assert.equal(app.nodes["search-results"].children[0].href, "../tag/ABCD/index.html");
  let prevented = false;
  app.nodes["search-form"].events.submit({preventDefault() { prevented = true; }});
  assert.equal(prevented, true);
  assert.equal(app.nodes["search-results"].children.length, 1);
  app.input.value = "no matching result";
  app.input.events.input();
  assert.equal(app.nodes["search-status"].textContent, "0 results");
});

test("hosted search still fetches the index and renders matching results", async () => {
  const app = await start();
  assert.equal(app.fetched, 1);
  assert.equal(app.nodes["search-results"].children.length, 1);
});

test("unavailable hosted search shows the existing browse fallback", async () => {
  const app = await start({ok: false});
  assert.equal(app.fetched, 1);
  assert.match(app.nodes["search-status"].textContent, /Browse the article index/);
  assert.equal(app.nodes["search-results"].children.length, 0);
});

