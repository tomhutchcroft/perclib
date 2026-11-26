import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import vm from "node:vm";

const script = await fs.readFile(new URL("../src/assets/article.js", import.meta.url), "utf8");

// A minimal DOM: enough structure for ancestors, ids and selectors used by article.js.
class Node {
  constructor(tagName, attrs = {}, children = []) {
    this.tagName = tagName.toUpperCase();
    this.attributes = { ...attrs };
    this.id = attrs.id ?? "";
    this.children = [];
    this.events = {};
    this.style = {};
    this.open = "open" in attrs;
    this.hidden = "hidden" in attrs;
    this.scrolled = 0;
    for (const c of children) this.append(c);
  }
  append(...nodes) {
    for (const n of nodes) {
      n.parentElement = this;
      this.children.push(n);
    }
  }
  remove() {
    const list = this.parentElement?.children;
    if (list) list.splice(list.indexOf(this), 1);
    this.parentElement = null;
  }
  getAttribute(name) {
    return this.attributes[name] ?? null;
  }
  setAttribute(name, value) {
    this.attributes[name] = value;
  }
  addEventListener(name, fn) {
    (this.events[name] ??= []).push(fn);
  }
  dispatch(name, event) {
    for (const fn of this.events[name] ?? []) fn(event);
  }
  scrollIntoView() {
    this.scrolled++;
  }
  *walk() {
    for (const c of this.children) {
      yield c;
      yield* c.walk();
    }
  }
  matches(selector) {
    if (selector === "details") return this.tagName === "DETAILS";
    if (selector === "a[href]") return this.tagName === "A" && this.getAttribute("href") !== null;
    if (selector === "a[data-preview]") return this.tagName === "A" && this.getAttribute("data-preview") !== null;
    if (selector === "[data-details-action]") return this.getAttribute("data-details-action") !== null;
    if (selector === ".article-tools") return (this.getAttribute("class") ?? "").split(" ").includes("article-tools");
    if (selector === "article.article") return this.tagName === "ARTICLE";
    throw Error(`Unsupported selector ${selector}`);
  }
  querySelectorAll(selector) {
    return [...this.walk()].filter((n) => n.matches(selector));
  }
  querySelector(selector) {
    return this.querySelectorAll(selector)[0] ?? null;
  }
  closest(selector) {
    for (let n = this; n; n = n.parentElement) if (n.matches(selector)) return n;
    return null;
  }
  getBoundingClientRect() {
    return { left: 100, top: 100, bottom: 120 };
  }
  get offsetWidth() {
    return 300;
  }
  get offsetHeight() {
    return 80;
  }
}
const h = (tag, attrs, ...children) => new Node(tag, attrs, children);

function page({ hash = "", previews = null } = {}) {
  const step = h("span", { id: "step-3" });
  const inner = h("details", { class: "collapsible" }, h("summary", {}), step);
  const outer = h("details", { class: "collapsible" }, h("summary", {}), inner);
  const other = h("details", {}, h("summary", {}), h("p", {}));
  const anchor = h("a", { id: "tag-ABCD" });
  const proofOfTag = h("details", {}, h("summary", {}), anchor);
  const expand = h("button", { "data-details-action": "expand" });
  const collapse = h("button", { "data-details-action": "collapse" });
  const tools = h("div", { class: "article-tools", hidden: "" }, expand, collapse);
  const fragLink = h("a", { href: "#step-3" });
  const tagLink = h("a", { href: "/tag/ABCD/" });
  const offlineTagLink = h("a", { href: "../../tag/ABCD/index.html" });
  const elsewhere = h("a", { href: "/tag/WXYZ/" });
  const preview = h("a", { href: "/articles/x/", "data-preview": "a:x" });
  const article = h("article", { class: "article" }, tools, fragLink, tagLink, offlineTagLink, elsewhere, preview, outer, other, proofOfTag);
  const body = h("body", {}, article);
  const json = previews ? h("script", { id: "link-preview-data" }) : null;
  if (json) json.textContent = JSON.stringify(previews);
  const windowEvents = {};
  const location = {
    pathname: "/articles/fixture/",
    search: "",
    _hash: hash,
    get href() {
      return "https://wiki.invalid" + this.pathname + this._hash;
    },
    get hash() {
      return this._hash;
    },
    set hash(value) {
      this._hash = "#" + value;
      for (const fn of windowEvents.hashchange ?? []) fn();
    },
  };
  const all = () => [body, ...body.walk()];
  const document = {
    body,
    events: {},
    querySelector: (s) => body.querySelector(s),
    getElementById: (id) => (json && id === json.id ? json : all().find((n) => n.id === id) ?? null),
    addEventListener(name, fn) {
      (this.events[name] ??= []).push(fn);
    },
    createElement: (tag) => h(tag, {}),
  };
  const context = {
    document,
    location,
    URL,
    innerWidth: 1000,
    innerHeight: 800,
    addEventListener(name, fn) {
      (windowEvents[name] ??= []).push(fn);
    },
  };
  vm.runInNewContext(script, context);
  const fire = (name) => (windowEvents[name] ?? []).forEach((fn) => fn());
  const click = (target) => {
    const event = { target, button: 0, defaultPrevented: false, preventDefault() { this.defaultPrevented = true; } };
    for (const fn of document.events.click ?? []) fn(event);
    return event;
  };
  return { step, inner, outer, other, anchor, proofOfTag, tools, expand, collapse, fragLink, tagLink, offlineTagLink, elsewhere, preview, article, body, location, fire, click };
}

test("loading a page whose fragment is inside collapsed blocks opens every enclosing block and scrolls to it", () => {
  const p = page({ hash: "#step-3" });
  assert.equal(p.outer.open, true);
  assert.equal(p.inner.open, true);
  assert.equal(p.other.open, false);
  assert.equal(p.step.scrolled, 1);
  // A /tag/XXXX/ citation redirects to #tag-XXXX, which is handled the same way.
  const q = page({ hash: "#tag-ABCD" });
  assert.equal(q.proofOfTag.open, true);
  assert.equal(q.anchor.scrolled, 1);
  // Unknown fragments are ignored.
  const r = page({ hash: "#absent" });
  assert.equal(r.outer.open, false);
});

test("clicking a fragment link or a /tag/ link to an assertion on this page reveals it in place", () => {
  const p = page();
  const e1 = p.click(p.fragLink);
  assert.equal(e1.defaultPrevented, true);
  assert.equal(p.location.hash, "#step-3");
  assert.equal(p.inner.open && p.outer.open, true);
  // Clicking again with an unchanged hash (no hashchange) still reveals the target.
  p.inner.open = p.outer.open = false;
  p.click(p.fragLink);
  assert.equal(p.inner.open && p.outer.open, true);
  assert.equal(p.step.scrolled, 2);

  for (const link of [p.tagLink, p.offlineTagLink]) {
    const q = page();
    const e = q.click(link === p.tagLink ? q.tagLink : q.offlineTagLink);
    assert.equal(e.defaultPrevented, true);
    assert.equal(q.location.hash, "#tag-ABCD");
    assert.equal(q.proofOfTag.open, true);
  }
  // A citation of an assertion elsewhere is an ordinary navigation.
  const q = page();
  assert.equal(q.click(q.elsewhere).defaultPrevented, false);
  assert.equal(q.location.hash, "");
});

test("expand all and collapse all act on every block of the article", () => {
  const p = page();
  assert.equal(p.tools.hidden, false);
  p.expand.dispatch("click");
  assert.ok([p.outer, p.inner, p.other, p.proofOfTag].every((d) => d.open));
  p.collapse.dispatch("click");
  assert.ok([p.outer, p.inner, p.other, p.proofOfTag].every((d) => !d.open));
});

test("printing opens every block and afterwards restores the reader's choice", () => {
  const p = page();
  p.other.open = true;
  p.fire("beforeprint");
  assert.ok([p.outer, p.inner, p.other, p.proofOfTag].every((d) => d.open));
  p.fire("afterprint");
  assert.deepEqual([p.outer.open, p.inner.open, p.other.open, p.proofOfTag.open], [false, false, true, false]);
});

test("hovering a linked statement shows its pre-rendered preview and leaving hides it", () => {
  const p = page({ previews: { "a:x": { k: "Article", t: "<b>Title</b>", s: "Summary" } } });
  p.article.dispatch("mouseover", { target: p.preview });
  const box = p.body.children.find((n) => n.className === "link-preview");
  assert.ok(box);
  assert.equal(box.innerHTML, "<small>Article</small><strong><b>Title</b></strong><p>Summary</p>");
  assert.equal(box.style.top, "128px");
  p.article.dispatch("mouseout", { target: p.preview });
  assert.ok(!p.body.children.some((n) => n.className === "link-preview"));
  // No preview data: hovering does nothing.
  const q = page();
  q.article.dispatch("mouseover", { target: q.preview });
  assert.ok(!q.body.children.some((n) => n.className === "link-preview"));
});
