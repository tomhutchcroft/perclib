// The GitHub Pages edition: a full build under the base path /perclib/, checked
// for the unfinished banner, robots meta, About page, draft markers and links.
import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { build } from "../src/build.mjs";
import { decode, plain, unfinishedNotice } from "../src/render.mjs";
import { readArticles } from "../scripts/articles.mjs";

const base = "/perclib/";
const commit = "0123456789abcdef0123456789abcdef01234567";

async function walk(dir, prefix = "") {
  const out = [];
  for (const entry of await fs.readdir(dir, { withFileTypes: true })) {
    const rel = prefix + entry.name;
    if (entry.isDirectory()) out.push(...(await walk(path.join(dir, entry.name), rel + "/")));
    else out.push(rel);
  }
  return out;
}

// Every local URL of a page, resolved as a browser would resolve it on
// https://host<base><file>, must stay under the base path and name a file
// written to the output directory (and an existing anchor in it).
function checkUrl(url, from, onDisk, html) {
  if (/^(https?:|mailto:|data:)/.test(url)) return;
  const resolved = new URL(url, `https://pages.invalid${base}${from}`);
  assert.equal(resolved.origin, "https://pages.invalid", `${from}: ${url} leaves the site`);
  const pathname = decodeURIComponent(resolved.pathname);
  assert.ok(pathname.startsWith(base), `${from}: ${url} is outside ${base}`);
  let target = pathname.slice(base.length);
  if (!target || target.endsWith("/")) target += "index.html";
  assert.ok(onDisk.has(target), `${from}: ${url} does not resolve inside dist/ (${target})`);
  if (resolved.hash && target.endsWith(".html"))
    assert.ok(
      html.get(target).includes(`id="${decodeURIComponent(resolved.hash.slice(1))}"`),
      `${from}: missing anchor ${url}`,
    );
}

test("Pages build under /perclib/: banner, robots, About, draft markers and every link inside dist/", async () => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-pages-"));
  try {
    const out = path.join(dir, "dist");
    const files = await build(out, {
      basePath: "/perclib",
      buildCommit: commit,
      buildDate: new Date("2026-11-21T12:34:56Z"),
    });
    const articles = await readArticles();
    const onDisk = new Set(await walk(out));
    const html = new Map();
    for (const file of onDisk)
      if (file.endsWith(".html")) html.set(file, await fs.readFile(path.join(out, file), "utf8"));
    assert.ok(html.size > articles.length);
    assert.deepEqual([...files.keys()].filter((f) => f.endsWith(".html")).sort(), [...html.keys()].sort());

    for (const [file, page] of html) {
      // Banner: once, at the top of the main content, with the exact words.
      const banners = [...page.matchAll(/<div class="unfinished-banner"[^>]*><p>([\s\S]*?)<\/p><\/div>/g)];
      assert.equal(banners.length, 1, `${file}: banner`);
      assert.equal(decode(banners[0][1].replace(/<[^>]*>/g, "")), unfinishedNotice, `${file}: banner text`);
      assert.ok(banners[0][1].includes(`<a href="${base}about/">About</a>`), `${file}: banner links About`);
      assert.ok(/<main[^>]*><div class="unfinished-banner"/.test(page), `${file}: banner first in main`);
      assert.ok(!/unfinished-banner[^>]*(hidden|dismiss)/.test(page), `${file}: banner not dismissible`);
      assert.equal(page.split('<meta name="robots" content="noindex">').length - 1, 1, `${file}: robots`);
      assert.ok(page.startsWith(`<!doctype html><html lang="en" data-base="${base}"`), `${file}: data-base`);
      // Links and assets.
      for (const m of page.matchAll(/\s(?:href|src|action)="([^"]*)"/g))
        checkUrl(decode(m[1]), file, onDisk, html);
      for (const m of page.matchAll(/content="0;url=([^"]*)"/g))
        checkUrl(decode(m[1]), file, onDisk, html);
    }
    assert.equal(plain(unfinishedNotice), unfinishedNotice);
    assert.equal(
      unfinishedNotice,
      "This wiki is unfinished and under active construction. Articles may be incomplete, and statements and proofs may contain errors. Only assertions marked 'proved' have been checked in Lean; see About.",
    );

    // Stylesheet URLs (KaTeX fonts) resolve too.
    for (const file of onDisk)
      if (file.endsWith(".css")) {
        const css = await fs.readFile(path.join(out, file), "utf8");
        for (const m of css.matchAll(/url\(\s*["']?([^"')\s]+)/g)) {
          if (m[1].startsWith("data:")) continue;
          const target = decodeURIComponent(new URL(m[1], `https://pages.invalid/${file}`).pathname.slice(1));
          assert.ok(onDisk.has(target), `${file}: ${m[1]}`);
        }
      }

    // The search index and the tag redirects use the base path.
    const index = JSON.parse(await fs.readFile(path.join(out, "search-index.json"), "utf8"));
    assert.ok(index.length > 0);
    for (const row of index) {
      assert.ok(row.url.startsWith(base), row.url);
      checkUrl(row.url, "search/index.html", onDisk, html);
    }
    const redirect = [...html.entries()].find(([f, p]) => f.startsWith("tag/") && p.includes('http-equiv="refresh"'));
    assert.match(redirect[1], /content="0;url=\/perclib\/articles\//);
    assert.match(html.get("search/index.html"), /action="\/perclib\/search\/"/);

    // About: generated page with every required key, no assertion tags.
    const about = html.get("about/index.html");
    for (const id of ["project", "progress", "status", "errata", "authorship", "contact", "licence", "build"])
      assert.ok(about.includes(`id="about-${id}"`), `About section ${id}`);
    const aboutText = plain(about);
    for (const key of [
      "work in progress",
      "Only assertions marked “proved” have been checked in Lean",
      "A prose proof without the “proved” mark has not been machine-checked",
      "proved-modulo",
      "unformalised",
      "provisional until Tom Hutchcroft confirms it",
      "drafted with AI assistance and is being reviewed",
      "Tom Hutchcroft is responsible for this wiki",
      "Mathematical gap",
      "Apache License, Version 2.0",
      "© Tom Hutchcroft and the PercLib contributors",
      "Creative Commons Attribution 4.0 International (CC BY 4.0)",
      commit,
      "2026-11-21 12:34 UTC",
      "This build shows no formal status",
    ])
      assert.ok(aboutText.toLowerCase().includes(key.toLowerCase()), `About: ${key}`);
    assert.ok(about.includes('href="https://github.com/tomhutchcroft/perclib/issues/new/choose"'));
    assert.ok(!/id="tag-|data-assertion/.test(about));
    assert.ok(about.includes('<footer class="footer">') && /<footer[^>]*>.*licenses\/by\/4\.0.*Apache-2\.0.*<\/footer>/s.test(about), "footer licence line");

    // Home page lead with the build's counts.
    const home = plain(html.get("index.html"));
    assert.ok(
      home.includes(
        `This wiki is unfinished and under active construction, so articles may be incomplete and statements and proofs may contain errors; it has ${articles.length.toLocaleString("en-US")} articles and`,
      ),
    );
    assert.ok(home.includes("formal status is not shown in this build"));

    // Draft marker on every article except those listed as passed.
    const passed = new Set(JSON.parse(await fs.readFile(new URL("../src/passed-articles.json", import.meta.url), "utf8")));
    assert.ok(passed.has("hierarchical-two-point"));
    for (const p of articles) {
      const page = html.get(`articles/${p.id}/index.html`);
      assert.equal(page.split('class="draft-marker"').length - 1, passed.has(p.id) ? 0 : 1, p.id);
    }
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
});
