// Units of the GitHub Pages edition: base path, draft list, home lead, command
// line, and the manifest rules of a Pages build (required; compiled in this run).
import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  normalizeBasePath,
  applyBasePath,
  loadPassedArticles,
  draftMarker,
  homeStatus,
  parseArguments,
  buildInfo,
} from "../src/build.mjs";
import { loadEvidence, validateSameRun } from "../src/manifest.mjs";

test("base paths are normalised and anything unsafe is refused", () => {
  for (const v of [undefined, null, "", "/"]) assert.equal(normalizeBasePath(v), "/");
  assert.equal(normalizeBasePath("/perclib"), "/perclib/");
  assert.equal(normalizeBasePath("perclib/"), "/perclib/");
  assert.equal(normalizeBasePath("/a/b.c"), "/a/b.c/");
  for (const v of ["/../x", "/a//b", "//evil.example", '/a"b', "/a b", "/a?x", "/a#x", "/./", "/a\\b"])
    assert.throws(() => normalizeBasePath(v), /Invalid base path/, v);
});

test("applyBasePath prefixes root-relative URLs only", () => {
  const files = new Map([
    [
      "x/index.html",
      '<!doctype html><html lang="en"><head><meta http-equiv="refresh" content="0;url=/articles/a/#tag-AAAA"><link href="/assets/s.css"></head><body><a href="/">h</a><a href="https://e.org/">e</a><a href="#f">f</a><a href="//cdn.example/x">c</a><a href="rel/">r</a><form action="/search/"></form><img src="/i.png"><button data-details-action="/z">b</button><code>href=&quot;/no/&quot;</code></body></html>',
    ],
    ["search-index.json", JSON.stringify([{ url: "/tag/AAAA/", title: "t" }]) + "\n"],
    ["assets/s.css", "a{background:url(/keep.png)}"],
  ]);
  assert.equal(applyBasePath(files, "/"), files);
  const out = applyBasePath(files, "/perclib/");
  const page = out.get("x/index.html");
  assert.ok(page.startsWith('<!doctype html><html lang="en" data-base="/perclib/">'));
  for (const s of [
    'content="0;url=/perclib/articles/a/#tag-AAAA"',
    'href="/perclib/assets/s.css"',
    'href="/perclib/"',
    'href="https://e.org/"',
    'href="#f"',
    'href="//cdn.example/x"',
    'href="rel/"',
    'action="/perclib/search/"',
    'src="/perclib/i.png"',
    "href=&quot;/no/&quot;",
    'data-details-action="/z"',
  ])
    assert.ok(page.includes(s), s);
  assert.deepEqual(JSON.parse(out.get("search-index.json")), [{ url: "/perclib/tag/AAAA/", title: "t" }]);
  assert.equal(out.get("assets/s.css"), files.get("assets/s.css"));
});

test("passed-articles list: validated, and only listed articles lose the draft marker", async () => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-passed-"));
  try {
    const articles = [{ id: "a" }, { id: "b" }];
    const write = async (value) => {
      const file = path.join(dir, "p.json");
      await fs.writeFile(file, JSON.stringify(value));
      return file;
    };
    const passed = await loadPassedArticles(await write(["a"]), articles);
    assert.deepEqual([...passed], ["a"]);
    assert.equal(draftMarker("a", passed), "");
    assert.match(draftMarker("b", passed), /class="draft-marker"[^]*Draft/);
    await assert.rejects(loadPassedArticles(await write(["c"]), articles), /unknown article c/);
    await assert.rejects(loadPassedArticles(await write(["a", "a"]), articles), /twice/);
    await assert.rejects(loadPassedArticles(await write({ a: 1 }), articles), /array/);
    await assert.rejects(loadPassedArticles(await write([1]), articles), /array/);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
  // The shipped list starts with the model article.
  const shipped = JSON.parse(await fs.readFile(new URL("../src/passed-articles.json", import.meta.url), "utf8"));
  assert.deepEqual(shipped, ["hierarchical-two-point"]);
});

test("home lead states the counts, with or without formal status", () => {
  assert.equal(
    homeStatus({ articles: 144, assertions: 1403, proved: 283 }),
    "<p class=\"home-status\">This wiki is unfinished and under active construction, so articles may be incomplete and statements and proofs may contain errors; of its 144 articles and 1,403 assertions, only the 283 marked 'proved' have been checked in Lean (see <a href=\"/about/\">About</a>).</p>",
  );
  assert.match(homeStatus({ articles: 2, assertions: 3, proved: null }), /it has 2 articles and 3 assertions, and formal status is not shown in this build/);
});

test("command line and build information", () => {
  assert.deepEqual(parseArguments([]), { output: undefined, options: {} });
  assert.deepEqual(parseArguments(["--base-path", "/perclib/", "out"]), {
    output: path.resolve("out"),
    options: { basePath: "/perclib/" },
  });
  assert.deepEqual(parseArguments(["--base-path=/x"]).options, { basePath: "/x" });
  assert.throws(() => parseArguments(["--base-path"]), /needs a value/);
  assert.throws(() => parseArguments(["--other"]), /Unexpected/);
  assert.throws(() => parseArguments(["a", "b"]), /Unexpected/);
  const sha = "a".repeat(40);
  assert.deepEqual(buildInfo({ buildCommit: sha, buildDate: new Date("2026-01-02T03:04:05Z") }), {
    commit: sha,
    date: "2026-01-02 03:04 UTC",
  });
  assert.throws(() => buildInfo({ buildCommit: "main" }), /Invalid build commit/);
});

test("a Pages build requires a manifest compiled in this run from the commit being built", async () => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-pages-manifest-"));
  try {
    const reviewsPath = path.join(dir, "reviews.json");
    await fs.writeFile(reviewsPath, JSON.stringify({ schema: "perclib-reviews-v1", reviews: [] }));
    const assertions = [{ tag: "AAAA" }];
    const commit = "b".repeat(40);
    const run = "https://github.com/tomhutchcroft/perclib/actions/runs/42";
    const manifest = {
      schema: "perclib-manifest-v1",
      commit,
      ci_run: run,
      assertions: [{ tag: "AAAA", declarations: [], proof_status: "unformalised" }],
    };
    const manifestPath = path.join(dir, "manifest.json");
    await fs.writeFile(manifestPath, JSON.stringify(manifest));
    const opts = { reviewsPath, manifestPath: undefined, receiptPath: undefined, sameRunUrl: undefined, buildCommit: undefined };

    // Without a manifest: allowed locally, refused when required.
    assert.equal((await loadEvidence(assertions, { ...opts, requireManifest: false })).entries, null);
    await assert.rejects(loadEvidence(assertions, { ...opts, requireManifest: true }), /compiled manifest is required/);
    // A manifest needs a receipt or this run; never both; never a run without manifest.
    await assert.rejects(loadEvidence(assertions, { ...opts, manifestPath }), /successful artifact receipt/);
    await assert.rejects(loadEvidence(assertions, { ...opts, sameRunUrl: run }), /without manifest/);
    await assert.rejects(
      loadEvidence(assertions, { ...opts, manifestPath, receiptPath: manifestPath, sameRunUrl: run }),
      /not both/,
    );
    const ok = await loadEvidence(assertions, { ...opts, manifestPath, sameRunUrl: run, buildCommit: commit, requireManifest: true });
    assert.equal(ok.entries.get("AAAA").proof_status, "unformalised");
    assert.deepEqual(ok.provenance, {
      repository: "tomhutchcroft/perclib",
      runUrl: run,
      commit,
      artifactId: null,
      runLabel: "Workflow run that built this site",
    });
    // The manifest must name this run and this commit.
    assert.throws(() => validateSameRun(manifest, run.replace("42", "43"), commit), /not compiled in this workflow run/);
    assert.throws(() => validateSameRun(manifest, run, "c".repeat(40)), /commit differs/);
    assert.throws(() => validateSameRun(manifest, run, undefined), /commit differs/);
    assert.throws(() => validateSameRun({ ...manifest, ci_run: "https://evil.example/actions/runs/42" }, "https://evil.example/actions/runs/42", commit), /workflow run URL/);
    assert.throws(() => validateSameRun({ ...manifest, ci_run: null }, undefined, commit), /workflow run URL/);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
});
