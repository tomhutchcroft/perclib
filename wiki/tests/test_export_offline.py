"""Regression tests for the offline export; no Lean toolchain or network."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import zipfile

spec = importlib.util.spec_from_file_location("offline", Path(__file__).parents[1] / "scripts/export_offline.py")
offline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(offline)


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.run_git("init", "-q")
        self.run_git("config", "user.name", "Fixture")
        self.run_git("config", "user.email", "fixture@example.invalid")
        (self.repo / "wiki").mkdir()
        (self.repo / "wiki/article.md").write_text("Unchanged mathematical text: $a<b$.\n")
        (self.repo / "PercLib").mkdir()
        (self.repo / "PercLib/Private.lean").write_text("Excluded from export.\n")
        self.run_git("add", ".")
        self.run_git("commit", "-qm", "Fixture source")
        self.sha = self.run_git("rev-parse", "HEAD").decode().strip()
        self.build = self.root / "build"
        files = {
            "index.html": '<html><body><a href="/articles/a%20b/?q=x&amp;y=1#proof">Math</a><a href="/search/">Search</a><a href="https://example.invalid/paper">Paper</a><p>$a&lt;b$</p></body></html>',
            "articles/a b/index.html": '<html><head><link href="/assets/katex.css" rel="stylesheet"></head><body><p id="proof">Unchanged formula</p><a href="/">Home</a></body></html>',
            "search/index.html": '<html><head><script defer src="/assets/site.js"></script></head><body><form action="/search/"></form><a href="/">Home</a></body></html>',
            "tag/ABCD/index.html": '<html><head><meta http-equiv="refresh" content="0;url=/articles/a%20b/#proof"></head><body><a href="/articles/a%20b/#proof">ABCD</a></body></html>',
            "assets/site.js": "globalThis.PERCLIB_OFFLINE_SEARCH;",
            "assets/katex.css": '@font-face{src:url("fonts/font.woff2")}',
            "assets/fonts/font.woff2": "fixture-font",
            "search-index.json": json.dumps([{"title": "Math", "url": "/articles/a%20b/#proof", "text": "</script> and \u2028", "summary": "Formula"}]),
            "metrics/history.json": json.dumps({"tip": self.sha, "snapshots": [{"commit": self.sha, "articles": 1, "readingMaps": 0, "assertions": 1, "reservedTags": 1, "withdrawnTags": 0, "errataSources": 0, "errataEntries": 0, "errataProvisional": 0}]}),
        }
        for name, data in files.items():
            p = self.build / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(data)

    def run_git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.repo), *args], stderr=subprocess.DEVNULL)

    def export(self, name="export"):
        dest = self.root / name
        report = offline.export_snapshot(self.repo, self.build, dest, "Unmerged fixture")
        return dest, report

    def test_offline_routes_search_fonts_and_exact_sources(self):
        dest, report = self.export()
        with zipfile.ZipFile(dest / "publish/perclib-wiki.zip") as z:
            prefix = "perclib-wiki-" + self.sha[:12] + "/"
            home = z.read(prefix + "index.html").decode()
            self.assertIn('href="articles/a%20b/index.html?q=x&amp;y=1#proof"', home)
            self.assertEqual(offline.parse_html(home).text, offline.parse_html((self.build / "index.html").read_text()).text)
            self.assertIn('url=../../articles/a%20b/index.html#proof', z.read(prefix + "tag/ABCD/index.html").decode())
            self.assertIn('../assets/offline-search.js', z.read(prefix + "search/index.html").decode())
            js = z.read(prefix + "assets/offline-search.js").decode()
            self.assertNotIn("</script>", js)
            self.assertIn("\\u2028", js)
            self.assertIn("../articles/a%20b/index.html#proof", js)
            self.assertEqual(z.read(prefix + "source/wiki/article.md"), self.run_git("show", self.sha + ":wiki/article.md"))
            self.assertFalse(any("PercLib/" in n or "/.git/" in n for n in z.namelist()))
            self.assertEqual(json.loads(z.read(prefix + "SNAPSHOT.json"))["revision"], self.sha)
            hashes = json.loads(z.read(prefix + "EXPORT-SHA256.json"))
            for name, digest in hashes.items():
                self.assertEqual(offline.digest(z.read(prefix + name)), digest)
        self.assertEqual(report["sourceFiles"], 1)

    def test_collapsed_blocks_are_expanded_in_the_offline_reader(self):
        page = self.build / "articles/c/index.html"
        page.parent.mkdir(parents=True)
        page.write_text('<html><body><details class="collapsible"><summary>Proof</summary><p id="s">Step $a&lt;b$</p></details>'
                        '<details open><summary>Open</summary></details><DETAILS><summary>Upper</summary></DETAILS>'
                        '<detailsx>not a block</detailsx><a href="#s">Step</a></body></html>')
        dest, _ = self.export()
        html = (dest / ("perclib-wiki-" + self.sha[:12]) / "articles/c/index.html").read_text()
        self.assertIn('<details open class="collapsible"><summary>Proof</summary>', html)
        self.assertIn('<details open><summary>Open</summary>', html)
        self.assertNotIn("open open", html)
        self.assertIn('<details open><summary>Upper</summary>', html)
        self.assertIn('<detailsx>not a block</detailsx>', html)
        self.assertEqual(offline.parse_html(html).text, offline.parse_html(page.read_text()).text)

    def test_same_input_produces_identical_zip(self):
        a, ra = self.export("one")
        b, rb = self.export("two")
        self.assertEqual(ra, rb)
        self.assertEqual((a / "publish/perclib-wiki.zip").read_bytes(), (b / "publish/perclib-wiki.zip").read_bytes())

    def test_dirty_source_and_stale_build_are_rejected(self):
        p = self.repo / "wiki/article.md"
        original = p.read_text()
        p.write_text("Uncommitted")
        with self.assertRaisesRegex(ValueError, "Commit source"):
            self.export()
        p.write_text(original)
        p = self.build / "metrics/history.json"
        data = json.loads(p.read_text())
        data["tip"] = "0" * 40
        p.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "does not match HEAD"):
            self.export()
        self.assertFalse((self.root / "export").exists())

    def test_missing_destination_anchor_and_escape_are_rejected(self):
        for link, message in [("/missing/", "Missing export destination"), ("/articles/a%20b/#absent", "Missing export anchor"), ("/../outside", "escapes export")]:
            with self.subTest(link=link):
                (self.build / "index.html").write_text(f'<a href="{link}">Bad link</a>')
                with self.assertRaisesRegex(ValueError, message):
                    self.export()
                self.assertFalse((self.root / "export").exists())

    def test_symlinks_and_export_ignored_sources_are_rejected(self):
        link = self.build / "linked"
        link.symlink_to(self.repo / "wiki/article.md")
        with self.assertRaisesRegex(ValueError, "Symlinks"):
            self.export()
        link.unlink()
        (self.repo / ".gitattributes").write_text("wiki/article.md export-ignore\n")
        self.run_git("add", ".gitattributes")
        self.run_git("commit", "-qm", "Exclude a source")
        data = json.loads((self.build / "metrics/history.json").read_text())
        data["tip"] = self.run_git("rev-parse", "HEAD").decode().strip()
        data["snapshots"][-1]["commit"] = data["tip"]
        (self.build / "metrics/history.json").write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "omitted tracked"):
            self.export()

    def test_existing_destination_is_not_overwritten(self):
        dest, _ = self.export()
        before = (dest / "publish/perclib-wiki.zip").read_bytes()
        with self.assertRaisesRegex(ValueError, "new export directory"):
            self.export()
        self.assertEqual(before, (dest / "publish/perclib-wiki.zip").read_bytes())


if __name__ == "__main__":
    unittest.main()

