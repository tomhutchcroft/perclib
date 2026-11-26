#!/usr/bin/env python3
"""Export a committed, freshly built wiki as a self-contained offline ZIP."""
import argparse
import hashlib
from html import escape, unescape
from html.parser import HTMLParser
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import tarfile
import tempfile
from urllib.parse import quote, unquote, urlsplit
import zipfile

ATTR = re.compile(r"\b(href|src|action)\s*=\s*([\"'])(.*?)\2", re.S)
REFRESH = re.compile(r'content="0;url=([^"<>]+)"')
DETAILS = re.compile(r"<details\b(?![^>]*\sopen(?:[\s=>]|$))([^>]*)>", re.I)
CSS_URL = re.compile(r"url\(\s*[\"']?([^\"')\s]+)")
FORMAT = 1


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


class HTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.text, self.links, self.ids = [], [], set()

    def handle_data(self, data):
        self.text.append(data)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        self.links.extend(attrs[k] for k in ("href", "src", "action") if attrs.get(k))
        if tag == "meta" and attrs.get("http-equiv", "").lower() == "refresh":
            self.links.append(attrs["content"].split("url=", 1)[1])


def parse_html(text):
    parsed = HTML()
    parsed.feed(text)
    return parsed


def target_for(root, current, url):
    parts = urlsplit(unescape(url))
    if parts.scheme or parts.netloc:
        return None
    pathname = unquote(parts.path)
    target = (root / pathname.lstrip("/") if pathname.startswith("/")
              else current.parent / pathname if pathname else current).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError(f"Link escapes export: {url}")
    if target.is_dir():
        target /= "index.html"
    if not target.is_file():
        raise ValueError(f"Missing export destination: {url}")
    return target


def relative_url(root, current, url):
    raw = unescape(url)
    parts = urlsplit(raw)
    if parts.scheme or parts.netloc or not parts.path.startswith("/"):
        return raw
    target = target_for(root, current, raw)
    rel = quote(os.path.relpath(target, current.parent).replace(os.sep, "/"), safe="/")
    return rel + ("?" + parts.query if parts.query else "") + ("#" + parts.fragment if parts.fragment else "")


def offline_html(root, current, text):
    result = ATTR.sub(lambda m: m[1] + "=" + m[2] + escape(
        relative_url(root, current, m[3]), quote=True) + m[2], text)
    # The offline reader shows every collapsed block expanded.
    result = DETAILS.sub(lambda m: "<details open" + m[1] + ">", result)
    result = REFRESH.sub(lambda m: 'content="0;url=' + escape(
        relative_url(root, current, m[1]), quote=True) + '"', result)
    if current == root / "search/index.html":
        needle = '<script defer src="../assets/site.js"></script>'
        if result.count(needle) != 1:
            raise ValueError("Search script entry changed; offline injection needs review")
        result = result.replace(needle,
            '<script defer src="../assets/offline-search.js"></script>' + needle)
    if parse_html(text).text != parse_html(result).text:
        raise ValueError(f"Export changed HTML text: {current}")
    return result


def validate_files(root, html_files):
    parsed = {p: parse_html(p.read_text()) for p in html_files}
    count = 0
    for current, page in parsed.items():
        for url in page.links:
            parts = urlsplit(unescape(url))
            if parts.scheme or parts.netloc:
                continue
            if parts.path.startswith("/"):
                raise ValueError(f"Root-relative offline link: {url}")
            target = target_for(root, current, url)
            if parts.fragment and target.suffix == ".html":
                if unquote(parts.fragment) not in parsed[target].ids:
                    raise ValueError(f"Missing export anchor: {url}")
            count += 1
    for current in (root / "assets").rglob("*.css"):
        for url in CSS_URL.findall(current.read_text()):
            parts = urlsplit(url)
            if not parts.scheme and not parts.netloc:
                if parts.path.startswith("/"):
                    raise ValueError(f"Root-relative offline font/asset: {url}")
                target_for(root, current, url)
                count += 1
    return count


def export_snapshot(repo, build, output, status):
    repo, build, output = (Path(p).resolve() for p in (repo, build, output))
    if output.exists() or output.is_relative_to(build):
        raise ValueError("Choose a new export directory outside the built site")
    if not status.strip():
        raise ValueError("A revision status is required")
    if git(repo, "status", "--porcelain").strip():
        raise ValueError("Commit source changes before exporting")
    revision = git(repo, "rev-parse", "HEAD").decode().strip()
    history = json.loads((build / "metrics/history.json").read_text())
    if history.get("tip") != revision:
        raise ValueError("Built history tip does not match HEAD; rebuild before exporting")
    latest = history["snapshots"][-1]
    if latest["commit"] != revision:
        raise ValueError("Built snapshot does not describe HEAD")
    original = {}
    for p in sorted(build.rglob("*")):
        if p.is_symlink():
            raise ValueError("Symlinks are not supported in the built site")
        if p.is_file():
            original[p.relative_to(build).as_posix()] = digest(p.read_bytes())
    if not {"index.html", "search/index.html", "assets/site.js", "search-index.json"} <= original.keys():
        raise ValueError("Incomplete static build")
    if "PERCLIB_OFFLINE_SEARCH" not in (build / "assets/site.js").read_text():
        raise ValueError("Build lacks offline search support; rebuild before exporting")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="wiki-export-", dir=output.parent) as temp:
        staging = Path(temp)
        root = staging / ("perclib-wiki-" + revision[:12])
        shutil.copytree(build, root)
        html_files = sorted(root.rglob("*.html"))
        for p in html_files:
            p.write_text(offline_html(root, p, p.read_text()))
        search = json.loads((build / "search-index.json").read_text())
        if not isinstance(search, list):
            raise ValueError("Invalid search index")
        for entry in search:
            entry["url"] = relative_url(root, root / "search/index.html", entry["url"])
        payload = json.dumps(search, ensure_ascii=False).replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
        (root / "assets/offline-search.js").write_text("globalThis.PERCLIB_OFFLINE_SEARCH=" + payload + ";\n")
        source_count = 0
        tree = {}
        for row in git(repo, "ls-tree", "-rz", revision, "wiki").split(b"\0"):
            if not row:
                continue
            meta, name = row.split(b"\t", 1)
            mode, kind, oid = meta.decode().split()
            if kind != "blob" or mode not in {"100644", "100755"}:
                raise ValueError("Only regular tracked wiki files may enter the source archive")
            tree[name.decode()] = oid
        object_format = git(repo, "rev-parse", "--show-object-format").decode().strip()
        source_names = set()
        with tarfile.open(fileobj=io.BytesIO(git(repo, "archive", revision, "wiki"))) as archive:
            for entry in archive:
                if entry.isdir():
                    continue
                name = PurePosixPath(entry.name)
                if not entry.isfile() or name.is_absolute() or ".." in name.parts or name.parts[0] != "wiki":
                    raise ValueError("Only regular tracked wiki files may enter the source archive")
                dest = root / "source" / entry.name
                dest.parent.mkdir(parents=True, exist_ok=True)
                data = archive.extractfile(entry).read()
                actual = hashlib.new(object_format, b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                if tree.get(entry.name) != actual or entry.name in source_names:
                    raise ValueError("Source archive differs from its committed blob")
                source_names.add(entry.name)
                dest.write_bytes(data)
                source_count += 1
        if source_names != tree.keys():
            raise ValueError("Source archive omitted tracked wiki files")
        counts = {k: latest[k] for k in ("articles", "readingMaps", "assertions", "reservedTags",
                                        "withdrawnTags", "errataSources", "errataEntries", "errataProvisional")}
        snapshot = {"format": FORMAT, "revision": revision, "status": status, "counts": counts,
                    "sourceFiles": source_count}
        (root / "SNAPSHOT.json").write_text(json.dumps(snapshot, indent=2) + "\n")
        readme = f"""PercLib wiki — offline snapshot

Revision: {revision}
Status: {status}
Repository: tomhutchcroft/perclib.

Extract the entire ZIP, then open index.html in a web browser.
Articles, source reading maps, errata, analytics, mathematical fonts and search
are included. The exported reader requires no local server or internet.
External links to papers and repositories still require internet access.
On phones, use a browser or HTML viewer that can open the extracted folder;
a file manager's quick preview may not support a multi-file website.

Contents: {counts['articles']} articles; {counts['readingMaps']} reading maps;
{counts['assertions']} active assertion tags; {counts['withdrawnTags']} tombstones;
{counts['errataEntries']} errata entries across {counts['errataSources']} sources.
Errata fix availability, significance and confirmation status are preserved.
This snapshot does not itself establish a Lean proof or author confirmation.

source/wiki/ contains the exact tracked wiki source at this revision.
No Git history, installed dependencies or Lean repository files are included.
The exported reader works immediately; rebuilding the source requires the
repository context and dependencies described in source/wiki/README.md.
HTML text and rendered mathematics are preserved; local URLs are made relative.
Collapsed blocks (proofs, long computations) are shown expanded.
Search uses an embedded data file instead of a file-origin network request.
BUILD-FILE-SHA256.json records the original build files.
EXPORT-SHA256.json records exported files, excluding that hash manifest itself.
"""
        (root / "READ-ME.txt").write_text(readme)
        (root / "BUILD-FILE-SHA256.json").write_text(json.dumps(original, indent=2) + "\n")
        link_count = validate_files(root, html_files)
        exported = {p.relative_to(root).as_posix(): digest(p.read_bytes())
                    for p in sorted(root.rglob("*")) if p.is_file()}
        (root / "EXPORT-SHA256.json").write_text(json.dumps(exported, indent=2) + "\n")
        publish = staging / "publish"
        publish.mkdir()
        zip_path = publish / "perclib-wiki.zip"
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED, compresslevel=6) as z:
            for p in sorted(root.rglob("*")):
                if p.is_file():
                    info = zipfile.ZipInfo(root.name + "/" + p.relative_to(root).as_posix(),
                                           date_time=(1980, 1, 1, 0, 0, 0))
                    info.compress_type = zipfile.ZIP_DEFLATED
                    info.create_system = 3
                    info.external_attr = 0o100644 << 16
                    z.writestr(info, p.read_bytes(), compresslevel=6)
        with zipfile.ZipFile(zip_path) as z:
            if z.testzip() is not None:
                raise ValueError("ZIP integrity check failed")
            for name, expected in exported.items():
                if digest(z.read(root.name + "/" + name)) != expected:
                    raise ValueError(f"ZIP content mismatch: {name}")
        report = {**snapshot, "archive": "perclib-wiki.zip", "bytes": zip_path.stat().st_size,
                  "sha256": digest(zip_path.read_bytes()), "htmlPages": len(html_files),
                  "localLinks": link_count, "archiveFiles": len(exported) + 1}
        (publish / "snapshot.json").write_text(json.dumps(report, indent=2) + "\n")
        (publish / "READ-ME.txt").write_text(readme)
        (publish / "index.html").write_text(f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Download the PercLib wiki</title><style>
body{{font:1rem/1.6 system-ui,sans-serif;max-width:48rem;margin:3rem auto;padding:0 1.25rem;color:#172c3e}}
a{{color:#125582}}code{{overflow-wrap:anywhere}}.download{{display:inline-block;padding:.6rem 1rem;border:1px solid;border-radius:.3rem}}
</style></head><body><p><a href="../">Return to the wiki</a></p><h1>Download the wiki</h1>
<p><a class="download" href="perclib-wiki.zip" download="perclib-wiki-{revision[:12]}.zip">Download ZIP · {report['bytes']/1048576:.1f} MB</a></p>
<p>Extract the whole folder, then open <code>index.html</code>. Navigation, search and mathematical fonts work offline.
Links to papers and repositories need an internet connection.</p>
<p>Includes {counts['articles']} articles, {counts['readingMaps']} source reading maps, errata, analytics and the wiki source.</p>
<p>Revision: <code>{revision}</code><br>{escape(status)}</p>
<p>On a phone, use a browser or HTML viewer that can open the extracted folder. File-manager previews may not support it.</p>
<p><a href="READ-ME.txt">Reading instructions</a> · <a href="snapshot.json">Snapshot details and SHA-256 checksum</a></p>
</body></html>
""")
        # The completed export is installed only after every check succeeds.
        staging.rename(output)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--status", required=True, help="Explicit merged/unmerged revision label")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    result = export_snapshot(repo, args.build or repo / "wiki/dist", args.output, args.status)
    print(json.dumps({"output": str(args.output.resolve()), **result}))


if __name__ == "__main__":
    main()

