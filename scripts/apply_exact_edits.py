#!/usr/bin/env python3
"""Apply exact text replacements to files, all or none.

Usage: python3 scripts/apply_exact_edits.py EDITS.json [--repo DIR]

EDITS.json is a list of objects {"file": path, "old": text, "new": text}; a
relative path is taken relative to DIR (default: the current directory). The
edits are applied in order. Every `old` must occur exactly once in its file as
it stands after the earlier edits of the list; this is checked for every edit
before any file is written, so on failure (exit 1) nothing is changed. One line
is printed per edit. Standard library only.
"""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import sys
import tempfile


class EditError(Exception):
    pass


def load_edits(path: pathlib.Path) -> list[dict]:
    try:
        edits = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise EditError(f"cannot read {path}: {exc}") from exc
    if not isinstance(edits, list):
        raise EditError(f"{path}: expected a JSON list of edits")
    for i, edit in enumerate(edits, 1):
        if not isinstance(edit, dict) or not all(
            isinstance(edit.get(k), str) for k in ("file", "old", "new")
        ):
            raise EditError(f"edit {i}: needs string fields file, old, new")
        if edit["old"] == "":
            raise EditError(f"edit {i}: empty old text")
    return edits


def plan(edits: list[dict], repo: pathlib.Path) -> tuple[dict[pathlib.Path, str], list[str]]:
    """Apply the edits in memory; return the new contents and one message per edit."""
    contents: dict[pathlib.Path, str] = {}
    messages = []
    for i, edit in enumerate(edits, 1):
        path = (repo / edit["file"]).resolve()
        if path not in contents:
            try:
                contents[path] = path.read_text(encoding="utf-8")
            except OSError as exc:
                raise EditError(f"edit {i}: cannot read {edit['file']}: {exc}") from exc
        text = contents[path]
        count = text.count(edit["old"])
        if count != 1:
            raise EditError(
                f"edit {i}: {edit['file']}: old text occurs {count} times (expected exactly 1)"
            )
        line = text[: text.index(edit["old"])].count("\n") + 1
        contents[path] = text.replace(edit["old"], edit["new"], 1)
        messages.append(f"edit {i}: {edit['file']}: replaced at line {line}")
    return contents, messages


def write_all(contents: dict[pathlib.Path, str]) -> None:
    for path, text in contents.items():
        fd, tmp = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
        try:
            with os.fdopen(fd, "w", encoding="utf-8", newline="") as handle:
                handle.write(text)
            os.chmod(tmp, path.stat().st_mode)
            os.replace(tmp, path)
        except BaseException:
            if os.path.exists(tmp):
                os.unlink(tmp)
            raise


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("edits", type=pathlib.Path)
    parser.add_argument("--repo", type=pathlib.Path, default=pathlib.Path("."))
    args = parser.parse_args(argv)
    try:
        contents, messages = plan(load_edits(args.edits), args.repo)
    except EditError as exc:
        print(f"error: {exc}; nothing written", file=sys.stderr)
        return 1
    write_all(contents)
    for message in messages:
        print(message)
    return 0


if __name__ == "__main__":
    sys.exit(main())
