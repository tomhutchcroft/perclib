#!/usr/bin/env python3
"""Gate checks added by D-35.

Usage: python3 scripts/check_d35.py [RAW]      (RAW default: .lake/manifest-raw.json)

(i)  No tagged Prop-valued definition is the type of a binder of any declaration's type,
     and every theorem whose statement is a tagged Prop-valued definition carries the
     same tag (D-16). Read from the ExtractManifest output RAW.
(iv) A Lean file under PercLib/ that is not listed in scripts/legacy_headers.txt fails if
     its header comment or module docstring carries a package, issue, agent or decision
     label (headers carry provenance and the mathematical reference only).
(v)  Such a file must contain a module docstring (`/-!`).
Files listed in scripts/legacy_headers.txt are exempt from (iv) and (v) until the header
migration of D-35 has run, after which the list is emptied.
Standard library only.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
# Upper-case-only labels must not match ordinary words case-insensitively.
CASE_SENSITIVE = re.compile(
    r'\b(?:[A-Z]{1,3}-\d+[a-z]?\b|STEWARD|COORDINATOR|INTEGRATOR|MANAGER|FIXER|AUDITOR|SCOUT'
    r'|PROVER|ARCHITECT|LEAD\b)')
LOWER = re.compile(r'(?:PR\s*#?\d+|pull request\s*#?\d+|issue\s*#?\d+|#\d{2,}\b|\bCodex\b'
                   r'|\bClaude\b|\bagents?\b|\bwork item|\btrain\s*\d+)', re.IGNORECASE)


def head(e):
    while isinstance(e, list) and e and e[0] == 'app':
        e = e[1]
    return e[1] if isinstance(e, list) and e and e[0] == 'const' else None


def binder_types(e):
    while isinstance(e, list) and e and e[0] == 'forall':
        yield e[2]
        e = e[3]


def body(e):
    while isinstance(e, list) and e and e[0] == 'forall':
        e = e[3]
    return e


def proves_exactly(t, name):
    """t is `∀ x₁ … xₙ, name x₁ … xₙ` (the D-16 proof shape, parameters fully generic)."""
    n = 0
    while isinstance(t, list) and t and t[0] == 'forall':
        n += 1
        t = t[3]
    args = []
    while isinstance(t, list) and t and t[0] == 'app':
        args.append(t[2])
        t = t[1]
    if not (isinstance(t, list) and t and t[0] == 'const' and t[1] == name):
        return False
    args.reverse()
    return args == [['bvar', n - 1 - i] for i in range(n)][:len(args)] and len(args) == n


def check_tags(raw_path: pathlib.Path) -> list[str]:
    decls = json.loads(raw_path.read_text())['declarations']
    targets = {d['name']: d['tag'] for d in decls
               if d['tag'] and d['kind'] == 'definition' and d.get('prop_valued')}
    exc_file = ROOT / 'scripts' / 'd35_exceptions.txt'
    exceptions = set(exc_file.read_text().split()) if exc_file.exists() else set()
    problems = []
    for d in decls:
        if d['name'] in exceptions:
            continue
        for t in binder_types(d['type']):
            h = head(t)
            if h in targets:
                problems.append(f'(i) {d["name"]}: a binder has type the tagged statement '
                                f'{h} ({targets[h]})')
        if d['kind'] == 'theorem':
            h = head(body(d['type']))
            if h in targets and proves_exactly(d['type'], h) and d['tag'] != targets[h]:
                problems.append(f'(i) theorem {d["name"]} proves tagged statement {h} but '
                                f'carries tag {d["tag"]!r}, not {targets[h]!r}')
    return problems


def header_text(text: str) -> str:
    """The header comments and the first module docstring, joined by newlines.

    The header is every block comment (`/- … -/`, `/-! … -/`, nested comments handled as
    Lean does: strings are not special inside a comment, so a `"-/"` there closes it in
    Lean and here alike) before the first token that is not a comment: normally the `module`
    keyword, after a copyright block and a provenance block. Blank space and `--` line
    comments between them are skipped; line comments are part of the result. The
    first `/-!` comment after the header is added as well (if it is not already
    one of the header comments).
    """
    def comment_end(start: int) -> int:
        # Lean starts the body after the third character of every opener (`/-x`, `/--`, `/-!`)
        depth, i = 1, start + 3
        while i < n:
            if text.startswith('-/', i):
                depth -= 1
                i += 2
                if depth == 0:
                    return i
            elif text.startswith('/-', i):
                depth += 1
                i += 2
            else:
                i += 1
        return n

    parts = []
    i, n = 0, len(text)
    while True:
        while i < n and text[i] in '\ufeff \t\r\n':
            i += 1
        if text.startswith('/-', i):
            j = comment_end(i)
            parts.append(text[i:j])
            i = j
        elif text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            parts.append(text[i:j])
            i = j
        else:
            break
    k = text.find('/-!', i)
    if k >= 0:
        doc = text[k:comment_end(k)]
        if doc not in parts:
            parts.append(doc)
    return '\n'.join(parts)


def check_headers() -> list[str]:
    legacy_file = ROOT / 'scripts' / 'legacy_headers.txt'
    legacy = set(legacy_file.read_text().split()) if legacy_file.exists() else set()
    problems = []
    for f in sorted((ROOT / 'PercLib').rglob('*.lean')):
        rel = f.relative_to(ROOT).as_posix()
        if rel in legacy:
            continue
        text = f.read_text(encoding='utf-8')
        h = header_text(text)
        bad = CASE_SENSITIVE.findall(h) + LOWER.findall(h)
        if bad:
            problems.append(f'(iv) {rel}: header carries labels {sorted(set(bad))}')
        if '/-!' not in text:
            problems.append(f'(v) {rel}: no module docstring (/-! ... -/)')
    return problems


def main() -> int:
    raw = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else '.lake/manifest-raw.json')
    problems = check_tags(raw) + check_headers()
    for p in problems:
        print('FAIL', p)
    if problems:
        print(f'D-35 checks failed: {len(problems)} problem(s).')
        return 1
    print('D-35 checks passed (tagged statements, headers of new files).')
    return 0


if __name__ == '__main__':
    sys.exit(main())
