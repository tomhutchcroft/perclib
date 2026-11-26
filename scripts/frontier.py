#!/usr/bin/env python3
"""Write the proof frontier: unproved assertions whose prerequisites are all proved.

Inputs
------
MANIFEST    the assertion manifest (schema ``perclib-manifest-v1``) built from the
            compiled snapshot. Each assertion carries ``tag``, ``title``, ``article``,
            ``proof_status`` and, when formalised, ``dependencies.statement`` and
            ``dependencies.proof`` (tags reached from the Lean statement and proof).
--proof-uses
            the authored proof prerequisites of the wiki: either a directory of article
            records (``*.json``, schema ``perclib-article-records-v1``, field
            ``proofUses``) or one file of schema ``perclib-proof-uses-v1``. Each row is
            ``{tag, proof_uses: [tags], reason}``.

Semantics (the same as the wiki's frontier page)
------------------------------------------------
* An assertion is *proved* when its ``proof_status`` is ``proved``; ``proved-modulo``
  (named ``...Input`` debts), ``statement-only`` and ``unformalised`` are unproved.
* The prerequisites of an unproved assertion are the union of its statement and proof
  dependencies from the manifest and its authored ``proof_uses``.
* An unproved assertion with no authored record has *unknown* prerequisites (an empty
  ``proof_uses`` list means "none"); it is counted but not placed on the frontier.
* It is *ready* (on the frontier) when every prerequisite is proved, otherwise
  *blocked*. A prerequisite tag absent from the manifest counts as unproved and is
  listed under "Missing prerequisites"; unproved assertions on a prerequisite cycle are
  listed under "Prerequisite cycles".

Ordering
--------
For a ready assertion T:
* ``unblocks(T)`` = number of blocked assertions whose only unproved prerequisite is T
  (they become ready once T is proved);
* ``dependents(T)`` = number of unproved assertions that depend on T transitively
  through prerequisite edges.
Within an article, entries are sorted by ``unblocks`` descending, then ``dependents``
descending, then tag. Articles are ordered by their first entry under the same key,
then by article name. Output is deterministic and carries no timestamp.
"""
import argparse
import json
from pathlib import Path
import sys

PROOF_USES_SCHEMA = 'perclib-proof-uses-v1'
RECORDS_SCHEMA = 'perclib-article-records-v1'


def load_proof_uses(path):
    """Return {tag: [prerequisite tags]} from a records directory or a proof-uses file."""
    path = Path(path)
    rows = []
    if path.is_dir():
        for f in sorted(path.glob('*.json')):
            data = json.loads(f.read_text())
            if data.get('schema') != RECORDS_SCHEMA:
                continue
            rows.extend(data.get('proofUses', []))
    else:
        data = json.loads(path.read_text())
        if data.get('schema') != PROOF_USES_SCHEMA:
            raise ValueError(f'{path}: expected schema {PROOF_USES_SCHEMA}')
        rows = data['assertions']
    result = {}
    for row in rows:
        tag, uses = row.get('tag'), row.get('proof_uses')
        if not isinstance(tag, str) or not isinstance(uses, list):
            raise ValueError(f'Malformed proof-uses row: {row!r}')
        if tag in result:
            raise ValueError(f'Duplicate proof-uses record: {tag}')
        result[tag] = sorted(set(uses) - {tag})
    return result


def compute(manifest, authored):
    """Classify assertions and rank the frontier. Returns a dict of results."""
    entries = {a['tag']: a for a in manifest['assertions']}
    proved = {t for t, a in entries.items() if a.get('proof_status') == 'proved'}
    prereqs, unknown, missing = {}, [], set()
    for tag in sorted(entries):
        if tag in proved:
            continue
        if tag not in authored:
            unknown.append(tag)
            continue
        deps = entries[tag].get('dependencies') or {}
        ps = set(deps.get('statement') or []) | set(deps.get('proof') or []) | set(authored[tag])
        ps.discard(tag)
        prereqs[tag] = sorted(ps)
        missing |= {p for p in ps if p not in entries}
    blocked_by = {t: [p for p in ps if p not in proved] for t, ps in prereqs.items()}
    ready = [t for t, b in blocked_by.items() if not b]
    blocked = [t for t, b in blocked_by.items() if b]

    # Reverse edges among unproved assertions (and missing tags), for dependents.
    reverse = {}
    for t, bs in blocked_by.items():
        for p in bs:
            reverse.setdefault(p, set()).add(t)

    def dependents(tag):
        seen, stack = set(), [tag]
        while stack:
            for d in reverse.get(stack.pop(), ()):
                if d not in seen:
                    seen.add(d)
                    stack.append(d)
        seen.discard(tag)
        return len(seen)

    unblocks = {t: 0 for t in ready}
    for t, bs in blocked_by.items():
        if len(bs) == 1 and bs[0] in unblocks:
            unblocks[bs[0]] += 1
    rows = [{'tag': t, 'title': entries[t].get('title', ''),
             'article': entries[t].get('article', ''),
             'proof_status': entries[t].get('proof_status', ''),
             'unblocks': unblocks[t], 'dependents': dependents(t)} for t in ready]
    key = lambda r: (-r['unblocks'], -r['dependents'], r['tag'])
    rows.sort(key=key)
    articles = {}
    for r in rows:
        articles.setdefault(r['article'], []).append(r)
    order = sorted(articles, key=lambda a: (key(articles[a][0]), a))
    return {'ranked': rows, 'articles': [(a, articles[a]) for a in order],
            'blocked': sorted(blocked), 'unknown': unknown, 'proved': sorted(proved),
            'missing': sorted(missing), 'cycles': cycles(blocked_by)}


def cycles(blocked_by):
    """Strongly connected components of size > 1, or self-loops, among unproved tags."""
    index, low, stack, on, result, counter = {}, {}, [], set(), [], [0]
    graph = {t: [p for p in bs if p in blocked_by] for t, bs in blocked_by.items()}

    def visit(root):
        work = [(root, iter(graph[root]))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        on.add(root)
        while work:
            node, it = work[-1]
            advanced = False
            for nxt in it:
                if nxt not in index:
                    index[nxt] = low[nxt] = counter[0]
                    counter[0] += 1
                    stack.append(nxt)
                    on.add(nxt)
                    work.append((nxt, iter(graph[nxt])))
                    advanced = True
                    break
                if nxt in on:
                    low[node] = min(low[node], index[nxt])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[node])
            if low[node] == index[node]:
                comp = []
                while True:
                    x = stack.pop()
                    on.discard(x)
                    comp.append(x)
                    if x == node:
                        break
                if len(comp) > 1 or node in graph[node]:
                    result.append(sorted(comp))

    for t in sorted(graph):
        if t not in index:
            visit(t)
    return sorted(result)


def escape(text):
    out = []
    for ch in text:
        if ch in '\\`*_[]<>|':
            out.append('\\' + ch)
        else:
            out.append(ch)
    return ''.join(out)


def render(result, commit):
    lines = [
        '# Proof frontier',
        '',
        '<!-- Generated by scripts/frontier.py. Do not edit by hand. -->',
        '',
        f'Generated by `scripts/frontier.py` from the assertion manifest of perclib commit '
        f'`{commit or "unknown"}`. Do not edit this file by hand.',
        '',
        'It lists the wiki assertions that are not yet proved but whose recorded '
        'prerequisites (the statement and proof dependencies extracted from Lean, plus the '
        'authored `proof_uses` of the wiki records) are all proved. `proved-modulo` '
        '(named literature inputs), `statement-only` and `unformalised` count as unproved. '
        'Readiness concerns prerequisites only: check open pull requests and `tasks/` '
        'before starting.',
        '',
        'Ordering: within each article, by the number of blocked assertions that would '
        'become ready once the entry is proved (*unblocks*), then by the number of unproved '
        'assertions depending on it transitively (*dependents*), then by tag; articles '
        'follow the rank of their first entry.',
        '',
        'To regenerate (from the repository root, after `lake build`):',
        '',
        '```',
        'lake env lean --run scripts/ExtractManifest.lean > .lake/manifest-raw.json',
        'python3 scripts/build_manifest.py .lake/manifest-raw.json --output .lake/manifest.json',
        'python3 scripts/frontier.py .lake/manifest.json --proof-uses wiki/records \\',
        '    --commit "$(git rev-parse HEAD)" --output docs/FRONTIER.md',
        '```',
        '',
        f'Summary: {len(result["ranked"])} ready, {len(result["blocked"])} blocked, '
        f'{len(result["unknown"])} without recorded prerequisites, '
        f'{len(result["proved"])} proved.',
        '',
    ]
    if not result['ranked']:
        lines += ['No assertion is ready in this snapshot.', '']
    for article, rows in result['articles']:
        lines += [f'## {escape(article)} ({len(rows)})', '']
        for r in rows:
            lines.append(f'- `{r["tag"]}` {escape(r["title"])} (article {escape(article)}; '
                         f'{r["proof_status"]}; unblocks {r["unblocks"]}, '
                         f'dependents {r["dependents"]})')
        lines.append('')
    if result['cycles']:
        lines += ['## Prerequisite cycles', '',
                  'These unproved assertions depend on each other and cannot become ready '
                  'until the records are corrected.', '']
        lines += ['- ' + ', '.join(f'`{t}`' for t in c) for c in result['cycles']]
        lines.append('')
    if result['missing']:
        lines += ['## Missing prerequisites', '',
                  'Prerequisite tags absent from the manifest (counted as unproved):', '',
                  ', '.join(f'`{t}`' for t in result['missing']), '']
    return '\n'.join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    parser.add_argument('manifest', type=Path)
    parser.add_argument('--proof-uses', type=Path,
                        help='wiki records directory or perclib-proof-uses-v1 file')
    parser.add_argument('--commit', help='perclib commit to name in the header '
                        '(default: the manifest\'s commit field)')
    parser.add_argument('--output', type=Path, help='output file (default: stdout)')
    args = parser.parse_args(argv)
    manifest = json.loads(args.manifest.read_text())
    if manifest.get('schema') != 'perclib-manifest-v1':
        raise SystemExit(f'{args.manifest}: expected schema perclib-manifest-v1')
    if args.proof_uses is None:
        print('warning: no --proof-uses given; unproved assertions have unknown '
              'prerequisites and the frontier is empty', file=sys.stderr)
    authored = load_proof_uses(args.proof_uses) if args.proof_uses else {}
    text = render(compute(manifest, authored), args.commit or manifest.get('commit'))
    if args.output:
        args.output.write_text(text)
    else:
        sys.stdout.write(text)


if __name__ == '__main__':
    main()
