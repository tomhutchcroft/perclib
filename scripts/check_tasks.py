#!/usr/bin/env python3
"""Check the task board under `tasks/` against the rules of `tasks/README.md`.

Usage: python3 scripts/check_tasks.py [--root DIR]

Prints one line per finding and exits 1 if there is an error, 0 otherwise. Checks:

1. every `tasks/{open,claimed,done}/*.md` opens with a front-matter block whose `id` equals
   the file name, with a `title`, a `difficulty` in {easy, medium, hard}, a `kind` in
   {proof-only, interface} and `labels` a list; a file in `open/` also has the sections
   Goal, Target, Owned files, Allowed inputs, Stop condition and Hand-off;
2. no id is in two of the three directories;
3. every repository path in backticks under "Owned files" or "Allowed inputs" of an open
   task exists, or its line says the file is new ("New"/"new"); a token with more than
   MAX_ALTERNATIVES brace alternatives (or more than MAX_BRACE_GROUPS groups, or longer than
   MAX_TOKEN characters) is reported instead of expanded;
4. every wiki tag written `**XXXX**` in an open task is anchored as `tag-XXXX` under
   `wiki/articles/`; a tag already attached in Lean (`@[tag "XXXX"]` under `PercLib/`) is
   reported as a "possibly done" warning (which does not change the exit status) unless a
   sentence of the task names that tag and says it is re-stated or extended (the Owned-files
   wording "tagged restatement(s)" does not count);
5. no open task targets (in its Goal or Target) an article of an area taken in
   `tasks/areas/*.md` (the articles linked from the map's tables), unless one sentence of the
   task says "shared prerequisite" and names that area (by its name in the `tasks/README.md`
   table, by `areas/<map>.md`, or by the map's stem followed by "area"; the bare stem does not
   count when it is also one of the area's articles).

Every regular expression runs in time linear in its input, and brace expansion is bounded,
so odd input cannot make a run slow. Standard library only.
"""

import argparse
import glob
import re
import sys
from pathlib import Path

DIRS = ('open', 'claimed', 'done')
DIFFICULTIES = {'easy', 'medium', 'hard'}
KINDS = {'proof-only', 'interface'}
SECTIONS = ('Goal', 'Target', 'Owned files', 'Allowed inputs', 'Stop condition', 'Hand-off')
PATH_SECTIONS = ('Owned files', 'Allowed inputs')
TARGET_SECTIONS = ('Goal', 'Target')

TAG_RE = re.compile(r'\*\*([0-9A-Z]{4})\*\*')
ANCHOR_RE = re.compile(r'''id\s*=\s*["']tag-([0-9A-Z]{4})["']''')
LEAN_TAG_NAME_RE = re.compile(r'\btag\s+"([0-9A-Z]{4})"')
LEAN_ATTR_LOOKBACK = 2000  # an attribute `@[...]` longer than this is not looked through
HEADING_RE = re.compile(r'^#{2,6}\s+(.*)$')
RESTATE_RE = re.compile(r'\bre-?stat|\bextend', re.IGNORECASE)
# Wording that contains RESTATE_RE without saying that a tag is re-stated or extended.
NOT_RESTATE_RE = re.compile(r'\btagged\s+restatements?\b|\bextended[\s-]+(?:nonnegative|real|'
                            r'valued|natural)', re.IGNORECASE)
BACKTICK_RE = re.compile(r'`([^`\n]+)`')
ARTICLE_LINK_RE = re.compile(r'articles/([A-Za-z0-9_-]+)\.md')
ARTICLE_WORD_RE = re.compile(r'\barticles?\b')
# One more backticked name in a list after "article(s)": `a`, `b`, and `c` / `a` or `b`.
ARTICLE_NEXT_RE = re.compile(r'\s*(?:,\s*(?:(?:and|or)\b\s*)?|(?:and|or)\b\s*)?'
                             r'`([A-Za-z0-9_-]+)`')
SENTENCE_END_RE = re.compile(r'(?<=[.;!?])\s+')
MAX_ALTERNATIVES = 256
MAX_BRACE_GROUPS = 64
MAX_TOKEN = 4096
NEW_RE = re.compile(r'\b[Nn]ew\b')
FILE_SUFFIXES = ('.lean', '.md', '.py', '.sh', '.json', '.toml', '.txt', '.yml', '.yaml')


def parse_front_matter(text):
    """Return (dict, body) for a file opening with a `---` block, or (None, text)."""
    lines = text.splitlines()
    if not lines or lines[0].strip() != '---':
        return None, text
    for end in range(1, len(lines)):
        if lines[end].strip() == '---':
            break
    else:
        return None, text
    fields, key = {}, None
    for line in lines[1:end]:
        m = re.match(r'^([A-Za-z_][\w-]*)\s*:\s*(.*)$', line)
        if m:
            key, value = m.group(1), m.group(2).strip()
            fields[key] = parse_value(value)
        elif key is not None and re.match(r'^\s*-\s*', line):
            item = line.strip()[1:].strip()
            if fields[key] == '':
                fields[key] = []
            if isinstance(fields[key], list):
                fields[key].append(unquote(item))
    return fields, '\n'.join(lines[end + 1:])


def unquote(s):
    s = s.strip()
    if len(s) >= 2 and s[0] == s[-1] and s[0] in '"\'':
        return s[1:-1]
    return s


def parse_value(value):
    if value.startswith('[') and value.endswith(']'):
        inner = value[1:-1].strip()
        return [unquote(x) for x in inner.split(',')] if inner else []
    return unquote(value)


def sections(body):
    """Map heading text (any level >= 2) to the text below it, up to the next heading."""
    out, current, buf = {}, None, []
    for line in body.splitlines():
        m = HEADING_RE.match(line)
        if m:
            if current is not None:
                out.setdefault(current, '\n'.join(buf))
            current, buf = m.group(1).rstrip().rstrip('#').rstrip(), []
        elif current is not None:
            buf.append(line)
    if current is not None:
        out.setdefault(current, '\n'.join(buf))
    return out


def find_section(secs, name):
    for heading, text in secs.items():
        if heading.strip().lower() == name.lower():
            return text
    return None


def logical_lines(text):
    """Join indented continuation lines onto the line (or bullet item) they continue."""
    out = []
    for line in text.splitlines():
        if out and line.startswith((' ', '\t')) and line.strip() \
                and not re.match(r'^\s*([-*+]|\d+\.)\s', line) and out[-1].strip():
            out[-1] += ' ' + line.strip()
        else:
            out.append(line)
    return out


def sentences(text):
    """Split text into sentences: paragraphs (blank lines, headings and list items start a
    new one) joined into one line each, then cut after `.`, `;`, `!` or `?`."""
    paragraphs, buf = [], []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith('#') \
                or re.match(r'^([-*+]|\d+\.)\s', stripped):
            if buf:
                paragraphs.append(' '.join(buf))
            buf = [stripped] if stripped else []
            if stripped.startswith('#'):
                paragraphs.append(stripped)
                buf = []
        else:
            buf.append(stripped)
    if buf:
        paragraphs.append(' '.join(buf))
    return [s for p in paragraphs for s in SENTENCE_END_RE.split(p) if s]


def expand_braces(s):
    """All brace alternatives of `s` (`a{b,c}` -> `ab`, `ac`; innermost groups first), or
    None if there are more than MAX_ALTERNATIVES of them, more than MAX_BRACE_GROUPS groups,
    or `s` is longer than MAX_TOKEN characters. Iterative; the number of strings held never
    exceeds MAX_ALTERNATIVES, since expanding a group never lowers it."""
    if len(s) > MAX_TOKEN or s.count('{') > MAX_BRACE_GROUPS:
        return None
    done, todo = [], [s]
    while todo:
        cur = todo.pop()
        m = re.search(r'\{([^{}]*)\}', cur)
        if not m:
            done.append(cur)
            continue
        alts = m.group(1).split(',')
        if len(done) + len(todo) + len(alts) > MAX_ALTERNATIVES:
            return None
        todo.extend(cur[:m.start()] + alt + cur[m.end():] for alt in reversed(alts))
    return list(dict.fromkeys(done))


def looks_like_path(token, top_level):
    if any(c.isspace() for c in token) or token.startswith(('-', '@', '.', 'http')):
        return False
    if '/' in token:
        first = token.split('/', 1)[0]
        return first in top_level or bool(re.search(r'\.[A-Za-z]+(\}|\*)?$', token)) \
            or token.endswith(('/', '/*'))
    return token.endswith(FILE_SUFFIXES) or bool(re.match(r'^[\w*]+\.\{[\w,]+\}$', token))


def path_exists(root, rel):
    rel = rel.rstrip('/')
    if any(c in rel for c in '*?['):
        return bool(glob.glob(str(root / rel)))
    return (root / rel).exists()


def resolve(root, alternatives, bases):
    """True if every alternative exists from the root or a base dir."""
    for alt in alternatives:
        if path_exists(root, alt):
            continue
        if not any(path_exists(root, str(Path(b) / alt)) for b in bases):
            return False
    return True


def check_paths(root, rel, secs, top_level):
    problems = []
    for name in PATH_SECTIONS:
        text = find_section(secs, name)
        if text is None:
            continue
        bases = []
        for line in logical_lines(text):
            for token in BACKTICK_RE.findall(line):
                if not looks_like_path(token, top_level):
                    continue
                alternatives = expand_braces(token)
                if alternatives is None:
                    shown = token if len(token) <= 80 else token[:77] + '...'
                    problems.append(f'{rel}: rule 3: path `{shown}` under "{name}" has too '
                                    f'many brace alternatives to check (limits: '
                                    f'{MAX_ALTERNATIVES} alternatives, {MAX_BRACE_GROUPS} '
                                    f'groups, {MAX_TOKEN} characters)')
                    continue
                ok = resolve(root, alternatives, bases)
                if '/' in token and token.split('/', 1)[0] in top_level:
                    parent = str(Path(alternatives[0].rstrip('/*')).parent)
                    ancestors = [parent] + [str(p) for p in Path(parent).parents
                                            if str(p) != '.']
                    bases = ancestors + [b for b in bases if b not in ancestors]
                if not ok and not NEW_RE.search(line):
                    problems.append(f'{rel}: rule 3: path `{token}` under "{name}" does not '
                                    f'exist and is not marked new')
    return problems


def wiki_anchors(root):
    """Map each anchored tag to the article (file stem) that holds it."""
    anchors = {}
    base = root / 'wiki' / 'articles'
    for p in sorted(base.rglob('*.md')) if base.is_dir() else []:
        for tag in ANCHOR_RE.findall(p.read_text(encoding='utf-8', errors='replace')):
            anchors.setdefault(tag, p.stem)
    return anchors


def attached_tags(text):
    """Tags `XXXX` written `tag "XXXX"` inside an attribute `@[...]` of a Lean text: the
    nearest `@[` before the occurrence (within LEAN_ATTR_LOOKBACK characters) is not
    closed by a `]` before it. Linear in the length of the text."""
    tags = set()
    for m in LEAN_TAG_NAME_RE.finditer(text):
        start = text.rfind('@[', max(0, m.start() - LEAN_ATTR_LOOKBACK), m.start())
        if start != -1 and text.find(']', start, m.start()) == -1:
            tags.add(m.group(1))
    return tags


def lean_tags(root):
    tags = set()
    base = root / 'PercLib'
    for p in sorted(base.rglob('*.lean')) if base.is_dir() else []:
        tags |= attached_tags(p.read_text(encoding='utf-8', errors='replace'))
    return tags


def area_maps(root):
    """List of (names by which the area may be cited, set of its articles)."""
    out = []
    base = root / 'tasks' / 'areas'
    readme = root / 'tasks' / 'README.md'
    readme_text = readme.read_text(encoding='utf-8') if readme.is_file() else ''
    for p in sorted(base.glob('*.md')) if base.is_dir() else []:
        text = p.read_text(encoding='utf-8')
        articles = set()
        for line in text.splitlines():
            if line.lstrip().startswith('|'):
                articles.update(ARTICLE_LINK_RE.findall(line))
        # The bare stem names the area only when it is not also one of its articles.
        names = {f'areas/{p.name}'.lower(), f'{p.stem} area'.lower(),
                 p.stem.lower(), p.stem.replace('-', ' ').lower()}
        if p.stem in articles:
            names.discard(p.stem.lower())
        for line in readme_text.splitlines():
            if line.lstrip().startswith('|') and f'areas/{p.name}' in line:
                cells = [c.strip() for c in line.strip().strip('|').split('|')]
                if cells and cells[0]:
                    names.add(cells[0].lower())
        out.append((p.stem, names, articles))
    return out


def article_names(text):
    """Every backticked name in a list after "article"/"articles":
    (articles `a`, `b` and `c`) gives a, b, c."""
    names = []
    for m in ARTICLE_WORD_RE.finditer(text):
        pos = m.end()
        while True:
            n = ARTICLE_NEXT_RE.match(text, pos)
            if not n:
                break
            names.append(n.group(1))
            pos = n.end()
    return names


def targeted_articles(secs, anchors):
    text = '\n'.join(find_section(secs, n) or '' for n in TARGET_SECTIONS)
    arts = set(ARTICLE_LINK_RE.findall(text)) | set(article_names(text))
    arts |= {anchors[t] for t in TAG_RE.findall(text) if t in anchors}
    return arts


def names_word(sentence, name):
    """True if `name` occurs in `sentence` not as part of a longer word or hyphenated name."""
    return re.search(r'(?<![\w-])' + re.escape(name) + r'(?![\w-])', sentence) is not None


def restated_tags(text):
    """Tags named in a sentence that says it re-states or extends something."""
    tags = set()
    for s in sentences(text):
        if RESTATE_RE.search(NOT_RESTATE_RE.sub(' ', s)):
            tags.update(re.findall(r'(?<![0-9A-Za-z])([0-9A-Z]{4})(?![0-9A-Za-z])', s))
    return tags


def names_area_as_shared(sents, names):
    """True if one sentence says "shared prerequisite" and names the area."""
    return any('shared prerequisite' in s and any(names_word(s, n) for n in names)
               for s in sents)


def check(root):
    """Return (errors, warnings), each a list of lines."""
    root = Path(root)
    errors, warnings = [], []
    top_level = {p.name for p in root.iterdir()} if root.is_dir() else set()
    seen = {}
    open_tasks = []
    for d in DIRS:
        for p in sorted((root / 'tasks' / d).glob('*.md')):
            rel = p.relative_to(root).as_posix()
            seen.setdefault(p.stem, []).append(d)
            text = p.read_text(encoding='utf-8', errors='replace')
            fm, body = parse_front_matter(text)
            if fm is None:
                errors.append(f'{rel}: rule 1: no front-matter block')
                continue
            if fm.get('id') != p.stem:
                errors.append(f'{rel}: rule 1: id {fm.get("id")!r} differs from file name '
                              f'{p.stem!r}')
            if not fm.get('title'):
                errors.append(f'{rel}: rule 1: missing title')
            if fm.get('difficulty') not in DIFFICULTIES:
                errors.append(f'{rel}: rule 1: difficulty {fm.get("difficulty")!r} not in '
                              f'easy, medium, hard')
            if fm.get('kind') not in KINDS:
                errors.append(f'{rel}: rule 1: kind {fm.get("kind")!r} not in '
                              f'proof-only, interface')
            if not isinstance(fm.get('labels'), list):
                errors.append(f'{rel}: rule 1: labels missing or not a list')
            if d == 'open':
                secs = sections(body)
                for s in SECTIONS:
                    if find_section(secs, s) is None:
                        errors.append(f'{rel}: rule 1: missing section "{s}"')
                open_tasks.append((rel, text, secs))
    for task_id, dirs in sorted(seen.items()):
        if len(dirs) > 1:
            errors.append(f'tasks: rule 2: id {task_id!r} is in {", ".join(dirs)}')
    if not open_tasks:
        return errors, warnings
    anchors = wiki_anchors(root)
    attached = lean_tags(root)
    areas = area_maps(root)
    for rel, text, secs in open_tasks:
        errors.extend(check_paths(root, rel, secs, top_level))
        restated = restated_tags(text)
        for tag in dict.fromkeys(TAG_RE.findall(text)):
            if tag not in anchors:
                errors.append(f'{rel}: rule 4: tag {tag} has no anchor tag-{tag} under '
                              f'wiki/articles/')
            elif tag in attached and tag not in restated:
                warnings.append(f'{rel}: rule 4: tag {tag} is already attached in Lean: '
                                f'possibly done')
        targets = targeted_articles(secs, anchors)
        sents = None
        for stem, names, articles in areas:
            hit = sorted(targets & articles)
            if not hit:
                continue
            if sents is None:
                sents = [s.lower() for s in sentences(text)]
            if not names_area_as_shared(sents, names):
                errors.append(f'{rel}: rule 5: targets article(s) {", ".join(hit)} of the '
                              f'taken area {stem} (tasks/areas/{stem}.md)')
    return errors, warnings


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument('--root', default='.', help='repository root (default: .)')
    args = ap.parse_args(argv)
    errors, warnings = check(args.root)
    for line in errors:
        print(f'error: {line}')
    for line in warnings:
        print(f'warning: {line}')
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())
