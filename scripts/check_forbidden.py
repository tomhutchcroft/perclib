#!/usr/bin/env python3
"""Forbidden-construct scan of the whole library (D-29, D-34).

Usage: python3 scripts/check_forbidden.py [ROOT]      (default ROOT: PercLib)

Fails if any Lean file under ROOT, outside comments and string literals, uses a
construct that leaves a proof unchecked, adds an axiom, or can run code at
elaboration time: `sorry`, `admit`, `native_decide`, `axiom`, `by_elab`, `run_tac`,
`run_cmd`, `run_elab`, any `#eval…` (`#eval!`, `#eval?`, …), `elab`, `macro`, `syntax`,
`initialize`, `unsafe`, `implemented_by`, `extern`, `skipKernelTC` (however quoted),
`addDecl`, `command_elab`, `term_elab`, `tactic_elab`, `run_meta`, `meta`, `simproc`,
`dsimproc`, `cbv_simproc`, `simproc_pattern`, `grind_propagator` and their `builtin_`/`_decl`
variants, the token-declaring commands `notation`, `notation3`, `infix`, `infixl`, `infixr`,
`prefix`, `postfix` and `binder_predicate`, the attributes `delab`, `app_delab`, `app_unexpander`, `tactic`, `init`,
`norm_num`, `positivity` and the `builtin_…` code-registering attributes (in `@[…]` or
`attribute […]`; the tactics `norm_num`, `positivity` and `done` are allowed), or a
`set_option` outside a short allowlist (D-35: no `maxHeartbeats` and no `linter.*`). The tag
attribute itself (`PercLib/Meta/Tag.lean`) is the one file allowed to declare syntax, an
initializer and `meta` code, and only those.

This is a second line behind the axiom audit and the kernel replay; it fails closed.
Standard library only.
"""
from __future__ import annotations

import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_proof_pr import code_without_literals  # noqa: E402

FORBIDDEN = set('sorry admit native_decide axiom axioms by_elab run_tac run_cmd run_elab '
                'elab elab_rules macro macro_rules syntax initialize builtin_initialize '
                'unsafe implemented_by extern skipKernelTC debug addDecl command_elab term_elab '
                'tactic_elab simproc dsimproc simproc_decl dsimproc_decl run_meta meta '
                'cbv_simproc cbv_simproc_decl cbv_simproc_pattern simproc_pattern '
                'grind_propagator builtin_simproc builtin_dsimproc '
                'builtin_grind_propagator notation notation3 infix infixl infixr prefix '
                'postfix binder_predicate'.split())
# The token-declaring commands above (`notation` … `binder_predicate`) are refused because a
# token declared in the scanned code changes Lean's lexing (longest match) in ways the scanner
# cannot follow, e.g. a `(--` token makes `--` code; a real need is an audited `EXEMPT` entry.
# Attributes that register code run by the elaborator, simp or a tactic; flagged only inside
# attribute brackets, since `norm_num` and `positivity` are also ordinary tactics.
FORBIDDEN_ATTRIBUTES = set('delab app_unexpander norm_num positivity tactic app_delab init '
                           'builtin_init builtin_tactic builtin_delab builtin_term_elab '
                           'builtin_command_elab builtin_macro'.split())
# D-35: maxHeartbeats, synthInstance.maxHeartbeats and linter.* are not allowed; a real
# need is an audited exception added here with its reason.
ALLOWED_OPTIONS = re.compile(r'(maxRecDepth|backward\.isDefEq\.respectTransparency|'
                             r'pp\.[\w.]+)$')
EXEMPT = {'PercLib/Meta/Tag.lean': {'syntax', 'initialize', 'meta'}}


def identifiers(code: str) -> list[str]:
    # «guillemet» quoting and dotted names are split into components, so
    # `«debug».skipKernelTC` and `set_option debug.skipKernelTC` are both caught.
    code = code.replace('«', ' ').replace('»', ' ')
    return re.findall(r'#?[A-Za-z_][A-Za-z0-9_!?\']*', code)


def attribute_blocks(code: str) -> list[str]:
    """The contents of every `@[…]` and `attribute […]`, brackets matched by depth."""
    blocks = []
    for m in re.finditer(r"@\[|attribute\s*\[", code):
        depth, i = 1, m.end()
        while i < len(code) and depth:
            depth += {'[': 1, ']': -1}.get(code[i], 0)
            i += 1
        if depth:
            raise ValueError('unterminated attribute brackets')
        blocks.append(code[m.end():i - 1])
    return blocks


def check_file(rel: str, text: str) -> list[str]:
    try:
        code = code_without_literals(text)
        blocks = attribute_blocks(code)
    except ValueError as e:
        return [f'{rel}: cannot parse ({e})']
    problems = []
    found = set()
    for tok in identifiers(code):
        if tok in FORBIDDEN or tok.startswith('#eval'):
            found.add(tok)
    for block in blocks:
        found |= FORBIDDEN_ATTRIBUTES.intersection(identifiers(block))
    found -= EXEMPT.get(rel, set())
    if found:
        problems.append(f'{rel}: forbidden tokens {sorted(found)}')
    for m in re.finditer(r'set_option\s+([^\s]+)', code.replace('«', '').replace('»', '')):
        if not ALLOWED_OPTIONS.match(m.group(1)):
            problems.append(f'{rel}: set_option {m.group(1)} is not on the allowlist')
    return problems


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else 'PercLib')
    files = sorted(root.rglob('*.lean')) + [root.with_suffix('.lean')]
    problems, n = [], 0
    for f in files:
        if not f.exists():
            continue
        n += 1
        problems += check_file(f.as_posix(), f.read_text(encoding='utf-8'))
    for p in problems:
        print('FAIL', p)
    if problems:
        print(f'Forbidden-construct scan failed: {len(problems)} problem(s) in {n} files.')
        return 1
    print(f'Forbidden-construct scan passed: {n} files under {root}.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
