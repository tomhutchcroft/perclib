#!/usr/bin/env python3
"""Unit tests of scripts/automerge_classify.py, on fixtures in the shape of the GitHub API."""
import copy
import difflib
import warnings
import io
import json
import re
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import automerge_classify as am  # noqa: E402

BASE_FILE = '''module

public import PercLib.Basic

/-! # Example

## Main results
* `foo_le`: a bound. The word def in a docstring is harmless.
-/

namespace PercLib

variable {n : ℕ}

/-- A helper; its proof may change. -/
theorem helper (h : n ≤ 3) : n ≤ 4 := by
  omega

@[tag "AB12"]
theorem foo_le (h : n ≤ 3) :
    n ≤ 5 := by
  have := helper h
  omega

noncomputable def bar : ℕ := 3

end PercLib
'''

PROOF_EDIT = BASE_FILE.replace('''  have := helper h
  omega''', '''  -- a new comment, mentioning a def and @[tag "ZZZZ"] is fine in a comment? no: see test
  exact Nat.le_trans (helper h) (by norm_num)''')

PROOF_EDIT_CLEAN = BASE_FILE.replace('''  have := helper h
  omega''', '''  -- shorter proof
  exact Nat.le_trans (helper h) (by norm_num)''')

NEW_LEMMA = BASE_FILE.replace('noncomputable def bar', '''/-- Another lemma; the instance of the
class of bounds is mentioned only in this docstring. -/
theorem foo_lt (h : n ≤ 3) : n < 6 := by
  have := foo_le h
  omega

noncomputable def bar''')

LINE_A = 'theorem a : True := trivial'
WITH_A = BASE_FILE.replace('end PercLib', LINE_A + '\n\nend PercLib')


def patch(old, new):
    lines = difflib.unified_diff(old.split('\n')[:-1] if old else [],
                                 new.split('\n')[:-1], lineterm='', n=3)
    return '\n'.join(l for l in lines if not l.startswith(('---', '+++')))


def entry(path, old, new, status=None, **extra):
    status = status or ('added' if old is None else 'modified')
    d = dict(filename=path, status=status, additions=1, deletions=1, changes=2,
             patch=patch(old or '', new))
    d.update(extra)
    return d


class Fixture:
    """A pull request: file listing plus the base and head trees on disk."""

    def __init__(self):
        self.root = Path(tempfile.mkdtemp(prefix='automerge-test-'))
        FIXTURES.append(self.root)
        self.entries = []

    def lean(self, path, old, new, **extra):
        for side, text in (('base', old), ('head', new)):
            if text is not None:
                f = self.root / side / path
                f.parent.mkdir(parents=True, exist_ok=True)
                f.write_text(text)
        self.entries.append(entry(path, old, new, **extra))
        return self

    def classify(self, title=None):
        am.classify(copy.deepcopy(self.entries), self.root / 'base', self.root / 'head',
                    title)


PATH = 'PercLib/Probability/Example.lean'
FIXTURES = []


def tearDownModule():
    for root in FIXTURES:
        shutil.rmtree(root, ignore_errors=True)


class SourceTests(unittest.TestCase):
    def test_compiles_without_warnings(self):
        # Note N1 of the third audit: the module docstring held invalid escapes (`\\s`),
        # a SyntaxWarning on Python 3.13 and an error in later versions.
        source = Path(am.__file__).read_text(encoding='utf-8')
        with warnings.catch_warnings():
            warnings.simplefilter('error')
            compile(source, am.__file__, 'exec')
        self.assertIn('`\\bwhere\\b`', am.__doc__)


class PathTests(unittest.TestCase):
    def rejected(self, entries, title=None):
        with self.assertRaises(am.Reject):
            am.check_paths(entries, title)

    def test_each_excluded_path_rejected(self):
        for path in ['PercLib/Basic.lean', 'PercLib/Models/Basic.lean',
                     'PercLib/Probability/Defs.lean', 'PercLib.lean', 'scripts/gate.sh',
                     'scripts/Foo.lean', '.github/workflows/ci.yml',
                     '.github/automerge-authors', '.github/CODEOWNERS', 'lean-toolchain',
                     'lake-manifest.json', 'lakefile.toml', 'docs/DECISIONS.md',
                     'docs/STATUS.md', 'README.md', 'wiki/articles/x.md',
                     'tasks/open/foo.md', 'tasks/done/foo.md', 'PercLib/Foo.md',
                     'PercLib/../scripts/x.lean', 'PercLib/a b.lean', 'Other/Foo.lean']:
            with self.subTest(path=path):
                self.rejected([dict(filename=path, status='modified', patch='@@ -1 +1 @@\n-a\n+b',
                                    changes=2, additions=1, deletions=1)])

    def test_removed_and_renamed_lean_rejected(self):
        self.rejected([dict(filename=PATH, status='removed', patch='', changes=1)])
        self.rejected([dict(filename=PATH, status='renamed',
                            previous_filename='PercLib/Old.lean', changes=0)])

    def test_rename_into_percLib_from_outside_rejected(self):
        for prev in ['scripts/Helper.lean', 'Scratch/Foo.lean', 'PercLib/Defs.lean',
                     'tasks/open/foo.md']:
            with self.subTest(prev=prev):
                self.rejected([dict(filename=PATH, status='renamed', previous_filename=prev,
                                    changes=0, additions=0, deletions=0, patch='')])

    def test_missing_patch_rejected(self):
        self.rejected([dict(filename=PATH, status='modified', changes=5000)])

    def test_own_task_move_accepted(self):
        move = dict(filename='tasks/done/nm-foo.md', previous_filename='tasks/open/nm-foo.md',
                    status='renamed', changes=0, additions=0, deletions=0)
        self.assertEqual(am.check_paths([move], 'nm-foo: prove the bound'), [])
        claimed = dict(move, previous_filename='tasks/claimed/nm-foo.md')
        self.assertEqual(am.check_paths([claimed], 'nm-foo'), [])

    def test_task_moves_rejected(self):
        move = dict(filename='tasks/done/nm-foo.md', previous_filename='tasks/open/nm-foo.md',
                    status='renamed', changes=0, additions=0, deletions=0)
        self.rejected([move], 'nm-bar: something else')       # not its own task
        self.rejected([move], 'nm-foo2: prefix of another id')
        self.rejected([move], None)
        self.rejected([dict(move, changes=2, additions=1, deletions=1)], 'nm-foo')  # edited
        self.rejected([dict(move, filename='tasks/done/nm-bar.md')], 'nm-foo')
        self.rejected([dict(move, filename='tasks/open/nm-foo.md',
                            previous_filename='tasks/done/nm-foo.md')], 'nm-foo')
        self.rejected([dict(filename='tasks/open/new.md', status='added', changes=3)], 'new')
        other = dict(move, filename='tasks/done/nm-baz.md',
                     previous_filename='tasks/open/nm-baz.md')
        self.rejected([move, other], 'nm-foo')


class ClassifyTests(unittest.TestCase):
    def accept(self, fixture, title=None):
        fixture.classify(title)

    def reject(self, fixture, title=None, contains=None):
        with self.assertRaises(am.Reject) as cm:
            fixture.classify(title)
        if contains:
            self.assertIn(contains, str(cm.exception))

    def test_proof_only_accepted(self):
        self.accept(Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN))

    def test_new_lemma_with_docstring_words_accepted(self):
        self.accept(Fixture().lean(PATH, BASE_FILE, NEW_LEMMA))

    def test_proof_only_with_own_task_move_accepted(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        f.entries.append(dict(filename='tasks/done/ex.md', previous_filename='tasks/open/ex.md',
                              status='renamed', changes=0, additions=0, deletions=0))
        self.accept(f, 'ex: shorten a proof')
        self.reject(f, 'other: title of another task')

    def test_new_or_removed_file_rejected(self):
        new = 'module\n\npublic import PercLib.Basic\n\ntheorem t : True := trivial\n'
        self.reject(Fixture().lean('PercLib/New/Proofs.lean', None, new), contains='added')
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        f.entries[0]['status'] = 'removed'
        self.reject(f, contains='removed')

    def test_tag_line_in_patch_rejected_even_in_comment(self):
        self.reject(Fixture().lean(PATH, BASE_FILE, PROOF_EDIT), contains='tag')

    def test_tag_line_added_rejected(self):
        new = NEW_LEMMA.replace('theorem foo_lt', '@[tag "CD34"]\ntheorem foo_lt')
        self.reject(Fixture().lean(PATH, BASE_FILE, new), contains='tag')

    def test_tag_removed_or_changed_rejected(self):
        for new in [BASE_FILE.replace('@[tag "AB12"]\n', ''),
                    BASE_FILE.replace('@[tag "AB12"]', '@[tag "AB13"]'),
                    BASE_FILE.replace('@[tag "AB12"]', '@[simp, tag "AB12"]')]:
            with self.subTest(new=new[:0]):
                self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_tagged_statement_change_rejected(self):
        # The changed line holds no tag and no keyword; only the statement comparison
        # (and the command check) can see it.
        new = BASE_FILE.replace('    n ≤ 5 := by', '    n ≤ 6 := by')
        self.reject(Fixture().lean(PATH, BASE_FILE, new), contains='AB12')

    def test_tagged_statement_far_from_tag_rejected(self):
        base = BASE_FILE.replace('theorem foo_le (h : n ≤ 3) :\n    n ≤ 5 := by',
                                 'theorem foo_le (h : n ≤ 3)\n' +
                                 ''.join(f'    (h{i} : {i} = {i})\n' for i in range(12)) +
                                 '    : n ≤ 5 := by')
        head = base.replace('(h7 : 7 = 7)', '(h7 : 7 ≤ 7)')
        self.reject(Fixture().lean(PATH, base, head), contains='AB12')

    def test_untagged_statement_change_accepted(self):
        new = BASE_FILE.replace('theorem helper (h : n ≤ 3) : n ≤ 4',
                                'theorem helper (h : n ≤ 3) : n ≤ 3 + 1')
        self.accept(Fixture().lean(PATH, BASE_FILE, new))

    def test_hidden_def_rejected(self):
        variants = {
            'new def': NEW_LEMMA.replace('theorem foo_lt', 'def sneaky : ℕ := 1\n\ntheorem foo_lt'),
            'private def': BASE_FILE.replace('end PercLib', 'private def s : ℕ := 2\n\nend PercLib'),
            'def inside a proof': PROOF_EDIT_CLEAN.replace(
                '  -- shorter proof', '  let _ : ℕ := 0\n  def x := 1'),
            'def body edited': BASE_FILE.replace('noncomputable def bar : ℕ := 3',
                                                 'noncomputable def bar : ℕ :=\n  3'),
            'def continuation edited': BASE_FILE.replace(
                'noncomputable def bar : ℕ := 3', 'noncomputable def bar : ℕ :=\n  3').replace(
                '  3\n\nend', '  4\n\nend'),
            'instance': BASE_FILE.replace('end PercLib', 'instance : Inhabited Foo := ⟨0⟩\nend PercLib'),
            'structure': BASE_FILE.replace('end PercLib', 'structure S where\n  x : ℕ\nend PercLib'),
            'abbrev': BASE_FILE.replace('end PercLib', 'abbrev T := ℕ\nend PercLib'),
            'class': BASE_FILE.replace('end PercLib', 'class C (α : Type) : Prop\nend PercLib'),
            'notation': BASE_FILE.replace('end PercLib', 'notation "‖" x "‖" => x\nend PercLib'),
            'local notation': BASE_FILE.replace('end PercLib', 'local notation "q" => 3\nend PercLib'),
            'axiom': BASE_FILE.replace('end PercLib', 'axiom ax : False\nend PercLib'),
            'opaque': BASE_FILE.replace('end PercLib', 'opaque o : ℕ\nend PercLib'),
            'attribute': BASE_FILE.replace('end PercLib', 'attribute [simp] foo_le\nend PercLib'),
            'instance attr on theorem': BASE_FILE.replace('/-- A helper', '@[instance]\n/-- A helper'),
            'variable': BASE_FILE.replace('variable {n : ℕ}', 'variable {n : ℕ} [Fact (n = 1)]'),
            'open': BASE_FILE.replace('namespace PercLib', 'namespace PercLib\n\nopen Real'),
            'import': BASE_FILE.replace('public import PercLib.Basic',
                                        'public import PercLib.Basic\npublic import Mathlib'),
            'run_cmd': BASE_FILE.replace('end PercLib', 'run_cmd pure ()\nend PercLib'),
            '#eval': BASE_FILE.replace('end PercLib', '#eval 1\nend PercLib'),
            'set_option in proof': PROOF_EDIT_CLEAN.replace(
                '  exact', '  set_option maxRecDepth 9000 in\n  exact'),
            'native_decide': PROOF_EDIT_CLEAN.replace('(by norm_num)', '(by native_decide)'),
            'elab': BASE_FILE.replace('end PercLib', 'elab "x" : tactic => pure ()\nend PercLib'),
            'def after block comment': BASE_FILE.replace(
                'end PercLib', '/- a comment -/ def z := 1\nend PercLib'),
            'def in docstring-adjacent line': NEW_LEMMA.replace(
                'class of bounds is mentioned only in this docstring. -/',
                'class of bounds is mentioned only in this docstring. -/ def w := 1\n'),
        }
        for name, new in variants.items():
            with self.subTest(variant=name):
                self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_edit_inside_definition_body_rejected(self):
        # No keyword on the changed line: the command check must see the enclosing def.
        base = BASE_FILE.replace('noncomputable def bar : ℕ := 3',
                                 'noncomputable def bar : ℕ :=\n  3 + 0')
        self.reject(Fixture().lean(PATH, base, base.replace('  3 + 0', '  4 + 0')),
                    contains="inside a 'noncomputable' command")
        base = BASE_FILE.replace('end PercLib', 'structure S where\n  x : ℕ\n\nend PercLib')
        self.reject(Fixture().lean(PATH, base, base.replace('  x : ℕ', '  x : ℤ')),
                    contains="inside a 'structure' command")
        base = BASE_FILE.replace('end PercLib',
                                 '@[simp]\ninstance : Inhabited S :=\n  ⟨1⟩\n\nend PercLib')
        self.reject(Fixture().lean(PATH, base, base.replace('  ⟨1⟩', '  ⟨2⟩')),
                    contains="inside a 'instance' command")

    def test_column_zero_continuation_rejected(self):
        new = BASE_FILE.replace('noncomputable def bar : ℕ := 3',
                                'noncomputable def bar : ℕ :=\n3')
        self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_patch_must_match_contents(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        # The head file on disk differs from what the patch says.
        (f.root / 'head' / PATH).write_text(PROOF_EDIT_CLEAN.replace('norm_num', 'omega'))
        self.reject(f, contains='does not reproduce')
        g = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        (g.root / 'base' / PATH).write_text(BASE_FILE.replace('helper h', 'helper  h'))
        self.reject(g, contains='does not apply')

    def test_missing_contents_rejected(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        with self.assertRaises(am.Reject):
            am.classify(f.entries, None, None)
        (f.root / 'head' / PATH).unlink()
        self.reject(f, contains='missing')

    def test_unterminated_comment_rejected(self):
        new = PROOF_EDIT_CLEAN.replace('  -- shorter proof', '  /- open comment')
        self.reject(Fixture().lean(PATH, BASE_FILE, new))

    def test_comment_and_string_handling(self):
        lines = am.split_lines(am.strip_comments(
            'a /- x /- nested -/ def -/ b\n"-- not a comment" -- def\nc \'"\' d\n'))
        self.assertEqual(lines, ['a   b', '"-- not a comment" ', 'c \'"\' d'])


    # Cases a-f of finding F1 of the audit of the automerge classifier: each edits only
    # untagged theorems and was accepted before the fix; Lean 4.35 parses each as a new
    # command (a, b, c and the interpolation cases were checked with `lean`).

    def test_guillemet_comment_desync_rejected(self):
        # Cases a and b (A1): `--` inside `«x--»` is not a comment.
        for name, new in {
            'a: def after «x--»': WITH_A.replace(
                LINE_A, 'theorem a : True := let «x--» := 0; trivial def evil : Nat := 1'),
            'b: instance after «y--»': WITH_A.replace(
                LINE_A, 'theorem a : True := let «y--» := 0; trivial '
                        'instance : Inhabited Nat := ⟨5⟩'),
        }.items():
            with self.subTest(case=name):
                self.reject(Fixture().lean(PATH, WITH_A, new), contains='changed line uses')

    def test_guillemet_identifier_rejected(self):
        # A1: no `«` on a changed line, even with nothing else wrong.
        new = WITH_A.replace(LINE_A, 'theorem a : True := let «y» := 0; trivial')
        self.reject(Fixture().lean(PATH, WITH_A, new), contains='«')

    def test_guillemet_scanning(self):
        # A1: `«…»` is copied verbatim and may not be left open.
        self.assertEqual(am.strip_comments('let «x--» := 0; def -- c\n'),
                         'let «x--» := 0; def \n')
        self.assertEqual(am.strip_comments('«a/-b» def'), '«a/-b» def')
        with self.assertRaises(am.Reject):
            am.strip_comments('theorem t : True := «x-- trivial\n')
        new = WITH_A.replace(LINE_A, 'theorem a : True := let «x-- := 0; trivial')
        self.reject(Fixture().lean(PATH, WITH_A, new), contains='unterminated «')

    def test_interpolated_string_desync_rejected(self):
        # A string inside `{…}` of an interpolated string can hide a comment opener from
        # the scanner: `s!"{"--"}"` and `s!"{"/-"}"` (verified with Lean 4.35).
        for name, new in {
            'line comment': WITH_A.replace(
                LINE_A, 'theorem a : True := let _ := s!"{"--"}"; trivial '
                        'def evil : Nat := 1'),
            'block comment': WITH_A.replace(
                LINE_A, 'theorem a : True := let _ := s!"{"/-"}"; trivial\n'
                        'def evil : Nat := 1\n-- -/'),
        }.items():
            with self.subTest(case=name):
                self.reject(Fixture().lean(PATH, WITH_A, new), contains='{')

    def test_hash_command_mid_line_rejected(self):
        # Case c (A2): `#eval!` in the middle of a line. (The token `eval` is forbidden
        # too, by A3, so the `#` rule is checked on its own below.)
        new = WITH_A.replace(
            LINE_A, 'theorem a : True := trivial #eval! IO.FS.writeFile "pwned.txt" "hi"')
        self.reject(Fixture().lean(PATH, WITH_A, new))
        self.assertTrue(any(line.startswith('theorem a') and '#' in line for line in
                            am.split_lines(am.strip_comments(new, blank_literals=True))))
        for line in ['theorem a : True := trivial #exit',
                     'theorem a : True := (trivial) #guard true',
                     'theorem a : True := trivial #check_failure (1 : Nat)']:
            with self.subTest(line=line):
                self.reject(Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)),
                            contains='`#`')

    def test_hash_in_literal_accepted(self):
        # A2: `#` inside string and character literals is not code.
        new = WITH_A.replace(LINE_A, "theorem a : \"#a\".length = 2 ∧ '#' = '#' := "
                                     "⟨rfl, rfl⟩")
        self.accept(Fixture().lean(PATH, WITH_A, new))

    def test_indented_command_keywords_rejected(self):
        # Cases d, e, f (A3): a command keyword on an indented line after a proof, or in
        # the middle of a line, starts a new command.
        after_helper = '  omega\n\n@[tag "AB12"]'
        for name, insert, word in [
            ('d: open ... in before a tagged theorem',
             '  omega\n  open Classical in\n\n@[tag "AB12"]', 'open'),
            ('e: irreducible_def', '  omega\n  irreducible_def evil : Nat := 1\n\n'
                                  '@[tag "AB12"]', 'irreducible_def'),
            ('f: simproc', '  omega\n  simproc evil (Nat.succ _) := fun _ => pure .continue'
                           '\n\n@[tag "AB12"]', 'simproc'),
            ('alias mid-line', '  omega alias evil := helper\n\n@[tag "AB12"]', 'alias'),
            ('add_decl_doc', '  omega\n  add_decl_doc helper\n\n@[tag "AB12"]',
             'add_decl_doc'),
        ]:
            with self.subTest(case=name):
                new = BASE_FILE.replace(after_helper, insert)
                self.assertNotEqual(new, BASE_FILE)
                self.reject(Fixture().lean(PATH, BASE_FILE, new), contains=word)

    def test_command_keyword_lists(self):
        # A3: the minimum list of the audit, and the generated list, are forbidden; the
        # proof commands and their modifiers are not.
        minimum = set('''open eval simproc dsimproc simproc_decl dsimproc_decl
            irreducible_def add_decl_doc seal unseal register_simp_attr register_label_attr
            suppress_compilation compile_inductive initialize_simps_projections
            recall'''.split())
        self.assertLessEqual(minimum, am.FORBIDDEN_TOKENS)
        self.assertLessEqual(am.COMMAND_KEYWORDS - am.PROOF_COMMANDS - am.MODIFIERS,
                             am.FORBIDDEN_TOKENS)
        self.assertTrue({'lemma', 'theorem', 'example', 'def', 'instance', 'alias',
                         'add_decl_doc', 'notation3'} <= am.COMMAND_KEYWORDS)
        self.assertFalse((am.PROOF_COMMANDS | am.MODIFIERS) & am.FORBIDDEN_TOKENS)
        self.assertTrue(all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', w)
                            for w in am.COMMAND_KEYWORDS))

    def test_attribute_on_theorem_accepted(self):
        # Note N7: attribute changes on untagged theorems are accepted.
        new = BASE_FILE.replace('theorem helper', '@[simp] theorem helper')
        self.accept(Fixture().lean(PATH, BASE_FILE, new))

    def test_where_and_let_rec_rejected(self):
        # R4: `where` and `let rec` inside a theorem add auxiliary definitions (`z.foo`,
        # `a.f`), which a proof-only change may not do.
        line_z = 'theorem z : True := trivial'
        with_z = BASE_FILE.replace('end PercLib', line_z + '\n\nend PercLib')
        cases = [
            ('where (R4 fixture)', with_z,
             with_z.replace(line_z, 'theorem z : True := trivial where\n  foo : Nat := 1')),
            ('let rec (R4 fixture)', WITH_A,
             WITH_A.replace(LINE_A, 'theorem a : True := let rec f : Nat → Nat '
                                    '| 0 => 0 | n+1 => f n; trivial')),
            ('where on its own line', with_z,
             with_z.replace(line_z, 'theorem z : True := trivial\nwhere\n  foo : Nat := 1')),
            ('let rec over lines', WITH_A,
             WITH_A.replace(LINE_A, 'theorem a : True := by\n  let\n    rec f : Nat → Nat '
                                    '| _ => 0\n  trivial')),
            ('body of an existing split let rec edited',
             WITH_A.replace(LINE_A, 'theorem a : True := by\n  let\n    rec f : Nat → Nat '
                                    '| _ => 0\n  trivial'),
             WITH_A.replace(LINE_A, 'theorem a : True := by\n  let\n    rec f : Nat → Nat '
                                    '| _ => 1\n  trivial')),
        ]
        for name, base, head in cases:
            with self.subTest(case=name):
                self.assertNotEqual(base, head)
                self.reject(Fixture().lean(PATH, base, head), contains='where` or `let rec')

    def test_recursor_and_where_in_comment_accepted(self):
        # `rec` is not a forbidden token: a proof may use `Nat.rec`; and `where` or
        # `let rec` inside a comment is not code.
        for line in ['theorem a : True := Nat.rec (motive := fun _ => True) trivial '
                     '(fun _ _ => trivial) 0',
                     'theorem a : True := trivial -- where, let rec',
                     'theorem a : True := /- where foo -/ trivial']:
            with self.subTest(line=line):
                self.accept(Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)))

    # Finding S1 of the third audit of the CI workflows: on an invalid escape such as `\q`
    # Lean abandons the string at the escape and lexes the rest as code, where `run_meta`
    # starts a new command. The lexer must refuse the literal itself, so the reason names
    # the escape and not a token that the line check happens to see.
    S1_LINE = ('theorem a : True := (fun _ => trivial) "\\q run_meta IO.FS.writeFile '
               "(toString 'q' ++ toString '1') (toString 'x') -- \"")

    def test_invalid_escape_rejected(self):
        cases = [
            ('S1 probe', self.S1_LINE, '`\\q` in a string literal'),
            ('char literal', "theorem a : True := (fun _ => trivial) '\\q' run_meta pure ()",
             '`\\q` in a character literal'),
            ('string, no command after', 'theorem a : "\\q".length = 1 := rfl',
             '`\\q` in a string literal'),
            ('char, no command after', "theorem a : '\\q' = 'q' := rfl",
             '`\\q` in a character literal'),
            ('\\x with one hex digit', 'theorem a : "\\x4g".length = 2 := rfl',
             '`\\x` in a string literal'),
            ('\\u with three hex digits', 'theorem a : "\\u03B".length = 1 := rfl',
             '`\\u` in a string literal'),
            ('\\0', 'theorem a : "\\0".length = 1 := rfl', '`\\0` in a string literal'),
            ('\\a', "theorem a : '\\a' = 'a' := rfl", '`\\a` in a character literal'),
            ('backslash-newline in a char', "theorem a : '\\\n' = 'a' := rfl",
             '`\\` before a newline in a character literal'),
        ]
        for name, line, reason in cases:
            with self.subTest(case=name):
                with self.assertRaises(am.Reject) as cm:
                    Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)).classify()
                message = str(cm.exception)
                self.assertIn('invalid escape ' + reason, message)
                self.assertNotIn('run_meta', message)
                self.assertNotIn('changed line', message)

    def test_valid_escapes_accepted(self):
        # Every escape Lean accepts still passes, in strings and in character literals.
        # (A forbidden token such as `def` cannot be put inside the string here: the token
        # check reads the line with literals present, by design. That an escaped quote does
        # not end the literal is checked on strip_comments directly, below.)
        escapes = ['\\\\', '\\"', "\\'", '\\n', '\\t', '\\r', '\\x41', '\\xfF', '\\u03B1',
                   '\\uabcd']
        for esc in escapes:
            for line in [f'theorem a : "a{esc}b c".length > 0 := by decide',
                         f"theorem a : '{esc}' = '{esc}' := rfl"]:
                with self.subTest(line=line):
                    self.accept(Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)))
        gap = 'theorem a : "ab\\\n    cd".length = 4 := by decide'
        self.accept(Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, gap)))
        self.assertEqual(am.strip_comments('x "\\" def" y \'\\\'\' z', blank_literals=True),
                         'x ' + ' ' * 8 + ' y ' + ' ' * 4 + ' z')

    # Finding S2 of the fourth audit of the CI workflows: Lean lexes the longest token, so
    # a `--`, `/-` or `'` directly after a symbol may continue a token (`<-`, `\/`, `//`,
    # `]'`, `''`) and be code to Lean. Probe lines A, B, C, P-Z (comment openers) and D, H
    # (character literals) of that audit, and the same with `]''`; each wrote a file when
    # Lean v4.35.0 elaborated it (P-Z with no error at all). The lexer must refuse the
    # opener or literal itself, not a token that the line check happens to see.
    S2_WRITE = "IO.FS.writeFile (toString 'q' ++ toString 'N') (toString 'x')"

    def test_comment_opener_after_symbol_rejected(self):
        w = self.S2_WRITE
        cases = [
            ('A', f'theorem b : True := trivial <-- run_meta {w}', '`<--`'),
            ('B', f'theorem b : True := trivial \\/- run_meta {w} -- -/', '`\\/-`'),
            ('C', f'theorem b : True := trivial //- run_meta {w} -- -/', '`//-`'),
            ('P-Z', "theorem b : ∃ y : { x : Int //- x < 1 }, y.1 = 0 := ⟨⟨0, by run_tac do "
                    "IO.FS.writeFile (toString 'q' ++ toString 'Z') (toString 'x'); "
                    "Lean.Elab.Tactic.evalTactic (← `(tactic| decide))⟩, rfl⟩ -- -/", '`//-`'),
        ]
        for name, line, shown in cases:
            with self.subTest(probe=name):
                with self.assertRaises(am.Reject) as cm:
                    Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)).classify()
                message = str(cm.exception)
                self.assertIn('directly after a symbol', message)
                self.assertIn('comment opener', message)
                self.assertIn(shown, message)
                self.assertNotIn('run_', message)
                self.assertNotIn('changed line', message)

    def test_char_literal_after_symbol_rejected(self):
        w = self.S2_WRITE
        cases = [
            ('D', f'theorem b : True := trivial ]\'"\' foo " run_meta {w} -- "'),
            ('E', f'theorem b : True := trivial ×\'"\' foo " run_meta {w} -- "'),
            ('H', f'theorem b : True := trivial \'\'\'"\' run_meta {w} -- "'),
            ("]''", f'theorem b : True := trivial ]\'\'"\' x " /- " run_meta {w} -- -/'),
            ('escape', "theorem b : True := trivial ]'\\n' run_meta pure ()"),
            ('invalid escape', "theorem b : True := trivial ]'\\q' run_meta pure ()"),
        ]
        for name, line in cases:
            with self.subTest(probe=name):
                with self.assertRaises(am.Reject) as cm:
                    Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)).classify()
                message = str(cm.exception)
                self.assertIn('character literal directly after a symbol', message)
                self.assertNotIn('run_meta', message)
                self.assertNotIn('changed line', message)

    def test_token_quotes_and_dashes_accepted(self):
        lines = [
            "theorem b : (∑' i : ℕ, (0 : ℝ)) = 0 := by simp",
            "theorem b (f : ℕ → ℕ) (s : Set ℕ) : f '' s = f '' s := rfl",
            "theorem b (f : ℕ → ℕ) (s : Set ℕ) : (f ⁻¹' s) = f ⁻¹' s := rfl",
            "theorem b : ['a', 'b'].length = 2 := rfl",
            "theorem b : True := by have h' := trivial; exact h'",
            "theorem b : True := by have h''a' := trivial; exact h''a'",
            'theorem b (x c : ℕ) : x--c\n    = x := rfl',
        ]
        for line in lines:
            with self.subTest(line=line):
                self.accept(Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)))
        self.assertEqual(am.strip_comments("x--c\n(-- c\n[/- c -/]"), 'x\n(\n[ ]')

    # Findings S3, S4 and S6 of the fifth audit of the CI workflows (probe numbers as
    # there; each wrote a file when Lean v4.35.0 ran it, after an error). S3: a `'` at a
    # token start that fits no character literal makes Lean consume two more characters
    # and resume after them. S4: `2r"…"` is a numeral and a raw string to Lean. S6: after
    # a numeral, `x.1`, a standalone `!` or `?`, or `²`, a `'` starts a character literal
    # in Lean, which an `isalnum` identifier test misses. The lexer must refuse each
    # itself, so the reason names the lexical problem, not a token the line check sees.
    def lexer_rejects(self, probe, reason):
        line = 'theorem b : True := trivial ' + probe
        with self.assertRaises(am.Reject) as cm:
            Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)).classify()
        message = str(cm.exception)
        self.assertIn(reason, message)
        self.assertNotIn('run_meta', message)
        self.assertNotIn('changed line', message)

    def test_unterminated_char_literal_rejected(self):
        w = self.S2_WRITE
        for name, probe in [('p1', f"'-- run_meta {w}"), ('p2', f"'/- run_meta {w} -- -/"),
                            ('p13', f"'x-- run_meta {w}"),
                            ('p14', f"'x/- run_meta {w} -- -/"),
                            ('p20', f"(' -- run_meta {w}"),
                            ('p16', f'\'a" run_meta {w} -- "')]:
            with self.subTest(probe=name):
                self.lexer_rejects(probe, 'unterminated character literal')

    def test_kept_quote_read_both_ways(self):
        # A `'` kept as code (after a symbol, or the second of `''`) may start a failing
        # character literal: Lean then resumes two characters later (p18: after `a"`,
        # so `run_meta` is code), and both readings must agree.
        w = self.S2_WRITE
        for name, probe in [('p18', f'+\'a" run_meta {w} -- "'),
                            ('p19', f'\'\'a" run_meta {w} -- "'),
                            ('p21', f'+\'ab2\'"\' run_meta {w} -- "'),
                            ('+ then string', f'+\'a" " run_meta {w} -- "')]:
            with self.subTest(probe=name):
                self.lexer_rejects(probe, 'reads differently if Lean starts another token')
        self.lexer_rejects(f"+'-- run_meta {w}", 'comment opener `--` directly after')  # p17

    def test_raw_string_after_numeral_rejected(self):
        w = self.S2_WRITE
        for name, probe in [('p12', f'2r"\\" " /- " run_meta {w} -- -/'),
                            ('p15', f'2r#"\\"# " /- " run_meta {w} -- -/')]:
            with self.subTest(probe=name):
                self.lexer_rejects(probe, 'raw string directly after a numeral')

    def test_lean_identifier_rules(self):
        w = self.S2_WRITE
        for name, probe, reason in [
                ('p4', f'2\'"\' " /- " run_meta {w} -- -/', "`'` directly after a numeral"),
                ('p7', f'x.1\'"\' " /- " run_meta {w} -- -/', "`'` directly after a numeral"),
                ('p5', f'!\'"\' " /- " run_meta {w} -- -/',
                 'character literal directly after a symbol'),
                ('p8', f'?\'"\' " /- " run_meta {w} -- -/',
                 'character literal directly after a symbol'),
                ('²', f'x²\'"\' " -- " run_meta {w}',
                 'character literal directly after a symbol'),
                ('«»', f'«x»\'"\' " -- " run_meta {w}', "`'` directly after a numeral or `»`")]:
            with self.subTest(probe=name):
                self.lexer_rejects(probe, reason)
        # Lean's identifier characters include Greek and Latin-1 letters and subscripts.
        self.assertEqual(am.strip_comments("η' ω₁' é' Σ' x²'"), "η' ω₁' é' Σ' x²'")

    def test_numeral_after_dot_read_both_ways(self):
        # Lean's parser reads `x.1.e5` as a field index `1` and the field `e5`, but its
        # error recovery (here after `.1`) reads the number `1.e5`, so `'"'` is a character
        # literal and `run_meta` code (checked with Lean v4.35.0: the file was written).
        w = self.S2_WRITE
        self.lexer_rejects(f'.1.e5\'"\' " -- " run_meta {w}',
                           'reads differently if Lean starts another token')
        self.lexer_rejects(f'2e-- run_meta {w}', 'malformed numeral')

    def test_lean_lexing_legitimate_forms_accepted(self):
        lines = [
            "theorem b (μ : M) : μ.real (A' ∩ Tn ⁻¹' B') = 0 := rfl",
            "theorem b : f = Sum.inl ⁻¹' η' := rfl",
            "theorem b : (Subtype.val : S → V) ⁻¹' ω' = s := rfl",
            "theorem b (f : ℕ → ℕ) (s t : Set ℕ) : f '' (s ∩ t) = f '' (s ∩ t) := rfl",
            "theorem b (h : 1 ≤ 2 ∧ True) : 1 < 3 := lt_of_le_of_lt h.1.le (by decide)",
            "theorem b (p : ℕ × ℕ × ℕ) : p.2.1 = p.2.1 := rfl",
            "theorem b : (1.5 : ℝ) + 2.5e3 + 1e-3 + 0x1F + 1_000 = 2 := by norm_num",
            "theorem b : [1, 2].map (· + 0) = [1, 2] := rfl",
            "theorem b : ('a', \"b\").1 = 'a' := rfl",
        ]
        for line in lines:
            with self.subTest(line=line):
                self.accept(Fixture().lean(PATH, WITH_A, WITH_A.replace(LINE_A, line)))


EVIDENCE_HEAD = 'a' * 40
EVIDENCE_BASE = 'b' * 40


def evidence():
    pr = dict(number=7, state='open', draft=False, merged=False, title='ex: shorten',
              user=dict(login='TomHutchcroft'), changed_files=1,
              head=dict(sha=EVIDENCE_HEAD, ref='x', repo=dict(full_name='o/perclib')),
              base=dict(sha=EVIDENCE_BASE, ref='main', repo=dict(full_name='o/perclib')))
    run = dict(id=99, workflow_id=5, event='pull_request', status='completed',
               conclusion='success', head_sha=EVIDENCE_HEAD,
               pull_requests=[dict(number=7, head=dict(sha=EVIDENCE_HEAD),
                                   base=dict(sha=EVIDENCE_BASE))])
    jobs = dict(jobs=[dict(name='gate', conclusion='success', head_sha=EVIDENCE_HEAD),
                      dict(name='kernel-replay', conclusion='success',
                           head_sha=EVIDENCE_HEAD)])
    branch = dict(name='main', protected=True, commit=dict(sha=EVIDENCE_BASE))
    compare = dict(behind_by=0, ahead_by=2, merge_base_commit=dict(sha=EVIDENCE_BASE))
    workflow = dict(id=5, path='.github/workflows/ci.yml')
    return dict(run=run, jobs=jobs, pr=pr, branch=branch, compare=compare, workflow=workflow)


class EvidenceTests(unittest.TestCase):
    authors = {'tomhutchcroft'}

    def check(self, ev):
        return am.check_evidence(ev['run'], ev['jobs'], ev['pr'], ev['branch'],
                                 ev['compare'], ev['workflow'], self.authors, 'main')

    def test_green_accepted(self):
        self.assertEqual(self.check(evidence()), (7, EVIDENCE_HEAD, EVIDENCE_BASE))

    def test_each_failure_rejected(self):
        def set_(path, value):
            def mutate(ev):
                d = ev
                for key in path[:-1]:
                    d = d[key]
                d[path[-1]] = value
            return mutate
        cases = {
            'author not listed': set_(('pr', 'user', 'login'), 'someone'),
            'draft': set_(('pr', 'draft'), True),
            'closed': set_(('pr', 'state'), 'closed'),
            'other base branch': set_(('pr', 'base', 'ref'), 'dev'),
            'fork': set_(('pr', 'head', 'repo', 'full_name'), 'fork/perclib'),
            'other workflow': set_(('run', 'workflow_id'), 6),
            'push event': set_(('run', 'event'), 'push'),
            'run failed': set_(('run', 'conclusion'), 'failure'),
            'stale head': set_(('run', 'head_sha'), 'c' * 40),
            'stale run head in PR entry': lambda ev: ev['run']['pull_requests'][0].update(
                head=dict(sha='c' * 40)),
            'base bound differently': lambda ev: ev['run']['pull_requests'][0].update(
                base=dict(sha='c' * 40)),
            'run for another PR': lambda ev: ev['run']['pull_requests'][0].update(number=8),
            'run for two PRs': lambda ev: ev['run']['pull_requests'].append(
                dict(number=8, head=dict(sha=EVIDENCE_HEAD), base=dict(sha=EVIDENCE_BASE))),
            'gate skipped': lambda ev: ev['jobs']['jobs'][0].update(conclusion='skipped'),
            'gate missing': lambda ev: ev['jobs'].update(jobs=[]),
            'two gates': lambda ev: ev['jobs']['jobs'].append(
                dict(name='gate', conclusion='success')),
            'kernel replay missing': lambda ev: ev['jobs'].update(
                jobs=[j for j in ev['jobs']['jobs'] if j['name'] != 'kernel-replay']),
            'kernel replay skipped': lambda ev: ev['jobs']['jobs'][1].update(
                conclusion='skipped'),
            'kernel replay failed': lambda ev: ev['jobs']['jobs'][1].update(
                conclusion='failure'),
            'kernel replay of another head': lambda ev: ev['jobs']['jobs'][1].update(
                head_sha='c' * 40),
            'two kernel replays': lambda ev: ev['jobs']['jobs'].append(
                dict(name='kernel-replay', conclusion='success')),
            'base moved': set_(('branch', 'commit', 'sha'), 'c' * 40),
            'unprotected': set_(('branch', 'protected'), False),
            'head behind base': set_(('compare', 'behind_by'), 1),
            'malformed sha': set_(('pr', 'head', 'sha'), 'main'),
        }
        for name, mutate in cases.items():
            with self.subTest(case=name):
                ev = evidence()
                mutate(ev)
                with self.assertRaises(am.Reject):
                    self.check(ev)


class CommandLineTests(unittest.TestCase):
    def run_main(self, argv, stdin):
        old = sys.stdin
        sys.stdin = io.StringIO(stdin)
        out = io.StringIO()
        try:
            with redirect_stdout(out):
                code = am.main(argv)
        finally:
            sys.stdin = old
        return code, out.getvalue()

    def test_decide_end_to_end(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN)
        ev = evidence()
        files = {}
        for key, value in ev.items():
            files[key] = f.root / f'{key}.json'
            files[key].write_text(json.dumps(value))
        authors = f.root / 'authors'
        authors.write_text('# Tom adds collaborators.\ntomhutchcroft\n')
        output = f.root / 'out'
        argv = ['decide', '--run', str(files['run']), '--jobs', str(files['jobs']),
                '--pr', str(files['pr']), '--branch', str(files['branch']),
                '--compare', str(files['compare']), '--ci-workflow', str(files['workflow']),
                '--authors', str(authors), '--default-branch', 'main',
                '--base-dir', str(f.root / 'base'), '--head-dir', str(f.root / 'head'),
                '--github-output', str(output)]
        stdin = '\n'.join(json.dumps(e) for e in f.entries) + '\n'
        code, text = self.run_main(argv, stdin)
        self.assertEqual(code, 0, text)
        self.assertIn('merge=true', output.read_text())
        self.assertIn(f'head={EVIDENCE_HEAD}', output.read_text())
        # Listing shorter than changed_files: rejected.
        ev['pr']['changed_files'] = 2
        files['pr'].write_text(json.dumps(ev['pr']))
        output.unlink()
        code, text = self.run_main(argv, stdin)
        self.assertEqual(code, 1)
        self.assertFalse(output.exists())
        # Malformed authors file: rejected.
        ev['pr']['changed_files'] = 1
        files['pr'].write_text(json.dumps(ev['pr']))
        authors.write_text('tomhutchcroft; rm -rf /\n')
        self.assertEqual(self.run_main(argv, stdin)[0], 1)

    def test_plan(self):
        other = 'PercLib/Other.lean'
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN).lean(other, BASE_FILE, NEW_LEMMA)
        pr = f.root / 'pr.json'
        pr.write_text(json.dumps(dict(title='x')))
        code, text = self.run_main(['plan', '--pr', str(pr)], json.dumps(f.entries))
        self.assertEqual(code, 0)
        self.assertEqual(text.split(), ['base', PATH, 'head', PATH, 'base', other, 'head', other])
        bad = f.entries + [dict(filename='scripts/x.py', status='modified', patch='')]
        self.assertEqual(self.run_main(['plan', '--pr', str(pr)], json.dumps(bad))[0], 1)

    def test_rejection_message_cannot_print_workflow_commands(self):
        f = Fixture()
        pr = f.root / 'pr.json'
        pr.write_text(json.dumps(dict(title='x')))
        payload = ('docs/x\n::set-output name=merge::true\n::set-output name=pr::7\r\n'
                   '::set-output name=head::' + 'a' * 40 + '\nz')
        listings = [
            [dict(filename=payload, status='modified', patch='')],
            [dict(filename=PATH, previous_filename=payload, status='renamed', patch='')],
        ]
        for listing in listings:
            code, text = self.run_main(['plan', '--pr', str(pr)], json.dumps(listing))
            self.assertEqual(code, 1, text)
            self.assertTrue(text.startswith('Not merging: '), text)
            self.assertIn('::set-output', text)
            for line in text.splitlines():
                self.assertFalse(line.lstrip().startswith('::'), text)

    def test_paginated_listing(self):
        f = Fixture().lean(PATH, BASE_FILE, PROOF_EDIT_CLEAN).lean(
            'PercLib/Other.lean', BASE_FILE, NEW_LEMMA)
        pages = json.dumps(f.entries[:1], indent=2) + json.dumps(f.entries[1:])
        self.assertEqual(len(am.read_files(io.StringIO(pages))), 2)
        lines = '\n'.join(json.dumps(e) for e in f.entries)
        self.assertEqual(len(am.read_files(io.StringIO(lines))), 2)

    def test_garbage_input_rejected(self):
        self.assertEqual(self.run_main(['classify'], 'not json')[0], 1)
        self.assertEqual(self.run_main(['classify'], '[]')[0], 1)


if __name__ == '__main__':
    unittest.main()
