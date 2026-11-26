#!/usr/bin/env python3
"""Unit tests of the forbidden-construct scan (`check_forbidden.py`). Standard library only."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))  # `python3 -I` omits it
from check_forbidden import check_file  # noqa: E402

REL = 'PercLib/Area/F.lean'


def flagged(text, rel=REL):
    return bool(check_file(rel, text))


class ForbiddenScanTests(unittest.TestCase):
    def test_audit_probe_lines(self):
        # The three probe lines that passed the scan before the fix.
        for line in ['theorem a : True := trivial #eval! IO.FS.writeFile "p" "hi"',
                     'theorem a : True := let «x--» := 0; trivial #eval 1',
                     'theorem a : True := let «x--» := 0; trivial axiom bad : False']:
            with self.subTest(line=line):
                self.assertTrue(flagged(line))

    def test_eval_variants(self):
        for cmd in ['#eval', '#eval!', '#eval?', '#evalFoo']:
            with self.subTest(cmd=cmd):
                self.assertTrue(flagged(f'theorem a : True := trivial\n{cmd} 1\n'))
                self.assertTrue(flagged(f'theorem a : True := trivial {cmd} 1\n'))

    def test_guillemets(self):
        for text in ['theorem a : True := let «y/-» := 0; trivial axiom bad : False',
                     'theorem a : True := let «y\"» := 0; trivial axiom bad : False',
                     'theorem a : True := let x.«y--».z := 0; trivial #eval 1',
                     'theorem «sorry» : True := trivial',
                     'theorem a : True := let «x := 0; trivial']:  # unterminated «
            with self.subTest(text=text):
                self.assertTrue(flagged(text))

    def test_char_literals(self):
        # `'"'` and `'«'` are character literals; neither opens a string or identifier.
        for text in ["def c : Char := '\"'\naxiom bad : False\ndef d : Char := '\"'\n",
                     "def c : Char := '«'\naxiom bad : False\ndef d : Char := '»'\n",
                     "def c : Nat := 2'\"'\naxiom bad : False\ndef d : Char := '\"'\n"]:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        # After an identifier, `'` is part of it: `x'"…"` is `x'` followed by a string.
        self.assertFalse(flagged('def x\' : Nat := 1\ndef c := x\'" axiom "\n'))

    def test_interpolated_strings_refused(self):
        for text in ['def t : String := s!"{ "a" ++ toString (by exact (sorry : Nat)) }"',
                     'def t : String := s! "{1}"', 'def t : String := "{"']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        self.assertFalse(flagged('def t : String := "no braces \\" here"'))

    def test_simprocs(self):
        for text in ['simproc reduceFoo (Foo _) := fun e => return .continue',
                     'dsimproc reduceFoo (Foo _) := fun e => return .continue',
                     'simproc_decl reduceFoo (Foo _) := fun e => return .continue',
                     'attribute [simproc] reduceFoo']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))

    def test_code_registering_attributes(self):
        for text in ['@[norm_num _ + _] def evalAdd : NormNumExt := sorryFree',
                     '@[positivity _ * _] def evalMul : PositivityExt := x',
                     '@[delab app.Foo] def delabFoo : Delab := x',
                     '@[app_unexpander Foo] def unexpandFoo : Unexpander := x',
                     '@[simp, scoped norm_num Nat.succ _] def f : Nat := 0',
                     '@[Mathlib.Meta.Positivity.«positivity» _] def f : Nat := 0',
                     'attribute [local norm_num Nat.succ _] evalSucc',
                     'attribute [positivity Real.exp _] evalExp',
                     '@[aesop safe (rule_sets := [Foo]), norm_num _] def f : Nat := 0']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))

    def test_elaboration_time_meta_code(self):
        # Finding R1: `run_meta` and a `meta def` registered as a tactic run IO when elaborated.
        for text in ['run_meta IO.FS.writeFile "pwned" "x"',
                     'theorem a : True := trivial run_meta IO.FS.writeFile "pwned" "x"',
                     '@[tactic Lean.Parser.Tactic.done] public meta def evalPwn : Tactic := '
                     'fun _ => throwUnsupportedSyntax',
                     'public meta def f : Nat := 0',
                     'public meta import Lean.Elab.Command']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        for cmd in ['cbv_simproc', 'cbv_simproc_decl', 'cbv_simproc_pattern', 'simproc_pattern',
                    'grind_propagator', 'builtin_simproc', 'builtin_dsimproc',
                    'builtin_grind_propagator']:
            with self.subTest(cmd=cmd):
                self.assertTrue(flagged(f'{cmd} reduceFoo (Foo _) := fun e => return .continue'))
        # The tag attribute file may use `meta`, and only that file.
        self.assertFalse(flagged('public meta import Lean.Elab.Command\npublic meta section',
                                 'PercLib/Meta/Tag.lean'))

    def test_invalid_escape_probe(self):
        # Finding S1 / GS3: Lean ends the string at the invalid escape `\q` and runs `run_meta`.
        line = ('theorem a : True := (fun _ => trivial) "\\q run_meta IO.FS.writeFile '
                "(toString 'q' ++ toString '1') (toString 'x') -- \"")
        for text in [line, 'def t : String := "\\q"', "def c : Char := '\\q'"]:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        self.assertFalse(flagged('theorem t : "\\x41\\u0042\\n" = "AB\\n" := rfl'))

    # Finding S2 / GS4: Lean lexes the longest token, so a comment opener or `'` right after a
    # symbol can continue a token (`<-`, `\\/`, `//`, `]'`, `×'`, `Σ'`, `⊕'`, `''`) and the
    # text after it is code that runs `run_meta` or `run_tac`.
    W = "IO.FS.writeFile (toString 'q' ++ toString 'N') (toString 'x')"
    HEAD = 'import Lean\ntheorem a : True := trivial\n'

    def test_comment_opener_after_symbol_probes(self):
        pz = ("theorem b : ∃ y : { x : Int //- x < 1 }, y.1 = 0 := ⟨⟨0, by run_tac do "
              "IO.FS.writeFile (toString 'q' ++ toString 'Z') (toString 'x'); "
              "Lean.Elab.Tactic.evalTactic (← `(tactic| decide))⟩, rfl⟩ -- -/")
        for line in [f'theorem b : True := trivial <-- run_meta {self.W}',
                     f'theorem b : True := trivial \\/- run_meta {self.W} -- -/',
                     f'theorem b : True := trivial //- run_meta {self.W} -- -/',
                     pz]:
            with self.subTest(line=line):
                self.assertTrue(flagged(self.HEAD + line + '\n'))

    def test_char_literal_after_symbol_probes(self):
        lines = [f'theorem b : True := trivial {tok}"\' foo " run_meta {self.W} -- "'
                 for tok in [']\'', '×\'', 'Σ\'', '⊕\'']]  # probes D, E, F, G
        lines.append(f'theorem b : True := trivial \'\'\'"\' run_meta {self.W} -- "')  # H
        for line in lines:
            with self.subTest(line=line):
                self.assertTrue(flagged(self.HEAD + line + '\n'))

    def test_quote_and_dash_tokens_pass(self):
        for line in ["theorem t (f : ℕ → ℝ) : ∑' i, f i = ∑' i, f i := rfl",
                     "theorem t (f : α → β) (s : Set α) : f '' s = f '' s := rfl",
                     "theorem t (f : α → β) (s : Set β) : (f ⁻¹' s) = f ⁻¹' s := rfl",
                     "theorem t : ['a', 'b'].length = 2 := rfl",
                     "theorem t (h' : True) : True := h'",
                     "theorem t (x : ℕ) : x = x := rfl -- x--c\ntheorem u (x : ℕ) : x = x--c\n  := rfl"]:
            with self.subTest(line=line):
                self.assertFalse(flagged(line + '\n'))

    # Findings S3, S4, S5 / GS5: Lean resumes three characters after a failing character
    # literal, reads `2r"…"` as `2` and a raw string, and lexes tokens the file declares.
    B = 'theorem b : True := trivial '

    def assert_all_flagged(self, probes):
        for probe in probes:
            with self.subTest(probe=probe):
                self.assertTrue(flagged(self.HEAD + self.B + probe + '\n'))

    def test_unterminated_char_literal_probes(self):
        # GS5 (a): a `'` at a token start that fits no character literal.
        self.assert_all_flagged([f"'-- run_meta {self.W}",                # p1
                                 f"'/- run_meta {self.W} -- -/",          # p2
                                 f"'x-- run_meta {self.W}",               # p13
                                 f"'x/- run_meta {self.W} -- -/",         # p14
                                 f"(' -- run_meta {self.W}",              # p20
                                 f"'a\" run_meta {self.W} -- \""])        # p16

    def test_kept_quote_alternative_reading_probes(self):
        # GS5 (b): a `'` kept as code after a symbol, where Lean may start a character
        # literal, skip two characters and resume.
        self.assert_all_flagged([f"+'-- run_meta {self.W}",               # p17
                                 f"+'a\" run_meta {self.W} -- \"",        # p18
                                 f"+'ab2'\"' run_meta {self.W} -- \"",    # p21
                                 f"''a\" run_meta {self.W} -- \""])       # p19

    def test_kept_quote_each_disagreement(self):
        # GS5 (b), one line per way the two readings can disagree before they meet.
        for probe in ['+\'-- run_meta pure ()',  # only the main reading opens something (`--`)
                      "+'a2'c' = d",             # only the other one does (`'c'` after `2`)
                      "+'ab'c' = d",             # the other reading raises (`'c'` after `b`)
                      "+'ab'c2'd' = e",          # a `'` kept by the other reading, read on
                      "+'a.«b» = c"]:            # `«…»` opened by the other reading only
            with self.subTest(probe=probe):
                self.assertTrue(flagged(self.HEAD + self.B + probe + '\n'))

    def test_raw_string_after_numeral_probes(self):
        # GS5 (c).
        self.assert_all_flagged([f'2r"\\" " /- " run_meta {self.W} -- -/',      # p12
                                 f'2r#"\\"# " /- " run_meta {self.W} -- -/'])   # p15

    def test_token_declaring_commands(self):
        # GS5 (d): probe n5 is error-free in Lean and runs `run_tac` IO through `(--`.
        n5 = ('import Lean\nnotation:max "(--" x ")" => x\ntheorem b : True := (-- by run_tac do '
              'IO.FS.writeFile (toString (Char.ofNat 113) ++ toString (Char.ofNat 84)) '
              '(toString (Char.ofNat 120)); Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))\n'
              '  )\n')
        self.assertTrue(flagged(n5))
        for cmd in ['notation "‖" x "‖" => abs x', 'notation3 "∑ "(...)", "r:67:(scoped f => s f) => r',
                    'infix:50 " ≺ " => Foo', 'infixl:65 " +' + "'" + ' " => f',
                    'infixr:67 " ::: " => g', 'prefix:max "√" => Real.sqrt',
                    'postfix:max "⁺" => pos', 'binder_predicate x " > " y:term => `($x > $y)']:
            with self.subTest(cmd=cmd):
                self.assertIn('forbidden tokens', ' '.join(check_file(REL, cmd + '\n')))

    def test_kept_quote_legitimate_forms_pass(self):
        for line in ["theorem t : μ.real (A' ∩ Tn ⁻¹' B') = 0 := rfl",
                     "theorem t : f = Sum.inl ⁻¹' η' := rfl",
                     "theorem t : (Subtype.val : S → V) ⁻¹' ω' = s := rfl",
                     "theorem t : ∑' (i : ℕ), f i = 0 := rfl",
                     "theorem t : f '' (s ∩ t) = u := rfl",
                     "theorem t : 2 = 2 := rfl -- 2r and r\"x\" in a comment",
                     "theorem t : (fun x => x) 2 = 2 := rfl"]:
            with self.subTest(line=line):
                self.assertFalse(flagged(line + '\n'))

    def test_elaborator_registering_attributes(self):
        # Finding R1 / GS2: attributes that register elaborator, delaborator or initializer code.
        for text in ['@[tactic X] def evalX : Tactic := fun _ => pure ()',
                     '@[app_delab Nat.succ] def delabSucc : Delab := failure',
                     '@[init act] opaque hook : Unit',
                     'attribute [tactic Lean.Parser.Tactic.done] evalPwn',
                     '@[builtin_init act] opaque hook : Unit',
                     '@[builtin_tactic X] def f : Tactic := fun _ => pure ()',
                     '@[builtin_delab app.Foo] def f : Delab := failure',
                     '@[builtin_term_elab foo] def f : TermElab := fun _ _ => failure',
                     '@[builtin_command_elab foo] def f : CommandElab := fun _ => pure ()',
                     '@[builtin_macro foo] def f : Macro := fun _ => Macro.throwUnsupported']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        # The tactics `trivial` and `done`, and the word `tactic` outside attributes, pass.
        for text in ['theorem t : True := by trivial; done',
                     'theorem t : True := by\n  trivial\n  done',
                     '-- this tactic proof uses @[tactic] nowhere\ntheorem t : True := by trivial',
                     '/- the tactic `init` and @[init act] -/\ntheorem t : True := trivial']:
            with self.subTest(text=text):
                self.assertFalse(flagged(text))

    def test_tactics_with_attribute_names_pass(self):
        ok = '''module
public import Mathlib.Tactic
/-! # Ordinary proofs -/
@[simp] theorem two_pos' : (0 : ℝ) < 2 := by norm_num
theorem sq_nonneg' (x : ℝ) : 0 ≤ x ^ 2 := by positivity
@[simp, grind =] theorem f_eq (x : ℕ) : x + 0 = x := by
  norm_num [Nat.add_zero]
theorem g (x : ℝ) (h : 0 < x) : 0 < x * 2 := by
  have h' : (0 : ℝ) < 2 := by norm_num
  nlinarith [h, h']
attribute [simp] two_pos'
attribute [local instance] Classical.propDecidable in
theorem k : True := by simp only [ite_true]; trivial
theorem chars : 'A' ≤ 'Z' ∧ ('\\'' : Char) = '\\'' := by decide
theorem names (h₁ : 1 = 1) (hα' : True) : True := by norm_num at h₁ ⊢
-- a comment mentioning sorry, #eval!, @[norm_num] and «unterminated
/- a block comment: axiom, @[positivity], "unbalanced quote -/
'''
        self.assertEqual(check_file(REL, ok), [])

    def test_existing_rules_kept(self):
        for text in ['theorem a : True := by sorry', 'theorem a : True := by native_decide',
                     'set_option maxHeartbeats 0 in\ntheorem a : True := trivial',
                     'set_option linter.unusedVariables false',
                     'unsafe def f : Nat := 0', '@[implemented_by g] def f : Nat := 0',
                     'set_option «debug».skipKernelTC true']:
            with self.subTest(text=text):
                self.assertTrue(flagged(text))
        self.assertFalse(flagged('set_option maxRecDepth 2000 in\ntheorem a : True := trivial'))
        self.assertFalse(flagged('syntax (name := tag) "tag " str : attr\ninitialize x : Nat ← pure 0',
                                 'PercLib/Meta/Tag.lean'))


if __name__ == '__main__':
    unittest.main()
