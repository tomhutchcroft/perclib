#!/usr/bin/env python3
import copy
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))  # `python3 -I` omits it
from check_proof_pr import check_compiled, check_paths_and_source, code_without_literals  # noqa: E402


def declaration(name, kind='theorem'):
    return dict(name=name, kind=kind, module='PercLib.Example', public=True, universes=0,
                type=['const', 'True', []], value=['const', 'True.intro', []], related=[],
                tag=None, statement_expr=None)


class ProofGateTests(unittest.TestCase):
    def test_theorem_and_root_import(self):
        check_paths_and_source({'PercLib/Proof.lean': 'module\n/- def outer /- opaque -/ -/\n'
            'public import PercLib.Basic\npublic theorem proof : True := by trivial\n',
            'PercLib.lean': 'module\npublic import PercLib.Proof\n'})
        check_compiled({'declarations': []}, {'declarations': [declaration('proof')]})

    def test_interface_paths_and_commands(self):
        for path, text in [('PercLib/Defs.lean', '-- comment only'),
                           ('lakefile.toml', ''), ('PercLib/Proof.lean', 'run_cmd pure ()'),
                           ('PercLib/Proof.lean', 'instance : Inhabited Nat := ⟨0⟩'),
                           ('PercLib.lean', 'theorem p : True := .intro')]:
            with self.assertRaises(ValueError):
                check_paths_and_source({path: text})

    def test_generated_private_definition_rejected(self):
        d = declaration('_private.Generated', 'definition')
        d['public'] = False
        with self.assertRaisesRegex(ValueError, 'non-theorem'):
            check_compiled({'declarations': []}, {'declarations': [d]})

    def test_changed_definition_and_tag(self):
        d = declaration('existing', 'definition')
        other = copy.deepcopy(d)
        other['value'] = ['const', 'False', []]
        with self.assertRaises(ValueError):
            check_compiled({'declarations': [d]}, {'declarations': [other]})
        proof = declaration('proof')
        proof['tag'] = 'A000'
        with self.assertRaisesRegex(ValueError, 'Tagged'):
            check_compiled({'declarations': []}, {'declarations': [proof]})

    def test_literals_cannot_hide_real_commands(self):
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': '"/-"\ndef x := 0'})
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': 'r#"/-"#\ndef x := 0'})
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': '/- unclosed'})

    def test_identifiers_and_chars_cannot_hide_real_commands(self):
        for text in ['theorem a : True := let «x--» := 0; trivial def evil : Nat := 1',
                     'theorem a : True := let «x/-» := 0; trivial instance : Inhabited Nat := ⟨5⟩',
                     'theorem a : True := let «x := 0; trivial',
                     "theorem a : '\"' = '\"' := rfl def evil : Nat := 1",
                     'theorem a : s!"{ "x" }" = "x" := rfl']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                check_paths_and_source({'PercLib/Proof.lean': text})
        self.assertEqual(code_without_literals("h' «a--b».c '\"' x"), "h' «a--b».c   x")


    def test_invalid_escapes_refused(self):
        # Finding S1 / GS3: on an invalid escape Lean abandons the literal and lexes the rest
        # as code, so `run_meta` after `"\q` is a command to Lean.
        probe = ('theorem a : True := (fun _ => trivial) "\\q run_meta IO.FS.writeFile '
                 "(toString 'q' ++ toString '1') (toString 'x') -- \"")
        for text in [probe, '"\\q"', "'\\q'", '"\\xZZ"', '"\\x4"', '"\\u12"', '"\\u12g4"',
                     '"\\X41"', '"\\U0041"', '"\\0"', '"\\{"', '"\\ "', '"a\\\r\nb"',
                     "'\\x4'", "'\\u12'", "'\\\n'", "'\\nx'", "'\\"]:
            with self.subTest(text=text), self.assertRaisesRegex(ValueError, 'invalid escape'):
                code_without_literals(text)
        with self.assertRaisesRegex(ValueError, 'invalid escape in string literal'):
            code_without_literals('"\\q"')
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': probe})

    def test_char_literal_resynchronisation_and_numeral_raw_strings(self):
        # Findings S3, S4 / GS5 (a)-(c), through the proof gate as well as the lexer.
        tail = " run_meta IO.FS.writeFile (toString 'q' ++ toString '1') (toString 'x')"
        for text, reason in [("trivial '--" + tail, 'unterminated character literal'),
                             ("trivial +'--" + tail, 'reads differently'),
                             ("trivial +'ab2'\"'" + tail + ' -- "', 'reads differently'),
                             ('trivial 2r"\\" " /- "' + tail + ' -- -/', 'raw string directly'),
                             ('trivial 2r#"x"#', 'raw string directly')]:
            with self.subTest(text=text):
                with self.assertRaisesRegex(ValueError, reason):
                    code_without_literals(text)
                with self.assertRaises(ValueError):
                    check_paths_and_source({'PercLib/Proof.lean': 'theorem b : True := ' + text})
        self.assertEqual(code_without_literals("(f ⁻¹' B') ∑' f '' s"), "(f ⁻¹' B') ∑' f '' s")

    def test_valid_escapes_pass(self):
        # Each escape Lean v4.35.0 accepts, in a string and (except the gap) a character.
        for esc in ['\\\\', '\\"', "\\'", '\\n', '\\t', '\\r', '\\x41', '\\x4f', '\\xA0',
                    '\\u00e9', '\\u00E9', '\\uFFFF']:
            with self.subTest(esc=esc):
                self.assertEqual(code_without_literals(f'a "x{esc}y" b'), 'a   b')
                self.assertEqual(code_without_literals(f"a '{esc}' b"), 'a   b')
        self.assertEqual(code_without_literals('a "gap\\\n   continued" b'), 'a   b')
        self.assertEqual(code_without_literals('a "\\\\" b "\\"" c'), 'a   b   c')
        check_paths_and_source({'PercLib/Proof.lean':
                                'theorem s : "a\\tb\\\\" = "a\\tb\\\\" := rfl\n'
                                "theorem c : '\\n' = '\\x0a' := rfl\n"})


if __name__ == '__main__':
    unittest.main()
