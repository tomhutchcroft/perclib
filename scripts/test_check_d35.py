#!/usr/bin/env python3
"""Unit tests of the header reading of check_d35.py (check (iv)). Standard library only."""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_d35 import CASE_SENSITIVE, LOWER, header_text

COPYRIGHT = ('/-\nCopyright (c) 2026 PercLib contributors. All rights reserved.\n'
             'Released under Apache 2.0 license as described in the file LICENSE.\n'
             'Authors: PercLib contributors\n-/\n')
DOC = '/-!\n# Title\n\n## Main results\n\n* `foo`\n-/\n'
CODE = 'theorem foo : True := trivial\n'


def labels(text):
    h = header_text(text)
    return CASE_SENSITIVE.findall(h) + LOWER.findall(h)


def two_blocks(provenance):
    return (COPYRIGHT + '/-\n' + provenance + '\n-/\nmodule\n\n'
            'public import Mathlib.Data.Real.Basic\n\n' + DOC + CODE)


class HeaderTextTests(unittest.TestCase):
    def test_label_in_second_block_flagged(self):
        text = two_blocks('New proofs, written for D-35 by the PROVER.')
        self.assertIn('D-35', labels(text))
        self.assertIn('PROVER', labels(text))

    def test_clean_second_block_passes(self):
        text = two_blocks('New proofs using mathlib, at the pinned revision 56a0058.')
        self.assertEqual(labels(text), [])
        self.assertIn('pinned revision', header_text(text))

    def test_single_block_as_before(self):
        clean = COPYRIGHT + 'module\n\n' + DOC + CODE
        self.assertEqual(header_text(clean), COPYRIGHT.rstrip('\n') + '\n' + DOC.rstrip('\n'))
        self.assertEqual(labels(clean), [])
        self.assertIn('I-12', labels('/- Source: I-12. -/\nmodule\n' + DOC + CODE))

    def test_label_in_code_after_module_ignored(self):
        text = (two_blocks('Clean provenance.')
                + '/- A comment naming D-35 and the LEAD. -/\n-- see PR #12\n'
                + 'theorem bar : True := trivial -- ARCHITECT\n')
        self.assertEqual(labels(text), [])

    def test_label_in_docstring_flagged(self):
        text = COPYRIGHT + 'module\n\n/-!\n# Title\n\nPorted in issue #41.\n-/\n' + CODE
        self.assertTrue(labels(text))

    def test_nested_comment_not_split(self):
        text = COPYRIGHT + '/-\nOuter /- inner -/ still the header: D-35.\n-/\nmodule\n' + DOC
        self.assertIn('D-35', labels(text))

    def test_line_comments_and_blank_lines_skipped(self):
        text = COPYRIGHT + '\n-- a line comment\n\n/- Written by an agent. -/\nmodule\n' + DOC
        self.assertTrue(labels(text))

    def test_header_stops_at_first_token(self):
        text = COPYRIGHT + 'import Mathlib\n/- D-35 -/\n' + DOC
        self.assertEqual(labels(text), [])

    # A `/-! … -/` inside a header comment must not hide the real module docstring.
    REAL_DOC = ('module\n\npublic import Mathlib\n\n'
                '/-!\n# T\n\nPorted in issue #41 by the LEAD.\n-/\n')

    def test_docstring_nested_in_header_block_does_not_hide_real_one(self):  # P13b
        text = COPYRIGHT + '/- Provenance; see /-! x -/ for the format. -/\n' + self.REAL_DOC
        self.assertEqual(sorted(set(labels(text))), ['LEAD', 'issue #41'])

    def test_docstring_in_header_line_comment_does_not_hide_real_one(self):  # P13c
        text = COPYRIGHT + '-- format: /-! x -/\n' + self.REAL_DOC
        self.assertEqual(sorted(set(labels(text))), ['LEAD', 'issue #41'])

    def test_label_in_line_comment_before_module_flagged(self):
        text = COPYRIGHT + '-- written by an agent, D-12\nmodule\n' + DOC
        self.assertTrue(labels(text))

    def test_opener_body_starts_after_third_character(self):  # P11
        text = (COPYRIGHT + '/-/- x -/\nmodule\n' + DOC
                + 'theorem t : True := trivial -- the LEAD\n/- D-99 -/\n')
        self.assertEqual(labels(text), [])


if __name__ == '__main__':
    unittest.main()
