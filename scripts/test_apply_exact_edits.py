#!/usr/bin/env python3
"""Tests for scripts/apply_exact_edits.py on temporary directories."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parent / "apply_exact_edits.py"


class ApplyExactEditsTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self.tmp.name)
        (self.dir / "a.txt").write_text("alpha\nbeta\ngamma\n")
        (self.dir / "b.txt").write_text("one\ntwo\ntwo\n")

    def tearDown(self):
        self.tmp.cleanup()

    def run_edits(self, edits):
        path = self.dir / "edits.json"
        path.write_text(json.dumps(edits))
        return subprocess.run(
            [sys.executable, str(SCRIPT), str(path), "--repo", str(self.dir)],
            capture_output=True, text=True,
        )

    def read(self, name):
        return (self.dir / name).read_text()

    def test_success_in_order(self):
        result = self.run_edits([
            {"file": "a.txt", "old": "beta", "new": "BETA"},
            {"file": "a.txt", "old": "BETA\ngamma", "new": "delta"},
            {"file": "b.txt", "old": "one", "new": "ONE"},
        ])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.read("a.txt"), "alpha\ndelta\n")
        self.assertEqual(self.read("b.txt"), "ONE\ntwo\ntwo\n")
        self.assertEqual(len(result.stdout.splitlines()), 3)
        self.assertIn("edit 1: a.txt: replaced at line 2", result.stdout)

    def test_zero_occurrences(self):
        result = self.run_edits([{"file": "a.txt", "old": "zeta", "new": "x"}])
        self.assertEqual(result.returncode, 1)
        self.assertIn("occurs 0 times", result.stderr)
        self.assertEqual(self.read("a.txt"), "alpha\nbeta\ngamma\n")

    def test_two_occurrences(self):
        result = self.run_edits([{"file": "b.txt", "old": "two", "new": "x"}])
        self.assertEqual(result.returncode, 1)
        self.assertIn("occurs 2 times", result.stderr)
        self.assertEqual(self.read("b.txt"), "one\ntwo\ntwo\n")

    def test_atomic_across_files(self):
        result = self.run_edits([
            {"file": "a.txt", "old": "alpha", "new": "ALPHA"},
            {"file": "b.txt", "old": "two", "new": "x"},
        ])
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.read("a.txt"), "alpha\nbeta\ngamma\n")
        self.assertEqual(self.read("b.txt"), "one\ntwo\ntwo\n")
        self.assertEqual(result.stdout, "")

    def test_missing_file(self):
        result = self.run_edits([
            {"file": "a.txt", "old": "alpha", "new": "ALPHA"},
            {"file": "nope.txt", "old": "x", "new": "y"},
        ])
        self.assertEqual(result.returncode, 1)
        self.assertEqual(self.read("a.txt"), "alpha\nbeta\ngamma\n")


if __name__ == "__main__":
    unittest.main()
