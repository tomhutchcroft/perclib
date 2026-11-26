#!/usr/bin/env python3
"""Tests for scripts/integrate.sh in a temporary git repository with a stub
scripts/gate.sh (fails when the file named by $STUB_GATE_FAIL_IF exists, then prints
the file $STUB_GATE_LOG; copies $STUB_GATE_MANIFEST to .lake/manifest-raw.json)."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent
INTEGRATION = "claude/zen-lovelace-rvlcw2"
TRAILER = "Co-Authored-By: Test <test@example.invalid>\nClaude-Session: test"

STUB_GATE = """#!/usr/bin/env bash
echo "== gate on $(git rev-parse HEAD)"
if [ -n "${STUB_GATE_MANIFEST:-}" ]; then
  mkdir -p .lake && cp "$STUB_GATE_MANIFEST" .lake/manifest-raw.json
fi
if [ -n "${STUB_GATE_FAIL_IF:-}" ] && [ -e "$STUB_GATE_FAIL_IF" ]; then
  [ -n "${STUB_GATE_LOG:-}" ] && cat "$STUB_GATE_LOG"
  echo "error: stub gate failed"; exit 1
fi
echo "== gate passed on $(git rev-parse HEAD)"
"""


class IntegrateTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        self.logs = Path(self.tmp.name) / "logs"
        self.repo.mkdir()
        self.env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e.invalid",
                        GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e.invalid",
                        GIT_EDITOR="true", INTEGRATE_TRAILER=TRAILER,
                        INTEGRATE_LOG_DIR=str(self.logs),
                        INTEGRATE_GATE_PATTERN="no-such-gate-process-" + os.urandom(4).hex())
        self.env.pop("STUB_GATE_FAIL_IF", None)
        self.git("init", "-q", "-b", INTEGRATION)
        (self.repo / "scripts").mkdir()
        for name in ("integrate.sh", "check_import_closure.py"):
            shutil.copy(SCRIPTS / name, self.repo / "scripts" / name)
        (self.repo / "scripts" / "gate.sh").write_text(STUB_GATE)
        (self.repo / "scripts" / "gate.sh").chmod(0o755)
        (self.repo / "PercLib").mkdir()
        self.write("PercLib/A.lean", "module\n\ndef a := 1\n")
        self.write("PercLib/M.lean", "module\n\ndef m := 1\n")
        self.write("PercLib.lean",
                   "module\n\npublic import PercLib.A\npublic import PercLib.M\n")
        self.commit_all("init")
        self.base = self.git("rev-parse", "HEAD")
        # the remote integration branch, for the transient-base check
        self.git("update-ref", f"refs/remotes/origin/{INTEGRATION}", self.base)

    def tearDown(self):
        self.tmp.cleanup()

    def git(self, *args):
        return subprocess.run(["git", *args], cwd=self.repo, env=self.env, check=True,
                              capture_output=True, text=True).stdout.strip()

    def write(self, rel, text):
        (self.repo / rel).write_text(text)

    def commit_all(self, msg):
        self.git("add", "-A")
        self.git("commit", "-q", "-m", msg)

    def branch(self, name, files, imports=()):
        """work/<name> off the base: new or changed files, and import lines appended
        after the last import of PercLib.lean (so two such branches conflict)."""
        self.git("checkout", "-q", "-b", f"work/{name}", self.base)
        for rel, text in files.items():
            self.write(rel, text)
        if imports:
            root = (self.repo / "PercLib.lean").read_text()
            self.write("PercLib.lean",
                       root + "".join(f"public import {m}\n" for m in imports))
        self.commit_all(f"{name} work")
        self.git("checkout", "-q", INTEGRATION)

    def integrate(self, *branches, **env):
        return subprocess.run(["bash", "scripts/integrate.sh", self.base, *branches],
                              cwd=self.repo, env=dict(self.env, **env),
                              capture_output=True, text=True)

    def root_imports(self):
        return [l for l in (self.repo / "PercLib.lean").read_text().splitlines()
                if l.startswith("public import")]

    def test_clean_merge_with_message_and_trailer(self):
        self.branch("x", {"PercLib/X.lean": "module\n"}, ["PercLib.X"])
        result = self.integrate("work/x", MSG_1="Merge work/x (one line)")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (1): work/x", result.stdout)
        self.assertIn("gate: == gate passed on", result.stdout)
        self.assertLessEqual(len(result.stdout.split("== integrate summary")[1].splitlines()), 20)
        msg = self.git("log", "-1", "--format=%B")
        self.assertTrue(msg.startswith("Merge work/x (one line)\n\nCo-Authored-By: Test"), msg)
        self.assertEqual(len(self.git("log", "-1", "--format=%P").split()), 2)

    def test_import_line_conflict_resolved(self):
        self.branch("x", {"PercLib/X.lean": "module\n"}, ["PercLib.X"])
        self.branch("b", {"PercLib/B.lean": "module\n"}, ["PercLib.B"])
        result = self.integrate("work/x", "work/b")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (2): work/x work/b", result.stdout)
        self.assertEqual(self.root_imports(), [
            "public import PercLib.A", "public import PercLib.B",
            "public import PercLib.M", "public import PercLib.X"])
        self.assertNotIn("<<<<<<<", (self.repo / "PercLib.lean").read_text())
        self.assertTrue(self.git("log", "-1", "--format=%B").startswith("Merge work/b\n\n"))

    def test_non_import_conflict_skipped_and_closure_import_added(self):
        self.branch("c", {"PercLib/A.lean": "module\n\ndef a := 2\n"})
        self.branch("d", {"PercLib/A.lean": "module\n\ndef a := 3\n"})
        self.branch("z", {"PercLib/C.lean": "module\n"})  # no import line
        result = self.integrate("work/c", "work/d", "work/z")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (2): work/c work/z; closure imports added: 1", result.stdout)
        self.assertIn("work/d: conflict in PercLib/A.lean", result.stdout)
        self.assertEqual((self.repo / "PercLib/A.lean").read_text(), "module\n\ndef a := 2\n")
        self.assertEqual(self.root_imports(), [
            "public import PercLib.A", "public import PercLib.C", "public import PercLib.M"])
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), "")

    def test_gate_failure_drops_last_branch(self):
        self.branch("x", {"PercLib/X.lean": "module\n"}, ["PercLib.X"])
        self.branch("bad", {"BAD": "x\n"})
        result = self.integrate("work/x", "work/bad", STUB_GATE_FAIL_IF="BAD")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("merged (1): work/x", result.stdout)
        self.assertIn("work/bad: dropped after gate failure", result.stdout)
        self.assertFalse((self.repo / "BAD").exists())
        self.assertEqual(len(list(self.logs.glob("gate-*.log"))), 2)

    def aux(self, name, text):
        path = Path(self.tmp.name) / name
        path.write_text(text)
        return str(path)

    def test_culprit_from_error_line(self):
        self.branch("bad", {"PercLib/Bad.lean": "module\n", "BAD": "x\n"})
        self.branch("x", {"PercLib/X.lean": "module\n"})
        self.branch("y", {"PercLib/Y.lean": "module\n"})
        log = self.aux("stub.log", "\u2716 [3/9] Building PercLib.Bad\n"
                       "error: PercLib/Bad.lean:3:7: unknown identifier 'foo'\n"
                       "error: build failed\n")
        result = self.integrate("work/bad", "work/x", "work/y",
                                STUB_GATE_FAIL_IF="BAD", STUB_GATE_LOG=log)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("integrate: dropping work/bad (culprit: PercLib/Bad.lean)", result.stdout)
        self.assertIn("merged (2): work/x work/y", result.stdout)
        self.assertIn("work/bad: dropped after gate failure, culprit PercLib/Bad.lean",
                      result.stdout)
        self.assertEqual(len(list(self.logs.glob("gate-*.log"))), 2)

    def test_culprit_from_d35_line(self):
        self.branch("bad", {"PercLib/Bad.lean": "module\n\ntheorem foo : True := trivial\n",
                            "BAD": "x\n"})
        self.branch("x", {"PercLib/X.lean": "module\n"})
        log = self.aux("stub.log", "FAIL (i) PercLib.Bad.foo: a binder has type the tagged "
                       "statement PercLib.T (ABCD)\nD-35 checks failed: 1 problem(s).\n")
        manifest = self.aux("manifest.json", json.dumps({"declarations": [
            {"name": "PercLib.Bad.foo", "module": "PercLib.Bad"},
            {"name": "PercLib.x", "module": "PercLib.X"}]}))
        result = self.integrate("work/bad", "work/x", STUB_GATE_FAIL_IF="BAD",
                                STUB_GATE_LOG=log, STUB_GATE_MANIFEST=manifest)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("integrate: dropping work/bad (culprit: PercLib/Bad.lean)", result.stdout)
        self.assertIn("merged (1): work/x", result.stdout)

    def test_culprit_from_d35_file_line(self):
        self.branch("bad", {"PercLib/Bad.lean": "module\n", "BAD": "x\n"})
        self.branch("x", {"PercLib/X.lean": "module\n"})
        log = self.aux("stub.log", "FAIL (v) PercLib/Bad.lean: no module docstring\n")
        result = self.integrate("work/bad", "work/x", STUB_GATE_FAIL_IF="BAD",
                                STUB_GATE_LOG=log)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("integrate: dropping work/bad (culprit: PercLib/Bad.lean)", result.stdout)

    def test_ambiguous_culprit_drops_last(self):
        self.branch("b1", {"PercLib/B1.lean": "module\n"})
        self.branch("b2", {"PercLib/B2.lean": "module\n", "BAD": "x\n"})
        log = self.aux("stub.log", "error: PercLib/B1.lean:1:0: oops\n"
                       "error: PercLib/B2.lean:1:0: oops\n")
        result = self.integrate("work/b1", "work/b2", STUB_GATE_FAIL_IF="BAD",
                                STUB_GATE_LOG=log)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn("integrate: dropping", result.stdout)
        self.assertIn("merged (1): work/b1", result.stdout)
        self.assertIn("work/b2: dropped after gate failure (log", result.stdout)

    def test_failing_file_no_branch_changed_drops_last(self):
        self.branch("bad", {"PercLib/Bad.lean": "module\n", "BAD": "x\n"})
        self.branch("x", {"PercLib/X.lean": "module\n"})
        log = self.aux("stub.log", "error: PercLib/Bad.lean:1:0: oops\n"
                       "error: PercLib/M.lean:1:0: downstream breakage\n")
        result = self.integrate("work/bad", "work/x", STUB_GATE_FAIL_IF="BAD",
                                STUB_GATE_LOG=log)
        self.assertNotIn("integrate: dropping", result.stdout)
        self.assertIn("work/x: dropped after gate failure (log", result.stdout)

    def test_refuses_branch_cut_from_transient_merge(self):
        self.write("PercLib/T.lean", "module\n")
        self.commit_all("transient integrate merge")  # local only, not on origin
        transient = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "-b", "work/late", transient)
        self.write("PercLib/L.lean", "module\n")
        self.commit_all("late work")
        self.git("checkout", "-q", INTEGRATION)
        result = self.integrate("work/late")
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("work/late was cut from", result.stderr)
        self.assertIn(f"not on origin/{INTEGRATION}", result.stderr)
        self.assertEqual(self.git("rev-parse", "HEAD"), transient)

    def test_gate_failure_with_no_branch_left_resets_to_tip(self):
        self.branch("bad", {"BAD": "x\n"})
        result = self.integrate("work/bad", STUB_GATE_FAIL_IF="BAD")
        self.assertEqual(result.returncode, 1)
        self.assertIn("no branch left", result.stdout)
        self.assertEqual(self.git("rev-parse", "HEAD"), self.base)

    def test_refuses_dirty_tree(self):
        self.write("PercLib/A.lean", "changed\n")
        result = self.integrate("work/x")
        self.assertEqual(result.returncode, 2)
        self.assertIn("dirty", result.stderr)

    def test_refuses_while_gate_runs(self):
        marker = self.env["INTEGRATE_GATE_PATTERN"]
        sleeper = subprocess.Popen(["bash", "-c", f"sleep 30; : {marker}"])
        try:
            result = self.integrate("work/x")
        finally:
            sleeper.kill()
            sleeper.wait()
        self.assertEqual(result.returncode, 2)
        self.assertIn("is running", result.stderr)


if __name__ == "__main__":
    unittest.main()
