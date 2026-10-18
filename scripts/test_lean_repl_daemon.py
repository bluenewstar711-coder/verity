#!/usr/bin/env python3
"""Unit tests for scripts/lean_repl_daemon.py using a mock REPL process."""

from __future__ import annotations

import contextlib
import io
import json
import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import lean_repl_daemon


MOCK_REPL_CODE = """#!/usr/bin/env python3
import json
import sys
import time

env_counter = 0
lines = []
for line in sys.stdin:
    if line in ("\\n", "\\r\\n"):
        if not lines:
            continue
        req = json.loads("".join(lines))
        lines = []
        cmd = req.get("cmd", "")
        if "HANG_HERE" in cmd:
            time.sleep(3600)
        messages = []
        if "FAIL_HERE" in cmd:
            messages.append({"severity": "error", "data": "synthetic error"})
        resp = {
            "env": env_counter,
            "messages": messages,
            "received_env": req.get("env"),
            "received_cmd": cmd,
        }
        env_counter += 1
        sys.stdout.write(json.dumps(resp) + "\\n\\n")
        sys.stdout.flush()
    else:
        lines.append(line)
"""

DECL_SAMPLE = """import Std

namespace Demo

theorem first : 1 = 1 := rfl

/-- Docstring
spanning lines. -/
@[simp]
set_option maxHeartbeats 400000 in
theorem target_lemma {n : Nat}
    (h : n = n) :
    n + 0 = n := by
  simp

def recursive : Nat → Nat
  | 0 => 0
  | n + 1 => recursive n
termination_by n => n

/-- One-line doc. -/ theorem after : True := trivial

end Demo
"""


class LocateDeclarationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.sample = Path(self.tempdir.name) / "Decls.lean"
        self.sample.write_text(DECL_SAMPLE, encoding="utf-8")

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def test_range_includes_doc_attrs_and_set_option_prefix(self) -> None:
        self.assertEqual(lean_repl_daemon.locate_declaration(self.sample, "target_lemma"), (7, 14))

    def test_range_keeps_column_zero_continuations(self) -> None:
        self.assertEqual(lean_repl_daemon.locate_declaration(self.sample, "recursive"), (16, 19))

    def test_qualified_and_single_line_declarations(self) -> None:
        self.assertEqual(lean_repl_daemon.locate_declaration(self.sample, "Demo.first"), (5, 5))
        self.assertEqual(lean_repl_daemon.locate_declaration(self.sample, "first"), (5, 5))

    def test_missing_and_ambiguous_names_raise(self) -> None:
        with self.assertRaises(LookupError):
            lean_repl_daemon.locate_declaration(self.sample, "absent")
        self.sample.write_text(DECL_SAMPLE + "theorem first : 2 = 2 := rfl\n", encoding="utf-8")
        with self.assertRaises(LookupError):
            lean_repl_daemon.locate_declaration(self.sample, "first")

    def test_locate_cli_reports_until_line(self) -> None:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            rc = lean_repl_daemon.main(
                ["locate", "--file", str(self.sample), "--decl", "target_lemma"]
            )
        self.assertEqual(rc, 0)
        self.assertEqual(
            json.loads(out.getvalue()),
            {"decl": "target_lemma", "start_line": 7, "end_line": 14, "until_line": 6},
        )

    def test_unknown_decl_exits_nonzero_without_traceback(self) -> None:
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            rc = lean_repl_daemon.main(["locate", "--file", str(self.sample), "--decl", "absent"])
        self.assertEqual(rc, 2)
        self.assertIn("not found", err.getvalue())


class DefaultSocketTests(unittest.TestCase):
    def test_socket_is_per_worktree_and_overridable(self) -> None:
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop("VERITY_LEAN_REPL_SOCKET", None)
            first = lean_repl_daemon.default_socket_path(Path("/tmp/worktree-a"))
            second = lean_repl_daemon.default_socket_path(Path("/tmp/worktree-b"))
            self.assertNotEqual(first, second)
            self.assertTrue(first.startswith("/tmp/verity-lean-repl-"))
        with mock.patch.dict(os.environ, {"VERITY_LEAN_REPL_SOCKET": "/tmp/custom.sock"}):
            self.assertEqual(
                lean_repl_daemon.default_socket_path(Path("/tmp/worktree-a")), "/tmp/custom.sock"
            )


class LeanReplDaemonTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.root = Path(self.tempdir.name)
        self.socket_path = self.root / "repl.sock"
        self.mock_repl = self.root / "mock_repl.py"
        self.mock_repl.write_text(MOCK_REPL_CODE, encoding="utf-8")
        self.mock_repl.chmod(self.mock_repl.stat().st_mode | stat.S_IEXEC)

    def tearDown(self) -> None:
        try:
            lean_repl_daemon.main(["stop", "--socket", str(self.socket_path)])
        except Exception:
            pass
        self.tempdir.cleanup()

    def test_extract_import_header_and_slice(self) -> None:
        sample = self.root / "Sample.lean"
        sample.write_text(
            "/- Outer /-\n   inner -/\n   still comment -/\nimport Std\nopen Classical\n\ndef foo : Nat := 1\ntheorem bar : foo = 1 := rfl\n",
            encoding="utf-8",
        )
        header = lean_repl_daemon.extract_import_header(sample, None)
        self.assertIn("import Std\nopen Classical", header)
        self.assertNotIn("def foo", header)
        sliced = lean_repl_daemon.extract_file_slice(sample, 7, 8)
        self.assertIn("def foo : Nat := 1", sliced)
        self.assertIn("theorem bar : foo = 1 := rfl", sliced)

    def test_persistent_daemon_preserves_header_env_across_invocations(self) -> None:
        sample = self.root / "Sample.lean"
        sample.write_text(
            "import Std\nopen Classical\n\ndef foo : Nat := 1\ntheorem bar : foo = 1 := rfl\n",
            encoding="utf-8",
        )
        rc = lean_repl_daemon.main(
            [
                "start",
                "--socket",
                str(self.socket_path),
                "--repl-bin",
                str(self.mock_repl),
                "--cwd",
                str(self.root),
                "--no-lake-env",
            ]
        )
        self.assertEqual(rc, 0)

        rc_header = lean_repl_daemon.main(
            [
                "load-header",
                "--socket",
                str(self.socket_path),
                "--file",
                str(sample),
                "--until-line",
                "2",
            ]
        )
        self.assertEqual(rc_header, 0)

        status = lean_repl_daemon.request_daemon(self.socket_path, {"action": "status"})
        self.assertEqual(status["header_env"], 0)

        rc_check = lean_repl_daemon.main(
            [
                "check",
                "--socket",
                str(self.socket_path),
                "--file",
                str(sample),
                "--start-line",
                "4",
                "--end-line",
                "5",
            ]
        )
        self.assertEqual(rc_check, 0)

        sample.write_text(
            "import Std\nopen Classical\n\ndef foo : Nat := FAIL_HERE\n",
            encoding="utf-8",
        )
        rc_fail = lean_repl_daemon.main(
            [
                "check",
                "--socket",
                str(self.socket_path),
                "--file",
                str(sample),
                "--start-line",
                "4",
                "--end-line",
                "4",
            ]
        )
        self.assertEqual(rc_fail, 1)

    def _start_mock_daemon(self) -> None:
        rc = lean_repl_daemon.main(
            [
                "start",
                "--socket",
                str(self.socket_path),
                "--repl-bin",
                str(self.mock_repl),
                "--cwd",
                str(self.root),
                "--no-lake-env",
            ]
        )
        self.assertEqual(rc, 0)

    def _run(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            rc = lean_repl_daemon.main(argv)
        return rc, out.getvalue(), err.getvalue()

    def test_before_decl_header_and_decl_check_send_only_the_edited_lines(self) -> None:
        sample = self.root / "Decls.lean"
        sample.write_text(DECL_SAMPLE, encoding="utf-8")
        self._start_mock_daemon()
        sock = ["--socket", str(self.socket_path), "--file", str(sample)]

        rc, out, err = self._run(["load-header", *sock, "--before-decl", "target_lemma"])
        self.assertEqual(rc, 0)
        self.assertEqual(err, "")
        lines = DECL_SAMPLE.splitlines()
        self.assertEqual(json.loads(out)["received_cmd"], "\n".join(lines[:6]))

        rc, out, err = self._run(["check", *sock, "--decl", "target_lemma"])
        self.assertEqual(rc, 0)
        self.assertEqual(err, "")
        resp = json.loads(out)
        self.assertEqual(resp["received_cmd"], "\n".join(lines[6:14]))
        self.assertEqual(resp["received_env"], 0)

    def test_unbounded_header_and_check_print_advice(self) -> None:
        sample = self.root / "Decls.lean"
        sample.write_text(DECL_SAMPLE, encoding="utf-8")
        self._start_mock_daemon()
        sock = ["--socket", str(self.socket_path), "--file", str(sample)]

        rc, _, err = self._run(["load-header", *sock])
        self.assertEqual(rc, 0)
        self.assertIn("--until-line <first_edited_decl - 1>", err)

        rc, _, err = self._run(["check", *sock, "--start-line", "5"])
        self.assertEqual(rc, 0)
        self.assertIn("through EOF", err)

        rc, _, err = self._run(["check", *sock, "--decl", "first", "--start-line", "5"])
        self.assertEqual(rc, 2)
        self.assertIn("not both", err)

    def test_runaway_request_restarts_repl_instead_of_wedging(self) -> None:
        self._start_mock_daemon()
        sample = self.root / "Decls.lean"
        sample.write_text(DECL_SAMPLE, encoding="utf-8")
        sock = ["--socket", str(self.socket_path)]
        rc, _, _ = self._run(["load-header", *sock, "--file", str(sample), "--until-line", "4"])
        self.assertEqual(rc, 0)
        before = lean_repl_daemon.request_daemon(self.socket_path, {"action": "status"})

        hung = lean_repl_daemon.request_daemon(
            self.socket_path,
            {"action": "send", "payload": {"cmd": "HANG_HERE"}},
            timeout=1.0,
        )
        self.assertTrue(hung.get("restarted"))
        self.assertIn("Re-run `load-header`", hung["error"])

        after = lean_repl_daemon.request_daemon(self.socket_path, {"action": "status"})
        self.assertTrue(after["ok"])
        self.assertIsNone(after["header_env"])
        self.assertNotEqual(after["repl_pid"], before["repl_pid"])
        rc, out, _ = self._run(["send", *sock, "--cmd", "def ok : Nat := 1"])
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["received_cmd"], "def ok : Nat := 1")

    def test_restart_frees_envs_and_reports_rss(self) -> None:
        self._start_mock_daemon()
        sample = self.root / "Decls.lean"
        sample.write_text(DECL_SAMPLE, encoding="utf-8")
        sock = ["--socket", str(self.socket_path)]
        rc, _, _ = self._run(["load-header", *sock, "--file", str(sample), "--until-line", "4"])
        self.assertEqual(rc, 0)
        before = lean_repl_daemon.request_daemon(self.socket_path, {"action": "status"})
        self.assertIsInstance(before["repl_rss_mb"], int)

        rc, _, _ = self._run(["restart", *sock])
        self.assertEqual(rc, 0)
        after = lean_repl_daemon.request_daemon(self.socket_path, {"action": "status"})
        self.assertIsNone(after["header_env"])
        self.assertNotEqual(after["repl_pid"], before["repl_pid"])

    def test_start_refuses_daemon_serving_another_worktree(self) -> None:
        self._start_mock_daemon()
        other = self.root / "other-worktree"
        other.mkdir()
        rc, _, err = self._run(
            [
                "start",
                "--socket",
                str(self.socket_path),
                "--repl-bin",
                str(self.mock_repl),
                "--cwd",
                str(other),
                "--no-lake-env",
            ]
        )
        self.assertEqual(rc, 1)
        self.assertIn("pass a distinct --socket", err)


if __name__ == "__main__":
    unittest.main()
