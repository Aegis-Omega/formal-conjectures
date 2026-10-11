"""Offline exact-head source exporter tests. No Lean theorem or proof changes."""
import subprocess
import tempfile
import unittest
from pathlib import Path
from export_aegis_dendrite import snapshot


def git(repo, *args):
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], stderr=subprocess.DEVNULL,
    ).decode().strip()


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        git(self.repo, "init", "-q")
        self.path = "FormalConjectures/Millennium/RiemannHypothesis.lean"
        target = self.repo / self.path
        target.parent.mkdir(parents=True)
        target.write_text("theorem example : True := by sorry\n", encoding="utf-8")
        git(self.repo, "add", ".")
        git(self.repo, "-c", "user.name=Tester", "-c", "user.email=test@example.com",
            "commit", "-qm", "fixture")

    def test_exact_head(self):
        obj = snapshot(self.repo)
        self.assertEqual(obj["source_head"], git(self.repo, "rev-parse", "HEAD"))
        self.assertEqual(len(obj["source_record"]), 64)
        self.assertIn("PROOF NOT VERIFIED", obj["text"])
        self.assertLessEqual(len(obj["text"].encode()), 4096)

    def test_dirty_tree_not_reported_as_head(self):
        old = snapshot(self.repo)
        (self.repo / self.path).write_text("theorem example : False := by sorry\n")
        self.assertEqual(snapshot(self.repo), old)

    def test_path_traversal(self):
        with self.assertRaisesRegex(ValueError, "INVALID_PATH"):
            snapshot(self.repo, "../../etc/passwd")

    def test_unlisted_path(self):
        with self.assertRaisesRegex(ValueError, "INVALID_PATH"):
            snapshot(self.repo, ".github/secrets.lean")

    def test_quarantine(self):
        self.assertEqual(snapshot(self.repo, channel="QUARANTINE")["channel"], "QUARANTINE")

    def test_invalid_channel(self):
        with self.assertRaisesRegex(ValueError, "INVALID_CHANNEL"):
            snapshot(self.repo, channel="AUTHORIZED")

    def test_missing_file(self):
        with self.assertRaises(subprocess.CalledProcessError):
            snapshot(self.repo, "AegisRH/missing.lean")

    def test_deterministic_snapshot(self):
        self.assertEqual(snapshot(self.repo), snapshot(self.repo))


if __name__ == "__main__":
    unittest.main()
