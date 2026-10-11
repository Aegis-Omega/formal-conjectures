# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#     https://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""Fail closed if the slow RH consolidated CI path filter drifts from its source manifest.

Uses stdlib only, so this checks the trigger in the inexpensive `Test scripts` CI job.
"""
import json
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "research/rh/consolidated_v1/manifest.json"
WORKFLOW = ROOT / ".github/workflows/rh-consolidated-v1.yml"
ARCHIVE_ROOT = "research/rh/consolidated_v1/**"


def manifest_triggers(entries):
    if not isinstance(entries, list) or not entries:
        raise ValueError("Manifest must be a nonempty list")
    tracked = set()
    for entry in entries:
        path = entry["path"]
        if not isinstance(path, str) or not path:
            raise ValueError("Manifest has an invalid path")
        if path.startswith(".li/") or path.startswith("research/rh/consolidated_v1/"):
            continue
        tracked.add(path)
    return [ARCHIVE_ROOT, *sorted(tracked)]


def workflow_triggers(source):
    try:
        section = source.split("\n  pull_request:\n", 1)[1]
        if "\n  workflow_dispatch:" not in section:
            raise ValueError("Missing workflow_dispatch")
        section = section.split("\n  workflow_dispatch:", 1)[0]
        parts = re.split(r"(?:^|\n)    paths:\n", section, maxsplit=1)
        if len(parts) != 2:
            raise ValueError("Missing pull_request.paths")
        entries = parts[1]
    except IndexError as e:
        raise ValueError("Missing pull_request.paths or manual workflow_dispatch") from e
    paths = []
    for line in entries.splitlines():
        match = re.fullmatch(r"      - '([^']+)'", line)
        if match:
            paths.append(match.group(1))
        elif line.strip() and not line.lstrip().startswith("#"):
            raise ValueError(f"Unexpected workflow path-filter line: {line!r}")
    if len(paths) != len(set(paths)):
        raise ValueError("Duplicate consolidated CI paths")
    return paths


class RHConsolidatedManifestTriggerTests(unittest.TestCase):
    def test_paths_are_exactly_manifest_dependencies(self):
        expected = manifest_triggers(json.loads(MANIFEST.read_text(encoding="utf-8")))
        actual = workflow_triggers(WORKFLOW.read_text(encoding="utf-8"))
        self.assertEqual(actual, expected)

    def test_rejects_untracked_overlay_and_duplicate_filters(self):
        self.assertEqual(manifest_triggers([{"path": "AEGISOverlay/RHFoo.lean"}]),
                         [ARCHIVE_ROOT, "AEGISOverlay/RHFoo.lean"])
        self.assertNotIn("AEGISOverlay/**", manifest_triggers([{"path": "AEGISOverlay/RHFoo.lean"}]))
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            workflow_triggers("\n  pull_request:\n    paths:\n      - 'x'\n      - 'x'\n  workflow_dispatch:\n")

    def test_rejects_missing_manual_dispatch(self):
        with self.assertRaisesRegex(ValueError, "Missing"):
            workflow_triggers("\n  pull_request:\n    paths:\n      - 'x'\n")


if __name__ == "__main__":
    unittest.main()
