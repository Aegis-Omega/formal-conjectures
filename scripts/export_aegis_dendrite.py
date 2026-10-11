"""Export HEAD-bound Lean source information for AEGIS dendrites, not an RH proof verdict.

The six-field JSON matches AEGIS agents.dendrite_system source ingress.
No theorem mutation, Lean execution, network, agent dispatch or authorization.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath

SHA = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})\Z")
ALLOWED = ("FormalConjectures/", "FormalConjecturesForMathlib/", "AegisRH/", "AEGISOverlay/")
DEFAULT = "FormalConjectures/Millennium/RiemannHypothesis.lean"
MAX_FILE = 1024 * 1024


def _git(repo: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", "-C", str(repo), *args],
        check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15,
    ).stdout


def snapshot(repo: Path, path: str = DEFAULT, channel: str = "CANDIDATE") -> dict:
    if not isinstance(path, str) or "\\" in path or "\x00" in path:
        raise ValueError("INVALID_PATH")
    clean = PurePosixPath(path)
    if (clean.is_absolute() or ".." in clean.parts or str(clean) != path
            or not path.endswith(".lean") or not path.startswith(ALLOWED)):
        raise ValueError("INVALID_PATH")
    if channel not in {"CANDIDATE", "QUARANTINE"}:
        raise ValueError("INVALID_CHANNEL")
    root = Path(_git(repo, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    sha = _git(root, "rev-parse", "--verify", "HEAD").decode().strip()
    if not SHA.fullmatch(sha):
        raise ValueError("INVALID_GIT_HEAD")
    object_size = int(_git(root, "cat-file", "-s", "HEAD:" + path))
    if not 0 < object_size <= MAX_FILE:
        raise ValueError("INVALID_LEAN_SOURCE_SIZE")
    raw = _git(root, "show", "HEAD:" + path)
    if len(raw) != object_size:
        raise ValueError("LEAN_SOURCE_SIZE_MISMATCH")
    content = raw.decode("utf-8", "strict")
    content_hash = hashlib.sha256(raw).hexdigest()
    prefix = (
        f"LEAN SOURCE ONLY — PROOF NOT VERIFIED; path={path}; "
        f"source_bytes_sha256={content_hash}; excerpt:\n"
    )
    if len(prefix.encode("utf-8")) >= 4000:
        raise ValueError("SOURCE_PREFIX_TOO_LARGE")
    allowance = 4000 - len(prefix.encode("utf-8"))
    excerpt = content.encode("utf-8")[:max(0, allowance)].decode("utf-8", "ignore")
    packet = {
        "source": "formal", "source_head": sha, "source_record": content_hash,
        "sequence": 0, "text": prefix + excerpt, "channel": channel,
    }
    # JSON escape expansion (e.g. Lean Unicode notation) can exceed the
    # AEGIS ingress 8192-byte limit even when original UTF-8 text is small.
    while len(json.dumps(packet, sort_keys=True, indent=2, ensure_ascii=True).encode("utf-8")) + 1 > 8192:
        if not excerpt:
            raise ValueError("ENCODED_RECORD_TOO_LARGE")
        excerpt = excerpt[:len(excerpt) // 2]
        packet["text"] = prefix + excerpt
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(description="Export Lean HEAD source to AEGIS informational dendrites")
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--path", default=DEFAULT)
    parser.add_argument("--channel", choices=("CANDIDATE", "QUARANTINE"), default="CANDIDATE")
    args = parser.parse_args()
    try:
        print(json.dumps(snapshot(args.repo, args.path, args.channel), sort_keys=True, indent=2))
    except (ValueError, UnicodeError, OSError, subprocess.SubprocessError) as exc:
        parser.error(f"source export denied: {type(exc).__name__}: {exc}")


if __name__ == "__main__":
    main()
