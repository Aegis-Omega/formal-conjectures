#!/usr/bin/env python3
# Copyright 2026 The Formal Conjectures Authors.
# SPDX-License-Identifier: Apache-2.0
"""Read-only verification of real recovered CI oleans (NOT RH proof admission).

A genuine 314/317 recovered bundle is useful evidence, but must NOT pass
--require-complete. Only actual binary objects can satisfy the final gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
import zipfile

SOURCE_MANIFEST_BLOB = "214ecf7be2f62829a42a3991e2ccfddee5a6d7e5"
EXPECTED_COUNT = 317
SCHEMA = "aegis.rh.recovered_native_ci_olean_bundle.v1"
HEX64 = re.compile(r"[a-f0-9]{64}\Z")


def member_digest(archive: zipfile.ZipFile, name: str) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with archive.open(name, "r") as stream:
        while part := stream.read(1024 * 1024):
            digest.update(part)
            size += len(part)
    return digest.hexdigest(), size


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify_bundle(path: Path, *, manifest: Path | None = None,
                  require_complete: bool = False) -> dict:
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError("DUPLICATE_ZIP_MEMBERS")
        for name in names:
            posix = PurePosixPath(name)
            if (posix.is_absolute() or ".." in posix.parts or "\\" in name
                    or name.startswith("./") or name.endswith("/")):
                raise ValueError("UNSAFE_ZIP_MEMBER " + name)
        try:
            evidence = json.loads(archive.read("checkpoint_provenance.json"))
            hashes = archive.read("recovered_oleans.sha256").decode("ascii").splitlines()
        except (KeyError, UnicodeDecodeError) as exc:
            raise ValueError("MISSING_RECOVERY_MANIFEST") from exc
        if evidence.get("schema") != SCHEMA:
            raise ValueError("WRONG_RECOVERY_SCHEMA")
        if evidence.get("original_manifest_git_blob") != SOURCE_MANIFEST_BLOB:
            raise ValueError("SOURCE_MANIFEST_IDENTITY_MISMATCH")
        if evidence.get("expected_source_module_count") != EXPECTED_COUNT:
            raise ValueError("WRONG_SOURCE_MODULE_COUNT")
        binaries = evidence.get("binaries")
        missing = evidence.get("missing_binary_modules")
        if not isinstance(binaries, list) or not isinstance(missing, list):
            raise ValueError("MALFORMED_PROVENANCE")
        if not all(isinstance(x, str) and x for x in missing):
            raise ValueError("BAD_MISSING_MODULE_NAME")
        if len(missing) != len(set(missing)):
            raise ValueError("DUPLICATE_MISSING_MODULES")
        recorded_hashes = {}
        for line in hashes:
            match = re.fullmatch(
                r"([0-9a-f]{64})  (oleans/[A-Za-z0-9_/.-]+\.olean)", line)
            if not match:
                raise ValueError("INVALID_CHECKSUM_LINE")
            digest, name = match.groups()
            if name in recorded_hashes:
                raise ValueError("DUPLICATE_CHECKSUM_ENTRY")
            recorded_hashes[name] = digest
        actual_files = {name for name in names if name.endswith(".olean")}
        if actual_files != set(recorded_hashes):
            raise ValueError("OLEAN_CHECKSUM_FILE_SET_MISMATCH")
        declared = {}
        for entry in binaries:
            if not isinstance(entry, dict):
                raise ValueError("MALFORMED_BINARY_RECORD")
            module = entry.get("module")
            filename = entry.get("file")
            digest = entry.get("sha256")
            if not isinstance(module, str) or not re.fullmatch("[A-Za-z0-9_.]+", module):
                raise ValueError("INVALID_BINARY_MODULE")
            canonical = "oleans/" + module.replace(".", "/") + ".olean"
            if filename != canonical or module in declared:
                raise ValueError("DUPLICATE_OR_NONCANONICAL_MODULE")
            if not isinstance(digest, str) or not HEX64.fullmatch(digest):
                raise ValueError("INVALID_BINARY_SHA")
            if recorded_hashes.get(filename) != digest:
                raise ValueError("BINARY_CHECKSUM_METADATA_MISMATCH " + module)
            actual_digest, size = member_digest(archive, filename)
            if (actual_digest != digest or size == 0
                    or size != entry.get("size_bytes")):
                raise ValueError("BINARY_CONTENT_MISMATCH " + module)
            declared[module] = filename
        if set(declared.values()) != actual_files:
            raise ValueError("BINARY_PROVENANCE_FILE_SET_MISMATCH")
        if set(declared) & set(missing):
            raise ValueError("PRESENT_AND_MISSING_CONFLICT")
        if len(declared) + len(missing) != EXPECTED_COUNT:
            raise ValueError("UNACCOUNTED_SOURCE_MODULES")
        if evidence.get("recovered_binary_count") != len(declared):
            raise ValueError("RECOVERY_COUNT_MISMATCH")
        if manifest is not None:
            payload = manifest.read_bytes()
            if git_blob(payload) != SOURCE_MANIFEST_BLOB:
                raise ValueError("CURRENT_SOURCE_MANIFEST_DRIFT")
            rows = json.loads(payload)
            source_modules = [row["module"] for row in rows]
            if len(source_modules) != EXPECTED_COUNT or len(set(source_modules)) != EXPECTED_COUNT:
                raise ValueError("BAD_SOURCE_MANIFEST_MODULE_SET")
            if set(source_modules) != set(declared) | set(missing):
                raise ValueError("SOURCE_BINARY_CLOSURE_MISMATCH")
        extra = set(names) - actual_files - {
            "checkpoint_provenance.json", "recovered_oleans.sha256", "README.txt"}
        if extra:
            raise ValueError("UNDECLARED_ARCHIVE_CONTENT")
        with path.open("rb") as stream:
            archive_sha = hashlib.file_digest(stream, "sha256").hexdigest()
        result = {
            "schema": "aegis.rh.olean_recovery_verification.v1",
            "archive_sha256": archive_sha,
            "source_manifest_git_blob": SOURCE_MANIFEST_BLOB,
            "source_manifest_matched": manifest is not None,
            "historical_run": evidence.get("source_workflow_run_id"),
            "historical_exact_head": evidence.get("source_exact_head"),
            "expected_modules": EXPECTED_COUNT,
            "verified_binary_objects": len(declared),
            "missing_binary_modules": sorted(missing),
            "archive_integrity": "VERIFIED",
            "complete": len(declared) == EXPECTED_COUNT and not missing,
            "current_head_kernel_verification": "NOT_ASSESSED",
            "unconditional_RH": "NOT_ASSESSED",
        }
        if require_complete and not result["complete"]:
            raise ValueError(
                "INCOMPLETE_OLEAN_CHECKPOINT %d/%d" % (len(declared), EXPECTED_COUNT))
        return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        result = verify_bundle(
            args.archive, manifest=args.manifest,
            require_complete=args.require_complete)
    except (ValueError, OSError, zipfile.BadZipFile, KeyError,
            json.JSONDecodeError) as exc:
        print("FAILED", str(exc), file=sys.stderr)
        return 1
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload)
    print(payload, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
