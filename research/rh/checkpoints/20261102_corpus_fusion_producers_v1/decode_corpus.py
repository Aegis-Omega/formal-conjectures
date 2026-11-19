#!/usr/bin/env python3
"""Restore the published source index; does not reconstruct or verify proofs."""
import gzip
import json
from pathlib import Path
import sqlite3
import sys

source = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("CORPUS_INDEX.json.gz")
target = Path(sys.argv[2]) if len(sys.argv) > 2 else Path("CORPUS_INDEX.sqlite")
if target.exists():
    raise FileExistsError("refusing to overwrite " + str(target))
with gzip.open(source, "rt") as stream:
    data = json.load(stream)
if data["schema"] != "AEGIS_CORPUS_LOSSLESS_DELTA_INDEX_V1":
    raise ValueError("unsupported index schema")
db = sqlite3.connect(target)
db.execute("CREATE TABLE files(commit_sha TEXT,path TEXT,blob TEXT,kind TEXT,PRIMARY KEY(commit_sha,path))")
db.execute("CREATE TABLE refs(repo TEXT,ref TEXT,commit_sha TEXT)")
entries = data["entries"]
previous = set()
previous_sha = None
count = 0
for row in data["snapshots"]:
    if "full" in row:
        current = set(row["full"])
    else:
        if row["base"] != previous_sha:
            raise ValueError("unexpected snapshot base")
        current = (previous - set(row["remove"])) | set(row["add"])
    if len(current) != row["count"]:
        raise ValueError("snapshot membership count mismatch")
    db.executemany("INSERT INTO files VALUES (?,?,?,?)",
                   ((row["commit"], *entries[i]) for i in sorted(current)))
    count += len(current)
    previous, previous_sha = current, row["commit"]
db.executemany("INSERT INTO refs VALUES (?,?,?)", data["refs"])
if count != data["source_file_occurrences"]:
    raise ValueError("total membership count mismatch")
db.execute("CREATE INDEX blobs ON files(blob)")
db.commit()
db.close()
print(json.dumps({"restored_source_occurrences": count,
                  "snapshots": len(data["snapshots"]), "semantic_audit": False,
                  "rh_proven": False}))
