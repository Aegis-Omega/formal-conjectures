# Formal source → AEGIS dendrite informational handoff

This script exports a **Git HEAD-bound Lean source snapshot**, not a proof certificate.
It neither modifies theorem statements nor runs Lean; a compile with `sorry`
cannot establish the Riemann Hypothesis.

From this repo (on a checked-out exact commit):

```sh
python3 scripts/export_aegis_dendrite.py --repo . > /tmp/formal_dendrite_source.json
python3 -m unittest discover -s scripts -p 'test_export_aegis_dendrite.py' -v
```

The JSON has the exact six-field `agents.dendrite_system.from_source_record`
ingress format: `source=formal`, Git HEAD SHA, SHA-256 of the Lean source
bytes read from `git show HEAD:path`, sequence 0, an explicitly
**UNVERIFIED** source excerpt, and a channel. Uncommitted worktree changes
are not misrepresented as HEAD content.

In the AEGIS-OMEGA candidate branch from [PR #773](https://github.com/Aegis-Omega/AEGIS-OMEGA/pull/773):

```sh
python3 -m agents.dendrite_system /tmp/formal_dendrite_source.json
```

This produces a read-only, in-memory routing receipt for the existing
applied_science, engineering, AI research and security nodes. For unverified
or unsafe content, use `--channel QUARANTINE` to restrict fan-out.
**No live agent receives a message, and no theorem is proved by this export.**

Trust boundary: Git SHA and source-byte digest are consistency metadata, not
authenticated third-party attestations. Files larger than 1 MiB, unexpected
paths, missing sources and invalid channels fail closed. No network,
secrets, payments, job execution or governance authority is involved.

The existing Lean pin, official RH target, test gates, and all proofs remain unchanged.
