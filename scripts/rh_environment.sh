#!/usr/bin/env bash
# Source-bound, no-paid-service Lean/Mathlib environment bootstrap for AEGIS RH.
# Reuses an existing exact-head repository checkout and its existing build plan.
set -Eeuo pipefail

LEAN_VERSION=4.33.1
LEAN_TOOLCHAIN='leanprover/lean4:v4.33.1'
MATHLIB_SHA='0df444a360eaa60ab8c11dca51a86af692955474'
LEAN_ARCHIVE_SHA='890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235'
LEAN_ARCHIVE_URL='https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst'
HERE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO="${AEGIS_RH_CHECKOUT:-$(cd "$HERE/.." && pwd)}"
CACHE="${AEGIS_RH_CACHE:-${XDG_CACHE_HOME:-$HOME/.cache}/aegis-rh}"
MODE="${1:---install}"

fail() { printf 'AEGIS_RH_ENV=BLOCKED code=%s detail=%s\n' "$1" "$2" >&2; exit 2; }
command -v git >/dev/null || fail GIT_MISSING 'Install git or use existing repository tools.'
command -v python3 >/dev/null || fail PYTHON_MISSING 'Python 3 required for pinned manifest audit.'
[[ -f "$REPO/lean-toolchain" && -f "$REPO/lake-manifest.json" ]] ||
  fail CHECKOUT_MISSING 'AEGIS_RH_CHECKOUT must point to existing formal-conjectures checkout.'
actual_head="$(git -C "$REPO" rev-parse --verify HEAD 2>/dev/null)" ||
  fail CHECKOUT_NOT_GIT 'No exact-head git checkout available.'
if [[ -n "${AEGIS_RH_EXPECTED_HEAD:-}" && "$actual_head" != "$AEGIS_RH_EXPECTED_HEAD" ]]; then
  fail HEAD_DRIFT "$actual_head is not $AEGIS_RH_EXPECTED_HEAD"
fi
[[ "$(cat "$REPO/lean-toolchain")" == "$LEAN_TOOLCHAIN" ]] ||
  fail TOOLCHAIN_PIN_DRIFT "lean-toolchain changed at $actual_head"
python3 - "$REPO/lake-manifest.json" "$MATHLIB_SHA" <<'PY' || fail MATHLIB_PIN_DRIFT 'Exact Mathlib revision not pinned.'
import json, sys
manifest = json.load(open(sys.argv[1], encoding='utf-8'))
mathlib = [p for p in manifest.get('packages', []) if p.get('name') == 'mathlib']
assert len(mathlib) == 1 and mathlib[0].get('rev') == sys.argv[2]
PY
printf 'AEGIS_RH_SOURCE_HEAD=%s\n' "$actual_head"
printf 'AEGIS_RH_PINS=VERIFIED lean=%s mathlib=%s\n' "$LEAN_VERSION" "$MATHLIB_SHA"

# Do not fetch, modify sources, or create GitHub work in read-only status mode.
LEAN_BIN=''
LAKE_BIN=''
if [[ -x "$CACHE/toolchains/lean-$LEAN_VERSION-linux/bin/lean" ]]; then
  LEAN_BIN="$CACHE/toolchains/lean-$LEAN_VERSION-linux/bin/lean"
  LAKE_BIN="$CACHE/toolchains/lean-$LEAN_VERSION-linux/bin/lake"
elif command -v lean >/dev/null 2>&1 && command -v lake >/dev/null 2>&1; then
  LEAN_BIN="$(command -v lean)"
  LAKE_BIN="$(command -v lake)"
fi
if [[ "$MODE" == '--status' ]]; then
  if [[ -z "$LEAN_BIN" ]] || [[ "$($LEAN_BIN --version 2>/dev/null)" != *'version 4.33.1'* ]]; then
    printf 'AEGIS_RH_TOOLCHAIN=MISSING\nAEGIS_RH_ENV=BLOCKED\n'; exit 2
  fi
  printf 'AEGIS_RH_TOOLCHAIN=VERIFIED path=%s\n' "$LEAN_BIN"
  if [[ "$(git -C "$REPO/.lake/packages/mathlib" rev-parse HEAD 2>/dev/null || :)" != "$MATHLIB_SHA" ]]; then
    printf 'AEGIS_RH_MATHLIB=NOT_RESTORED\nAEGIS_RH_ENV=BLOCKED\n'; exit 2
  fi
  [[ -x "$LAKE_BIN" ]] || fail LAKE_MISSING 'Lake binary is missing.'
  # Avoid a false-green status when the source checkout exists but its
  # compiled imports are absent or incompatible with the pinned compiler.
  export PATH="$(dirname "$LEAN_BIN"):$PATH"
  smoke="$(mktemp "${TMPDIR:-/tmp}/aegis-rh-status.XXXXXX.lean")"
  trap 'rm -f "$smoke"' EXIT
  printf 'import Mathlib\nexample : True := by trivial\n' > "$smoke"
  if ! (cd "$REPO" && lake env lean --trust=0 "$smoke"); then
    fail MATHLIB_KERNEL_SMOKE_FAILED 'Mathlib source is pinned but cannot be imported by the Lean kernel.'
  fi
  rm -f "$smoke"
  trap - EXIT
  printf 'AEGIS_RH_MATHLIB=KERNEL_SMOKE_PASS\nAEGIS_RH_ENV=SOURCE_BOUND_READY\n'; exit 0
fi
[[ "$MODE" == '--install' ]] || fail BAD_ARGUMENT 'Use --status or --install.'

# Reuse existing verified binaries first. If missing, use a local release archive
# or fetch the official archive, *before* unpacking and verifying the digest.
if [[ -z "$LEAN_BIN" ]] || [[ "$($LEAN_BIN --version 2>/dev/null || :)" != *'version 4.33.1'* ]]; then
  command -v sha256sum >/dev/null || fail SHA256_MISSING 'sha256sum required.'
  command -v tar >/dev/null || fail TAR_MISSING 'tar required.'
  command -v zstd >/dev/null || fail ZSTD_MISSING 'zstd required for official release archive.'
  mkdir -p "$CACHE/downloads" "$CACHE/toolchains"
  archive="${AEGIS_LEAN_ARCHIVE:-$CACHE/downloads/lean-$LEAN_VERSION-linux.tar.zst}"
  if [[ ! -f "$archive" ]]; then
    [[ -z "${AEGIS_LEAN_ARCHIVE:-}" ]] || fail ARCHIVE_MISSING "$archive"
    command -v curl >/dev/null || fail CURL_MISSING 'curl or a verified offline release archive is required.'
    download_tmp="$archive.partial.$$"
    trap 'rm -f "$download_tmp"' EXIT
    if ! curl --fail --location --retry 2 --connect-timeout 15 --max-time 900 \
      --output "$download_tmp" "$LEAN_ARCHIVE_URL"; then
      fail NETWORK_UNAVAILABLE 'No internet to download official Lean; use AEGIS_LEAN_ARCHIVE with the verified release archive.'
    fi
    actual_digest="$(sha256sum "$download_tmp" | cut -d ' ' -f 1)"
    [[ "$actual_digest" == "$LEAN_ARCHIVE_SHA" ]] || fail ARCHIVE_HASH_MISMATCH "$actual_digest"
    mv "$download_tmp" "$archive"
    trap - EXIT
  fi
  actual_digest="$(sha256sum "$archive" | cut -d ' ' -f 1)"
  [[ "$actual_digest" == "$LEAN_ARCHIVE_SHA" ]] || fail ARCHIVE_HASH_MISMATCH "$actual_digest"
  if [[ ! -x "$CACHE/toolchains/lean-$LEAN_VERSION-linux/bin/lean" ]]; then
    # The official archive contains exactly the lean-4.33.1-linux directory.
    tar --zstd --extract --file "$archive" --directory "$CACHE/toolchains"
  fi
  LEAN_BIN="$CACHE/toolchains/lean-$LEAN_VERSION-linux/bin/lean"
  LAKE_BIN="$CACHE/toolchains/lean-$LEAN_VERSION-linux/bin/lake"
fi
[[ -x "$LEAN_BIN" && -x "$LAKE_BIN" ]] || fail EXECUTABLE_MISSING 'Lean or Lake binary absent after restoration.'
[[ "$($LEAN_BIN --version)" == *'version 4.33.1'* ]] || fail WRONG_LEAN_VERSION "$($LEAN_BIN --version)"
export PATH="$(dirname "$LEAN_BIN"):$PATH"
printf 'AEGIS_RH_TOOLCHAIN=VERIFIED %s\n' "$(lean --version)"

cd "$REPO"
# Reuse existing package store and Mathlib compiled cache; never silently
# substitute a different version for a successful dependency resolution.
if [[ "$(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || :)" != "$MATHLIB_SHA" ]]; then
  lake update || fail MATHLIB_DOWNLOAD_FAILED 'Cannot restore package sources; cache/checkouts are preserved.'
fi
[[ "$(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || :)" == "$MATHLIB_SHA" ]] ||
  fail MATHLIB_SHA_MISMATCH 'Lake resolved unexpected mathlib revision.'
# Check the actual Mathlib import before asking the network for cache data.
# This preserves a previously-green local olean closure when offline.
smoke="$(mktemp "${TMPDIR:-/tmp}/aegis-rh-smoke.XXXXXX.lean")"
trap 'rm -f "$smoke"' EXIT
printf 'import Mathlib\nexample : True := by trivial\n' > "$smoke"
if ! lake env lean --trust=0 "$smoke"; then
  lake exe cache get || fail MATHLIB_OLEAN_RESTORE_FAILED 'Mathlib compiled cache fetch failed; preserved prior checkpoints.'
  lake env lean --trust=0 "$smoke" || fail MATHLIB_KERNEL_SMOKE_FAILED 'Actual Mathlib import/kernel smoke failed.'
fi
rm -f "$smoke"
trap - EXIT
printf 'AEGIS_RH_MATHLIB=KERNEL_SMOKE_PASS sha=%s\n' "$MATHLIB_SHA"
printf 'AEGIS_RH_ENV=SOURCE_BOUND_READY head=%s\n' "$actual_head"
