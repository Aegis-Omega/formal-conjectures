#!/usr/bin/env bash
# One-command build of the AEGIS RH Weil chain: the 186 modules of the PR92 eleven-kernel packet,
# 13 checkpoint modules and one check module, against Lean 4.33.1 + Mathlib 0df444a3.
set -euo pipefail
cd "$(dirname "$0")"
ZDIR=../checkpoints/20261110_independent_eleven_analytic_closure_v1
ZIP=AEGIS_PR92_Independent_Eleven_Kernel_20261110.zip
(cd "$ZDIR" && sha256sum -c "$ZIP.sha256")
[ -d .pr92 ] || unzip -q "$ZDIR/$ZIP" -d .pr92
(cd .pr92/AEGIS_PR92_Independent_Eleven_Kernel_20261110 && grep '  closure/' SHA256SUMS | sha256sum -c --quiet)
sha256sum -c --quiet SHA256SUMS
echo "sources verified: 186 closure + 14 modules"
if [ "${1:-}" != "--no-cache" ]; then lake exe cache get; fi
lake build
