#!/usr/bin/env bash
# Regenerate the 69 generated Lean modules of the window 31/20, the 8 derived scripts and the diagonal
# data into OUT and check them against generated.sha256. Run from this directory; REPO is a checkout
# of the PR branch. The row-certificate stage reads rr/rr43_data.pkl and rr/cert43_80.pkl (README).
# usage: bash regen.sh REPO OUT
set -euo pipefail
REPO=$(realpath "$1"); OUT=$(realpath -m "$2"); C=$REPO/research/rh/checkpoints; H=$(pwd)
S=$OUT/scripts; M=$OUT/modules; mkdir -p "$S" "$M" "$OUT/emit"
# derived scripts
python3 make_gen_cert3120.py "$C/20261031_window_l118/gen_cert118.py" > "$S/gen_cert3120.py"
python3 make_diag_ports3120.py "$C/20261111_window_l32_diagonal_v1" "$S"
python3 "$S/make_gen_diag3120.py" "$REPO" "$S"
python3 make_tau_gen3120.py "$C/20261111_window_l32_tau_v1" "$S"
(cd rr && python3 make_emit_rr3120.py "$REPO" > "$S/emit_rr3120.py")
# trace, tau, diagonal
python3 port_trace_l3120.py "$REPO" "$M"
python3 "$S/gen_cert3120.py" "$M/CvSTraceCertL3120V1.lean" cert3120_totals.json
python3 port_tau_l3120.py "$REPO" "$M"
python3 make_node3120.py "$C/20261111_window_l32_diagonal_v1/CvSNodeL32V1.lean" "$M/CvSNodeL3120V1.lean"
python3 "$S/gen_diag3120.py" 300 157 > "$OUT/diag3120_data.txt"
python3 "$S/port_diag_l3120.py" "$REPO" "$M" "$OUT/diag3120_data.txt" 300 157 8
python3 make_taufast3120.py "$C/20261111_window_l32_tau_v1/CvSTauFastL32V1.lean" "$M/CvSTauFastL3120V1.lean"
cp "$M/CvSNodeL3120V1.lean" "$S/"   # build_tau3120.py and assemble_tau3120.py read its licence header
for s in $(seq 1 50 1951); do python3 "$S/build_tau3120.py" "$s" $((s + 49)) "$M"; done
python3 "$S/assemble_tau3120.py" "$M"
python3 make_taufar3120.py "$C/20261112_window_l32_rowcert_v1/CvSTauFarL32V1.lean" "$M/CvSTauFarL3120V1.lean"
# row certificate
(cd rr && python3 "$S/emit_rr3120.py" "$OUT/emit")
python3 rr/chunk_data3120.py "$OUT/emit/CvSRelRowDataL3120V1.lean" "$M/CvSRelRowDataL3120V1.lean"
python3 rr/split_dataA3120.py "$M"
python3 rr/fast_tq3120.py "$M" apply
python3 rr/chunk_h3120.py "$M/CvSRelRowDataL3120V1.lean"
cp "$OUT/emit/CvSRelRowCertL3120V1.lean" "$M/"
for X in Form Box Err Q Kt Out Tail Inv In HB; do python3 rr/port_mod3120.py "$REPO" "$M" "$X"; done
python3 rr/chunk_box3120.py "$M/CvSRelRowBoxL3120V1.lean"
python3 rr/make_rr3120_check.py "$REPO" "$M"
python3 rr/fast_hq3120.py "$M"
# window and exhaustion
python3 make_window3120.py "$C/20261112_window_l32_v1" "$M"
cd "$OUT" && sha256sum -c --quiet "$H/generated.sha256" && echo "regen: all $(wc -l < "$H/generated.sha256") files match"
