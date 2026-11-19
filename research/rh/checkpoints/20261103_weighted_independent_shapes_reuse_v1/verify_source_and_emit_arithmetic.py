"""Reuse the pinned eleven-lattice data; no weight optimization or Lean import.

Outputs a finite exact arithmetic certificate. Its interpretation in the
actual Weil form is supplied by WEIGHTED_SHAPE_COMPOSITION.md, not by this
program or by a successful exit code.
"""
from fractions import Fraction
from pathlib import Path
from math import lcm
import hashlib
import json
import re
import argparse

ROOT = Path(__file__).resolve().parent
SOURCE = Path('/workspace/aegis-replay-20261103/AEGISOverlay/RHActualElevenLatticeV1.lean')
EXPECTED_BLOB = '97a98db382e433488ed20f7df0980f41b20e4cbc'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=SOURCE,
                        help='Exact RHActualElevenLatticeV1.lean source file')
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    raw = args.source.read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    require(blob == EXPECTED_BLOB, 'Unexpected original source blob')
    text = raw.decode('utf8')
    cb = re.search(r'def elevenCost \(k : ℕ\) : ℝ :=\n(.*?)\n\ntheorem', text, re.S)
    require(cb is not None, 'Original exact cost definition missing')
    cp = re.fullmatch(r'\s*if k = 9 then (\d+) / (\d+) else\s*'
                      r'if k = 10 then (\d+) / (\d+) else (\d+) / (\d+)\s*', cb.group(1))
    require(cp is not None, 'Unrecognized exact cost definition')
    nums = list(map(int, cp.groups()))
    c9, c10, cother = [Fraction(nums[i], nums[i+1]) for i in (0,2,4)]
    wb = re.search(r'def elevenOptimizedWeightUnits \(i : Fin 11\) : ℕ :=\n(.*?)\n\ndef', text, re.S)
    require(wb is not None, 'Original optimized weights missing')
    wp = re.fullmatch(r'\s*if \(i : ℕ\) = 0 ∨ \(i : ℕ\) = 10 then (\d+) else\s*'
                      r'if \(i : ℕ\) = 1 ∨ \(i : ℕ\) = 9 then (\d+) else (\d+)\s*', wb.group(1))
    require(wp is not None, 'Unrecognized original weight definition')
    edge, near, middle = map(int, wp.groups())
    w = [edge, near] + [middle]*7 + [near, edge]
    require(all(x > 0 for x in w), 'Nonpositive weight')
    def c(i,j):
        k = abs(i-j)
        return Fraction(0) if not k else c9 if k==9 else c10 if k==10 else cother
    rows = [sum((c(i,j)*Fraction(w[j],w[i]) for j in range(11)),Fraction(0)) for i in range(11)]
    S = max(rows)
    margin = Fraction(5671,3200)-2*S
    require(S == Fraction(25289,35500), 'Row constant mismatch')
    require(margin == Fraction(394709,1136000), 'Margin mismatch')
    den = lcm(c9.denominator,c10.denominator,cother.denominator)
    costnums = [int(den*x) for x in (c9,c10,cother)]
    rownums = [sum(int(den*c(i,j))*w[j] for j in range(11)) for i in range(11)]
    # Clear the positive denominator 3700 from c, then cancel a factor100.
    require(den == 3700 and costnums == [2109,837,37], 'Cost export mismatch')
    require(all(355*rownums[i] <= 25289*37*w[i] for i in range(11)), 'Row certificate failed')
    source = f'''/- Source-bound exact arithmetic for the weighted independent-shape
composition. The original weights and exact costs are extracted from Git
blob {blob}; they are not newly optimized.
This module proves integer facts only. It does not define B, prove the
analytic mixed estimate, or prove RH. Lean4.33.1, no Mathlib dependency. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace AEGIS.WeightedIndependentShapeArithmetic

def weights : List Nat := {str(w)}
def weight (i : Nat) : Nat := weights[i]!
def costNum (i j : Nat) : Nat :=
  if i = j then 0 else
  if i - j = 9 ∨ j - i = 9 then 2109 else
  if i - j = 10 ∨ j - i = 10 then 837 else 37
def rowNum (i : Nat) : Nat :=
  ((List.range 11).map (fun j => costNum i j * weight j)).sum

theorem exact_row_ledger :
    (List.range 11).map rowNum = {str(rownums)} := by decide

theorem positive_weights :
    (List.range 11).all (fun i => decide (0 < weight i)) = true := by decide

theorem all_eleven_weighted_rows :
    (List.range 11).all (fun i =>
      decide (355 * rowNum i ≤ 25289 * 37 * weight i)) = true := by decide

theorem maximum_attained :
    355 * rowNum 1 = 25289 * 37 * weight 1 := by decide

theorem exact_margin :
    5671 * 355 = 2 * 25289 * 32 + 394709 := by decide

theorem positive_margin : 0 < (394709 : Nat) := by decide

theorem improves_previous_weights :
    (732143 : Nat) * 1136000 < 394709 * 2107520 := by decide

end AEGIS.WeightedIndependentShapeArithmetic

#print axioms AEGIS.WeightedIndependentShapeArithmetic.exact_row_ledger
#print axioms AEGIS.WeightedIndependentShapeArithmetic.positive_weights
#print axioms AEGIS.WeightedIndependentShapeArithmetic.all_eleven_weighted_rows
#print axioms AEGIS.WeightedIndependentShapeArithmetic.maximum_attained
#print axioms AEGIS.WeightedIndependentShapeArithmetic.exact_margin
#print axioms AEGIS.WeightedIndependentShapeArithmetic.positive_margin
#print axioms AEGIS.WeightedIndependentShapeArithmetic.improves_previous_weights
'''
    lean = output/'WeightedIndependentShapeArithmetic.lean'
    lean.write_text(source)
    receipt = dict(schema='AEGIS_EXACT_SOURCE_WEIGHT_REUSE_V1',
                   source_repo='Aegis-Omega/formal-conjectures',
                   source_commit='1f70364296eee931d0cae5ecc16a0c9810c0c4cc',
                   original_source_path='AEGISOverlay/RHActualElevenLatticeV1.lean',
                   source_git_blob=blob, source_sha256=hashlib.sha256(raw).hexdigest(),
                   weights=w, row_bounds=[str(r) for r in rows], max_row=str(S),
                   independent_shape_margin=str(margin),
                   margin_for_previous_weights='732143/2107520',
                   lean_file=lean.name, lean_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),
                   new_weight_optimization=False, kernel_replay='SEPARATE_RECEIPT',
                   rh_proven=False)
    (output/'EXACT_SOURCE_REUSE_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(source_blob=blob, rows_checked=len(rows), max_row=str(S),
                          margin=str(margin), emitted=lean.name)))


if __name__ == '__main__':
    main()
