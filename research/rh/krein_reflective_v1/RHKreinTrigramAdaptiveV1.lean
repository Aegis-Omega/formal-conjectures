/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
AEGIS Ω — adaptive trigram/dyadic finite-interval certificate candidate.
Generated from exact-rational Python mirror. LEAN_KERNEL_NOT_RUN.
AUTHORITY_EFFECT = NONE. No RH claim.
-/
import RHKreinCellBatchV1
import RHKreinFifteenthCellDirectV1

set_option autoImplicit false
noncomputable section

namespace AEGIS.RHKreinTrigramAdaptiveV1

open AEGIS.RHKreinCellCheckerV1
open AEGIS.RHKreinCellBatchV1
open AEGIS.RHKreinFiniteCertificateAssemblyV1
open AEGIS.RHKreinFiniteCertificateDataV1
open AEGIS.RHKreinFirstCellV1
open AEGIS.RHKreinSecondCellReductionV1

def NonnegOnQ (a b : ℚ) : Prop :=
  ∀ t : ℝ, (a : ℝ) ≤ t → t ≤ (b : ℝ) → 0 ≤ correctedExpression t

theorem nonnegOn_of_checkPiece_zero (a b : ℚ) (ha : 0 < a)
    (h : checkPiece pa19 a 0 a b = true) : NonnegOnQ a b := by
  intro t hta htb
  have hb := checkPiece_sound pa19 a 0 a b h t hta htb
  unfold Budget at hb
  simpa [correctedExpression] using hb

theorem nonnegOn_of_cellSound (c : FiniteCellV1)
    (hs : CellAnalyticSoundV1 c) (hp : (0 : ℚ) < lowerValue c) :
    NonnegOnQ c.lo c.hi := by
  intro t hlo hhi
  apply correctedExpression_nonnegative_of_normalizedExcess_v1
  have hs' := hs t hlo hhi
  have hp' : (0 : ℝ) < (lowerValue c : ℝ) := by exact_mod_cast hp
  exact hp'.le.trans hs'

theorem nonnegOn_union (a m b : ℚ)
    (hl : NonnegOnQ a m) (hr : NonnegOnQ m b) : NonnegOnQ a b := by
  intro t hat htb
  by_cases htm : t ≤ (m : ℝ)
  · exact hl t hat htm
  · exact hr t (le_of_lt (lt_of_not_ge htm)) htb

/-- First two cells reuse their existing dedicated analytic proofs. -/
theorem n0000 : NonnegOnQ 0 (75/4096) := by
  apply nonnegOn_of_cellSound firstCell AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound.1
  norm_num [firstCell, lowerValue]

theorem n0001 : NonnegOnQ (75/4096) (225/8192) := by
  apply nonnegOn_of_cellSound secondCell AEGIS.RHKreinFifteenthCellDirectV1.first_fifteen_cells_sound.2.1
  norm_num [secondCell, lowerValue]

theorem c0002 : checkPiece pa19 (225/8192) 0 (225/8192) (525/16384) = true := by decide +kernel
theorem n0002 : NonnegOnQ (225/8192) (525/16384) :=
  nonnegOn_of_checkPiece_zero (225/8192) (525/16384) (by norm_num) c0002

theorem c0003 : checkPiece pa19 (525/16384) 0 (525/16384) (75/2048) = true := by decide +kernel
theorem n0003 : NonnegOnQ (525/16384) (75/2048) :=
  nonnegOn_of_checkPiece_zero (525/16384) (75/2048) (by norm_num) c0003

theorem c0004 : checkPiece pa19 (75/2048) 0 (75/2048) (375/8192) = true := by decide +kernel
theorem n0004 : NonnegOnQ (75/2048) (375/8192) :=
  nonnegOn_of_checkPiece_zero (75/2048) (375/8192) (by norm_num) c0004

theorem c0005 : checkPiece pa19 (375/8192) 0 (375/8192) (225/4096) = true := by decide +kernel
theorem n0005 : NonnegOnQ (375/8192) (225/4096) :=
  nonnegOn_of_checkPiece_zero (375/8192) (225/4096) (by norm_num) c0005

theorem c0006 : checkPiece pa19 (225/4096) 0 (225/4096) (525/8192) = true := by decide +kernel
theorem n0006 : NonnegOnQ (225/4096) (525/8192) :=
  nonnegOn_of_checkPiece_zero (225/4096) (525/8192) (by norm_num) c0006

theorem c0007 : checkPiece pa19 (525/8192) 0 (525/8192) (75/1024) = true := by decide +kernel
theorem n0007 : NonnegOnQ (525/8192) (75/1024) :=
  nonnegOn_of_checkPiece_zero (525/8192) (75/1024) (by norm_num) c0007

theorem c0008 : checkPiece pa19 (75/1024) 0 (75/1024) (675/8192) = true := by decide +kernel
theorem n0008 : NonnegOnQ (75/1024) (675/8192) :=
  nonnegOn_of_checkPiece_zero (75/1024) (675/8192) (by norm_num) c0008

theorem c0009 : checkPiece pa19 (675/8192) 0 (675/8192) (375/4096) = true := by decide +kernel
theorem n0009 : NonnegOnQ (675/8192) (375/4096) :=
  nonnegOn_of_checkPiece_zero (675/8192) (375/4096) (by norm_num) c0009

theorem c0010 : checkPiece pa19 (375/4096) 0 (375/4096) (825/8192) = true := by decide +kernel
theorem n0010 : NonnegOnQ (375/4096) (825/8192) :=
  nonnegOn_of_checkPiece_zero (375/4096) (825/8192) (by norm_num) c0010

theorem c0011 : checkPiece pa19 (825/8192) 0 (825/8192) (225/2048) = true := by decide +kernel
theorem n0011 : NonnegOnQ (825/8192) (225/2048) :=
  nonnegOn_of_checkPiece_zero (825/8192) (225/2048) (by norm_num) c0011

theorem c0012 : checkPiece pa19 (225/2048) 0 (225/2048) (975/8192) = true := by decide +kernel
theorem n0012 : NonnegOnQ (225/2048) (975/8192) :=
  nonnegOn_of_checkPiece_zero (225/2048) (975/8192) (by norm_num) c0012

theorem c0013 : checkPiece pa19 (975/8192) 0 (975/8192) (525/4096) = true := by decide +kernel
theorem n0013 : NonnegOnQ (975/8192) (525/4096) :=
  nonnegOn_of_checkPiece_zero (975/8192) (525/4096) (by norm_num) c0013

theorem c0014 : checkPiece pa19 (525/4096) 0 (525/4096) (1125/8192) = true := by decide +kernel
theorem n0014 : NonnegOnQ (525/4096) (1125/8192) :=
  nonnegOn_of_checkPiece_zero (525/4096) (1125/8192) (by norm_num) c0014

theorem c0015 : checkPiece pa19 (1125/8192) 0 (1125/8192) (75/512) = true := by decide +kernel
theorem n0015 : NonnegOnQ (1125/8192) (75/512) :=
  nonnegOn_of_checkPiece_zero (1125/8192) (75/512) (by norm_num) c0015

theorem c0016 : checkPiece pa19 (75/512) 0 (75/512) (1275/8192) = true := by decide +kernel
theorem n0016 : NonnegOnQ (75/512) (1275/8192) :=
  nonnegOn_of_checkPiece_zero (75/512) (1275/8192) (by norm_num) c0016

theorem c0017 : checkPiece pa19 (1275/8192) 0 (1275/8192) (675/4096) = true := by decide +kernel
theorem n0017 : NonnegOnQ (1275/8192) (675/4096) :=
  nonnegOn_of_checkPiece_zero (1275/8192) (675/4096) (by norm_num) c0017

theorem c0018 : checkPiece pa19 (675/4096) 0 (675/4096) (1425/8192) = true := by decide +kernel
theorem n0018 : NonnegOnQ (675/4096) (1425/8192) :=
  nonnegOn_of_checkPiece_zero (675/4096) (1425/8192) (by norm_num) c0018

theorem c0019 : checkPiece pa19 (1425/8192) 0 (1425/8192) (375/2048) = true := by decide +kernel
theorem n0019 : NonnegOnQ (1425/8192) (375/2048) :=
  nonnegOn_of_checkPiece_zero (1425/8192) (375/2048) (by norm_num) c0019

theorem c0020 : checkPiece pa19 (375/2048) 0 (375/2048) (1575/8192) = true := by decide +kernel
theorem n0020 : NonnegOnQ (375/2048) (1575/8192) :=
  nonnegOn_of_checkPiece_zero (375/2048) (1575/8192) (by norm_num) c0020

theorem c0021 : checkPiece pa19 (1575/8192) 0 (1575/8192) (825/4096) = true := by decide +kernel
theorem n0021 : NonnegOnQ (1575/8192) (825/4096) :=
  nonnegOn_of_checkPiece_zero (1575/8192) (825/4096) (by norm_num) c0021

theorem c0022 : checkPiece pa19 (825/4096) 0 (825/4096) (1725/8192) = true := by decide +kernel
theorem n0022 : NonnegOnQ (825/4096) (1725/8192) :=
  nonnegOn_of_checkPiece_zero (825/4096) (1725/8192) (by norm_num) c0022

theorem c0023 : checkPiece pa19 (1725/8192) 0 (1725/8192) (225/1024) = true := by decide +kernel
theorem n0023 : NonnegOnQ (1725/8192) (225/1024) :=
  nonnegOn_of_checkPiece_zero (1725/8192) (225/1024) (by norm_num) c0023

theorem c0024 : checkPiece pa19 (225/1024) 0 (225/1024) (1875/8192) = true := by decide +kernel
theorem n0024 : NonnegOnQ (225/1024) (1875/8192) :=
  nonnegOn_of_checkPiece_zero (225/1024) (1875/8192) (by norm_num) c0024

theorem c0025 : checkPiece pa19 (1875/8192) 0 (1875/8192) (975/4096) = true := by decide +kernel
theorem n0025 : NonnegOnQ (1875/8192) (975/4096) :=
  nonnegOn_of_checkPiece_zero (1875/8192) (975/4096) (by norm_num) c0025

theorem c0026 : checkPiece pa19 (975/4096) 0 (975/4096) (2025/8192) = true := by decide +kernel
theorem n0026 : NonnegOnQ (975/4096) (2025/8192) :=
  nonnegOn_of_checkPiece_zero (975/4096) (2025/8192) (by norm_num) c0026

theorem c0027 : checkPiece pa19 (2025/8192) 0 (2025/8192) (525/2048) = true := by decide +kernel
theorem n0027 : NonnegOnQ (2025/8192) (525/2048) :=
  nonnegOn_of_checkPiece_zero (2025/8192) (525/2048) (by norm_num) c0027

theorem c0028 : checkPiece pa19 (525/2048) 0 (525/2048) (2175/8192) = true := by decide +kernel
theorem n0028 : NonnegOnQ (525/2048) (2175/8192) :=
  nonnegOn_of_checkPiece_zero (525/2048) (2175/8192) (by norm_num) c0028

theorem c0029 : checkPiece pa19 (2175/8192) 0 (2175/8192) (1125/4096) = true := by decide +kernel
theorem n0029 : NonnegOnQ (2175/8192) (1125/4096) :=
  nonnegOn_of_checkPiece_zero (2175/8192) (1125/4096) (by norm_num) c0029

theorem c0030 : checkPiece pa19 (1125/4096) 0 (1125/4096) (2325/8192) = true := by decide +kernel
theorem n0030 : NonnegOnQ (1125/4096) (2325/8192) :=
  nonnegOn_of_checkPiece_zero (1125/4096) (2325/8192) (by norm_num) c0030

theorem c0031 : checkPiece pa19 (2325/8192) 0 (2325/8192) (75/256) = true := by decide +kernel
theorem n0031 : NonnegOnQ (2325/8192) (75/256) :=
  nonnegOn_of_checkPiece_zero (2325/8192) (75/256) (by norm_num) c0031

theorem c0032 : checkPiece pa19 (75/256) 0 (75/256) (2475/8192) = true := by decide +kernel
theorem n0032 : NonnegOnQ (75/256) (2475/8192) :=
  nonnegOn_of_checkPiece_zero (75/256) (2475/8192) (by norm_num) c0032

theorem c0033 : checkPiece pa19 (2475/8192) 0 (2475/8192) (1275/4096) = true := by decide +kernel
theorem n0033 : NonnegOnQ (2475/8192) (1275/4096) :=
  nonnegOn_of_checkPiece_zero (2475/8192) (1275/4096) (by norm_num) c0033

theorem c0034 : checkPiece pa19 (1275/4096) 0 (1275/4096) (2625/8192) = true := by decide +kernel
theorem n0034 : NonnegOnQ (1275/4096) (2625/8192) :=
  nonnegOn_of_checkPiece_zero (1275/4096) (2625/8192) (by norm_num) c0034

theorem c0035 : checkPiece pa19 (2625/8192) 0 (2625/8192) (675/2048) = true := by decide +kernel
theorem n0035 : NonnegOnQ (2625/8192) (675/2048) :=
  nonnegOn_of_checkPiece_zero (2625/8192) (675/2048) (by norm_num) c0035

theorem c0036 : checkPiece pa19 (675/2048) 0 (675/2048) (2775/8192) = true := by decide +kernel
theorem n0036 : NonnegOnQ (675/2048) (2775/8192) :=
  nonnegOn_of_checkPiece_zero (675/2048) (2775/8192) (by norm_num) c0036

theorem c0037 : checkPiece pa19 (2775/8192) 0 (2775/8192) (1425/4096) = true := by decide +kernel
theorem n0037 : NonnegOnQ (2775/8192) (1425/4096) :=
  nonnegOn_of_checkPiece_zero (2775/8192) (1425/4096) (by norm_num) c0037

theorem c0038 : checkPiece pa19 (1425/4096) 0 (1425/4096) (2925/8192) = true := by decide +kernel
theorem n0038 : NonnegOnQ (1425/4096) (2925/8192) :=
  nonnegOn_of_checkPiece_zero (1425/4096) (2925/8192) (by norm_num) c0038

theorem c0039 : checkPiece pa19 (2925/8192) 0 (2925/8192) (375/1024) = true := by decide +kernel
theorem n0039 : NonnegOnQ (2925/8192) (375/1024) :=
  nonnegOn_of_checkPiece_zero (2925/8192) (375/1024) (by norm_num) c0039

theorem c0040 : checkPiece pa19 (375/1024) 0 (375/1024) (3075/8192) = true := by decide +kernel
theorem n0040 : NonnegOnQ (375/1024) (3075/8192) :=
  nonnegOn_of_checkPiece_zero (375/1024) (3075/8192) (by norm_num) c0040

theorem c0041 : checkPiece pa19 (3075/8192) 0 (3075/8192) (1575/4096) = true := by decide +kernel
theorem n0041 : NonnegOnQ (3075/8192) (1575/4096) :=
  nonnegOn_of_checkPiece_zero (3075/8192) (1575/4096) (by norm_num) c0041

theorem c0042 : checkPiece pa19 (1575/4096) 0 (1575/4096) (3225/8192) = true := by decide +kernel
theorem n0042 : NonnegOnQ (1575/4096) (3225/8192) :=
  nonnegOn_of_checkPiece_zero (1575/4096) (3225/8192) (by norm_num) c0042

theorem c0043 : checkPiece pa19 (3225/8192) 0 (3225/8192) (825/2048) = true := by decide +kernel
theorem n0043 : NonnegOnQ (3225/8192) (825/2048) :=
  nonnegOn_of_checkPiece_zero (3225/8192) (825/2048) (by norm_num) c0043

theorem c0044 : checkPiece pa19 (825/2048) 0 (825/2048) (3375/8192) = true := by decide +kernel
theorem n0044 : NonnegOnQ (825/2048) (3375/8192) :=
  nonnegOn_of_checkPiece_zero (825/2048) (3375/8192) (by norm_num) c0044

theorem c0045 : checkPiece pa19 (3375/8192) 0 (3375/8192) (1725/4096) = true := by decide +kernel
theorem n0045 : NonnegOnQ (3375/8192) (1725/4096) :=
  nonnegOn_of_checkPiece_zero (3375/8192) (1725/4096) (by norm_num) c0045

theorem c0046 : checkPiece pa19 (1725/4096) 0 (1725/4096) (3525/8192) = true := by decide +kernel
theorem n0046 : NonnegOnQ (1725/4096) (3525/8192) :=
  nonnegOn_of_checkPiece_zero (1725/4096) (3525/8192) (by norm_num) c0046

theorem c0047 : checkPiece pa19 (3525/8192) 0 (3525/8192) (225/512) = true := by decide +kernel
theorem n0047 : NonnegOnQ (3525/8192) (225/512) :=
  nonnegOn_of_checkPiece_zero (3525/8192) (225/512) (by norm_num) c0047

theorem c0048 : checkPiece pa19 (225/512) 0 (225/512) (3675/8192) = true := by decide +kernel
theorem n0048 : NonnegOnQ (225/512) (3675/8192) :=
  nonnegOn_of_checkPiece_zero (225/512) (3675/8192) (by norm_num) c0048

theorem c0049 : checkPiece pa19 (3675/8192) 0 (3675/8192) (1875/4096) = true := by decide +kernel
theorem n0049 : NonnegOnQ (3675/8192) (1875/4096) :=
  nonnegOn_of_checkPiece_zero (3675/8192) (1875/4096) (by norm_num) c0049

theorem c0050 : checkPiece pa19 (1875/4096) 0 (1875/4096) (3825/8192) = true := by decide +kernel
theorem n0050 : NonnegOnQ (1875/4096) (3825/8192) :=
  nonnegOn_of_checkPiece_zero (1875/4096) (3825/8192) (by norm_num) c0050

theorem c0051 : checkPiece pa19 (3825/8192) 0 (3825/8192) (975/2048) = true := by decide +kernel
theorem n0051 : NonnegOnQ (3825/8192) (975/2048) :=
  nonnegOn_of_checkPiece_zero (3825/8192) (975/2048) (by norm_num) c0051

theorem c0052 : checkPiece pa19 (975/2048) 0 (975/2048) (3975/8192) = true := by decide +kernel
theorem n0052 : NonnegOnQ (975/2048) (3975/8192) :=
  nonnegOn_of_checkPiece_zero (975/2048) (3975/8192) (by norm_num) c0052

theorem c0053 : checkPiece pa19 (3975/8192) 0 (3975/8192) (2025/4096) = true := by decide +kernel
theorem n0053 : NonnegOnQ (3975/8192) (2025/4096) :=
  nonnegOn_of_checkPiece_zero (3975/8192) (2025/4096) (by norm_num) c0053

theorem c0054 : checkPiece pa19 (2025/4096) 0 (2025/4096) (4125/8192) = true := by decide +kernel
theorem n0054 : NonnegOnQ (2025/4096) (4125/8192) :=
  nonnegOn_of_checkPiece_zero (2025/4096) (4125/8192) (by norm_num) c0054

theorem c0055 : checkPiece pa19 (4125/8192) 0 (4125/8192) (525/1024) = true := by decide +kernel
theorem n0055 : NonnegOnQ (4125/8192) (525/1024) :=
  nonnegOn_of_checkPiece_zero (4125/8192) (525/1024) (by norm_num) c0055

theorem c0056 : checkPiece pa19 (525/1024) 0 (525/1024) (4275/8192) = true := by decide +kernel
theorem n0056 : NonnegOnQ (525/1024) (4275/8192) :=
  nonnegOn_of_checkPiece_zero (525/1024) (4275/8192) (by norm_num) c0056

theorem c0057 : checkPiece pa19 (4275/8192) 0 (4275/8192) (2175/4096) = true := by decide +kernel
theorem n0057 : NonnegOnQ (4275/8192) (2175/4096) :=
  nonnegOn_of_checkPiece_zero (4275/8192) (2175/4096) (by norm_num) c0057

theorem c0058 : checkPiece pa19 (2175/4096) 0 (2175/4096) (4425/8192) = true := by decide +kernel
theorem n0058 : NonnegOnQ (2175/4096) (4425/8192) :=
  nonnegOn_of_checkPiece_zero (2175/4096) (4425/8192) (by norm_num) c0058

theorem c0059 : checkPiece pa19 (4425/8192) 0 (4425/8192) (1125/2048) = true := by decide +kernel
theorem n0059 : NonnegOnQ (4425/8192) (1125/2048) :=
  nonnegOn_of_checkPiece_zero (4425/8192) (1125/2048) (by norm_num) c0059

theorem c0060 : checkPiece pa19 (1125/2048) 0 (1125/2048) (4575/8192) = true := by decide +kernel
theorem n0060 : NonnegOnQ (1125/2048) (4575/8192) :=
  nonnegOn_of_checkPiece_zero (1125/2048) (4575/8192) (by norm_num) c0060

theorem c0061 : checkPiece pa19 (4575/8192) 0 (4575/8192) (2325/4096) = true := by decide +kernel
theorem n0061 : NonnegOnQ (4575/8192) (2325/4096) :=
  nonnegOn_of_checkPiece_zero (4575/8192) (2325/4096) (by norm_num) c0061

theorem c0062 : checkPiece pa19 (2325/4096) 0 (2325/4096) (4725/8192) = true := by decide +kernel
theorem n0062 : NonnegOnQ (2325/4096) (4725/8192) :=
  nonnegOn_of_checkPiece_zero (2325/4096) (4725/8192) (by norm_num) c0062

theorem c0063 : checkPiece pa19 (4725/8192) 0 (4725/8192) (75/128) = true := by decide +kernel
theorem n0063 : NonnegOnQ (4725/8192) (75/128) :=
  nonnegOn_of_checkPiece_zero (4725/8192) (75/128) (by norm_num) c0063

theorem c0064 : checkPiece pa19 (75/128) 0 (75/128) (4875/8192) = true := by decide +kernel
theorem n0064 : NonnegOnQ (75/128) (4875/8192) :=
  nonnegOn_of_checkPiece_zero (75/128) (4875/8192) (by norm_num) c0064

theorem c0065 : checkPiece pa19 (4875/8192) 0 (4875/8192) (2475/4096) = true := by decide +kernel
theorem n0065 : NonnegOnQ (4875/8192) (2475/4096) :=
  nonnegOn_of_checkPiece_zero (4875/8192) (2475/4096) (by norm_num) c0065

theorem c0066 : checkPiece pa19 (2475/4096) 0 (2475/4096) (5025/8192) = true := by decide +kernel
theorem n0066 : NonnegOnQ (2475/4096) (5025/8192) :=
  nonnegOn_of_checkPiece_zero (2475/4096) (5025/8192) (by norm_num) c0066

theorem c0067 : checkPiece pa19 (5025/8192) 0 (5025/8192) (1275/2048) = true := by decide +kernel
theorem n0067 : NonnegOnQ (5025/8192) (1275/2048) :=
  nonnegOn_of_checkPiece_zero (5025/8192) (1275/2048) (by norm_num) c0067

theorem c0068 : checkPiece pa19 (1275/2048) 0 (1275/2048) (5175/8192) = true := by decide +kernel
theorem n0068 : NonnegOnQ (1275/2048) (5175/8192) :=
  nonnegOn_of_checkPiece_zero (1275/2048) (5175/8192) (by norm_num) c0068

theorem c0069 : checkPiece pa19 (5175/8192) 0 (5175/8192) (2625/4096) = true := by decide +kernel
theorem n0069 : NonnegOnQ (5175/8192) (2625/4096) :=
  nonnegOn_of_checkPiece_zero (5175/8192) (2625/4096) (by norm_num) c0069

theorem c0070 : checkPiece pa19 (2625/4096) 0 (2625/4096) (5325/8192) = true := by decide +kernel
theorem n0070 : NonnegOnQ (2625/4096) (5325/8192) :=
  nonnegOn_of_checkPiece_zero (2625/4096) (5325/8192) (by norm_num) c0070

theorem c0071 : checkPiece pa19 (5325/8192) 0 (5325/8192) (675/1024) = true := by decide +kernel
theorem n0071 : NonnegOnQ (5325/8192) (675/1024) :=
  nonnegOn_of_checkPiece_zero (5325/8192) (675/1024) (by norm_num) c0071

theorem c0072 : checkPiece pa19 (675/1024) 0 (675/1024) (5475/8192) = true := by decide +kernel
theorem n0072 : NonnegOnQ (675/1024) (5475/8192) :=
  nonnegOn_of_checkPiece_zero (675/1024) (5475/8192) (by norm_num) c0072

theorem c0073 : checkPiece pa19 (5475/8192) 0 (5475/8192) (2775/4096) = true := by decide +kernel
theorem n0073 : NonnegOnQ (5475/8192) (2775/4096) :=
  nonnegOn_of_checkPiece_zero (5475/8192) (2775/4096) (by norm_num) c0073

theorem c0074 : checkPiece pa19 (2775/4096) 0 (2775/4096) (5625/8192) = true := by decide +kernel
theorem n0074 : NonnegOnQ (2775/4096) (5625/8192) :=
  nonnegOn_of_checkPiece_zero (2775/4096) (5625/8192) (by norm_num) c0074

theorem c0075 : checkPiece pa19 (5625/8192) 0 (5625/8192) (1425/2048) = true := by decide +kernel
theorem n0075 : NonnegOnQ (5625/8192) (1425/2048) :=
  nonnegOn_of_checkPiece_zero (5625/8192) (1425/2048) (by norm_num) c0075

theorem c0076 : checkPiece pa19 (1425/2048) 0 (1425/2048) (5775/8192) = true := by decide +kernel
theorem n0076 : NonnegOnQ (1425/2048) (5775/8192) :=
  nonnegOn_of_checkPiece_zero (1425/2048) (5775/8192) (by norm_num) c0076

theorem c0077 : checkPiece pa19 (5775/8192) 0 (5775/8192) (2925/4096) = true := by decide +kernel
theorem n0077 : NonnegOnQ (5775/8192) (2925/4096) :=
  nonnegOn_of_checkPiece_zero (5775/8192) (2925/4096) (by norm_num) c0077

theorem c0078 : checkPiece pa19 (2925/4096) 0 (2925/4096) (5925/8192) = true := by decide +kernel
theorem n0078 : NonnegOnQ (2925/4096) (5925/8192) :=
  nonnegOn_of_checkPiece_zero (2925/4096) (5925/8192) (by norm_num) c0078

theorem c0079 : checkPiece pa19 (5925/8192) 0 (5925/8192) (375/512) = true := by decide +kernel
theorem n0079 : NonnegOnQ (5925/8192) (375/512) :=
  nonnegOn_of_checkPiece_zero (5925/8192) (375/512) (by norm_num) c0079

theorem c0080 : checkPiece pa19 (375/512) 0 (375/512) (6075/8192) = true := by decide +kernel
theorem n0080 : NonnegOnQ (375/512) (6075/8192) :=
  nonnegOn_of_checkPiece_zero (375/512) (6075/8192) (by norm_num) c0080

theorem c0081 : checkPiece pa19 (6075/8192) 0 (6075/8192) (3075/4096) = true := by decide +kernel
theorem n0081 : NonnegOnQ (6075/8192) (3075/4096) :=
  nonnegOn_of_checkPiece_zero (6075/8192) (3075/4096) (by norm_num) c0081

theorem c0082 : checkPiece pa19 (3075/4096) 0 (3075/4096) (6225/8192) = true := by decide +kernel
theorem n0082 : NonnegOnQ (3075/4096) (6225/8192) :=
  nonnegOn_of_checkPiece_zero (3075/4096) (6225/8192) (by norm_num) c0082

theorem c0083 : checkPiece pa19 (6225/8192) 0 (6225/8192) (1575/2048) = true := by decide +kernel
theorem n0083 : NonnegOnQ (6225/8192) (1575/2048) :=
  nonnegOn_of_checkPiece_zero (6225/8192) (1575/2048) (by norm_num) c0083

theorem c0084 : checkPiece pa19 (1575/2048) 0 (1575/2048) (6375/8192) = true := by decide +kernel
theorem n0084 : NonnegOnQ (1575/2048) (6375/8192) :=
  nonnegOn_of_checkPiece_zero (1575/2048) (6375/8192) (by norm_num) c0084

theorem c0085 : checkPiece pa19 (6375/8192) 0 (6375/8192) (3225/4096) = true := by decide +kernel
theorem n0085 : NonnegOnQ (6375/8192) (3225/4096) :=
  nonnegOn_of_checkPiece_zero (6375/8192) (3225/4096) (by norm_num) c0085

theorem c0086 : checkPiece pa19 (3225/4096) 0 (3225/4096) (6525/8192) = true := by decide +kernel
theorem n0086 : NonnegOnQ (3225/4096) (6525/8192) :=
  nonnegOn_of_checkPiece_zero (3225/4096) (6525/8192) (by norm_num) c0086

theorem c0087 : checkPiece pa19 (6525/8192) 0 (6525/8192) (825/1024) = true := by decide +kernel
theorem n0087 : NonnegOnQ (6525/8192) (825/1024) :=
  nonnegOn_of_checkPiece_zero (6525/8192) (825/1024) (by norm_num) c0087

theorem c0088 : checkPiece pa19 (825/1024) 0 (825/1024) (6675/8192) = true := by decide +kernel
theorem n0088 : NonnegOnQ (825/1024) (6675/8192) :=
  nonnegOn_of_checkPiece_zero (825/1024) (6675/8192) (by norm_num) c0088

theorem c0089 : checkPiece pa19 (6675/8192) 0 (6675/8192) (3375/4096) = true := by decide +kernel
theorem n0089 : NonnegOnQ (6675/8192) (3375/4096) :=
  nonnegOn_of_checkPiece_zero (6675/8192) (3375/4096) (by norm_num) c0089

theorem c0090 : checkPiece pa19 (3375/4096) 0 (3375/4096) (6825/8192) = true := by decide +kernel
theorem n0090 : NonnegOnQ (3375/4096) (6825/8192) :=
  nonnegOn_of_checkPiece_zero (3375/4096) (6825/8192) (by norm_num) c0090

theorem c0091 : checkPiece pa19 (6825/8192) 0 (6825/8192) (1725/2048) = true := by decide +kernel
theorem n0091 : NonnegOnQ (6825/8192) (1725/2048) :=
  nonnegOn_of_checkPiece_zero (6825/8192) (1725/2048) (by norm_num) c0091

theorem c0092 : checkPiece pa19 (1725/2048) 0 (1725/2048) (6975/8192) = true := by decide +kernel
theorem n0092 : NonnegOnQ (1725/2048) (6975/8192) :=
  nonnegOn_of_checkPiece_zero (1725/2048) (6975/8192) (by norm_num) c0092

theorem c0093 : checkPiece pa19 (6975/8192) 0 (6975/8192) (3525/4096) = true := by decide +kernel
theorem n0093 : NonnegOnQ (6975/8192) (3525/4096) :=
  nonnegOn_of_checkPiece_zero (6975/8192) (3525/4096) (by norm_num) c0093

theorem c0094 : checkPiece pa19 (3525/4096) 0 (3525/4096) (7125/8192) = true := by decide +kernel
theorem n0094 : NonnegOnQ (3525/4096) (7125/8192) :=
  nonnegOn_of_checkPiece_zero (3525/4096) (7125/8192) (by norm_num) c0094

theorem c0095 : checkPiece pa19 (7125/8192) 0 (7125/8192) (225/256) = true := by decide +kernel
theorem n0095 : NonnegOnQ (7125/8192) (225/256) :=
  nonnegOn_of_checkPiece_zero (7125/8192) (225/256) (by norm_num) c0095

theorem c0096 : checkPiece pa19 (225/256) 0 (225/256) (7275/8192) = true := by decide +kernel
theorem n0096 : NonnegOnQ (225/256) (7275/8192) :=
  nonnegOn_of_checkPiece_zero (225/256) (7275/8192) (by norm_num) c0096

theorem c0097 : checkPiece pa19 (7275/8192) 0 (7275/8192) (3675/4096) = true := by decide +kernel
theorem n0097 : NonnegOnQ (7275/8192) (3675/4096) :=
  nonnegOn_of_checkPiece_zero (7275/8192) (3675/4096) (by norm_num) c0097

theorem c0098 : checkPiece pa19 (3675/4096) 0 (3675/4096) (7425/8192) = true := by decide +kernel
theorem n0098 : NonnegOnQ (3675/4096) (7425/8192) :=
  nonnegOn_of_checkPiece_zero (3675/4096) (7425/8192) (by norm_num) c0098

theorem c0099 : checkPiece pa19 (7425/8192) 0 (7425/8192) (1875/2048) = true := by decide +kernel
theorem n0099 : NonnegOnQ (7425/8192) (1875/2048) :=
  nonnegOn_of_checkPiece_zero (7425/8192) (1875/2048) (by norm_num) c0099

theorem c0100 : checkPiece pa19 (1875/2048) 0 (1875/2048) (7575/8192) = true := by decide +kernel
theorem n0100 : NonnegOnQ (1875/2048) (7575/8192) :=
  nonnegOn_of_checkPiece_zero (1875/2048) (7575/8192) (by norm_num) c0100

theorem c0101 : checkPiece pa19 (7575/8192) 0 (7575/8192) (3825/4096) = true := by decide +kernel
theorem n0101 : NonnegOnQ (7575/8192) (3825/4096) :=
  nonnegOn_of_checkPiece_zero (7575/8192) (3825/4096) (by norm_num) c0101

theorem c0102 : checkPiece pa19 (3825/4096) 0 (3825/4096) (975/1024) = true := by decide +kernel
theorem n0102 : NonnegOnQ (3825/4096) (975/1024) :=
  nonnegOn_of_checkPiece_zero (3825/4096) (975/1024) (by norm_num) c0102

theorem c0103 : checkPiece pa19 (975/1024) 0 (975/1024) (3975/4096) = true := by decide +kernel
theorem n0103 : NonnegOnQ (975/1024) (3975/4096) :=
  nonnegOn_of_checkPiece_zero (975/1024) (3975/4096) (by norm_num) c0103

theorem c0104 : checkPiece pa19 (3975/4096) 0 (3975/4096) (2025/2048) = true := by decide +kernel
theorem n0104 : NonnegOnQ (3975/4096) (2025/2048) :=
  nonnegOn_of_checkPiece_zero (3975/4096) (2025/2048) (by norm_num) c0104

theorem c0105 : checkPiece pa19 (2025/2048) 0 (2025/2048) (4125/4096) = true := by decide +kernel
theorem n0105 : NonnegOnQ (2025/2048) (4125/4096) :=
  nonnegOn_of_checkPiece_zero (2025/2048) (4125/4096) (by norm_num) c0105

theorem c0106 : checkPiece pa19 (4125/4096) 0 (4125/4096) (525/512) = true := by decide +kernel
theorem n0106 : NonnegOnQ (4125/4096) (525/512) :=
  nonnegOn_of_checkPiece_zero (4125/4096) (525/512) (by norm_num) c0106

theorem c0107 : checkPiece pa19 (525/512) 0 (525/512) (4275/4096) = true := by decide +kernel
theorem n0107 : NonnegOnQ (525/512) (4275/4096) :=
  nonnegOn_of_checkPiece_zero (525/512) (4275/4096) (by norm_num) c0107

theorem c0108 : checkPiece pa19 (4275/4096) 0 (4275/4096) (2175/2048) = true := by decide +kernel
theorem n0108 : NonnegOnQ (4275/4096) (2175/2048) :=
  nonnegOn_of_checkPiece_zero (4275/4096) (2175/2048) (by norm_num) c0108

theorem c0109 : checkPiece pa19 (2175/2048) 0 (2175/2048) (4425/4096) = true := by decide +kernel
theorem n0109 : NonnegOnQ (2175/2048) (4425/4096) :=
  nonnegOn_of_checkPiece_zero (2175/2048) (4425/4096) (by norm_num) c0109

theorem c0110 : checkPiece pa19 (4425/4096) 0 (4425/4096) (1125/1024) = true := by decide +kernel
theorem n0110 : NonnegOnQ (4425/4096) (1125/1024) :=
  nonnegOn_of_checkPiece_zero (4425/4096) (1125/1024) (by norm_num) c0110

theorem c0111 : checkPiece pa19 (1125/1024) 0 (1125/1024) (4575/4096) = true := by decide +kernel
theorem n0111 : NonnegOnQ (1125/1024) (4575/4096) :=
  nonnegOn_of_checkPiece_zero (1125/1024) (4575/4096) (by norm_num) c0111

theorem c0112 : checkPiece pa19 (4575/4096) 0 (4575/4096) (2325/2048) = true := by decide +kernel
theorem n0112 : NonnegOnQ (4575/4096) (2325/2048) :=
  nonnegOn_of_checkPiece_zero (4575/4096) (2325/2048) (by norm_num) c0112

theorem c0113 : checkPiece pa19 (2325/2048) 0 (2325/2048) (4725/4096) = true := by decide +kernel
theorem n0113 : NonnegOnQ (2325/2048) (4725/4096) :=
  nonnegOn_of_checkPiece_zero (2325/2048) (4725/4096) (by norm_num) c0113

theorem c0114 : checkPiece pa19 (4725/4096) 0 (4725/4096) (75/64) = true := by decide +kernel
theorem n0114 : NonnegOnQ (4725/4096) (75/64) :=
  nonnegOn_of_checkPiece_zero (4725/4096) (75/64) (by norm_num) c0114

theorem c0115 : checkPiece pa19 (75/64) 0 (75/64) (4875/4096) = true := by decide +kernel
theorem n0115 : NonnegOnQ (75/64) (4875/4096) :=
  nonnegOn_of_checkPiece_zero (75/64) (4875/4096) (by norm_num) c0115

theorem c0116 : checkPiece pa19 (4875/4096) 0 (4875/4096) (2475/2048) = true := by decide +kernel
theorem n0116 : NonnegOnQ (4875/4096) (2475/2048) :=
  nonnegOn_of_checkPiece_zero (4875/4096) (2475/2048) (by norm_num) c0116

theorem c0117 : checkPiece pa19 (2475/2048) 0 (2475/2048) (5025/4096) = true := by decide +kernel
theorem n0117 : NonnegOnQ (2475/2048) (5025/4096) :=
  nonnegOn_of_checkPiece_zero (2475/2048) (5025/4096) (by norm_num) c0117

theorem c0118 : checkPiece pa19 (5025/4096) 0 (5025/4096) (1275/1024) = true := by decide +kernel
theorem n0118 : NonnegOnQ (5025/4096) (1275/1024) :=
  nonnegOn_of_checkPiece_zero (5025/4096) (1275/1024) (by norm_num) c0118

theorem c0119 : checkPiece pa19 (1275/1024) 0 (1275/1024) (5175/4096) = true := by decide +kernel
theorem n0119 : NonnegOnQ (1275/1024) (5175/4096) :=
  nonnegOn_of_checkPiece_zero (1275/1024) (5175/4096) (by norm_num) c0119

theorem c0120 : checkPiece pa19 (5175/4096) 0 (5175/4096) (2625/2048) = true := by decide +kernel
theorem n0120 : NonnegOnQ (5175/4096) (2625/2048) :=
  nonnegOn_of_checkPiece_zero (5175/4096) (2625/2048) (by norm_num) c0120

theorem c0121 : checkPiece pa19 (2625/2048) 0 (2625/2048) (5325/4096) = true := by decide +kernel
theorem n0121 : NonnegOnQ (2625/2048) (5325/4096) :=
  nonnegOn_of_checkPiece_zero (2625/2048) (5325/4096) (by norm_num) c0121

theorem c0122 : checkPiece pa19 (5325/4096) 0 (5325/4096) (675/512) = true := by decide +kernel
theorem n0122 : NonnegOnQ (5325/4096) (675/512) :=
  nonnegOn_of_checkPiece_zero (5325/4096) (675/512) (by norm_num) c0122

theorem c0123 : checkPiece pa19 (675/512) 0 (675/512) (5475/4096) = true := by decide +kernel
theorem n0123 : NonnegOnQ (675/512) (5475/4096) :=
  nonnegOn_of_checkPiece_zero (675/512) (5475/4096) (by norm_num) c0123

theorem c0124 : checkPiece pa19 (5475/4096) 0 (5475/4096) (2775/2048) = true := by decide +kernel
theorem n0124 : NonnegOnQ (5475/4096) (2775/2048) :=
  nonnegOn_of_checkPiece_zero (5475/4096) (2775/2048) (by norm_num) c0124

theorem c0125 : checkPiece pa19 (2775/2048) 0 (2775/2048) (5625/4096) = true := by decide +kernel
theorem n0125 : NonnegOnQ (2775/2048) (5625/4096) :=
  nonnegOn_of_checkPiece_zero (2775/2048) (5625/4096) (by norm_num) c0125

theorem c0126 : checkPiece pa19 (5625/4096) 0 (5625/4096) (1425/1024) = true := by decide +kernel
theorem n0126 : NonnegOnQ (5625/4096) (1425/1024) :=
  nonnegOn_of_checkPiece_zero (5625/4096) (1425/1024) (by norm_num) c0126

theorem c0127 : checkPiece pa19 (1425/1024) 0 (1425/1024) (2925/2048) = true := by decide +kernel
theorem n0127 : NonnegOnQ (1425/1024) (2925/2048) :=
  nonnegOn_of_checkPiece_zero (1425/1024) (2925/2048) (by norm_num) c0127

theorem c0128 : checkPiece pa19 (2925/2048) 0 (2925/2048) (375/256) = true := by decide +kernel
theorem n0128 : NonnegOnQ (2925/2048) (375/256) :=
  nonnegOn_of_checkPiece_zero (2925/2048) (375/256) (by norm_num) c0128

theorem c0129 : checkPiece pa19 (375/256) 0 (375/256) (3075/2048) = true := by decide +kernel
theorem n0129 : NonnegOnQ (375/256) (3075/2048) :=
  nonnegOn_of_checkPiece_zero (375/256) (3075/2048) (by norm_num) c0129

theorem c0130 : checkPiece pa19 (3075/2048) 0 (3075/2048) (1575/1024) = true := by decide +kernel
theorem n0130 : NonnegOnQ (3075/2048) (1575/1024) :=
  nonnegOn_of_checkPiece_zero (3075/2048) (1575/1024) (by norm_num) c0130

theorem c0131 : checkPiece pa19 (1575/1024) 0 (1575/1024) (3225/2048) = true := by decide +kernel
theorem n0131 : NonnegOnQ (1575/1024) (3225/2048) :=
  nonnegOn_of_checkPiece_zero (1575/1024) (3225/2048) (by norm_num) c0131

theorem c0132 : checkPiece pa19 (3225/2048) 0 (3225/2048) (825/512) = true := by decide +kernel
theorem n0132 : NonnegOnQ (3225/2048) (825/512) :=
  nonnegOn_of_checkPiece_zero (3225/2048) (825/512) (by norm_num) c0132

theorem c0133 : checkPiece pa19 (825/512) 0 (825/512) (3375/2048) = true := by decide +kernel
theorem n0133 : NonnegOnQ (825/512) (3375/2048) :=
  nonnegOn_of_checkPiece_zero (825/512) (3375/2048) (by norm_num) c0133

theorem c0134 : checkPiece pa19 (3375/2048) 0 (3375/2048) (1725/1024) = true := by decide +kernel
theorem n0134 : NonnegOnQ (3375/2048) (1725/1024) :=
  nonnegOn_of_checkPiece_zero (3375/2048) (1725/1024) (by norm_num) c0134

theorem c0135 : checkPiece pa19 (1725/1024) 0 (1725/1024) (3525/2048) = true := by decide +kernel
theorem n0135 : NonnegOnQ (1725/1024) (3525/2048) :=
  nonnegOn_of_checkPiece_zero (1725/1024) (3525/2048) (by norm_num) c0135

theorem c0136 : checkPiece pa19 (3525/2048) 0 (3525/2048) (225/128) = true := by decide +kernel
theorem n0136 : NonnegOnQ (3525/2048) (225/128) :=
  nonnegOn_of_checkPiece_zero (3525/2048) (225/128) (by norm_num) c0136

theorem c0137 : checkPiece pa19 (225/128) 0 (225/128) (3675/2048) = true := by decide +kernel
theorem n0137 : NonnegOnQ (225/128) (3675/2048) :=
  nonnegOn_of_checkPiece_zero (225/128) (3675/2048) (by norm_num) c0137

theorem c0138 : checkPiece pa19 (3675/2048) 0 (3675/2048) (1875/1024) = true := by decide +kernel
theorem n0138 : NonnegOnQ (3675/2048) (1875/1024) :=
  nonnegOn_of_checkPiece_zero (3675/2048) (1875/1024) (by norm_num) c0138

theorem c0139 : checkPiece pa19 (1875/1024) 0 (1875/1024) (3825/2048) = true := by decide +kernel
theorem n0139 : NonnegOnQ (1875/1024) (3825/2048) :=
  nonnegOn_of_checkPiece_zero (1875/1024) (3825/2048) (by norm_num) c0139

theorem c0140 : checkPiece pa19 (3825/2048) 0 (3825/2048) (975/512) = true := by decide +kernel
theorem n0140 : NonnegOnQ (3825/2048) (975/512) :=
  nonnegOn_of_checkPiece_zero (3825/2048) (975/512) (by norm_num) c0140

theorem c0141 : checkPiece pa19 (975/512) 0 (975/512) (3975/2048) = true := by decide +kernel
theorem n0141 : NonnegOnQ (975/512) (3975/2048) :=
  nonnegOn_of_checkPiece_zero (975/512) (3975/2048) (by norm_num) c0141

theorem c0142 : checkPiece pa19 (3975/2048) 0 (3975/2048) (2025/1024) = true := by decide +kernel
theorem n0142 : NonnegOnQ (3975/2048) (2025/1024) :=
  nonnegOn_of_checkPiece_zero (3975/2048) (2025/1024) (by norm_num) c0142

theorem c0143 : checkPiece pa19 (2025/1024) 0 (2025/1024) (4125/2048) = true := by decide +kernel
theorem n0143 : NonnegOnQ (2025/1024) (4125/2048) :=
  nonnegOn_of_checkPiece_zero (2025/1024) (4125/2048) (by norm_num) c0143

theorem c0144 : checkPiece pa19 (4125/2048) 0 (4125/2048) (525/256) = true := by decide +kernel
theorem n0144 : NonnegOnQ (4125/2048) (525/256) :=
  nonnegOn_of_checkPiece_zero (4125/2048) (525/256) (by norm_num) c0144

theorem c0145 : checkPiece pa19 (525/256) 0 (525/256) (4275/2048) = true := by decide +kernel
theorem n0145 : NonnegOnQ (525/256) (4275/2048) :=
  nonnegOn_of_checkPiece_zero (525/256) (4275/2048) (by norm_num) c0145

theorem c0146 : checkPiece pa19 (4275/2048) 0 (4275/2048) (2175/1024) = true := by decide +kernel
theorem n0146 : NonnegOnQ (4275/2048) (2175/1024) :=
  nonnegOn_of_checkPiece_zero (4275/2048) (2175/1024) (by norm_num) c0146

theorem c0147 : checkPiece pa19 (2175/1024) 0 (2175/1024) (4425/2048) = true := by decide +kernel
theorem n0147 : NonnegOnQ (2175/1024) (4425/2048) :=
  nonnegOn_of_checkPiece_zero (2175/1024) (4425/2048) (by norm_num) c0147

theorem c0148 : checkPiece pa19 (4425/2048) 0 (4425/2048) (1125/512) = true := by decide +kernel
theorem n0148 : NonnegOnQ (4425/2048) (1125/512) :=
  nonnegOn_of_checkPiece_zero (4425/2048) (1125/512) (by norm_num) c0148

theorem c0149 : checkPiece pa19 (1125/512) 0 (1125/512) (4575/2048) = true := by decide +kernel
theorem n0149 : NonnegOnQ (1125/512) (4575/2048) :=
  nonnegOn_of_checkPiece_zero (1125/512) (4575/2048) (by norm_num) c0149

theorem c0150 : checkPiece pa19 (4575/2048) 0 (4575/2048) (2325/1024) = true := by decide +kernel
theorem n0150 : NonnegOnQ (4575/2048) (2325/1024) :=
  nonnegOn_of_checkPiece_zero (4575/2048) (2325/1024) (by norm_num) c0150

theorem c0151 : checkPiece pa19 (2325/1024) 0 (2325/1024) (4725/2048) = true := by decide +kernel
theorem n0151 : NonnegOnQ (2325/1024) (4725/2048) :=
  nonnegOn_of_checkPiece_zero (2325/1024) (4725/2048) (by norm_num) c0151

theorem c0152 : checkPiece pa19 (4725/2048) 0 (4725/2048) (75/32) = true := by decide +kernel
theorem n0152 : NonnegOnQ (4725/2048) (75/32) :=
  nonnegOn_of_checkPiece_zero (4725/2048) (75/32) (by norm_num) c0152

theorem c0153 : checkPiece pa19 (75/32) 0 (75/32) (4875/2048) = true := by decide +kernel
theorem n0153 : NonnegOnQ (75/32) (4875/2048) :=
  nonnegOn_of_checkPiece_zero (75/32) (4875/2048) (by norm_num) c0153

theorem c0154 : checkPiece pa19 (4875/2048) 0 (4875/2048) (2475/1024) = true := by decide +kernel
theorem n0154 : NonnegOnQ (4875/2048) (2475/1024) :=
  nonnegOn_of_checkPiece_zero (4875/2048) (2475/1024) (by norm_num) c0154

theorem c0155 : checkPiece pa19 (2475/1024) 0 (2475/1024) (1275/512) = true := by decide +kernel
theorem n0155 : NonnegOnQ (2475/1024) (1275/512) :=
  nonnegOn_of_checkPiece_zero (2475/1024) (1275/512) (by norm_num) c0155

theorem c0156 : checkPiece pa19 (1275/512) 0 (1275/512) (2625/1024) = true := by decide +kernel
theorem n0156 : NonnegOnQ (1275/512) (2625/1024) :=
  nonnegOn_of_checkPiece_zero (1275/512) (2625/1024) (by norm_num) c0156

theorem c0157 : checkPiece pa19 (2625/1024) 0 (2625/1024) (675/256) = true := by decide +kernel
theorem n0157 : NonnegOnQ (2625/1024) (675/256) :=
  nonnegOn_of_checkPiece_zero (2625/1024) (675/256) (by norm_num) c0157

theorem c0158 : checkPiece pa19 (675/256) 0 (675/256) (2775/1024) = true := by decide +kernel
theorem n0158 : NonnegOnQ (675/256) (2775/1024) :=
  nonnegOn_of_checkPiece_zero (675/256) (2775/1024) (by norm_num) c0158

theorem c0159 : checkPiece pa19 (2775/1024) 0 (2775/1024) (1425/512) = true := by decide +kernel
theorem n0159 : NonnegOnQ (2775/1024) (1425/512) :=
  nonnegOn_of_checkPiece_zero (2775/1024) (1425/512) (by norm_num) c0159

theorem c0160 : checkPiece pa19 (1425/512) 0 (1425/512) (2925/1024) = true := by decide +kernel
theorem n0160 : NonnegOnQ (1425/512) (2925/1024) :=
  nonnegOn_of_checkPiece_zero (1425/512) (2925/1024) (by norm_num) c0160

theorem c0161 : checkPiece pa19 (2925/1024) 0 (2925/1024) (375/128) = true := by decide +kernel
theorem n0161 : NonnegOnQ (2925/1024) (375/128) :=
  nonnegOn_of_checkPiece_zero (2925/1024) (375/128) (by norm_num) c0161

theorem c0162 : checkPiece pa19 (375/128) 0 (375/128) (3075/1024) = true := by decide +kernel
theorem n0162 : NonnegOnQ (375/128) (3075/1024) :=
  nonnegOn_of_checkPiece_zero (375/128) (3075/1024) (by norm_num) c0162

theorem c0163 : checkPiece pa19 (3075/1024) 0 (3075/1024) (1575/512) = true := by decide +kernel
theorem n0163 : NonnegOnQ (3075/1024) (1575/512) :=
  nonnegOn_of_checkPiece_zero (3075/1024) (1575/512) (by norm_num) c0163

theorem c0164 : checkPiece pa19 (1575/512) 0 (1575/512) (3225/1024) = true := by decide +kernel
theorem n0164 : NonnegOnQ (1575/512) (3225/1024) :=
  nonnegOn_of_checkPiece_zero (1575/512) (3225/1024) (by norm_num) c0164

theorem c0165 : checkPiece pa19 (3225/1024) 0 (3225/1024) (825/256) = true := by decide +kernel
theorem n0165 : NonnegOnQ (3225/1024) (825/256) :=
  nonnegOn_of_checkPiece_zero (3225/1024) (825/256) (by norm_num) c0165

theorem c0166 : checkPiece pa19 (825/256) 0 (825/256) (3375/1024) = true := by decide +kernel
theorem n0166 : NonnegOnQ (825/256) (3375/1024) :=
  nonnegOn_of_checkPiece_zero (825/256) (3375/1024) (by norm_num) c0166

theorem c0167 : checkPiece pa19 (3375/1024) 0 (3375/1024) (1725/512) = true := by decide +kernel
theorem n0167 : NonnegOnQ (3375/1024) (1725/512) :=
  nonnegOn_of_checkPiece_zero (3375/1024) (1725/512) (by norm_num) c0167

theorem c0168 : checkPiece pa19 (1725/512) 0 (1725/512) (3525/1024) = true := by decide +kernel
theorem n0168 : NonnegOnQ (1725/512) (3525/1024) :=
  nonnegOn_of_checkPiece_zero (1725/512) (3525/1024) (by norm_num) c0168

theorem c0169 : checkPiece pa19 (3525/1024) 0 (3525/1024) (225/64) = true := by decide +kernel
theorem n0169 : NonnegOnQ (3525/1024) (225/64) :=
  nonnegOn_of_checkPiece_zero (3525/1024) (225/64) (by norm_num) c0169

theorem c0170 : checkPiece pa19 (225/64) 0 (225/64) (3675/1024) = true := by decide +kernel
theorem n0170 : NonnegOnQ (225/64) (3675/1024) :=
  nonnegOn_of_checkPiece_zero (225/64) (3675/1024) (by norm_num) c0170

theorem c0171 : checkPiece pa19 (3675/1024) 0 (3675/1024) (1875/512) = true := by decide +kernel
theorem n0171 : NonnegOnQ (3675/1024) (1875/512) :=
  nonnegOn_of_checkPiece_zero (3675/1024) (1875/512) (by norm_num) c0171

theorem c0172 : checkPiece pa19 (1875/512) 0 (1875/512) (3825/1024) = true := by decide +kernel
theorem n0172 : NonnegOnQ (1875/512) (3825/1024) :=
  nonnegOn_of_checkPiece_zero (1875/512) (3825/1024) (by norm_num) c0172

theorem c0173 : checkPiece pa19 (3825/1024) 0 (3825/1024) (975/256) = true := by decide +kernel
theorem n0173 : NonnegOnQ (3825/1024) (975/256) :=
  nonnegOn_of_checkPiece_zero (3825/1024) (975/256) (by norm_num) c0173

theorem c0174 : checkPiece pa19 (975/256) 0 (975/256) (3975/1024) = true := by decide +kernel
theorem n0174 : NonnegOnQ (975/256) (3975/1024) :=
  nonnegOn_of_checkPiece_zero (975/256) (3975/1024) (by norm_num) c0174

theorem c0175 : checkPiece pa19 (3975/1024) 0 (3975/1024) (2025/512) = true := by decide +kernel
theorem n0175 : NonnegOnQ (3975/1024) (2025/512) :=
  nonnegOn_of_checkPiece_zero (3975/1024) (2025/512) (by norm_num) c0175

theorem c0176 : checkPiece pa19 (2025/512) 0 (2025/512) (4125/1024) = true := by decide +kernel
theorem n0176 : NonnegOnQ (2025/512) (4125/1024) :=
  nonnegOn_of_checkPiece_zero (2025/512) (4125/1024) (by norm_num) c0176

theorem c0177 : checkPiece pa19 (4125/1024) 0 (4125/1024) (525/128) = true := by decide +kernel
theorem n0177 : NonnegOnQ (4125/1024) (525/128) :=
  nonnegOn_of_checkPiece_zero (4125/1024) (525/128) (by norm_num) c0177

theorem c0178 : checkPiece pa19 (525/128) 0 (525/128) (4275/1024) = true := by decide +kernel
theorem n0178 : NonnegOnQ (525/128) (4275/1024) :=
  nonnegOn_of_checkPiece_zero (525/128) (4275/1024) (by norm_num) c0178

theorem c0179 : checkPiece pa19 (4275/1024) 0 (4275/1024) (2175/512) = true := by decide +kernel
theorem n0179 : NonnegOnQ (4275/1024) (2175/512) :=
  nonnegOn_of_checkPiece_zero (4275/1024) (2175/512) (by norm_num) c0179

theorem c0180 : checkPiece pa19 (2175/512) 0 (2175/512) (4425/1024) = true := by decide +kernel
theorem n0180 : NonnegOnQ (2175/512) (4425/1024) :=
  nonnegOn_of_checkPiece_zero (2175/512) (4425/1024) (by norm_num) c0180

theorem c0181 : checkPiece pa19 (4425/1024) 0 (4425/1024) (1125/256) = true := by decide +kernel
theorem n0181 : NonnegOnQ (4425/1024) (1125/256) :=
  nonnegOn_of_checkPiece_zero (4425/1024) (1125/256) (by norm_num) c0181

theorem c0182 : checkPiece pa19 (1125/256) 0 (1125/256) (4575/1024) = true := by decide +kernel
theorem n0182 : NonnegOnQ (1125/256) (4575/1024) :=
  nonnegOn_of_checkPiece_zero (1125/256) (4575/1024) (by norm_num) c0182

theorem c0183 : checkPiece pa19 (4575/1024) 0 (4575/1024) (2325/512) = true := by decide +kernel
theorem n0183 : NonnegOnQ (4575/1024) (2325/512) :=
  nonnegOn_of_checkPiece_zero (4575/1024) (2325/512) (by norm_num) c0183

theorem c0184 : checkPiece pa19 (2325/512) 0 (2325/512) (4725/1024) = true := by decide +kernel
theorem n0184 : NonnegOnQ (2325/512) (4725/1024) :=
  nonnegOn_of_checkPiece_zero (2325/512) (4725/1024) (by norm_num) c0184

theorem c0185 : checkPiece pa19 (4725/1024) 0 (4725/1024) (75/16) = true := by decide +kernel
theorem n0185 : NonnegOnQ (4725/1024) (75/16) :=
  nonnegOn_of_checkPiece_zero (4725/1024) (75/16) (by norm_num) c0185

theorem c0186 : checkPiece pa19 (75/16) 0 (75/16) (2475/512) = true := by decide +kernel
theorem n0186 : NonnegOnQ (75/16) (2475/512) :=
  nonnegOn_of_checkPiece_zero (75/16) (2475/512) (by norm_num) c0186

theorem c0187 : checkPiece pa19 (2475/512) 0 (2475/512) (1275/256) = true := by decide +kernel
theorem n0187 : NonnegOnQ (2475/512) (1275/256) :=
  nonnegOn_of_checkPiece_zero (2475/512) (1275/256) (by norm_num) c0187

theorem c0188 : checkPiece pa19 (1275/256) 0 (1275/256) (2625/512) = true := by decide +kernel
theorem n0188 : NonnegOnQ (1275/256) (2625/512) :=
  nonnegOn_of_checkPiece_zero (1275/256) (2625/512) (by norm_num) c0188

theorem c0189 : checkPiece pa19 (2625/512) 0 (2625/512) (675/128) = true := by decide +kernel
theorem n0189 : NonnegOnQ (2625/512) (675/128) :=
  nonnegOn_of_checkPiece_zero (2625/512) (675/128) (by norm_num) c0189

theorem c0190 : checkPiece pa19 (675/128) 0 (675/128) (2775/512) = true := by decide +kernel
theorem n0190 : NonnegOnQ (675/128) (2775/512) :=
  nonnegOn_of_checkPiece_zero (675/128) (2775/512) (by norm_num) c0190

theorem c0191 : checkPiece pa19 (2775/512) 0 (2775/512) (1425/256) = true := by decide +kernel
theorem n0191 : NonnegOnQ (2775/512) (1425/256) :=
  nonnegOn_of_checkPiece_zero (2775/512) (1425/256) (by norm_num) c0191

theorem c0192 : checkPiece pa19 (1425/256) 0 (1425/256) (2925/512) = true := by decide +kernel
theorem n0192 : NonnegOnQ (1425/256) (2925/512) :=
  nonnegOn_of_checkPiece_zero (1425/256) (2925/512) (by norm_num) c0192

theorem c0193 : checkPiece pa19 (2925/512) 0 (2925/512) (375/64) = true := by decide +kernel
theorem n0193 : NonnegOnQ (2925/512) (375/64) :=
  nonnegOn_of_checkPiece_zero (2925/512) (375/64) (by norm_num) c0193

theorem c0194 : checkPiece pa19 (375/64) 0 (375/64) (3075/512) = true := by decide +kernel
theorem n0194 : NonnegOnQ (375/64) (3075/512) :=
  nonnegOn_of_checkPiece_zero (375/64) (3075/512) (by norm_num) c0194

theorem c0195 : checkPiece pa19 (3075/512) 0 (3075/512) (1575/256) = true := by decide +kernel
theorem n0195 : NonnegOnQ (3075/512) (1575/256) :=
  nonnegOn_of_checkPiece_zero (3075/512) (1575/256) (by norm_num) c0195

theorem c0196 : checkPiece pa19 (1575/256) 0 (1575/256) (3225/512) = true := by decide +kernel
theorem n0196 : NonnegOnQ (1575/256) (3225/512) :=
  nonnegOn_of_checkPiece_zero (1575/256) (3225/512) (by norm_num) c0196

theorem c0197 : checkPiece pa19 (3225/512) 0 (3225/512) (825/128) = true := by decide +kernel
theorem n0197 : NonnegOnQ (3225/512) (825/128) :=
  nonnegOn_of_checkPiece_zero (3225/512) (825/128) (by norm_num) c0197

theorem c0198 : checkPiece pa19 (825/128) 0 (825/128) (3375/512) = true := by decide +kernel
theorem n0198 : NonnegOnQ (825/128) (3375/512) :=
  nonnegOn_of_checkPiece_zero (825/128) (3375/512) (by norm_num) c0198

theorem c0199 : checkPiece pa19 (3375/512) 0 (3375/512) (1725/256) = true := by decide +kernel
theorem n0199 : NonnegOnQ (3375/512) (1725/256) :=
  nonnegOn_of_checkPiece_zero (3375/512) (1725/256) (by norm_num) c0199

theorem c0200 : checkPiece pa19 (1725/256) 0 (1725/256) (3525/512) = true := by decide +kernel
theorem n0200 : NonnegOnQ (1725/256) (3525/512) :=
  nonnegOn_of_checkPiece_zero (1725/256) (3525/512) (by norm_num) c0200

theorem c0201 : checkPiece pa19 (3525/512) 0 (3525/512) (225/32) = true := by decide +kernel
theorem n0201 : NonnegOnQ (3525/512) (225/32) :=
  nonnegOn_of_checkPiece_zero (3525/512) (225/32) (by norm_num) c0201

theorem c0202 : checkPiece pa19 (225/32) 0 (225/32) (3675/512) = true := by decide +kernel
theorem n0202 : NonnegOnQ (225/32) (3675/512) :=
  nonnegOn_of_checkPiece_zero (225/32) (3675/512) (by norm_num) c0202

theorem c0203 : checkPiece pa19 (3675/512) 0 (3675/512) (1875/256) = true := by decide +kernel
theorem n0203 : NonnegOnQ (3675/512) (1875/256) :=
  nonnegOn_of_checkPiece_zero (3675/512) (1875/256) (by norm_num) c0203

theorem c0204 : checkPiece pa19 (1875/256) 0 (1875/256) (3825/512) = true := by decide +kernel
theorem n0204 : NonnegOnQ (1875/256) (3825/512) :=
  nonnegOn_of_checkPiece_zero (1875/256) (3825/512) (by norm_num) c0204

theorem c0205 : checkPiece pa19 (3825/512) 0 (3825/512) (975/128) = true := by decide +kernel
theorem n0205 : NonnegOnQ (3825/512) (975/128) :=
  nonnegOn_of_checkPiece_zero (3825/512) (975/128) (by norm_num) c0205

theorem c0206 : checkPiece pa19 (975/128) 0 (975/128) (3975/512) = true := by decide +kernel
theorem n0206 : NonnegOnQ (975/128) (3975/512) :=
  nonnegOn_of_checkPiece_zero (975/128) (3975/512) (by norm_num) c0206

theorem c0207 : checkPiece pa19 (3975/512) 0 (3975/512) (2025/256) = true := by decide +kernel
theorem n0207 : NonnegOnQ (3975/512) (2025/256) :=
  nonnegOn_of_checkPiece_zero (3975/512) (2025/256) (by norm_num) c0207

theorem c0208 : checkPiece pa19 (2025/256) 0 (2025/256) (4125/512) = true := by decide +kernel
theorem n0208 : NonnegOnQ (2025/256) (4125/512) :=
  nonnegOn_of_checkPiece_zero (2025/256) (4125/512) (by norm_num) c0208

theorem c0209 : checkPiece pa19 (4125/512) 0 (4125/512) (525/64) = true := by decide +kernel
theorem n0209 : NonnegOnQ (4125/512) (525/64) :=
  nonnegOn_of_checkPiece_zero (4125/512) (525/64) (by norm_num) c0209

theorem c0210 : checkPiece pa19 (525/64) 0 (525/64) (4275/512) = true := by decide +kernel
theorem n0210 : NonnegOnQ (525/64) (4275/512) :=
  nonnegOn_of_checkPiece_zero (525/64) (4275/512) (by norm_num) c0210

theorem c0211 : checkPiece pa19 (4275/512) 0 (4275/512) (2175/256) = true := by decide +kernel
theorem n0211 : NonnegOnQ (4275/512) (2175/256) :=
  nonnegOn_of_checkPiece_zero (4275/512) (2175/256) (by norm_num) c0211

theorem c0212 : checkPiece pa19 (2175/256) 0 (2175/256) (4425/512) = true := by decide +kernel
theorem n0212 : NonnegOnQ (2175/256) (4425/512) :=
  nonnegOn_of_checkPiece_zero (2175/256) (4425/512) (by norm_num) c0212

theorem c0213 : checkPiece pa19 (4425/512) 0 (4425/512) (1125/128) = true := by decide +kernel
theorem n0213 : NonnegOnQ (4425/512) (1125/128) :=
  nonnegOn_of_checkPiece_zero (4425/512) (1125/128) (by norm_num) c0213

theorem c0214 : checkPiece pa19 (1125/128) 0 (1125/128) (4575/512) = true := by decide +kernel
theorem n0214 : NonnegOnQ (1125/128) (4575/512) :=
  nonnegOn_of_checkPiece_zero (1125/128) (4575/512) (by norm_num) c0214

theorem c0215 : checkPiece pa19 (4575/512) 0 (4575/512) (2325/256) = true := by decide +kernel
theorem n0215 : NonnegOnQ (4575/512) (2325/256) :=
  nonnegOn_of_checkPiece_zero (4575/512) (2325/256) (by norm_num) c0215

theorem c0216 : checkPiece pa19 (2325/256) 0 (2325/256) (4725/512) = true := by decide +kernel
theorem n0216 : NonnegOnQ (2325/256) (4725/512) :=
  nonnegOn_of_checkPiece_zero (2325/256) (4725/512) (by norm_num) c0216

theorem c0217 : checkPiece pa19 (4725/512) 0 (4725/512) (75/8) = true := by decide +kernel
theorem n0217 : NonnegOnQ (4725/512) (75/8) :=
  nonnegOn_of_checkPiece_zero (4725/512) (75/8) (by norm_num) c0217

theorem c0218 : checkPiece pa19 (75/8) 0 (75/8) (4875/512) = true := by decide +kernel
theorem n0218 : NonnegOnQ (75/8) (4875/512) :=
  nonnegOn_of_checkPiece_zero (75/8) (4875/512) (by norm_num) c0218

theorem c0219 : checkPiece pa19 (4875/512) 0 (4875/512) (2475/256) = true := by decide +kernel
theorem n0219 : NonnegOnQ (4875/512) (2475/256) :=
  nonnegOn_of_checkPiece_zero (4875/512) (2475/256) (by norm_num) c0219

theorem c0220 : checkPiece pa19 (2475/256) 0 (2475/256) (1275/128) = true := by decide +kernel
theorem n0220 : NonnegOnQ (2475/256) (1275/128) :=
  nonnegOn_of_checkPiece_zero (2475/256) (1275/128) (by norm_num) c0220

theorem c0221 : checkPiece pa19 (1275/128) 0 (1275/128) (2625/256) = true := by decide +kernel
theorem n0221 : NonnegOnQ (1275/128) (2625/256) :=
  nonnegOn_of_checkPiece_zero (1275/128) (2625/256) (by norm_num) c0221

theorem c0222 : checkPiece pa19 (2625/256) 0 (2625/256) (675/64) = true := by decide +kernel
theorem n0222 : NonnegOnQ (2625/256) (675/64) :=
  nonnegOn_of_checkPiece_zero (2625/256) (675/64) (by norm_num) c0222

theorem c0223 : checkPiece pa19 (675/64) 0 (675/64) (2775/256) = true := by decide +kernel
theorem n0223 : NonnegOnQ (675/64) (2775/256) :=
  nonnegOn_of_checkPiece_zero (675/64) (2775/256) (by norm_num) c0223

theorem c0224 : checkPiece pa19 (2775/256) 0 (2775/256) (1425/128) = true := by decide +kernel
theorem n0224 : NonnegOnQ (2775/256) (1425/128) :=
  nonnegOn_of_checkPiece_zero (2775/256) (1425/128) (by norm_num) c0224

theorem c0225 : checkPiece pa19 (1425/128) 0 (1425/128) (2925/256) = true := by decide +kernel
theorem n0225 : NonnegOnQ (1425/128) (2925/256) :=
  nonnegOn_of_checkPiece_zero (1425/128) (2925/256) (by norm_num) c0225

theorem c0226 : checkPiece pa19 (2925/256) 0 (2925/256) (375/32) = true := by decide +kernel
theorem n0226 : NonnegOnQ (2925/256) (375/32) :=
  nonnegOn_of_checkPiece_zero (2925/256) (375/32) (by norm_num) c0226

theorem c0227 : checkPiece pa19 (375/32) 0 (375/32) (3075/256) = true := by decide +kernel
theorem n0227 : NonnegOnQ (375/32) (3075/256) :=
  nonnegOn_of_checkPiece_zero (375/32) (3075/256) (by norm_num) c0227

theorem c0228 : checkPiece pa19 (3075/256) 0 (3075/256) (1575/128) = true := by decide +kernel
theorem n0228 : NonnegOnQ (3075/256) (1575/128) :=
  nonnegOn_of_checkPiece_zero (3075/256) (1575/128) (by norm_num) c0228

theorem c0229 : checkPiece pa19 (1575/128) 0 (1575/128) (3225/256) = true := by decide +kernel
theorem n0229 : NonnegOnQ (1575/128) (3225/256) :=
  nonnegOn_of_checkPiece_zero (1575/128) (3225/256) (by norm_num) c0229

theorem c0230 : checkPiece pa19 (3225/256) 0 (3225/256) (825/64) = true := by decide +kernel
theorem n0230 : NonnegOnQ (3225/256) (825/64) :=
  nonnegOn_of_checkPiece_zero (3225/256) (825/64) (by norm_num) c0230

theorem c0231 : checkPiece pa19 (825/64) 0 (825/64) (6675/512) = true := by decide +kernel
theorem n0231 : NonnegOnQ (825/64) (6675/512) :=
  nonnegOn_of_checkPiece_zero (825/64) (6675/512) (by norm_num) c0231

theorem c0232 : checkPiece pa19 (6675/512) 0 (6675/512) (3375/256) = true := by decide +kernel
theorem n0232 : NonnegOnQ (6675/512) (3375/256) :=
  nonnegOn_of_checkPiece_zero (6675/512) (3375/256) (by norm_num) c0232

theorem c0233 : checkPiece pa19 (3375/256) 0 (3375/256) (6825/512) = true := by decide +kernel
theorem n0233 : NonnegOnQ (3375/256) (6825/512) :=
  nonnegOn_of_checkPiece_zero (3375/256) (6825/512) (by norm_num) c0233

theorem c0234 : checkPiece pa19 (6825/512) 0 (6825/512) (1725/128) = true := by decide +kernel
theorem n0234 : NonnegOnQ (6825/512) (1725/128) :=
  nonnegOn_of_checkPiece_zero (6825/512) (1725/128) (by norm_num) c0234

theorem c0235 : checkPiece pa19 (1725/128) 0 (1725/128) (3525/256) = true := by decide +kernel
theorem n0235 : NonnegOnQ (1725/128) (3525/256) :=
  nonnegOn_of_checkPiece_zero (1725/128) (3525/256) (by norm_num) c0235

theorem c0236 : checkPiece pa19 (3525/256) 0 (3525/256) (225/16) = true := by decide +kernel
theorem n0236 : NonnegOnQ (3525/256) (225/16) :=
  nonnegOn_of_checkPiece_zero (3525/256) (225/16) (by norm_num) c0236

theorem c0237 : checkPiece pa19 (225/16) 0 (225/16) (3675/256) = true := by decide +kernel
theorem n0237 : NonnegOnQ (225/16) (3675/256) :=
  nonnegOn_of_checkPiece_zero (225/16) (3675/256) (by norm_num) c0237

theorem c0238 : checkPiece pa19 (3675/256) 0 (3675/256) (1875/128) = true := by decide +kernel
theorem n0238 : NonnegOnQ (3675/256) (1875/128) :=
  nonnegOn_of_checkPiece_zero (3675/256) (1875/128) (by norm_num) c0238

theorem c0239 : checkPiece pa19 (1875/128) 0 (1875/128) (3825/256) = true := by decide +kernel
theorem n0239 : NonnegOnQ (1875/128) (3825/256) :=
  nonnegOn_of_checkPiece_zero (1875/128) (3825/256) (by norm_num) c0239

theorem c0240 : checkPiece pa19 (3825/256) 0 (3825/256) (975/64) = true := by decide +kernel
theorem n0240 : NonnegOnQ (3825/256) (975/64) :=
  nonnegOn_of_checkPiece_zero (3825/256) (975/64) (by norm_num) c0240

theorem c0241 : checkPiece pa19 (975/64) 0 (975/64) (3975/256) = true := by decide +kernel
theorem n0241 : NonnegOnQ (975/64) (3975/256) :=
  nonnegOn_of_checkPiece_zero (975/64) (3975/256) (by norm_num) c0241

theorem c0242 : checkPiece pa19 (3975/256) 0 (3975/256) (2025/128) = true := by decide +kernel
theorem n0242 : NonnegOnQ (3975/256) (2025/128) :=
  nonnegOn_of_checkPiece_zero (3975/256) (2025/128) (by norm_num) c0242

theorem c0243 : checkPiece pa19 (2025/128) 0 (2025/128) (4125/256) = true := by decide +kernel
theorem n0243 : NonnegOnQ (2025/128) (4125/256) :=
  nonnegOn_of_checkPiece_zero (2025/128) (4125/256) (by norm_num) c0243

theorem c0244 : checkPiece pa19 (4125/256) 0 (4125/256) (8325/512) = true := by decide +kernel
theorem n0244 : NonnegOnQ (4125/256) (8325/512) :=
  nonnegOn_of_checkPiece_zero (4125/256) (8325/512) (by norm_num) c0244

theorem c0245 : checkPiece pa19 (8325/512) 0 (8325/512) (525/32) = true := by decide +kernel
theorem n0245 : NonnegOnQ (8325/512) (525/32) :=
  nonnegOn_of_checkPiece_zero (8325/512) (525/32) (by norm_num) c0245

theorem c0246 : checkPiece pa19 (525/32) 0 (525/32) (4275/256) = true := by decide +kernel
theorem n0246 : NonnegOnQ (525/32) (4275/256) :=
  nonnegOn_of_checkPiece_zero (525/32) (4275/256) (by norm_num) c0246

theorem c0247 : checkPiece pa19 (4275/256) 0 (4275/256) (2175/128) = true := by decide +kernel
theorem n0247 : NonnegOnQ (4275/256) (2175/128) :=
  nonnegOn_of_checkPiece_zero (4275/256) (2175/128) (by norm_num) c0247

theorem c0248 : checkPiece pa19 (2175/128) 0 (2175/128) (4425/256) = true := by decide +kernel
theorem n0248 : NonnegOnQ (2175/128) (4425/256) :=
  nonnegOn_of_checkPiece_zero (2175/128) (4425/256) (by norm_num) c0248

theorem c0249 : checkPiece pa19 (4425/256) 0 (4425/256) (1125/64) = true := by decide +kernel
theorem n0249 : NonnegOnQ (4425/256) (1125/64) :=
  nonnegOn_of_checkPiece_zero (4425/256) (1125/64) (by norm_num) c0249

theorem c0250 : checkPiece pa19 (1125/64) 0 (1125/64) (4575/256) = true := by decide +kernel
theorem n0250 : NonnegOnQ (1125/64) (4575/256) :=
  nonnegOn_of_checkPiece_zero (1125/64) (4575/256) (by norm_num) c0250

theorem c0251 : checkPiece pa19 (4575/256) 0 (4575/256) (2325/128) = true := by decide +kernel
theorem n0251 : NonnegOnQ (4575/256) (2325/128) :=
  nonnegOn_of_checkPiece_zero (4575/256) (2325/128) (by norm_num) c0251

theorem c0252 : checkPiece pa19 (2325/128) 0 (2325/128) (4725/256) = true := by decide +kernel
theorem n0252 : NonnegOnQ (2325/128) (4725/256) :=
  nonnegOn_of_checkPiece_zero (2325/128) (4725/256) (by norm_num) c0252

theorem c0253 : checkPiece pa19 (4725/256) 0 (4725/256) (75/4) = true := by decide +kernel
theorem n0253 : NonnegOnQ (4725/256) (75/4) :=
  nonnegOn_of_checkPiece_zero (4725/256) (75/4) (by norm_num) c0253

theorem c0254 : checkPiece pa19 (75/4) 0 (75/4) (4875/256) = true := by decide +kernel
theorem n0254 : NonnegOnQ (75/4) (4875/256) :=
  nonnegOn_of_checkPiece_zero (75/4) (4875/256) (by norm_num) c0254

theorem c0255 : checkPiece pa19 (4875/256) 0 (4875/256) (2475/128) = true := by decide +kernel
theorem n0255 : NonnegOnQ (4875/256) (2475/128) :=
  nonnegOn_of_checkPiece_zero (4875/256) (2475/128) (by norm_num) c0255

theorem c0256 : checkPiece pa19 (2475/128) 0 (2475/128) (5025/256) = true := by decide +kernel
theorem n0256 : NonnegOnQ (2475/128) (5025/256) :=
  nonnegOn_of_checkPiece_zero (2475/128) (5025/256) (by norm_num) c0256

theorem c0257 : checkPiece pa19 (5025/256) 0 (5025/256) (1275/64) = true := by decide +kernel
theorem n0257 : NonnegOnQ (5025/256) (1275/64) :=
  nonnegOn_of_checkPiece_zero (5025/256) (1275/64) (by norm_num) c0257

theorem c0258 : checkPiece pa19 (1275/64) 0 (1275/64) (5175/256) = true := by decide +kernel
theorem n0258 : NonnegOnQ (1275/64) (5175/256) :=
  nonnegOn_of_checkPiece_zero (1275/64) (5175/256) (by norm_num) c0258

theorem c0259 : checkPiece pa19 (5175/256) 0 (5175/256) (10425/512) = true := by decide +kernel
theorem n0259 : NonnegOnQ (5175/256) (10425/512) :=
  nonnegOn_of_checkPiece_zero (5175/256) (10425/512) (by norm_num) c0259

theorem c0260 : checkPiece pa19 (10425/512) 0 (10425/512) (2625/128) = true := by decide +kernel
theorem n0260 : NonnegOnQ (10425/512) (2625/128) :=
  nonnegOn_of_checkPiece_zero (10425/512) (2625/128) (by norm_num) c0260

theorem c0261 : checkPiece pa19 (2625/128) 0 (2625/128) (5325/256) = true := by decide +kernel
theorem n0261 : NonnegOnQ (2625/128) (5325/256) :=
  nonnegOn_of_checkPiece_zero (2625/128) (5325/256) (by norm_num) c0261

theorem c0262 : checkPiece pa19 (5325/256) 0 (5325/256) (675/32) = true := by decide +kernel
theorem n0262 : NonnegOnQ (5325/256) (675/32) :=
  nonnegOn_of_checkPiece_zero (5325/256) (675/32) (by norm_num) c0262

theorem c0263 : checkPiece pa19 (675/32) 0 (675/32) (2775/128) = true := by decide +kernel
theorem n0263 : NonnegOnQ (675/32) (2775/128) :=
  nonnegOn_of_checkPiece_zero (675/32) (2775/128) (by norm_num) c0263

theorem c0264 : checkPiece pa19 (2775/128) 0 (2775/128) (1425/64) = true := by decide +kernel
theorem n0264 : NonnegOnQ (2775/128) (1425/64) :=
  nonnegOn_of_checkPiece_zero (2775/128) (1425/64) (by norm_num) c0264

theorem c0265 : checkPiece pa19 (1425/64) 0 (1425/64) (375/16) = true := by decide +kernel
theorem n0265 : NonnegOnQ (1425/64) (375/16) :=
  nonnegOn_of_checkPiece_zero (1425/64) (375/16) (by norm_num) c0265

theorem c0266 : checkPiece pa19 (375/16) 0 (375/16) (1575/64) = true := by decide +kernel
theorem n0266 : NonnegOnQ (375/16) (1575/64) :=
  nonnegOn_of_checkPiece_zero (375/16) (1575/64) (by norm_num) c0266

theorem c0267 : checkPiece pa19 (1575/64) 0 (1575/64) (3225/128) = true := by decide +kernel
theorem n0267 : NonnegOnQ (1575/64) (3225/128) :=
  nonnegOn_of_checkPiece_zero (1575/64) (3225/128) (by norm_num) c0267

theorem c0268 : checkPiece pa19 (3225/128) 0 (3225/128) (6525/256) = true := by decide +kernel
theorem n0268 : NonnegOnQ (3225/128) (6525/256) :=
  nonnegOn_of_checkPiece_zero (3225/128) (6525/256) (by norm_num) c0268

theorem c0269 : checkPiece pa19 (6525/256) 0 (6525/256) (825/32) = true := by decide +kernel
theorem n0269 : NonnegOnQ (6525/256) (825/32) :=
  nonnegOn_of_checkPiece_zero (6525/256) (825/32) (by norm_num) c0269

theorem c0270 : checkPiece pa19 (825/32) 0 (825/32) (6675/256) = true := by decide +kernel
theorem n0270 : NonnegOnQ (825/32) (6675/256) :=
  nonnegOn_of_checkPiece_zero (825/32) (6675/256) (by norm_num) c0270

theorem c0271 : checkPiece pa19 (6675/256) 0 (6675/256) (13425/512) = true := by decide +kernel
theorem n0271 : NonnegOnQ (6675/256) (13425/512) :=
  nonnegOn_of_checkPiece_zero (6675/256) (13425/512) (by norm_num) c0271

theorem c0272 : checkPiece pa19 (13425/512) 0 (13425/512) (3375/128) = true := by decide +kernel
theorem n0272 : NonnegOnQ (13425/512) (3375/128) :=
  nonnegOn_of_checkPiece_zero (13425/512) (3375/128) (by norm_num) c0272

theorem c0273 : checkPiece pa19 (3375/128) 0 (3375/128) (6825/256) = true := by decide +kernel
theorem n0273 : NonnegOnQ (3375/128) (6825/256) :=
  nonnegOn_of_checkPiece_zero (3375/128) (6825/256) (by norm_num) c0273

theorem c0274 : checkPiece pa19 (6825/256) 0 (6825/256) (1725/64) = true := by decide +kernel
theorem n0274 : NonnegOnQ (6825/256) (1725/64) :=
  nonnegOn_of_checkPiece_zero (6825/256) (1725/64) (by norm_num) c0274

theorem c0275 : checkPiece pa19 (1725/64) 0 (1725/64) (6975/256) = true := by decide +kernel
theorem n0275 : NonnegOnQ (1725/64) (6975/256) :=
  nonnegOn_of_checkPiece_zero (1725/64) (6975/256) (by norm_num) c0275

theorem c0276 : checkPiece pa19 (6975/256) 0 (6975/256) (3525/128) = true := by decide +kernel
theorem n0276 : NonnegOnQ (6975/256) (3525/128) :=
  nonnegOn_of_checkPiece_zero (6975/256) (3525/128) (by norm_num) c0276

theorem c0277 : checkPiece pa19 (3525/128) 0 (3525/128) (7125/256) = true := by decide +kernel
theorem n0277 : NonnegOnQ (3525/128) (7125/256) :=
  nonnegOn_of_checkPiece_zero (3525/128) (7125/256) (by norm_num) c0277

theorem c0278 : checkPiece pa19 (7125/256) 0 (7125/256) (225/8) = true := by decide +kernel
theorem n0278 : NonnegOnQ (7125/256) (225/8) :=
  nonnegOn_of_checkPiece_zero (7125/256) (225/8) (by norm_num) c0278

theorem c0279 : checkPiece pa19 (225/8) 0 (225/8) (7275/256) = true := by decide +kernel
theorem n0279 : NonnegOnQ (225/8) (7275/256) :=
  nonnegOn_of_checkPiece_zero (225/8) (7275/256) (by norm_num) c0279

theorem c0280 : checkPiece pa19 (7275/256) 0 (7275/256) (3675/128) = true := by decide +kernel
theorem n0280 : NonnegOnQ (7275/256) (3675/128) :=
  nonnegOn_of_checkPiece_zero (7275/256) (3675/128) (by norm_num) c0280

theorem c0281 : checkPiece pa19 (3675/128) 0 (3675/128) (7425/256) = true := by decide +kernel
theorem n0281 : NonnegOnQ (3675/128) (7425/256) :=
  nonnegOn_of_checkPiece_zero (3675/128) (7425/256) (by norm_num) c0281

theorem c0282 : checkPiece pa19 (7425/256) 0 (7425/256) (1875/64) = true := by decide +kernel
theorem n0282 : NonnegOnQ (7425/256) (1875/64) :=
  nonnegOn_of_checkPiece_zero (7425/256) (1875/64) (by norm_num) c0282

theorem c0283 : checkPiece pa19 (1875/64) 0 (1875/64) (975/32) = true := by decide +kernel
theorem n0283 : NonnegOnQ (1875/64) (975/32) :=
  nonnegOn_of_checkPiece_zero (1875/64) (975/32) (by norm_num) c0283

theorem c0284 : checkPiece pa19 (975/32) 0 (975/32) (525/16) = true := by decide +kernel
theorem n0284 : NonnegOnQ (975/32) (525/16) :=
  nonnegOn_of_checkPiece_zero (975/32) (525/16) (by norm_num) c0284

theorem c0285 : checkPiece pa19 (525/16) 0 (525/16) (2175/64) = true := by decide +kernel
theorem n0285 : NonnegOnQ (525/16) (2175/64) :=
  nonnegOn_of_checkPiece_zero (525/16) (2175/64) (by norm_num) c0285

theorem c0286 : checkPiece pa19 (2175/64) 0 (2175/64) (4425/128) = true := by decide +kernel
theorem n0286 : NonnegOnQ (2175/64) (4425/128) :=
  nonnegOn_of_checkPiece_zero (2175/64) (4425/128) (by norm_num) c0286

theorem c0287 : checkPiece pa19 (4425/128) 0 (4425/128) (8925/256) = true := by decide +kernel
theorem n0287 : NonnegOnQ (4425/128) (8925/256) :=
  nonnegOn_of_checkPiece_zero (4425/128) (8925/256) (by norm_num) c0287

theorem c0288 : checkPiece pa19 (8925/256) 0 (8925/256) (1125/32) = true := by decide +kernel
theorem n0288 : NonnegOnQ (8925/256) (1125/32) :=
  nonnegOn_of_checkPiece_zero (8925/256) (1125/32) (by norm_num) c0288

theorem c0289 : checkPiece pa19 (1125/32) 0 (1125/32) (9075/256) = true := by decide +kernel
theorem n0289 : NonnegOnQ (1125/32) (9075/256) :=
  nonnegOn_of_checkPiece_zero (1125/32) (9075/256) (by norm_num) c0289

theorem c0290 : checkPiece pa19 (9075/256) 0 (9075/256) (4575/128) = true := by decide +kernel
theorem n0290 : NonnegOnQ (9075/256) (4575/128) :=
  nonnegOn_of_checkPiece_zero (9075/256) (4575/128) (by norm_num) c0290

theorem c0291 : checkPiece pa19 (4575/128) 0 (4575/128) (9225/256) = true := by decide +kernel
theorem n0291 : NonnegOnQ (4575/128) (9225/256) :=
  nonnegOn_of_checkPiece_zero (4575/128) (9225/256) (by norm_num) c0291

theorem c0292 : checkPiece pa19 (9225/256) 0 (9225/256) (18525/512) = true := by decide +kernel
theorem n0292 : NonnegOnQ (9225/256) (18525/512) :=
  nonnegOn_of_checkPiece_zero (9225/256) (18525/512) (by norm_num) c0292

theorem c0293 : checkPiece pa19 (18525/512) 0 (18525/512) (2325/64) = true := by decide +kernel
theorem n0293 : NonnegOnQ (18525/512) (2325/64) :=
  nonnegOn_of_checkPiece_zero (18525/512) (2325/64) (by norm_num) c0293

theorem c0294 : checkPiece pa19 (2325/64) 0 (2325/64) (9375/256) = true := by decide +kernel
theorem n0294 : NonnegOnQ (2325/64) (9375/256) :=
  nonnegOn_of_checkPiece_zero (2325/64) (9375/256) (by norm_num) c0294

theorem c0295 : checkPiece pa19 (9375/256) 0 (9375/256) (4725/128) = true := by decide +kernel
theorem n0295 : NonnegOnQ (9375/256) (4725/128) :=
  nonnegOn_of_checkPiece_zero (9375/256) (4725/128) (by norm_num) c0295

theorem c0296 : checkPiece pa19 (4725/128) 0 (4725/128) (75/2) = true := by decide +kernel
theorem n0296 : NonnegOnQ (4725/128) (75/2) :=
  nonnegOn_of_checkPiece_zero (4725/128) (75/2) (by norm_num) c0296

theorem c0297 : checkPiece pa19 (75/2) 0 (75/2) (1275/32) = true := by decide +kernel
theorem n0297 : NonnegOnQ (75/2) (1275/32) :=
  nonnegOn_of_checkPiece_zero (75/2) (1275/32) (by norm_num) c0297

theorem c0298 : checkPiece pa19 (1275/32) 0 (1275/32) (675/16) = true := by decide +kernel
theorem n0298 : NonnegOnQ (1275/32) (675/16) :=
  nonnegOn_of_checkPiece_zero (1275/32) (675/16) (by norm_num) c0298

theorem c0299 : checkPiece pa19 (675/16) 0 (675/16) (2775/64) = true := by decide +kernel
theorem n0299 : NonnegOnQ (675/16) (2775/64) :=
  nonnegOn_of_checkPiece_zero (675/16) (2775/64) (by norm_num) c0299

theorem c0300 : checkPiece pa19 (2775/64) 0 (2775/64) (1425/32) = true := by decide +kernel
theorem n0300 : NonnegOnQ (2775/64) (1425/32) :=
  nonnegOn_of_checkPiece_zero (2775/64) (1425/32) (by norm_num) c0300

theorem c0301 : checkPiece pa19 (1425/32) 0 (1425/32) (2925/64) = true := by decide +kernel
theorem n0301 : NonnegOnQ (1425/32) (2925/64) :=
  nonnegOn_of_checkPiece_zero (1425/32) (2925/64) (by norm_num) c0301

theorem c0302 : checkPiece pa19 (2925/64) 0 (2925/64) (375/8) = true := by decide +kernel
theorem n0302 : NonnegOnQ (2925/64) (375/8) :=
  nonnegOn_of_checkPiece_zero (2925/64) (375/8) (by norm_num) c0302

theorem c0303 : checkPiece pa19 (375/8) 0 (375/8) (1575/32) = true := by decide +kernel
theorem n0303 : NonnegOnQ (375/8) (1575/32) :=
  nonnegOn_of_checkPiece_zero (375/8) (1575/32) (by norm_num) c0303

theorem c0304 : checkPiece pa19 (1575/32) 0 (1575/32) (825/16) = true := by decide +kernel
theorem n0304 : NonnegOnQ (1575/32) (825/16) :=
  nonnegOn_of_checkPiece_zero (1575/32) (825/16) (by norm_num) c0304

theorem c0305 : checkPiece pa19 (825/16) 0 (825/16) (1725/32) = true := by decide +kernel
theorem n0305 : NonnegOnQ (825/16) (1725/32) :=
  nonnegOn_of_checkPiece_zero (825/16) (1725/32) (by norm_num) c0305

theorem c0306 : checkPiece pa19 (1725/32) 0 (1725/32) (225/4) = true := by decide +kernel
theorem n0306 : NonnegOnQ (1725/32) (225/4) :=
  nonnegOn_of_checkPiece_zero (1725/32) (225/4) (by norm_num) c0306

theorem c0307 : checkPiece pa19 (225/4) 0 (225/4) (1875/32) = true := by decide +kernel
theorem n0307 : NonnegOnQ (225/4) (1875/32) :=
  nonnegOn_of_checkPiece_zero (225/4) (1875/32) (by norm_num) c0307

theorem c0308 : checkPiece pa19 (1875/32) 0 (1875/32) (975/16) = true := by decide +kernel
theorem n0308 : NonnegOnQ (1875/32) (975/16) :=
  nonnegOn_of_checkPiece_zero (1875/32) (975/16) (by norm_num) c0308

theorem c0309 : checkPiece pa19 (975/16) 0 (975/16) (2025/32) = true := by decide +kernel
theorem n0309 : NonnegOnQ (975/16) (2025/32) :=
  nonnegOn_of_checkPiece_zero (975/16) (2025/32) (by norm_num) c0309

theorem c0310 : checkPiece pa19 (2025/32) 0 (2025/32) (525/8) = true := by decide +kernel
theorem n0310 : NonnegOnQ (2025/32) (525/8) :=
  nonnegOn_of_checkPiece_zero (2025/32) (525/8) (by norm_num) c0310

theorem c0311 : checkPiece pa19 (525/8) 0 (525/8) (2175/32) = true := by decide +kernel
theorem n0311 : NonnegOnQ (525/8) (2175/32) :=
  nonnegOn_of_checkPiece_zero (525/8) (2175/32) (by norm_num) c0311

theorem c0312 : checkPiece pa19 (2175/32) 0 (2175/32) (1125/16) = true := by decide +kernel
theorem n0312 : NonnegOnQ (2175/32) (1125/16) :=
  nonnegOn_of_checkPiece_zero (2175/32) (1125/16) (by norm_num) c0312

theorem c0313 : checkPiece pa19 (1125/16) 0 (1125/16) (2325/32) = true := by decide +kernel
theorem n0313 : NonnegOnQ (1125/16) (2325/32) :=
  nonnegOn_of_checkPiece_zero (1125/16) (2325/32) (by norm_num) c0313

theorem c0314 : checkPiece pa19 (2325/32) 0 (2325/32) (4725/64) = true := by decide +kernel
theorem n0314 : NonnegOnQ (2325/32) (4725/64) :=
  nonnegOn_of_checkPiece_zero (2325/32) (4725/64) (by norm_num) c0314

theorem c0315 : checkPiece pa19 (4725/64) 0 (4725/64) (75) = true := by decide +kernel
theorem n0315 : NonnegOnQ (4725/64) (75) :=
  nonnegOn_of_checkPiece_zero (4725/64) (75) (by norm_num) c0315

theorem c0316 : checkPiece pa19 (75) 0 (75) (2475/32) = true := by decide +kernel
theorem n0316 : NonnegOnQ (75) (2475/32) :=
  nonnegOn_of_checkPiece_zero (75) (2475/32) (by norm_num) c0316

theorem c0317 : checkPiece pa19 (2475/32) 0 (2475/32) (1275/16) = true := by decide +kernel
theorem n0317 : NonnegOnQ (2475/32) (1275/16) :=
  nonnegOn_of_checkPiece_zero (2475/32) (1275/16) (by norm_num) c0317

theorem c0318 : checkPiece pa19 (1275/16) 0 (1275/16) (5175/64) = true := by decide +kernel
theorem n0318 : NonnegOnQ (1275/16) (5175/64) :=
  nonnegOn_of_checkPiece_zero (1275/16) (5175/64) (by norm_num) c0318

theorem c0319 : checkPiece pa19 (5175/64) 0 (5175/64) (2625/32) = true := by decide +kernel
theorem n0319 : NonnegOnQ (5175/64) (2625/32) :=
  nonnegOn_of_checkPiece_zero (5175/64) (2625/32) (by norm_num) c0319

theorem c0320 : checkPiece pa19 (2625/32) 0 (2625/32) (5325/64) = true := by decide +kernel
theorem n0320 : NonnegOnQ (2625/32) (5325/64) :=
  nonnegOn_of_checkPiece_zero (2625/32) (5325/64) (by norm_num) c0320

theorem c0321 : checkPiece pa19 (5325/64) 0 (5325/64) (675/8) = true := by decide +kernel
theorem n0321 : NonnegOnQ (5325/64) (675/8) :=
  nonnegOn_of_checkPiece_zero (5325/64) (675/8) (by norm_num) c0321

theorem c0322 : checkPiece pa19 (675/8) 0 (675/8) (2775/32) = true := by decide +kernel
theorem n0322 : NonnegOnQ (675/8) (2775/32) :=
  nonnegOn_of_checkPiece_zero (675/8) (2775/32) (by norm_num) c0322

theorem c0323 : checkPiece pa19 (2775/32) 0 (2775/32) (1425/16) = true := by decide +kernel
theorem n0323 : NonnegOnQ (2775/32) (1425/16) :=
  nonnegOn_of_checkPiece_zero (2775/32) (1425/16) (by norm_num) c0323

theorem c0324 : checkPiece pa19 (1425/16) 0 (1425/16) (5775/64) = true := by decide +kernel
theorem n0324 : NonnegOnQ (1425/16) (5775/64) :=
  nonnegOn_of_checkPiece_zero (1425/16) (5775/64) (by norm_num) c0324

theorem c0325 : checkPiece pa19 (5775/64) 0 (5775/64) (2925/32) = true := by decide +kernel
theorem n0325 : NonnegOnQ (5775/64) (2925/32) :=
  nonnegOn_of_checkPiece_zero (5775/64) (2925/32) (by norm_num) c0325

theorem c0326 : checkPiece pa19 (2925/32) 0 (2925/32) (375/4) = true := by decide +kernel
theorem n0326 : NonnegOnQ (2925/32) (375/4) :=
  nonnegOn_of_checkPiece_zero (2925/32) (375/4) (by norm_num) c0326

theorem c0327 : checkPiece pa19 (375/4) 0 (375/4) (3075/32) = true := by decide +kernel
theorem n0327 : NonnegOnQ (375/4) (3075/32) :=
  nonnegOn_of_checkPiece_zero (375/4) (3075/32) (by norm_num) c0327

theorem c0328 : checkPiece pa19 (3075/32) 0 (3075/32) (1575/16) = true := by decide +kernel
theorem n0328 : NonnegOnQ (3075/32) (1575/16) :=
  nonnegOn_of_checkPiece_zero (3075/32) (1575/16) (by norm_num) c0328

theorem c0329 : checkPiece pa19 (1575/16) 0 (1575/16) (3225/32) = true := by decide +kernel
theorem n0329 : NonnegOnQ (1575/16) (3225/32) :=
  nonnegOn_of_checkPiece_zero (1575/16) (3225/32) (by norm_num) c0329

theorem c0330 : checkPiece pa19 (3225/32) 0 (3225/32) (825/8) = true := by decide +kernel
theorem n0330 : NonnegOnQ (3225/32) (825/8) :=
  nonnegOn_of_checkPiece_zero (3225/32) (825/8) (by norm_num) c0330

theorem c0331 : checkPiece pa19 (825/8) 0 (825/8) (3375/32) = true := by decide +kernel
theorem n0331 : NonnegOnQ (825/8) (3375/32) :=
  nonnegOn_of_checkPiece_zero (825/8) (3375/32) (by norm_num) c0331

theorem c0332 : checkPiece pa19 (3375/32) 0 (3375/32) (1725/16) = true := by decide +kernel
theorem n0332 : NonnegOnQ (3375/32) (1725/16) :=
  nonnegOn_of_checkPiece_zero (3375/32) (1725/16) (by norm_num) c0332

theorem c0333 : checkPiece pa19 (1725/16) 0 (1725/16) (3525/32) = true := by decide +kernel
theorem n0333 : NonnegOnQ (1725/16) (3525/32) :=
  nonnegOn_of_checkPiece_zero (1725/16) (3525/32) (by norm_num) c0333

theorem c0334 : checkPiece pa19 (3525/32) 0 (3525/32) (225/2) = true := by decide +kernel
theorem n0334 : NonnegOnQ (3525/32) (225/2) :=
  nonnegOn_of_checkPiece_zero (3525/32) (225/2) (by norm_num) c0334

theorem c0335 : checkPiece pa19 (225/2) 0 (225/2) (3675/32) = true := by decide +kernel
theorem n0335 : NonnegOnQ (225/2) (3675/32) :=
  nonnegOn_of_checkPiece_zero (225/2) (3675/32) (by norm_num) c0335

theorem c0336 : checkPiece pa19 (3675/32) 0 (3675/32) (1875/16) = true := by decide +kernel
theorem n0336 : NonnegOnQ (3675/32) (1875/16) :=
  nonnegOn_of_checkPiece_zero (3675/32) (1875/16) (by norm_num) c0336

theorem c0337 : checkPiece pa19 (1875/16) 0 (1875/16) (3825/32) = true := by decide +kernel
theorem n0337 : NonnegOnQ (1875/16) (3825/32) :=
  nonnegOn_of_checkPiece_zero (1875/16) (3825/32) (by norm_num) c0337

theorem c0338 : checkPiece pa19 (3825/32) 0 (3825/32) (975/8) = true := by decide +kernel
theorem n0338 : NonnegOnQ (3825/32) (975/8) :=
  nonnegOn_of_checkPiece_zero (3825/32) (975/8) (by norm_num) c0338

theorem c0339 : checkPiece pa19 (975/8) 0 (975/8) (2025/16) = true := by decide +kernel
theorem n0339 : NonnegOnQ (975/8) (2025/16) :=
  nonnegOn_of_checkPiece_zero (975/8) (2025/16) (by norm_num) c0339

theorem c0340 : checkPiece pa19 (2025/16) 0 (2025/16) (4125/32) = true := by decide +kernel
theorem n0340 : NonnegOnQ (2025/16) (4125/32) :=
  nonnegOn_of_checkPiece_zero (2025/16) (4125/32) (by norm_num) c0340

theorem c0341 : checkPiece pa19 (4125/32) 0 (4125/32) (525/4) = true := by decide +kernel
theorem n0341 : NonnegOnQ (4125/32) (525/4) :=
  nonnegOn_of_checkPiece_zero (4125/32) (525/4) (by norm_num) c0341

theorem c0342 : checkPiece pa19 (525/4) 0 (525/4) (4275/32) = true := by decide +kernel
theorem n0342 : NonnegOnQ (525/4) (4275/32) :=
  nonnegOn_of_checkPiece_zero (525/4) (4275/32) (by norm_num) c0342

theorem c0343 : checkPiece pa19 (4275/32) 0 (4275/32) (8625/64) = true := by decide +kernel
theorem n0343 : NonnegOnQ (4275/32) (8625/64) :=
  nonnegOn_of_checkPiece_zero (4275/32) (8625/64) (by norm_num) c0343

theorem c0344 : checkPiece pa19 (8625/64) 0 (8625/64) (2175/16) = true := by decide +kernel
theorem n0344 : NonnegOnQ (8625/64) (2175/16) :=
  nonnegOn_of_checkPiece_zero (8625/64) (2175/16) (by norm_num) c0344

theorem c0345 : checkPiece pa19 (2175/16) 0 (2175/16) (8775/64) = true := by decide +kernel
theorem n0345 : NonnegOnQ (2175/16) (8775/64) :=
  nonnegOn_of_checkPiece_zero (2175/16) (8775/64) (by norm_num) c0345

theorem c0346 : checkPiece pa19 (8775/64) 0 (8775/64) (4425/32) = true := by decide +kernel
theorem n0346 : NonnegOnQ (8775/64) (4425/32) :=
  nonnegOn_of_checkPiece_zero (8775/64) (4425/32) (by norm_num) c0346

theorem c0347 : checkPiece pa19 (4425/32) 0 (4425/32) (1125/8) = true := by decide +kernel
theorem n0347 : NonnegOnQ (4425/32) (1125/8) :=
  nonnegOn_of_checkPiece_zero (4425/32) (1125/8) (by norm_num) c0347

theorem c0348 : checkPiece pa19 (1125/8) 0 (1125/8) (2325/16) = true := by decide +kernel
theorem n0348 : NonnegOnQ (1125/8) (2325/16) :=
  nonnegOn_of_checkPiece_zero (1125/8) (2325/16) (by norm_num) c0348

theorem c0349 : checkPiece pa19 (2325/16) 0 (2325/16) (150) = true := by decide +kernel
theorem n0349 : NonnegOnQ (2325/16) (150) :=
  nonnegOn_of_checkPiece_zero (2325/16) (150) (by norm_num) c0349

theorem c0350 : checkPiece pa19 (150) 0 (150) (4875/32) = true := by decide +kernel
theorem n0350 : NonnegOnQ (150) (4875/32) :=
  nonnegOn_of_checkPiece_zero (150) (4875/32) (by norm_num) c0350

theorem c0351 : checkPiece pa19 (4875/32) 0 (4875/32) (2475/16) = true := by decide +kernel
theorem n0351 : NonnegOnQ (4875/32) (2475/16) :=
  nonnegOn_of_checkPiece_zero (4875/32) (2475/16) (by norm_num) c0351

theorem c0352 : checkPiece pa19 (2475/16) 0 (2475/16) (1275/8) = true := by decide +kernel
theorem n0352 : NonnegOnQ (2475/16) (1275/8) :=
  nonnegOn_of_checkPiece_zero (2475/16) (1275/8) (by norm_num) c0352

theorem c0353 : checkPiece pa19 (1275/8) 0 (1275/8) (5175/32) = true := by decide +kernel
theorem n0353 : NonnegOnQ (1275/8) (5175/32) :=
  nonnegOn_of_checkPiece_zero (1275/8) (5175/32) (by norm_num) c0353

theorem c0354 : checkPiece pa19 (5175/32) 0 (5175/32) (2625/16) = true := by decide +kernel
theorem n0354 : NonnegOnQ (5175/32) (2625/16) :=
  nonnegOn_of_checkPiece_zero (5175/32) (2625/16) (by norm_num) c0354

theorem c0355 : checkPiece pa19 (2625/16) 0 (2625/16) (5325/32) = true := by decide +kernel
theorem n0355 : NonnegOnQ (2625/16) (5325/32) :=
  nonnegOn_of_checkPiece_zero (2625/16) (5325/32) (by norm_num) c0355

theorem c0356 : checkPiece pa19 (5325/32) 0 (5325/32) (675/4) = true := by decide +kernel
theorem n0356 : NonnegOnQ (5325/32) (675/4) :=
  nonnegOn_of_checkPiece_zero (5325/32) (675/4) (by norm_num) c0356

theorem c0357 : checkPiece pa19 (675/4) 0 (675/4) (2775/16) = true := by decide +kernel
theorem n0357 : NonnegOnQ (675/4) (2775/16) :=
  nonnegOn_of_checkPiece_zero (675/4) (2775/16) (by norm_num) c0357

theorem c0358 : checkPiece pa19 (2775/16) 0 (2775/16) (5625/32) = true := by decide +kernel
theorem n0358 : NonnegOnQ (2775/16) (5625/32) :=
  nonnegOn_of_checkPiece_zero (2775/16) (5625/32) (by norm_num) c0358

theorem c0359 : checkPiece pa19 (5625/32) 0 (5625/32) (1425/8) = true := by decide +kernel
theorem n0359 : NonnegOnQ (5625/32) (1425/8) :=
  nonnegOn_of_checkPiece_zero (5625/32) (1425/8) (by norm_num) c0359

theorem c0360 : checkPiece pa19 (1425/8) 0 (1425/8) (2925/16) = true := by decide +kernel
theorem n0360 : NonnegOnQ (1425/8) (2925/16) :=
  nonnegOn_of_checkPiece_zero (1425/8) (2925/16) (by norm_num) c0360

theorem c0361 : checkPiece pa19 (2925/16) 0 (2925/16) (375/2) = true := by decide +kernel
theorem n0361 : NonnegOnQ (2925/16) (375/2) :=
  nonnegOn_of_checkPiece_zero (2925/16) (375/2) (by norm_num) c0361

theorem c0362 : checkPiece pa19 (375/2) 0 (375/2) (6075/32) = true := by decide +kernel
theorem n0362 : NonnegOnQ (375/2) (6075/32) :=
  nonnegOn_of_checkPiece_zero (375/2) (6075/32) (by norm_num) c0362

theorem c0363 : checkPiece pa19 (6075/32) 0 (6075/32) (12225/64) = true := by decide +kernel
theorem n0363 : NonnegOnQ (6075/32) (12225/64) :=
  nonnegOn_of_checkPiece_zero (6075/32) (12225/64) (by norm_num) c0363

theorem c0364 : checkPiece pa19 (12225/64) 0 (12225/64) (3075/16) = true := by decide +kernel
theorem n0364 : NonnegOnQ (12225/64) (3075/16) :=
  nonnegOn_of_checkPiece_zero (12225/64) (3075/16) (by norm_num) c0364

theorem c0365 : checkPiece pa19 (3075/16) 0 (3075/16) (1575/8) = true := by decide +kernel
theorem n0365 : NonnegOnQ (3075/16) (1575/8) :=
  nonnegOn_of_checkPiece_zero (3075/16) (1575/8) (by norm_num) c0365

theorem c0366 : checkPiece pa19 (1575/8) 0 (1575/8) (825/4) = true := by decide +kernel
theorem n0366 : NonnegOnQ (1575/8) (825/4) :=
  nonnegOn_of_checkPiece_zero (1575/8) (825/4) (by norm_num) c0366

theorem c0367 : checkPiece pa19 (825/4) 0 (825/4) (1725/8) = true := by decide +kernel
theorem n0367 : NonnegOnQ (825/4) (1725/8) :=
  nonnegOn_of_checkPiece_zero (825/4) (1725/8) (by norm_num) c0367

theorem c0368 : checkPiece pa19 (1725/8) 0 (1725/8) (225) = true := by decide +kernel
theorem n0368 : NonnegOnQ (1725/8) (225) :=
  nonnegOn_of_checkPiece_zero (1725/8) (225) (by norm_num) c0368

theorem c0369 : checkPiece pa19 (225) 0 (225) (1875/8) = true := by decide +kernel
theorem n0369 : NonnegOnQ (225) (1875/8) :=
  nonnegOn_of_checkPiece_zero (225) (1875/8) (by norm_num) c0369

theorem c0370 : checkPiece pa19 (1875/8) 0 (1875/8) (975/4) = true := by decide +kernel
theorem n0370 : NonnegOnQ (1875/8) (975/4) :=
  nonnegOn_of_checkPiece_zero (1875/8) (975/4) (by norm_num) c0370

theorem c0371 : checkPiece pa19 (975/4) 0 (975/4) (2025/8) = true := by decide +kernel
theorem n0371 : NonnegOnQ (975/4) (2025/8) :=
  nonnegOn_of_checkPiece_zero (975/4) (2025/8) (by norm_num) c0371

theorem c0372 : checkPiece pa19 (2025/8) 0 (2025/8) (525/2) = true := by decide +kernel
theorem n0372 : NonnegOnQ (2025/8) (525/2) :=
  nonnegOn_of_checkPiece_zero (2025/8) (525/2) (by norm_num) c0372

theorem c0373 : checkPiece pa19 (525/2) 0 (525/2) (1125/4) = true := by decide +kernel
theorem n0373 : NonnegOnQ (525/2) (1125/4) :=
  nonnegOn_of_checkPiece_zero (525/2) (1125/4) (by norm_num) c0373

theorem c0374 : checkPiece pa19 (1125/4) 0 (1125/4) (300) = true := by decide +kernel
theorem n0374 : NonnegOnQ (1125/4) (300) :=
  nonnegOn_of_checkPiece_zero (1125/4) (300) (by norm_num) c0374

/-- Generated contiguous fold of all 375 certified intervals. -/
set_option maxRecDepth 4096 in
theorem finite_interval_nonneg : NonnegOnQ 0 300 := by
  have h0 := n0000
  have h1 : NonnegOnQ 0 (225/8192) := nonnegOn_union 0 (75/4096) (225/8192) h0 n0001
  have h2 : NonnegOnQ 0 (525/16384) := nonnegOn_union 0 (225/8192) (525/16384) h1 n0002
  have h3 : NonnegOnQ 0 (75/2048) := nonnegOn_union 0 (525/16384) (75/2048) h2 n0003
  have h4 : NonnegOnQ 0 (375/8192) := nonnegOn_union 0 (75/2048) (375/8192) h3 n0004
  have h5 : NonnegOnQ 0 (225/4096) := nonnegOn_union 0 (375/8192) (225/4096) h4 n0005
  have h6 : NonnegOnQ 0 (525/8192) := nonnegOn_union 0 (225/4096) (525/8192) h5 n0006
  have h7 : NonnegOnQ 0 (75/1024) := nonnegOn_union 0 (525/8192) (75/1024) h6 n0007
  have h8 : NonnegOnQ 0 (675/8192) := nonnegOn_union 0 (75/1024) (675/8192) h7 n0008
  have h9 : NonnegOnQ 0 (375/4096) := nonnegOn_union 0 (675/8192) (375/4096) h8 n0009
  have h10 : NonnegOnQ 0 (825/8192) := nonnegOn_union 0 (375/4096) (825/8192) h9 n0010
  have h11 : NonnegOnQ 0 (225/2048) := nonnegOn_union 0 (825/8192) (225/2048) h10 n0011
  have h12 : NonnegOnQ 0 (975/8192) := nonnegOn_union 0 (225/2048) (975/8192) h11 n0012
  have h13 : NonnegOnQ 0 (525/4096) := nonnegOn_union 0 (975/8192) (525/4096) h12 n0013
  have h14 : NonnegOnQ 0 (1125/8192) := nonnegOn_union 0 (525/4096) (1125/8192) h13 n0014
  have h15 : NonnegOnQ 0 (75/512) := nonnegOn_union 0 (1125/8192) (75/512) h14 n0015
  have h16 : NonnegOnQ 0 (1275/8192) := nonnegOn_union 0 (75/512) (1275/8192) h15 n0016
  have h17 : NonnegOnQ 0 (675/4096) := nonnegOn_union 0 (1275/8192) (675/4096) h16 n0017
  have h18 : NonnegOnQ 0 (1425/8192) := nonnegOn_union 0 (675/4096) (1425/8192) h17 n0018
  have h19 : NonnegOnQ 0 (375/2048) := nonnegOn_union 0 (1425/8192) (375/2048) h18 n0019
  have h20 : NonnegOnQ 0 (1575/8192) := nonnegOn_union 0 (375/2048) (1575/8192) h19 n0020
  have h21 : NonnegOnQ 0 (825/4096) := nonnegOn_union 0 (1575/8192) (825/4096) h20 n0021
  have h22 : NonnegOnQ 0 (1725/8192) := nonnegOn_union 0 (825/4096) (1725/8192) h21 n0022
  have h23 : NonnegOnQ 0 (225/1024) := nonnegOn_union 0 (1725/8192) (225/1024) h22 n0023
  have h24 : NonnegOnQ 0 (1875/8192) := nonnegOn_union 0 (225/1024) (1875/8192) h23 n0024
  have h25 : NonnegOnQ 0 (975/4096) := nonnegOn_union 0 (1875/8192) (975/4096) h24 n0025
  have h26 : NonnegOnQ 0 (2025/8192) := nonnegOn_union 0 (975/4096) (2025/8192) h25 n0026
  have h27 : NonnegOnQ 0 (525/2048) := nonnegOn_union 0 (2025/8192) (525/2048) h26 n0027
  have h28 : NonnegOnQ 0 (2175/8192) := nonnegOn_union 0 (525/2048) (2175/8192) h27 n0028
  have h29 : NonnegOnQ 0 (1125/4096) := nonnegOn_union 0 (2175/8192) (1125/4096) h28 n0029
  have h30 : NonnegOnQ 0 (2325/8192) := nonnegOn_union 0 (1125/4096) (2325/8192) h29 n0030
  have h31 : NonnegOnQ 0 (75/256) := nonnegOn_union 0 (2325/8192) (75/256) h30 n0031
  have h32 : NonnegOnQ 0 (2475/8192) := nonnegOn_union 0 (75/256) (2475/8192) h31 n0032
  have h33 : NonnegOnQ 0 (1275/4096) := nonnegOn_union 0 (2475/8192) (1275/4096) h32 n0033
  have h34 : NonnegOnQ 0 (2625/8192) := nonnegOn_union 0 (1275/4096) (2625/8192) h33 n0034
  have h35 : NonnegOnQ 0 (675/2048) := nonnegOn_union 0 (2625/8192) (675/2048) h34 n0035
  have h36 : NonnegOnQ 0 (2775/8192) := nonnegOn_union 0 (675/2048) (2775/8192) h35 n0036
  have h37 : NonnegOnQ 0 (1425/4096) := nonnegOn_union 0 (2775/8192) (1425/4096) h36 n0037
  have h38 : NonnegOnQ 0 (2925/8192) := nonnegOn_union 0 (1425/4096) (2925/8192) h37 n0038
  have h39 : NonnegOnQ 0 (375/1024) := nonnegOn_union 0 (2925/8192) (375/1024) h38 n0039
  have h40 : NonnegOnQ 0 (3075/8192) := nonnegOn_union 0 (375/1024) (3075/8192) h39 n0040
  have h41 : NonnegOnQ 0 (1575/4096) := nonnegOn_union 0 (3075/8192) (1575/4096) h40 n0041
  have h42 : NonnegOnQ 0 (3225/8192) := nonnegOn_union 0 (1575/4096) (3225/8192) h41 n0042
  have h43 : NonnegOnQ 0 (825/2048) := nonnegOn_union 0 (3225/8192) (825/2048) h42 n0043
  have h44 : NonnegOnQ 0 (3375/8192) := nonnegOn_union 0 (825/2048) (3375/8192) h43 n0044
  have h45 : NonnegOnQ 0 (1725/4096) := nonnegOn_union 0 (3375/8192) (1725/4096) h44 n0045
  have h46 : NonnegOnQ 0 (3525/8192) := nonnegOn_union 0 (1725/4096) (3525/8192) h45 n0046
  have h47 : NonnegOnQ 0 (225/512) := nonnegOn_union 0 (3525/8192) (225/512) h46 n0047
  have h48 : NonnegOnQ 0 (3675/8192) := nonnegOn_union 0 (225/512) (3675/8192) h47 n0048
  have h49 : NonnegOnQ 0 (1875/4096) := nonnegOn_union 0 (3675/8192) (1875/4096) h48 n0049
  have h50 : NonnegOnQ 0 (3825/8192) := nonnegOn_union 0 (1875/4096) (3825/8192) h49 n0050
  have h51 : NonnegOnQ 0 (975/2048) := nonnegOn_union 0 (3825/8192) (975/2048) h50 n0051
  have h52 : NonnegOnQ 0 (3975/8192) := nonnegOn_union 0 (975/2048) (3975/8192) h51 n0052
  have h53 : NonnegOnQ 0 (2025/4096) := nonnegOn_union 0 (3975/8192) (2025/4096) h52 n0053
  have h54 : NonnegOnQ 0 (4125/8192) := nonnegOn_union 0 (2025/4096) (4125/8192) h53 n0054
  have h55 : NonnegOnQ 0 (525/1024) := nonnegOn_union 0 (4125/8192) (525/1024) h54 n0055
  have h56 : NonnegOnQ 0 (4275/8192) := nonnegOn_union 0 (525/1024) (4275/8192) h55 n0056
  have h57 : NonnegOnQ 0 (2175/4096) := nonnegOn_union 0 (4275/8192) (2175/4096) h56 n0057
  have h58 : NonnegOnQ 0 (4425/8192) := nonnegOn_union 0 (2175/4096) (4425/8192) h57 n0058
  have h59 : NonnegOnQ 0 (1125/2048) := nonnegOn_union 0 (4425/8192) (1125/2048) h58 n0059
  have h60 : NonnegOnQ 0 (4575/8192) := nonnegOn_union 0 (1125/2048) (4575/8192) h59 n0060
  have h61 : NonnegOnQ 0 (2325/4096) := nonnegOn_union 0 (4575/8192) (2325/4096) h60 n0061
  have h62 : NonnegOnQ 0 (4725/8192) := nonnegOn_union 0 (2325/4096) (4725/8192) h61 n0062
  have h63 : NonnegOnQ 0 (75/128) := nonnegOn_union 0 (4725/8192) (75/128) h62 n0063
  have h64 : NonnegOnQ 0 (4875/8192) := nonnegOn_union 0 (75/128) (4875/8192) h63 n0064
  have h65 : NonnegOnQ 0 (2475/4096) := nonnegOn_union 0 (4875/8192) (2475/4096) h64 n0065
  have h66 : NonnegOnQ 0 (5025/8192) := nonnegOn_union 0 (2475/4096) (5025/8192) h65 n0066
  have h67 : NonnegOnQ 0 (1275/2048) := nonnegOn_union 0 (5025/8192) (1275/2048) h66 n0067
  have h68 : NonnegOnQ 0 (5175/8192) := nonnegOn_union 0 (1275/2048) (5175/8192) h67 n0068
  have h69 : NonnegOnQ 0 (2625/4096) := nonnegOn_union 0 (5175/8192) (2625/4096) h68 n0069
  have h70 : NonnegOnQ 0 (5325/8192) := nonnegOn_union 0 (2625/4096) (5325/8192) h69 n0070
  have h71 : NonnegOnQ 0 (675/1024) := nonnegOn_union 0 (5325/8192) (675/1024) h70 n0071
  have h72 : NonnegOnQ 0 (5475/8192) := nonnegOn_union 0 (675/1024) (5475/8192) h71 n0072
  have h73 : NonnegOnQ 0 (2775/4096) := nonnegOn_union 0 (5475/8192) (2775/4096) h72 n0073
  have h74 : NonnegOnQ 0 (5625/8192) := nonnegOn_union 0 (2775/4096) (5625/8192) h73 n0074
  have h75 : NonnegOnQ 0 (1425/2048) := nonnegOn_union 0 (5625/8192) (1425/2048) h74 n0075
  have h76 : NonnegOnQ 0 (5775/8192) := nonnegOn_union 0 (1425/2048) (5775/8192) h75 n0076
  have h77 : NonnegOnQ 0 (2925/4096) := nonnegOn_union 0 (5775/8192) (2925/4096) h76 n0077
  have h78 : NonnegOnQ 0 (5925/8192) := nonnegOn_union 0 (2925/4096) (5925/8192) h77 n0078
  have h79 : NonnegOnQ 0 (375/512) := nonnegOn_union 0 (5925/8192) (375/512) h78 n0079
  have h80 : NonnegOnQ 0 (6075/8192) := nonnegOn_union 0 (375/512) (6075/8192) h79 n0080
  have h81 : NonnegOnQ 0 (3075/4096) := nonnegOn_union 0 (6075/8192) (3075/4096) h80 n0081
  have h82 : NonnegOnQ 0 (6225/8192) := nonnegOn_union 0 (3075/4096) (6225/8192) h81 n0082
  have h83 : NonnegOnQ 0 (1575/2048) := nonnegOn_union 0 (6225/8192) (1575/2048) h82 n0083
  have h84 : NonnegOnQ 0 (6375/8192) := nonnegOn_union 0 (1575/2048) (6375/8192) h83 n0084
  have h85 : NonnegOnQ 0 (3225/4096) := nonnegOn_union 0 (6375/8192) (3225/4096) h84 n0085
  have h86 : NonnegOnQ 0 (6525/8192) := nonnegOn_union 0 (3225/4096) (6525/8192) h85 n0086
  have h87 : NonnegOnQ 0 (825/1024) := nonnegOn_union 0 (6525/8192) (825/1024) h86 n0087
  have h88 : NonnegOnQ 0 (6675/8192) := nonnegOn_union 0 (825/1024) (6675/8192) h87 n0088
  have h89 : NonnegOnQ 0 (3375/4096) := nonnegOn_union 0 (6675/8192) (3375/4096) h88 n0089
  have h90 : NonnegOnQ 0 (6825/8192) := nonnegOn_union 0 (3375/4096) (6825/8192) h89 n0090
  have h91 : NonnegOnQ 0 (1725/2048) := nonnegOn_union 0 (6825/8192) (1725/2048) h90 n0091
  have h92 : NonnegOnQ 0 (6975/8192) := nonnegOn_union 0 (1725/2048) (6975/8192) h91 n0092
  have h93 : NonnegOnQ 0 (3525/4096) := nonnegOn_union 0 (6975/8192) (3525/4096) h92 n0093
  have h94 : NonnegOnQ 0 (7125/8192) := nonnegOn_union 0 (3525/4096) (7125/8192) h93 n0094
  have h95 : NonnegOnQ 0 (225/256) := nonnegOn_union 0 (7125/8192) (225/256) h94 n0095
  have h96 : NonnegOnQ 0 (7275/8192) := nonnegOn_union 0 (225/256) (7275/8192) h95 n0096
  have h97 : NonnegOnQ 0 (3675/4096) := nonnegOn_union 0 (7275/8192) (3675/4096) h96 n0097
  have h98 : NonnegOnQ 0 (7425/8192) := nonnegOn_union 0 (3675/4096) (7425/8192) h97 n0098
  have h99 : NonnegOnQ 0 (1875/2048) := nonnegOn_union 0 (7425/8192) (1875/2048) h98 n0099
  have h100 : NonnegOnQ 0 (7575/8192) := nonnegOn_union 0 (1875/2048) (7575/8192) h99 n0100
  have h101 : NonnegOnQ 0 (3825/4096) := nonnegOn_union 0 (7575/8192) (3825/4096) h100 n0101
  have h102 : NonnegOnQ 0 (975/1024) := nonnegOn_union 0 (3825/4096) (975/1024) h101 n0102
  have h103 : NonnegOnQ 0 (3975/4096) := nonnegOn_union 0 (975/1024) (3975/4096) h102 n0103
  have h104 : NonnegOnQ 0 (2025/2048) := nonnegOn_union 0 (3975/4096) (2025/2048) h103 n0104
  have h105 : NonnegOnQ 0 (4125/4096) := nonnegOn_union 0 (2025/2048) (4125/4096) h104 n0105
  have h106 : NonnegOnQ 0 (525/512) := nonnegOn_union 0 (4125/4096) (525/512) h105 n0106
  have h107 : NonnegOnQ 0 (4275/4096) := nonnegOn_union 0 (525/512) (4275/4096) h106 n0107
  have h108 : NonnegOnQ 0 (2175/2048) := nonnegOn_union 0 (4275/4096) (2175/2048) h107 n0108
  have h109 : NonnegOnQ 0 (4425/4096) := nonnegOn_union 0 (2175/2048) (4425/4096) h108 n0109
  have h110 : NonnegOnQ 0 (1125/1024) := nonnegOn_union 0 (4425/4096) (1125/1024) h109 n0110
  have h111 : NonnegOnQ 0 (4575/4096) := nonnegOn_union 0 (1125/1024) (4575/4096) h110 n0111
  have h112 : NonnegOnQ 0 (2325/2048) := nonnegOn_union 0 (4575/4096) (2325/2048) h111 n0112
  have h113 : NonnegOnQ 0 (4725/4096) := nonnegOn_union 0 (2325/2048) (4725/4096) h112 n0113
  have h114 : NonnegOnQ 0 (75/64) := nonnegOn_union 0 (4725/4096) (75/64) h113 n0114
  have h115 : NonnegOnQ 0 (4875/4096) := nonnegOn_union 0 (75/64) (4875/4096) h114 n0115
  have h116 : NonnegOnQ 0 (2475/2048) := nonnegOn_union 0 (4875/4096) (2475/2048) h115 n0116
  have h117 : NonnegOnQ 0 (5025/4096) := nonnegOn_union 0 (2475/2048) (5025/4096) h116 n0117
  have h118 : NonnegOnQ 0 (1275/1024) := nonnegOn_union 0 (5025/4096) (1275/1024) h117 n0118
  have h119 : NonnegOnQ 0 (5175/4096) := nonnegOn_union 0 (1275/1024) (5175/4096) h118 n0119
  have h120 : NonnegOnQ 0 (2625/2048) := nonnegOn_union 0 (5175/4096) (2625/2048) h119 n0120
  have h121 : NonnegOnQ 0 (5325/4096) := nonnegOn_union 0 (2625/2048) (5325/4096) h120 n0121
  have h122 : NonnegOnQ 0 (675/512) := nonnegOn_union 0 (5325/4096) (675/512) h121 n0122
  have h123 : NonnegOnQ 0 (5475/4096) := nonnegOn_union 0 (675/512) (5475/4096) h122 n0123
  have h124 : NonnegOnQ 0 (2775/2048) := nonnegOn_union 0 (5475/4096) (2775/2048) h123 n0124
  have h125 : NonnegOnQ 0 (5625/4096) := nonnegOn_union 0 (2775/2048) (5625/4096) h124 n0125
  have h126 : NonnegOnQ 0 (1425/1024) := nonnegOn_union 0 (5625/4096) (1425/1024) h125 n0126
  have h127 : NonnegOnQ 0 (2925/2048) := nonnegOn_union 0 (1425/1024) (2925/2048) h126 n0127
  have h128 : NonnegOnQ 0 (375/256) := nonnegOn_union 0 (2925/2048) (375/256) h127 n0128
  have h129 : NonnegOnQ 0 (3075/2048) := nonnegOn_union 0 (375/256) (3075/2048) h128 n0129
  have h130 : NonnegOnQ 0 (1575/1024) := nonnegOn_union 0 (3075/2048) (1575/1024) h129 n0130
  have h131 : NonnegOnQ 0 (3225/2048) := nonnegOn_union 0 (1575/1024) (3225/2048) h130 n0131
  have h132 : NonnegOnQ 0 (825/512) := nonnegOn_union 0 (3225/2048) (825/512) h131 n0132
  have h133 : NonnegOnQ 0 (3375/2048) := nonnegOn_union 0 (825/512) (3375/2048) h132 n0133
  have h134 : NonnegOnQ 0 (1725/1024) := nonnegOn_union 0 (3375/2048) (1725/1024) h133 n0134
  have h135 : NonnegOnQ 0 (3525/2048) := nonnegOn_union 0 (1725/1024) (3525/2048) h134 n0135
  have h136 : NonnegOnQ 0 (225/128) := nonnegOn_union 0 (3525/2048) (225/128) h135 n0136
  have h137 : NonnegOnQ 0 (3675/2048) := nonnegOn_union 0 (225/128) (3675/2048) h136 n0137
  have h138 : NonnegOnQ 0 (1875/1024) := nonnegOn_union 0 (3675/2048) (1875/1024) h137 n0138
  have h139 : NonnegOnQ 0 (3825/2048) := nonnegOn_union 0 (1875/1024) (3825/2048) h138 n0139
  have h140 : NonnegOnQ 0 (975/512) := nonnegOn_union 0 (3825/2048) (975/512) h139 n0140
  have h141 : NonnegOnQ 0 (3975/2048) := nonnegOn_union 0 (975/512) (3975/2048) h140 n0141
  have h142 : NonnegOnQ 0 (2025/1024) := nonnegOn_union 0 (3975/2048) (2025/1024) h141 n0142
  have h143 : NonnegOnQ 0 (4125/2048) := nonnegOn_union 0 (2025/1024) (4125/2048) h142 n0143
  have h144 : NonnegOnQ 0 (525/256) := nonnegOn_union 0 (4125/2048) (525/256) h143 n0144
  have h145 : NonnegOnQ 0 (4275/2048) := nonnegOn_union 0 (525/256) (4275/2048) h144 n0145
  have h146 : NonnegOnQ 0 (2175/1024) := nonnegOn_union 0 (4275/2048) (2175/1024) h145 n0146
  have h147 : NonnegOnQ 0 (4425/2048) := nonnegOn_union 0 (2175/1024) (4425/2048) h146 n0147
  have h148 : NonnegOnQ 0 (1125/512) := nonnegOn_union 0 (4425/2048) (1125/512) h147 n0148
  have h149 : NonnegOnQ 0 (4575/2048) := nonnegOn_union 0 (1125/512) (4575/2048) h148 n0149
  have h150 : NonnegOnQ 0 (2325/1024) := nonnegOn_union 0 (4575/2048) (2325/1024) h149 n0150
  have h151 : NonnegOnQ 0 (4725/2048) := nonnegOn_union 0 (2325/1024) (4725/2048) h150 n0151
  have h152 : NonnegOnQ 0 (75/32) := nonnegOn_union 0 (4725/2048) (75/32) h151 n0152
  have h153 : NonnegOnQ 0 (4875/2048) := nonnegOn_union 0 (75/32) (4875/2048) h152 n0153
  have h154 : NonnegOnQ 0 (2475/1024) := nonnegOn_union 0 (4875/2048) (2475/1024) h153 n0154
  have h155 : NonnegOnQ 0 (1275/512) := nonnegOn_union 0 (2475/1024) (1275/512) h154 n0155
  have h156 : NonnegOnQ 0 (2625/1024) := nonnegOn_union 0 (1275/512) (2625/1024) h155 n0156
  have h157 : NonnegOnQ 0 (675/256) := nonnegOn_union 0 (2625/1024) (675/256) h156 n0157
  have h158 : NonnegOnQ 0 (2775/1024) := nonnegOn_union 0 (675/256) (2775/1024) h157 n0158
  have h159 : NonnegOnQ 0 (1425/512) := nonnegOn_union 0 (2775/1024) (1425/512) h158 n0159
  have h160 : NonnegOnQ 0 (2925/1024) := nonnegOn_union 0 (1425/512) (2925/1024) h159 n0160
  have h161 : NonnegOnQ 0 (375/128) := nonnegOn_union 0 (2925/1024) (375/128) h160 n0161
  have h162 : NonnegOnQ 0 (3075/1024) := nonnegOn_union 0 (375/128) (3075/1024) h161 n0162
  have h163 : NonnegOnQ 0 (1575/512) := nonnegOn_union 0 (3075/1024) (1575/512) h162 n0163
  have h164 : NonnegOnQ 0 (3225/1024) := nonnegOn_union 0 (1575/512) (3225/1024) h163 n0164
  have h165 : NonnegOnQ 0 (825/256) := nonnegOn_union 0 (3225/1024) (825/256) h164 n0165
  have h166 : NonnegOnQ 0 (3375/1024) := nonnegOn_union 0 (825/256) (3375/1024) h165 n0166
  have h167 : NonnegOnQ 0 (1725/512) := nonnegOn_union 0 (3375/1024) (1725/512) h166 n0167
  have h168 : NonnegOnQ 0 (3525/1024) := nonnegOn_union 0 (1725/512) (3525/1024) h167 n0168
  have h169 : NonnegOnQ 0 (225/64) := nonnegOn_union 0 (3525/1024) (225/64) h168 n0169
  have h170 : NonnegOnQ 0 (3675/1024) := nonnegOn_union 0 (225/64) (3675/1024) h169 n0170
  have h171 : NonnegOnQ 0 (1875/512) := nonnegOn_union 0 (3675/1024) (1875/512) h170 n0171
  have h172 : NonnegOnQ 0 (3825/1024) := nonnegOn_union 0 (1875/512) (3825/1024) h171 n0172
  have h173 : NonnegOnQ 0 (975/256) := nonnegOn_union 0 (3825/1024) (975/256) h172 n0173
  have h174 : NonnegOnQ 0 (3975/1024) := nonnegOn_union 0 (975/256) (3975/1024) h173 n0174
  have h175 : NonnegOnQ 0 (2025/512) := nonnegOn_union 0 (3975/1024) (2025/512) h174 n0175
  have h176 : NonnegOnQ 0 (4125/1024) := nonnegOn_union 0 (2025/512) (4125/1024) h175 n0176
  have h177 : NonnegOnQ 0 (525/128) := nonnegOn_union 0 (4125/1024) (525/128) h176 n0177
  have h178 : NonnegOnQ 0 (4275/1024) := nonnegOn_union 0 (525/128) (4275/1024) h177 n0178
  have h179 : NonnegOnQ 0 (2175/512) := nonnegOn_union 0 (4275/1024) (2175/512) h178 n0179
  have h180 : NonnegOnQ 0 (4425/1024) := nonnegOn_union 0 (2175/512) (4425/1024) h179 n0180
  have h181 : NonnegOnQ 0 (1125/256) := nonnegOn_union 0 (4425/1024) (1125/256) h180 n0181
  have h182 : NonnegOnQ 0 (4575/1024) := nonnegOn_union 0 (1125/256) (4575/1024) h181 n0182
  have h183 : NonnegOnQ 0 (2325/512) := nonnegOn_union 0 (4575/1024) (2325/512) h182 n0183
  have h184 : NonnegOnQ 0 (4725/1024) := nonnegOn_union 0 (2325/512) (4725/1024) h183 n0184
  have h185 : NonnegOnQ 0 (75/16) := nonnegOn_union 0 (4725/1024) (75/16) h184 n0185
  have h186 : NonnegOnQ 0 (2475/512) := nonnegOn_union 0 (75/16) (2475/512) h185 n0186
  have h187 : NonnegOnQ 0 (1275/256) := nonnegOn_union 0 (2475/512) (1275/256) h186 n0187
  have h188 : NonnegOnQ 0 (2625/512) := nonnegOn_union 0 (1275/256) (2625/512) h187 n0188
  have h189 : NonnegOnQ 0 (675/128) := nonnegOn_union 0 (2625/512) (675/128) h188 n0189
  have h190 : NonnegOnQ 0 (2775/512) := nonnegOn_union 0 (675/128) (2775/512) h189 n0190
  have h191 : NonnegOnQ 0 (1425/256) := nonnegOn_union 0 (2775/512) (1425/256) h190 n0191
  have h192 : NonnegOnQ 0 (2925/512) := nonnegOn_union 0 (1425/256) (2925/512) h191 n0192
  have h193 : NonnegOnQ 0 (375/64) := nonnegOn_union 0 (2925/512) (375/64) h192 n0193
  have h194 : NonnegOnQ 0 (3075/512) := nonnegOn_union 0 (375/64) (3075/512) h193 n0194
  have h195 : NonnegOnQ 0 (1575/256) := nonnegOn_union 0 (3075/512) (1575/256) h194 n0195
  have h196 : NonnegOnQ 0 (3225/512) := nonnegOn_union 0 (1575/256) (3225/512) h195 n0196
  have h197 : NonnegOnQ 0 (825/128) := nonnegOn_union 0 (3225/512) (825/128) h196 n0197
  have h198 : NonnegOnQ 0 (3375/512) := nonnegOn_union 0 (825/128) (3375/512) h197 n0198
  have h199 : NonnegOnQ 0 (1725/256) := nonnegOn_union 0 (3375/512) (1725/256) h198 n0199
  have h200 : NonnegOnQ 0 (3525/512) := nonnegOn_union 0 (1725/256) (3525/512) h199 n0200
  have h201 : NonnegOnQ 0 (225/32) := nonnegOn_union 0 (3525/512) (225/32) h200 n0201
  have h202 : NonnegOnQ 0 (3675/512) := nonnegOn_union 0 (225/32) (3675/512) h201 n0202
  have h203 : NonnegOnQ 0 (1875/256) := nonnegOn_union 0 (3675/512) (1875/256) h202 n0203
  have h204 : NonnegOnQ 0 (3825/512) := nonnegOn_union 0 (1875/256) (3825/512) h203 n0204
  have h205 : NonnegOnQ 0 (975/128) := nonnegOn_union 0 (3825/512) (975/128) h204 n0205
  have h206 : NonnegOnQ 0 (3975/512) := nonnegOn_union 0 (975/128) (3975/512) h205 n0206
  have h207 : NonnegOnQ 0 (2025/256) := nonnegOn_union 0 (3975/512) (2025/256) h206 n0207
  have h208 : NonnegOnQ 0 (4125/512) := nonnegOn_union 0 (2025/256) (4125/512) h207 n0208
  have h209 : NonnegOnQ 0 (525/64) := nonnegOn_union 0 (4125/512) (525/64) h208 n0209
  have h210 : NonnegOnQ 0 (4275/512) := nonnegOn_union 0 (525/64) (4275/512) h209 n0210
  have h211 : NonnegOnQ 0 (2175/256) := nonnegOn_union 0 (4275/512) (2175/256) h210 n0211
  have h212 : NonnegOnQ 0 (4425/512) := nonnegOn_union 0 (2175/256) (4425/512) h211 n0212
  have h213 : NonnegOnQ 0 (1125/128) := nonnegOn_union 0 (4425/512) (1125/128) h212 n0213
  have h214 : NonnegOnQ 0 (4575/512) := nonnegOn_union 0 (1125/128) (4575/512) h213 n0214
  have h215 : NonnegOnQ 0 (2325/256) := nonnegOn_union 0 (4575/512) (2325/256) h214 n0215
  have h216 : NonnegOnQ 0 (4725/512) := nonnegOn_union 0 (2325/256) (4725/512) h215 n0216
  have h217 : NonnegOnQ 0 (75/8) := nonnegOn_union 0 (4725/512) (75/8) h216 n0217
  have h218 : NonnegOnQ 0 (4875/512) := nonnegOn_union 0 (75/8) (4875/512) h217 n0218
  have h219 : NonnegOnQ 0 (2475/256) := nonnegOn_union 0 (4875/512) (2475/256) h218 n0219
  have h220 : NonnegOnQ 0 (1275/128) := nonnegOn_union 0 (2475/256) (1275/128) h219 n0220
  have h221 : NonnegOnQ 0 (2625/256) := nonnegOn_union 0 (1275/128) (2625/256) h220 n0221
  have h222 : NonnegOnQ 0 (675/64) := nonnegOn_union 0 (2625/256) (675/64) h221 n0222
  have h223 : NonnegOnQ 0 (2775/256) := nonnegOn_union 0 (675/64) (2775/256) h222 n0223
  have h224 : NonnegOnQ 0 (1425/128) := nonnegOn_union 0 (2775/256) (1425/128) h223 n0224
  have h225 : NonnegOnQ 0 (2925/256) := nonnegOn_union 0 (1425/128) (2925/256) h224 n0225
  have h226 : NonnegOnQ 0 (375/32) := nonnegOn_union 0 (2925/256) (375/32) h225 n0226
  have h227 : NonnegOnQ 0 (3075/256) := nonnegOn_union 0 (375/32) (3075/256) h226 n0227
  have h228 : NonnegOnQ 0 (1575/128) := nonnegOn_union 0 (3075/256) (1575/128) h227 n0228
  have h229 : NonnegOnQ 0 (3225/256) := nonnegOn_union 0 (1575/128) (3225/256) h228 n0229
  have h230 : NonnegOnQ 0 (825/64) := nonnegOn_union 0 (3225/256) (825/64) h229 n0230
  have h231 : NonnegOnQ 0 (6675/512) := nonnegOn_union 0 (825/64) (6675/512) h230 n0231
  have h232 : NonnegOnQ 0 (3375/256) := nonnegOn_union 0 (6675/512) (3375/256) h231 n0232
  have h233 : NonnegOnQ 0 (6825/512) := nonnegOn_union 0 (3375/256) (6825/512) h232 n0233
  have h234 : NonnegOnQ 0 (1725/128) := nonnegOn_union 0 (6825/512) (1725/128) h233 n0234
  have h235 : NonnegOnQ 0 (3525/256) := nonnegOn_union 0 (1725/128) (3525/256) h234 n0235
  have h236 : NonnegOnQ 0 (225/16) := nonnegOn_union 0 (3525/256) (225/16) h235 n0236
  have h237 : NonnegOnQ 0 (3675/256) := nonnegOn_union 0 (225/16) (3675/256) h236 n0237
  have h238 : NonnegOnQ 0 (1875/128) := nonnegOn_union 0 (3675/256) (1875/128) h237 n0238
  have h239 : NonnegOnQ 0 (3825/256) := nonnegOn_union 0 (1875/128) (3825/256) h238 n0239
  have h240 : NonnegOnQ 0 (975/64) := nonnegOn_union 0 (3825/256) (975/64) h239 n0240
  have h241 : NonnegOnQ 0 (3975/256) := nonnegOn_union 0 (975/64) (3975/256) h240 n0241
  have h242 : NonnegOnQ 0 (2025/128) := nonnegOn_union 0 (3975/256) (2025/128) h241 n0242
  have h243 : NonnegOnQ 0 (4125/256) := nonnegOn_union 0 (2025/128) (4125/256) h242 n0243
  have h244 : NonnegOnQ 0 (8325/512) := nonnegOn_union 0 (4125/256) (8325/512) h243 n0244
  have h245 : NonnegOnQ 0 (525/32) := nonnegOn_union 0 (8325/512) (525/32) h244 n0245
  have h246 : NonnegOnQ 0 (4275/256) := nonnegOn_union 0 (525/32) (4275/256) h245 n0246
  have h247 : NonnegOnQ 0 (2175/128) := nonnegOn_union 0 (4275/256) (2175/128) h246 n0247
  have h248 : NonnegOnQ 0 (4425/256) := nonnegOn_union 0 (2175/128) (4425/256) h247 n0248
  have h249 : NonnegOnQ 0 (1125/64) := nonnegOn_union 0 (4425/256) (1125/64) h248 n0249
  have h250 : NonnegOnQ 0 (4575/256) := nonnegOn_union 0 (1125/64) (4575/256) h249 n0250
  have h251 : NonnegOnQ 0 (2325/128) := nonnegOn_union 0 (4575/256) (2325/128) h250 n0251
  have h252 : NonnegOnQ 0 (4725/256) := nonnegOn_union 0 (2325/128) (4725/256) h251 n0252
  have h253 : NonnegOnQ 0 (75/4) := nonnegOn_union 0 (4725/256) (75/4) h252 n0253
  have h254 : NonnegOnQ 0 (4875/256) := nonnegOn_union 0 (75/4) (4875/256) h253 n0254
  have h255 : NonnegOnQ 0 (2475/128) := nonnegOn_union 0 (4875/256) (2475/128) h254 n0255
  have h256 : NonnegOnQ 0 (5025/256) := nonnegOn_union 0 (2475/128) (5025/256) h255 n0256
  have h257 : NonnegOnQ 0 (1275/64) := nonnegOn_union 0 (5025/256) (1275/64) h256 n0257
  have h258 : NonnegOnQ 0 (5175/256) := nonnegOn_union 0 (1275/64) (5175/256) h257 n0258
  have h259 : NonnegOnQ 0 (10425/512) := nonnegOn_union 0 (5175/256) (10425/512) h258 n0259
  have h260 : NonnegOnQ 0 (2625/128) := nonnegOn_union 0 (10425/512) (2625/128) h259 n0260
  have h261 : NonnegOnQ 0 (5325/256) := nonnegOn_union 0 (2625/128) (5325/256) h260 n0261
  have h262 : NonnegOnQ 0 (675/32) := nonnegOn_union 0 (5325/256) (675/32) h261 n0262
  have h263 : NonnegOnQ 0 (2775/128) := nonnegOn_union 0 (675/32) (2775/128) h262 n0263
  have h264 : NonnegOnQ 0 (1425/64) := nonnegOn_union 0 (2775/128) (1425/64) h263 n0264
  have h265 : NonnegOnQ 0 (375/16) := nonnegOn_union 0 (1425/64) (375/16) h264 n0265
  have h266 : NonnegOnQ 0 (1575/64) := nonnegOn_union 0 (375/16) (1575/64) h265 n0266
  have h267 : NonnegOnQ 0 (3225/128) := nonnegOn_union 0 (1575/64) (3225/128) h266 n0267
  have h268 : NonnegOnQ 0 (6525/256) := nonnegOn_union 0 (3225/128) (6525/256) h267 n0268
  have h269 : NonnegOnQ 0 (825/32) := nonnegOn_union 0 (6525/256) (825/32) h268 n0269
  have h270 : NonnegOnQ 0 (6675/256) := nonnegOn_union 0 (825/32) (6675/256) h269 n0270
  have h271 : NonnegOnQ 0 (13425/512) := nonnegOn_union 0 (6675/256) (13425/512) h270 n0271
  have h272 : NonnegOnQ 0 (3375/128) := nonnegOn_union 0 (13425/512) (3375/128) h271 n0272
  have h273 : NonnegOnQ 0 (6825/256) := nonnegOn_union 0 (3375/128) (6825/256) h272 n0273
  have h274 : NonnegOnQ 0 (1725/64) := nonnegOn_union 0 (6825/256) (1725/64) h273 n0274
  have h275 : NonnegOnQ 0 (6975/256) := nonnegOn_union 0 (1725/64) (6975/256) h274 n0275
  have h276 : NonnegOnQ 0 (3525/128) := nonnegOn_union 0 (6975/256) (3525/128) h275 n0276
  have h277 : NonnegOnQ 0 (7125/256) := nonnegOn_union 0 (3525/128) (7125/256) h276 n0277
  have h278 : NonnegOnQ 0 (225/8) := nonnegOn_union 0 (7125/256) (225/8) h277 n0278
  have h279 : NonnegOnQ 0 (7275/256) := nonnegOn_union 0 (225/8) (7275/256) h278 n0279
  have h280 : NonnegOnQ 0 (3675/128) := nonnegOn_union 0 (7275/256) (3675/128) h279 n0280
  have h281 : NonnegOnQ 0 (7425/256) := nonnegOn_union 0 (3675/128) (7425/256) h280 n0281
  have h282 : NonnegOnQ 0 (1875/64) := nonnegOn_union 0 (7425/256) (1875/64) h281 n0282
  have h283 : NonnegOnQ 0 (975/32) := nonnegOn_union 0 (1875/64) (975/32) h282 n0283
  have h284 : NonnegOnQ 0 (525/16) := nonnegOn_union 0 (975/32) (525/16) h283 n0284
  have h285 : NonnegOnQ 0 (2175/64) := nonnegOn_union 0 (525/16) (2175/64) h284 n0285
  have h286 : NonnegOnQ 0 (4425/128) := nonnegOn_union 0 (2175/64) (4425/128) h285 n0286
  have h287 : NonnegOnQ 0 (8925/256) := nonnegOn_union 0 (4425/128) (8925/256) h286 n0287
  have h288 : NonnegOnQ 0 (1125/32) := nonnegOn_union 0 (8925/256) (1125/32) h287 n0288
  have h289 : NonnegOnQ 0 (9075/256) := nonnegOn_union 0 (1125/32) (9075/256) h288 n0289
  have h290 : NonnegOnQ 0 (4575/128) := nonnegOn_union 0 (9075/256) (4575/128) h289 n0290
  have h291 : NonnegOnQ 0 (9225/256) := nonnegOn_union 0 (4575/128) (9225/256) h290 n0291
  have h292 : NonnegOnQ 0 (18525/512) := nonnegOn_union 0 (9225/256) (18525/512) h291 n0292
  have h293 : NonnegOnQ 0 (2325/64) := nonnegOn_union 0 (18525/512) (2325/64) h292 n0293
  have h294 : NonnegOnQ 0 (9375/256) := nonnegOn_union 0 (2325/64) (9375/256) h293 n0294
  have h295 : NonnegOnQ 0 (4725/128) := nonnegOn_union 0 (9375/256) (4725/128) h294 n0295
  have h296 : NonnegOnQ 0 (75/2) := nonnegOn_union 0 (4725/128) (75/2) h295 n0296
  have h297 : NonnegOnQ 0 (1275/32) := nonnegOn_union 0 (75/2) (1275/32) h296 n0297
  have h298 : NonnegOnQ 0 (675/16) := nonnegOn_union 0 (1275/32) (675/16) h297 n0298
  have h299 : NonnegOnQ 0 (2775/64) := nonnegOn_union 0 (675/16) (2775/64) h298 n0299
  have h300 : NonnegOnQ 0 (1425/32) := nonnegOn_union 0 (2775/64) (1425/32) h299 n0300
  have h301 : NonnegOnQ 0 (2925/64) := nonnegOn_union 0 (1425/32) (2925/64) h300 n0301
  have h302 : NonnegOnQ 0 (375/8) := nonnegOn_union 0 (2925/64) (375/8) h301 n0302
  have h303 : NonnegOnQ 0 (1575/32) := nonnegOn_union 0 (375/8) (1575/32) h302 n0303
  have h304 : NonnegOnQ 0 (825/16) := nonnegOn_union 0 (1575/32) (825/16) h303 n0304
  have h305 : NonnegOnQ 0 (1725/32) := nonnegOn_union 0 (825/16) (1725/32) h304 n0305
  have h306 : NonnegOnQ 0 (225/4) := nonnegOn_union 0 (1725/32) (225/4) h305 n0306
  have h307 : NonnegOnQ 0 (1875/32) := nonnegOn_union 0 (225/4) (1875/32) h306 n0307
  have h308 : NonnegOnQ 0 (975/16) := nonnegOn_union 0 (1875/32) (975/16) h307 n0308
  have h309 : NonnegOnQ 0 (2025/32) := nonnegOn_union 0 (975/16) (2025/32) h308 n0309
  have h310 : NonnegOnQ 0 (525/8) := nonnegOn_union 0 (2025/32) (525/8) h309 n0310
  have h311 : NonnegOnQ 0 (2175/32) := nonnegOn_union 0 (525/8) (2175/32) h310 n0311
  have h312 : NonnegOnQ 0 (1125/16) := nonnegOn_union 0 (2175/32) (1125/16) h311 n0312
  have h313 : NonnegOnQ 0 (2325/32) := nonnegOn_union 0 (1125/16) (2325/32) h312 n0313
  have h314 : NonnegOnQ 0 (4725/64) := nonnegOn_union 0 (2325/32) (4725/64) h313 n0314
  have h315 : NonnegOnQ 0 (75) := nonnegOn_union 0 (4725/64) (75) h314 n0315
  have h316 : NonnegOnQ 0 (2475/32) := nonnegOn_union 0 (75) (2475/32) h315 n0316
  have h317 : NonnegOnQ 0 (1275/16) := nonnegOn_union 0 (2475/32) (1275/16) h316 n0317
  have h318 : NonnegOnQ 0 (5175/64) := nonnegOn_union 0 (1275/16) (5175/64) h317 n0318
  have h319 : NonnegOnQ 0 (2625/32) := nonnegOn_union 0 (5175/64) (2625/32) h318 n0319
  have h320 : NonnegOnQ 0 (5325/64) := nonnegOn_union 0 (2625/32) (5325/64) h319 n0320
  have h321 : NonnegOnQ 0 (675/8) := nonnegOn_union 0 (5325/64) (675/8) h320 n0321
  have h322 : NonnegOnQ 0 (2775/32) := nonnegOn_union 0 (675/8) (2775/32) h321 n0322
  have h323 : NonnegOnQ 0 (1425/16) := nonnegOn_union 0 (2775/32) (1425/16) h322 n0323
  have h324 : NonnegOnQ 0 (5775/64) := nonnegOn_union 0 (1425/16) (5775/64) h323 n0324
  have h325 : NonnegOnQ 0 (2925/32) := nonnegOn_union 0 (5775/64) (2925/32) h324 n0325
  have h326 : NonnegOnQ 0 (375/4) := nonnegOn_union 0 (2925/32) (375/4) h325 n0326
  have h327 : NonnegOnQ 0 (3075/32) := nonnegOn_union 0 (375/4) (3075/32) h326 n0327
  have h328 : NonnegOnQ 0 (1575/16) := nonnegOn_union 0 (3075/32) (1575/16) h327 n0328
  have h329 : NonnegOnQ 0 (3225/32) := nonnegOn_union 0 (1575/16) (3225/32) h328 n0329
  have h330 : NonnegOnQ 0 (825/8) := nonnegOn_union 0 (3225/32) (825/8) h329 n0330
  have h331 : NonnegOnQ 0 (3375/32) := nonnegOn_union 0 (825/8) (3375/32) h330 n0331
  have h332 : NonnegOnQ 0 (1725/16) := nonnegOn_union 0 (3375/32) (1725/16) h331 n0332
  have h333 : NonnegOnQ 0 (3525/32) := nonnegOn_union 0 (1725/16) (3525/32) h332 n0333
  have h334 : NonnegOnQ 0 (225/2) := nonnegOn_union 0 (3525/32) (225/2) h333 n0334
  have h335 : NonnegOnQ 0 (3675/32) := nonnegOn_union 0 (225/2) (3675/32) h334 n0335
  have h336 : NonnegOnQ 0 (1875/16) := nonnegOn_union 0 (3675/32) (1875/16) h335 n0336
  have h337 : NonnegOnQ 0 (3825/32) := nonnegOn_union 0 (1875/16) (3825/32) h336 n0337
  have h338 : NonnegOnQ 0 (975/8) := nonnegOn_union 0 (3825/32) (975/8) h337 n0338
  have h339 : NonnegOnQ 0 (2025/16) := nonnegOn_union 0 (975/8) (2025/16) h338 n0339
  have h340 : NonnegOnQ 0 (4125/32) := nonnegOn_union 0 (2025/16) (4125/32) h339 n0340
  have h341 : NonnegOnQ 0 (525/4) := nonnegOn_union 0 (4125/32) (525/4) h340 n0341
  have h342 : NonnegOnQ 0 (4275/32) := nonnegOn_union 0 (525/4) (4275/32) h341 n0342
  have h343 : NonnegOnQ 0 (8625/64) := nonnegOn_union 0 (4275/32) (8625/64) h342 n0343
  have h344 : NonnegOnQ 0 (2175/16) := nonnegOn_union 0 (8625/64) (2175/16) h343 n0344
  have h345 : NonnegOnQ 0 (8775/64) := nonnegOn_union 0 (2175/16) (8775/64) h344 n0345
  have h346 : NonnegOnQ 0 (4425/32) := nonnegOn_union 0 (8775/64) (4425/32) h345 n0346
  have h347 : NonnegOnQ 0 (1125/8) := nonnegOn_union 0 (4425/32) (1125/8) h346 n0347
  have h348 : NonnegOnQ 0 (2325/16) := nonnegOn_union 0 (1125/8) (2325/16) h347 n0348
  have h349 : NonnegOnQ 0 (150) := nonnegOn_union 0 (2325/16) (150) h348 n0349
  have h350 : NonnegOnQ 0 (4875/32) := nonnegOn_union 0 (150) (4875/32) h349 n0350
  have h351 : NonnegOnQ 0 (2475/16) := nonnegOn_union 0 (4875/32) (2475/16) h350 n0351
  have h352 : NonnegOnQ 0 (1275/8) := nonnegOn_union 0 (2475/16) (1275/8) h351 n0352
  have h353 : NonnegOnQ 0 (5175/32) := nonnegOn_union 0 (1275/8) (5175/32) h352 n0353
  have h354 : NonnegOnQ 0 (2625/16) := nonnegOn_union 0 (5175/32) (2625/16) h353 n0354
  have h355 : NonnegOnQ 0 (5325/32) := nonnegOn_union 0 (2625/16) (5325/32) h354 n0355
  have h356 : NonnegOnQ 0 (675/4) := nonnegOn_union 0 (5325/32) (675/4) h355 n0356
  have h357 : NonnegOnQ 0 (2775/16) := nonnegOn_union 0 (675/4) (2775/16) h356 n0357
  have h358 : NonnegOnQ 0 (5625/32) := nonnegOn_union 0 (2775/16) (5625/32) h357 n0358
  have h359 : NonnegOnQ 0 (1425/8) := nonnegOn_union 0 (5625/32) (1425/8) h358 n0359
  have h360 : NonnegOnQ 0 (2925/16) := nonnegOn_union 0 (1425/8) (2925/16) h359 n0360
  have h361 : NonnegOnQ 0 (375/2) := nonnegOn_union 0 (2925/16) (375/2) h360 n0361
  have h362 : NonnegOnQ 0 (6075/32) := nonnegOn_union 0 (375/2) (6075/32) h361 n0362
  have h363 : NonnegOnQ 0 (12225/64) := nonnegOn_union 0 (6075/32) (12225/64) h362 n0363
  have h364 : NonnegOnQ 0 (3075/16) := nonnegOn_union 0 (12225/64) (3075/16) h363 n0364
  have h365 : NonnegOnQ 0 (1575/8) := nonnegOn_union 0 (3075/16) (1575/8) h364 n0365
  have h366 : NonnegOnQ 0 (825/4) := nonnegOn_union 0 (1575/8) (825/4) h365 n0366
  have h367 : NonnegOnQ 0 (1725/8) := nonnegOn_union 0 (825/4) (1725/8) h366 n0367
  have h368 : NonnegOnQ 0 (225) := nonnegOn_union 0 (1725/8) (225) h367 n0368
  have h369 : NonnegOnQ 0 (1875/8) := nonnegOn_union 0 (225) (1875/8) h368 n0369
  have h370 : NonnegOnQ 0 (975/4) := nonnegOn_union 0 (1875/8) (975/4) h369 n0370
  have h371 : NonnegOnQ 0 (2025/8) := nonnegOn_union 0 (975/4) (2025/8) h370 n0371
  have h372 : NonnegOnQ 0 (525/2) := nonnegOn_union 0 (2025/8) (525/2) h371 n0372
  have h373 : NonnegOnQ 0 (1125/4) := nonnegOn_union 0 (525/2) (1125/4) h372 n0373
  have h374 : NonnegOnQ 0 (300) := nonnegOn_union 0 (1125/4) (300) h373 n0374
  simpa using h374

theorem finiteIntervalCertificate_trigram_v1 : FiniteIntervalCertificateV1 := by
  intro t ht0 ht300
  exact finite_interval_nonneg t ht0 ht300

end AEGIS.RHKreinTrigramAdaptiveV1

#print axioms AEGIS.RHKreinTrigramAdaptiveV1.finiteIntervalCertificate_trigram_v1
