# OPTIMUS V7 (H64 contractive Weil packets): Lean receipt, 2026-11-15

Kernel-checked formalization of the V7 manuscript (`PROOF_V7.md`, OPTIMUS V7 package of 2026-11-15) on the
actual repository functional `B a b = WeilExplicitRightSideV1 (mixed a b)` (`WeilMixedAlgebraV2`).

**Main theorem** — `AEGIS.WeilH64AssemblyV7.h64_coercive`: for packets `g : Fin 2 × Fin 32 → WeilCompactSmoothGV1`
with logarithmic support `[c x − 1/4096, c x + 1/4096]`, `c (a, b) = ∓ log 2/2 + (2b − 31)/2048`, and energy `1`
(any shapes and phases; no moment condition, no equal prime edges), and every `z`,

    (1475/6144) Σ ‖z x‖² ≤ Re Σ_{x,y} z x · (−B (g x) (g y)) · conj (z y).

| Module | Content |
|---|---|
| `WeilH64ElementaryV7` | Hermitian Gershgorin; `w(u) ≤ 1 + 1/(2u)`; `log 1023 < 7`; `log 2/√2 < 1/2`; diagonal constant; margin |
| `WeilH64DiagonalV7` | general-radius diagonal (`diag_radius`) and `diag_v7`: `(13/3 − 1/2048) E ≤ −Re B(g, g)` |
| `WeilH64CrossV7` | `‖C_pq‖ ≤ (E_p+E_q)/2`; separated Archimedean bounds (`sep_arch_le`, `sep_arch_le_two`) |
| `WeilH64PrimeV7` | prime window: only `m = 2` survives, `‖·‖ ≤ (log 2/√2)·E`; `‖B‖ ≤ ‖prime‖ + ‖Arch‖` |
| `WeilH64AssemblyV7` | 64 centres, entry bounds, row budget (telescoping product checked by `decide +kernel`), `h64_coercive` |
| `WeilH64WitnessV7` | V7 §4: `pkt c = k · mulPacket (momentKiller ψ)`, energy 1, both moments zero; `h64_nonvacuous` |

Built on the existing lane V21–V31 (`WeilWidthArchIntegralV27`, `WeilSeparatedArchBridgeV31`,
`WeilThreeBlockPrimeEvaluationV30`, …) by module name, as the other `AegisRH/PR606` files.

**Replay** (Lean 4.33.1, Mathlib of this repository's lake packages, dependencies from compiled oleans):
default trust and `--trust=0`, all six modules exit 0, 0 errors, 0 warnings, no `sorry`.
Every `#print axioms` line reads `[propext, Classical.choice, Quot.sound]`.

**Non-emptiness.** `AEGIS.WeilH64WitnessV7.h64_nonvacuous` exhibits 64 packets (smooth, compact support in
`Ioi 0`, log-radius `1/4096` at the V7 centres, energy `1`, `WeilMomentConditionsV1`) and applies `h64_coercive`
to them, so the bound holds on a genuine 64-dimensional space of moment-zero test packets.

**Scope.** `--trust=0` re-checks the declarations of these six files; imported oleans (V21–V31,
`WeilLogTransportCanonicalV1`, Mathlib) are loaded as compiled and were not re-elaborated here.
Finite-dimensional coercivity of the restricted Weil form only: not RH, and not Weil positivity on any
function space.

| sha256 | file |
|---|---|
| `eeeec8c19cf064e6b30ab6225865de7b5437663702631b94fabf626d4505ccb6` | `WeilH64ElementaryV7.lean` |
| `646574e982602d9dfb3c547fc6230976f0be22398a9b01ac9f6518cc6bd95ac4` | `WeilH64DiagonalV7.lean` |
| `953059539830f1accd7285d1aef1fa567b0d981d7b5c8f3b8ff5e485e0ef2d03` | `WeilH64CrossV7.lean` |
| `193c59be2db7ba6b008a22915eebaefb03cd8ebb30dc54fb3630d6bba09dcecc` | `WeilH64PrimeV7.lean` |
| `23037034b74480b0073aa10fcff0081d074e08fbb8dd16875d4551d510620912` | `WeilH64AssemblyV7.lean` |
| `b13871fc2a0a2ad1204fa10c16f2a70436125778cce8ab7ef55d49a86185f463` | `WeilH64WitnessV7.lean` |
