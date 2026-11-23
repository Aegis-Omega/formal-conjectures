# RH equivalences in the lab, by open side (2026-11-10)

Found by name search (`rh_iff`, `_iff_rh`, `iff_riemannHypothesis`, `riemannHypothesis_iff`) over
`.lean` and `.lean.src`. Statements were read for family 3; families 1 and 2 are sorted by name
and by the frontier theorems read in `HANDOFF_ADDENDUM_20261110.md`. 28 theorems, three families.

## 1. Sign of the Weil form for every packet

`rh_iff_weil_negativity_v13`, `rh_iff_universal_v13`, `rh_iff_universal_arithmetic_v13`,
`rh_iff_final_sign_v13`, `final_sign_iff_rh_v13`, `universal_iff_rh_restated_v13`,
`millennium_moment_iff_rh_v13`, `rh_iff_certificate_v13`, `rh_iff_one_actual_sharp_signed_budget`,
`rh_iff_remaining_windows_actual_sharp_signed_budget`,
`cofinal_lower_certificates_iff_riemannHypothesis`.

Open side: the sign for every moment-zero packet.

## 2. Windows

`rh_iff_all_windows`, `rh_iff_all_windows_v13`, `rh_iff_nat_windows_v13`, `rh_iff_pi_nat_windows`,
`rh_iff_windows_from_21_40`, `rh_iff_windows_above_three_fifths`,
`rh_iff_windows_above_two_thirds`, `rh_iff_windows_above_eleven_sixteenths`.

Open side: the window sign for every half-width above the frontier. This is the only family with
a monotone, permanent measure of progress: each proved window stays proved.

## 3. One fixed packet, large shifts

`rh_iff_zero_shift_dominance_v13`, `rh_iff_prime_only_orbit_eventually_bounded`,
`rh_iff_combined_orbit_eventually_bounded`, `fixed_signed_prime_eventually_bounded_iff_rh`,
`fixed_detecting_packet_subexponential_iff_rh`,
`prime_only_subexponential_iff_rh_of_reflected_bridge` (conditional on `hBridge`),
`fsTwoThreeDetectorSign_iff_riemannHypothesis`, `dense_narrow_detector_iff_riemannHypothesis`,
`rh_iff_dense_packet_two_phase_real_kernel_v1`.

Open side: for one detecting packet, the shifted correlation stays bounded (or subexponential, or
keeps a sign for a dense set of shifts) as the shift `d` tends to infinity. This is square-root
cancellation of the primes at scale `e^d`, in smoothed form. No finite computation bounds it for
every `d`.

## Checked

No theorem in the tree proves a right-hand side without assuming RH. Searched for unconditional
producers of `ZeroShiftComponentDominanceV1`, `EveryPacketCofinalLowerCertificate`,
`DenseNarrowDetectorFourPhaseSign`, `FsTwoThreeDetectorSign`,
`ReflectedFixedKernelArithmeticRemainderBoundedV2` and
`PacketKernelSubexponentialV1 detectingPacket`; the only producers have the form
`(h : RiemannHypothesis) : …` or sit inside a proof under that assumption.

## Reading

The 28 statements are three views of one open fact. None is closer to a proof than the others.

- Family 2 is where the lab can keep proving new unconditional theorems (next: the window `3/2`,
  see `research/rh/checkpoints/20261110_window_l32_feasibility_v1/`). Its cost grows doubly
  exponentially in the window, so it cannot be exhausted.
- Family 3 is where a uniform argument would have to live, because it concerns one fixed packet
  and all shifts at once. Nothing in the lab bounds that orbit unconditionally.
- Hypotheses offered as shortcuts must be tested before work is spent on them. Three were found
  equivalent to the sign itself (`checkpoints/20261110_hrepresentation_equivalence_v1/`), one was
  found to fail (`checkpoints/20261110_hresidual_obstruction_v1/`).
