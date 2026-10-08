/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionNestedReconstruction

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionSymmetricReconstruction"

namespace DkMath.FLT.Seven

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The existing alternating split's residual root is a seven-unit. This
exposes arithmetic used inside its constructor without refactoring Row Z. -/
theorem PrescribedCarrierAlternatingPowerSplit.seven_not_dvd_b
    {x y z : ℕ} {source : CounterexamplePack x y z} {hz : 7 ∣ z}
    (split : PrescribedCarrierAlternatingPowerSplit source hz) : ¬ 7 ∣ split.b := by
  have hsum := seven_dvd_sum_of_seven_dvd_third source hz
  have hy := seven_not_dvd_second_of_seven_dvd_sum source hsum
  have hyInt : ¬ (7 : ℤ) ∣ -(y : ℤ) := by
    simpa only [dvd_neg] using
      (show ¬ (7 : ℤ) ∣ (y : ℤ) from fun h => hy (Int.ofNat_dvd.mp h))
  intro hb
  have h49 : 49 ∣ alternatingCyclotomicSeven x y := by
    rcases hb with ⟨k, hk⟩
    rw [split.residual_eq, hk]
    use 7 ^ 6 * k ^ 7
    ring
  apply not_fortyNine_dvd_cyclotomicSeven
    (seven_dvd_signed_gap_of_seven_dvd_third source hz) hyInt
  rw [← alternatingCyclotomicSeven_intCast]
  exact Int.ofNat_dvd.mpr h49

/-- Both outer packet types now use the same purely natural allocation. -/
theorem PrescribedCarrierAlternatingPowerSplit.exists_nested_seventh_roots
    {M x y : ℕ} {source : CounterexamplePack x y (7 ^ 4 * M ^ 7)}
    {hz : 7 ∣ 7 ^ 4 * M ^ 7}
    (split : PrescribedCarrierAlternatingPowerSplit source hz) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
      split.a = 7 ^ 3 * r ^ 7 ∧ split.b = s ^ 7 ∧ M = r * s :=
  exists_nested_seventh_allocation split.a_pos split.b_pos
    split.coprime_a_b split.seven_not_dvd_b split.distinguished_eq

theorem PrescribedCarrierAlternatingPowerSplit.nested_sum_residual
    {M x y r s : ℕ} {source : CounterexamplePack x y (7 ^ 4 * M ^ 7)}
    {hz : 7 ∣ 7 ^ 4 * M ^ 7}
    (split : PrescribedCarrierAlternatingPowerSplit source hz)
    (ha : split.a = 7 ^ 3 * r ^ 7) (hb : split.b = s ^ 7) :
    x + y = 7 ^ 27 * r ^ 49 ∧ alternatingCyclotomicSeven x y = 7 * s ^ 49 := by
  constructor
  · rw [split.sum_eq, ha, mul_pow, ← pow_mul, ← pow_mul]
    ring
  · rw [split.residual_eq, hb, ← pow_mul]

/-- The right-hand-side branch has one endpoint variable on the positive
sum interval. Coprimality with the sum is equivalent to primitive endpoints.
No orientation or literal endpoint uniqueness is imposed here. -/
def NestedRightHandSideCondition (M : ℕ) : Prop :=
  ∃ r s u : ℕ, 0 < r ∧ 0 < s ∧ 0 < u ∧ u < 7 ^ 27 * r ^ 49 ∧
    M = r * s ∧ Nat.Coprime r s ∧ Nat.Coprime u (7 ^ 27 * r ^ 49) ∧
    alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * s ^ 49

/-- Exact scalar equivalence, including the positive primitive natural
Fermat equation in the reverse direction. -/
theorem rightHandSideChart_iff_nested (M : ℕ) :
    (∃ u v : ℕ, CounterexamplePack u v (7 ^ 4 * M ^ 7)) ↔
      NestedRightHandSideCondition M := by
  constructor
  · rintro ⟨u, v, source⟩
    have hz : 7 ∣ 7 ^ 4 * M ^ 7 := dvd_mul_of_dvd_left (by norm_num) _
    rcases nonempty_prescribedCarrierAlternatingPowerSplit source hz with ⟨split⟩
    rcases split.exists_nested_seventh_roots with ⟨r, s, hr, hs, hrs, ha, hb, hM⟩
    have hident := split.nested_sum_residual ha hb
    have huv : u < 7 ^ 27 * r ^ 49 := by rw [← hident.1]; exact Nat.lt_add_of_pos_right source.hy
    have hcop : Nat.Coprime u (7 ^ 27 * r ^ 49) := by
      rw [← hident.1]
      simpa using source.hxy
    have hv : 7 ^ 27 * r ^ 49 - u = v := by rw [← hident.1]; omega
    exact ⟨r, s, u, hr, hs, source.hx, huv, hM, hrs, hcop,
      by simpa only [hv] using hident.2⟩
  · rintro ⟨r, s, u, hr, hs, hu, huD, hM, hrs, hcop, hAlt⟩
    let D := 7 ^ 27 * r ^ 49
    have hsum : u + (D - u) = D := Nat.add_sub_of_le huD.le
    have hv : 0 < D - u := Nat.sub_pos_of_lt huD
    have hpair : Nat.Coprime u (D - u) :=
      (Nat.coprime_sub_self_right huD.le).mpr hcop
    have hc : 0 < 7 ^ 4 * M ^ 7 := by
      have hMpos : 0 < M := by rw [hM]; exact Nat.mul_pos hr hs
      positivity
    have heq : Fermat7Equation u (D - u) (7 ^ 4 * M ^ 7) := by
      change u ^ 7 + (D - u) ^ 7 = (7 ^ 4 * M ^ 7) ^ 7
      calc
        _ = D * alternatingCyclotomicSeven u (D - u) := by
          rw [← add_mul_alternatingCyclotomicSeven, hsum]
        _ = _ := by
          rw [hAlt, hM]
          dsimp [D]
          simp only [mul_pow, ← pow_mul]
          ring
    exact ⟨u, D - u, ⟨hu, hv, hc, hpair, heq⟩⟩

/-- Endpoint exchange preserves the natural alternating residual. -/
theorem alternatingCyclotomicSeven_comm (x y : ℕ) :
    alternatingCyclotomicSeven x y = alternatingCyclotomicSeven y x := by
  simp only [alternatingCyclotomicSeven, Nat.add_comm]

/-- Canonical endpoint order loses no receiver. This selects the half
interval; it does not assert uniqueness on that interval. -/
theorem nestedRightHandSideCondition_iff_ordered (M : ℕ) :
    NestedRightHandSideCondition M ↔
      ∃ r s u : ℕ, 0 < r ∧ 0 < s ∧ 0 < u ∧ u < 7 ^ 27 * r ^ 49 ∧
        M = r * s ∧ Nat.Coprime r s ∧ Nat.Coprime u (7 ^ 27 * r ^ 49) ∧
        u ≤ 7 ^ 27 * r ^ 49 - u ∧
        alternatingCyclotomicSeven u (7 ^ 27 * r ^ 49 - u) = 7 * s ^ 49 := by
  constructor
  · rintro ⟨r, s, u, hr, hs, hu, huD, hM, hcop, hprimitive, hAlt⟩
    by_cases horder : u ≤ 7 ^ 27 * r ^ 49 - u
    · exact ⟨r, s, u, hr, hs, hu, huD, hM, hcop, hprimitive, horder, hAlt⟩
    · have hv : 0 < 7 ^ 27 * r ^ 49 - u := Nat.sub_pos_of_lt huD
      have hvD : 7 ^ 27 * r ^ 49 - u < 7 ^ 27 * r ^ 49 := by omega
      have hu' : 7 ^ 27 * r ^ 49 - (7 ^ 27 * r ^ 49 - u) = u := by omega
      refine ⟨r, s, 7 ^ 27 * r ^ 49 - u, hr, hs, hv, hvD, hM, hcop,
        (Nat.coprime_self_sub_left huD.le).mpr hprimitive, ?_, ?_⟩
      · omega
      · rw [hu', alternatingCyclotomicSeven_comm]
        exact hAlt
  · rintro ⟨r, s, u, hr, hs, hu, huD, hM, hcop, hprimitive, _, hAlt⟩
    exact ⟨r, s, u, hr, hs, hu, huD, hM, hcop, hprimitive, hAlt⟩

/-- Signed coefficients do not lose a factor of seven in the modulus:
the whole higher polynomial is divisible by seven when the sum is. -/
theorem alternatingCyclotomicSeven_div_seven_modEq_sum (x y : ℕ)
    (h7 : 7 ∣ x + y) :
    Nat.ModEq (x + y) (alternatingCyclotomicSeven x y / 7) (y ^ 6) := by
  rcases h7 with ⟨k, hk⟩
  let D : ℤ := ((x + y : ℕ) : ℤ)
  let Q : ℤ := (k : ℤ) * D ^ 4 - D ^ 4 * y + 3 * D ^ 3 * y ^ 2 -
    5 * D ^ 2 * y ^ 3 + 5 * D * y ^ 4 - 3 * y ^ 5
  have hD : D = 7 * (k : ℤ) := by dsimp [D]; exact_mod_cast hk
  have heq : (alternatingCyclotomicSeven x y : ℤ) =
      7 * ((y : ℤ) ^ 6 + D * Q) := by
    rw [alternatingCyclotomicSeven_intCast, alternatingCyclotomicSeven_sum_expansion]
    change D * (D ^ 5 - 7 * D ^ 4 * y + 21 * D ^ 3 * y ^ 2 -
      35 * D ^ 2 * y ^ 3 + 35 * D * y ^ 4 - 21 * y ^ 5) + 7 * y ^ 6 = _
    dsimp [Q]
    rw [hD]
    ring
  have hAlt : 7 ∣ alternatingCyclotomicSeven x y :=
    Int.ofNat_dvd.mp ⟨(y : ℤ) ^ 6 + D * Q, heq⟩
  have hcancel : (7 : ℤ) * ((alternatingCyclotomicSeven x y / 7 : ℕ) : ℤ) =
      (alternatingCyclotomicSeven x y : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hAlt
  have hdiv : ((alternatingCyclotomicSeven x y / 7 : ℕ) : ℤ) =
      (y : ℤ) ^ 6 + D * Q :=
    mul_left_cancel₀ (by decide : (7 : ℤ) ≠ 0) (hcancel.trans heq)
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨-Q, ?_⟩
  rw [hdiv]
  simp only [Nat.cast_pow]
  change (y : ℤ) ^ 6 - ((y : ℤ) ^ 6 + D * Q) = D * -Q
  ring

/-- Exact normalization and the full-sum congruence at the nested scale. -/
theorem nestedAlternatingResidual_full_sum_congruence {r s x y : ℕ}
    (hsum : x + y = 7 ^ 27 * r ^ 49)
    (hAlt : alternatingCyclotomicSeven x y = 7 * s ^ 49) :
    alternatingCyclotomicSeven x y / 7 = s ^ 49 ∧
      Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (y ^ 6) := by
  have hdiv : alternatingCyclotomicSeven x y / 7 = s ^ 49 := by
    rw [hAlt, Nat.mul_div_cancel_left _ (by decide : 0 < 7)]
  refine ⟨hdiv, ?_⟩
  have h7 : 7 ∣ x + y := by rw [hsum]; exact dvd_mul_of_dvd_left (by norm_num) _
  simpa only [hsum, hdiv] using alternatingCyclotomicSeven_div_seven_modEq_sum x y h7

/-- Division-free comparison with the reconstructed away root, using its
actual endpoint ledger. Seven-unit multipliers do not imply equality of
root coordinates or equality up to integer units. -/
theorem AwayValuationTransferPacket.rightHandSide_root_unit_comparison
    {u v c : ℕ} (route : AwayValuationTransferPacket u v c)
    {source : CounterexamplePack u v c} {hc : 7 ∣ c}
    (split : PrescribedCarrierAlternatingPowerSplit source hc) :
    split.a * (split.b * v * (v + c)) =
        Int.natAbs route.normal.root.snd *
          Int.natAbs (seventhPowerSndCore route.normal.root.fst route.normal.root.snd) ∧
      ¬ 7 ∣ split.b * v * (v + c) ∧
      ¬ 7 ∣ Int.natAbs (seventhPowerSndCore route.normal.root.fst route.normal.root.snd) := by
  have hv := seven_not_dvd_second_of_seven_dvd_sum source
    (seven_dvd_sum_of_seven_dvd_third source hc)
  have hvc : ¬ 7 ∣ v + c := by
    intro h
    exact hv ((Nat.dvd_add_iff_left (m := v) hc).mpr h)
  have heq : split.a * (split.b * v * (v + c)) =
      Int.natAbs route.normal.root.snd *
        Int.natAbs (seventhPowerSndCore route.normal.root.fst route.normal.root.snd) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7)
    calc
      _ = c * v * (v + c) := by
        calc
          _ = (7 * split.a * split.b) * v * (v + c) := by ring
          _ = _ := congrArg (fun k => k * v * (v + c)) split.distinguished_eq.symm
      _ = _ := by
        simpa only [mul_assoc, mul_comm c v] using away_endpoint_product_load_eq route.normal
  refine ⟨heq, ?_, route.normal.seven_not_dvd_natAbs_sndCore⟩
  intro h
  rcases (by norm_num : Nat.Prime 7).dvd_mul.mp h with h | h
  · rcases (by norm_num : Nat.Prime 7).dvd_mul.mp h with h | h
    · exact split.seven_not_dvd_b h
    · exact hv h
  · exact hvc h

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Both branches now have the same source-core allocation and large scale;
only their residual polynomial and endpoint geometry differ. Neither thin
receiver is asserted to be inhabited. -/
theorem internalDepthFourReconstruction_iff_two_nested_receivers
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      NestedPrescribedSummandCondition (internalDepthFourSeventhCore p) ∨
        NestedRightHandSideCondition (internalDepthFourSeventhCore p) := by
  rw [internalDepthFourReconstruction_iff_nested_or_left,
    internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow,
    rightHandSideChart_iff_nested]

/-- The actual source supplies seven-unit factors, exact sum depth 27, and
the normalized alternating congruence modulo the entire sum. -/
theorem internalDepthFourRightHandSide_nested_normal_form
    (p : RamifiedSignedRootRoutingPacket) {u v : ℕ}
    (pack : CounterexamplePack u v (internalDepthFourCarrier p)) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
      internalDepthFourSeventhCore p = r * s ∧ ¬ 7 ∣ r ∧ ¬ 7 ∣ s ∧
      u + v = 7 ^ 27 * r ^ 49 ∧ alternatingCyclotomicSeven u v = 7 * s ^ 49 ∧
      padicValNat 7 (u + v) = 27 ∧
      Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (v ^ 6) := by
  have pack' : CounterexamplePack u v (7 ^ 4 * internalDepthFourSeventhCore p ^ 7) := by
    simpa only [internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow] using pack
  have hc : 7 ∣ 7 ^ 4 * internalDepthFourSeventhCore p ^ 7 :=
    dvd_mul_of_dvd_left (by norm_num) _
  rcases nonempty_prescribedCarrierAlternatingPowerSplit pack' hc with ⟨split⟩
  rcases split.exists_nested_seventh_roots with ⟨r, s, hr, hs, hcop, ha, hb, hM⟩
  have hr7 : ¬ 7 ∣ r := by
    intro h
    exact internalDepthFourSeventhCore_not_seven_dvd p (hM ▸ dvd_mul_of_dvd_left h s)
  have hs7 : ¬ 7 ∣ s := by
    intro h
    exact internalDepthFourSeventhCore_not_seven_dvd p (hM ▸ dvd_mul_of_dvd_right h r)
  have hident := split.nested_sum_residual ha hb
  exact ⟨r, s, hr, hs, hcop, hM, hr7, hs7, hident.1, hident.2,
    by rw [hident.1]; exact (nestedFactor_exact_depths hr7).2,
    (nestedAlternatingResidual_full_sum_congruence hident.1 hident.2).2⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
