/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenAdicNestedPowerSplit
import DkMath.FLT.Seven.SevenRamifiedFusionDepthFourReconstructionAudit
import DkMath.FLT.Seven.PrimeTraceOneReconstructionRamifiedResolution

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionNestedReconstruction"

namespace DkMath.FLT.Seven

open DkMath.CosmicFormulaBinom

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Coprime factor allocations of the source seventh-root core, with one
normalized GN equation. No enumeration and no existence assumption are hidden
in this predicate. -/
def NestedPrescribedSummandCondition (M : ℕ) : Prop :=
  ∃ r s u : ℕ, 0 < r ∧ 0 < s ∧ 0 < u ∧ M = r * s ∧
    Nat.Coprime r s ∧ Nat.Coprime u (7 * M) ∧
    GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49

/-- The hypothetical prescribed-summand chart enters the existing ramified
packet by exchanging its summands. The second extraction retains the exact
original power split as provenance. -/
theorem CounterexamplePack.prescribedSummand_nested_split {M u v : ℕ}
    (pack : CounterexamplePack u (7 ^ 4 * M ^ 7) v) :
    ∃ split : SevenAdicPowerSplit (7 ^ 4 * M ^ 7) u v,
      ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
        split.a = 7 ^ 3 * r ^ 7 ∧ split.b = s ^ 7 ∧ M = r * s := by
  have h7 : 7 ∣ 7 ^ 4 * M ^ 7 := dvd_mul_of_dvd_left (by norm_num) _
  rcases nonempty_ramified_of_seven_dvd_second pack h7 with ⟨normal⟩
  let split := normal.seventhPower.residual.powerSplit
  rcases split.exists_nested_seventh_roots with ⟨r, s, hr, hs, hcop, ha, hb, hM⟩
  exact ⟨split, r, s, hr, hs, hcop, ha, hb, hM⟩

/-- The scalar normal form is equivalent to the entire prescribed-summand
existence branch. In the reverse direction the next endpoint is exactly
`u + 7^27*r^49`, and the cosmic identity supplies its Fermat equation. -/
theorem prescribedSummandChart_iff_nested (M : ℕ) :
    (∃ u v : ℕ, CounterexamplePack u (7 ^ 4 * M ^ 7) v) ↔
      NestedPrescribedSummandCondition M := by
  constructor
  · rintro ⟨u, v, pack⟩
    rcases pack.prescribedSummand_nested_split with
      ⟨split, r, s, hr, hs, hcop, ha, hb, hM⟩
    have hident := split.nested_gap_residual ha hb
    have huc : Nat.Coprime u (7 * M) := by
      apply pack.hxy.of_dvd_right
      use 7 ^ 3 * M ^ 6
      ring
    exact ⟨r, s, u, hr, hs, pack.hx, hM, hcop, huc,
      by rw [← hident.1]; exact hident.2⟩
  · rintro ⟨r, s, u, hr, hs, hu, hM, hrs, huc, hGN⟩
    let d := 7 ^ 27 * r ^ 49
    have hMpos : 0 < M := by rw [hM]; exact Nat.mul_pos hr hs
    have hcpos : 0 < 7 ^ 4 * M ^ 7 := by positivity
    have hcop : Nat.Coprime u (7 ^ 4 * M ^ 7) :=
      ((Nat.coprime_mul_iff_right.mp huc).1.pow_right 4).mul_right
        ((Nat.coprime_mul_iff_right.mp huc).2.pow_right 7)
    have hbody : d * GN 7 d u = (7 ^ 4 * M ^ 7) ^ 7 := by
      rw [hGN, hM]
      dsimp [d]
      simp only [mul_pow, ← pow_mul]
      ring
    have hEq : Fermat7Equation u (7 ^ 4 * M ^ 7) (u + d) := by
      have h := cosmic_id_csr' (R := ℕ) 7 d u
      change (d + u) ^ 7 = d * GN 7 d u + u ^ 7 at h
      rw [hbody] at h
      simpa only [Fermat7Equation, add_comm] using h.symm
    exact ⟨u, u + d, ⟨hu, hcpos, Nat.add_pos_left hu d, hcop, hEq⟩⟩

/-- The normalized forty-ninth-power residual retains the full large gap
modulus. The proof divides only exact multiples of seven. -/
theorem nestedResidual_normalized_congruence {r s u : ℕ}
    (hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    GN 7 (7 ^ 27 * r ^ 49) u / 7 = s ^ 49 ∧
      Nat.ModEq (7 ^ 26 * r ^ 49) (s ^ 49) (u ^ 6) := by
  have hd : 7 ^ 27 * r ^ 49 / 7 = 7 ^ 26 * r ^ 49 := by
    have heq : 7 ^ 27 * r ^ 49 = 7 * (7 ^ 26 * r ^ 49) := by ring
    rw [heq, Nat.mul_div_cancel_left _ (by decide : 0 < 7)]
  have h7 : 7 ∣ 7 ^ 27 * r ^ 49 := dvd_mul_of_dvd_left (by norm_num) _
  have hdiv : GN 7 (7 ^ 27 * r ^ 49) u / 7 = s ^ 49 := by
    rw [hGN, Nat.mul_div_cancel_left _ (by decide : 0 < 7)]
  exact ⟨hdiv, by simpa only [hd, hdiv] using
    GN_seven_div_seven_modEq_head (7 ^ 27 * r ^ 49) u h7⟩

/-- The coefficient divisibility strengthens the requested congruence by one
additional factor of seven, to the complete natural gap modulus. -/
theorem nestedResidual_full_gap_congruence {r s u : ℕ}
    (hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49) :
    Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (u ^ 6) := by
  have h7 : 7 ∣ 7 ^ 27 * r ^ 49 := dvd_mul_of_dvd_left (by norm_num) _
  have h := GN_seven_div_seven_modEq_gap (7 ^ 27 * r ^ 49) u h7
  simpa only [hGN, Nat.mul_div_cancel_left _ (by decide : 0 < 7)] using h

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- The absolute seventh-root core already chosen by the signed ramified
norm packet; it is not a new root obtained from the valuation statement. -/
def internalDepthFourSeventhCore (p : RamifiedSignedRootRoutingPacket) : ℕ :=
  Int.natAbs p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot

theorem internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow
    (p : RamifiedSignedRootRoutingPacket) :
    internalDepthFourCarrier p = 7 ^ 4 * internalDepthFourSeventhCore p ^ 7 := by
  let q := p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket
  have h := congrArg Int.natAbs q.innerSnd_eq
  simpa [Int.natAbs_mul, Int.natAbs_pow, q,
    internalDepthFourCarrier, internalDepthFourSeventhCore] using h

theorem internalDepthFourSeventhCore_not_seven_dvd
    (p : RamifiedSignedRootRoutingPacket) :
    ¬ 7 ∣ internalDepthFourSeventhCore p := by
  intro h
  exact p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.innerSndRoot_not_seven_dvd
    (Int.natCast_dvd.mpr h)

theorem internalDepthFourSeventhCore_pos
    (p : RamifiedSignedRootRoutingPacket) : 0 < internalDepthFourSeventhCore p := by
  by_contra h
  have hz : internalDepthFourSeventhCore p = 0 := Nat.eq_zero_of_not_pos h
  exact internalDepthFourSeventhCore_not_seven_dvd p (hz ▸ dvd_zero 7)

/-- The full reconstruction obligation keeps the right-hand-side branch.
Only the summand branch is replaced by the thinner nested GN condition. -/
theorem internalDepthFourReconstruction_iff_nested_or_left
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      NestedPrescribedSummandCondition (internalDepthFourSeventhCore p) ∨
        ∃ u v : ℕ, CounterexamplePack u v (internalDepthFourCarrier p) := by
  rw [internalDepthFourReconstruction_iff_fermatChart]
  constructor
  · intro chart
    cases chart with
    | right pack h7 =>
        apply Or.inl
        apply (prescribedSummandChart_iff_nested _).mp
        exact ⟨_, _, by simpa only [internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow] using pack⟩
    | left pack h7 => exact Or.inr ⟨_, _, pack⟩
    | sum pack heq h7 => exact (AwayCarrierFermatChart.sum_impossible pack heq h7).elim
  · intro h
    rcases h with hnest | ⟨u, v, pack⟩
    · rcases (prescribedSummandChart_iff_nested _).mpr hnest with ⟨u, v, pack⟩
      exact .right (by simpa only [internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow] using pack)
        (internalDepthFourCarrier_admissible p).2.2
    · exact .left pack (internalDepthFourCarrier_admissible p).2.2

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Finite factor support replaces the two-endpoint grid. The endpoint `u`
is not enumerated; strict monotonicity gives at most one solution per factor.
-/
theorem nestedPrescribedSummandCondition_iff_divisor (M : ℕ) (hM : 0 < M) :
    NestedPrescribedSummandCondition M ↔
      ∃ r ∈ M.divisors, ∃ u : ℕ, 0 < u ∧ Nat.Coprime r (M / r) ∧
        Nat.Coprime u (7 * M) ∧
        GN 7 (7 ^ 27 * r ^ 49) u = 7 * (M / r) ^ 49 := by
  constructor
  · rintro ⟨r, s, u, hr, hs, hu, hprod, hcop, huc, heq⟩
    have hdiv : r ∣ M := ⟨s, hprod⟩
    have hsEq : M / r = s := by rw [hprod]; exact Nat.mul_div_cancel_left s hr
    exact ⟨r, Nat.mem_divisors.mpr ⟨hdiv, hM.ne'⟩, u, hu,
      by simpa only [hsEq] using hcop, huc, by simpa only [hsEq] using heq⟩
  · rintro ⟨r, hmem, u, hu, hcop, huc, heq⟩
    have hdiv := Nat.dvd_of_mem_divisors hmem
    have hr : 0 < r := Nat.pos_of_dvd_of_pos hdiv hM
    have hprod : M = r * (M / r) := (Nat.mul_div_cancel' hdiv).symm
    have hs : 0 < M / r := by
      by_contra hzero
      have hz : M / r = 0 := Nat.eq_zero_of_not_pos hzero
      rw [hz, mul_zero] at hprod
      exact hM.ne' hprod
    exact ⟨r, M / r, u, hr, hs, hu, hprod, hcop, huc, heq⟩

/-- The nested exceptional factor has depth three and its gap has depth
twenty-seven whenever the allocated core is a seven-unit. -/
theorem nestedFactor_exact_depths {r : ℕ} (hr : ¬ 7 ∣ r) :
    padicValNat 7 (7 ^ 3 * r ^ 7) = 3 ∧
      padicValNat 7 (7 ^ 27 * r ^ 49) = 27 := by
  have hr0 : r ≠ 0 := by intro h; exact hr (h ▸ dvd_zero 7)
  constructor
  · rw [padicValNat.mul (by norm_num) (pow_ne_zero 7 hr0),
      padicValNat.prime_pow, padicValNat.pow, padicValNat.eq_zero_of_not_dvd hr]
  · rw [padicValNat.mul (by norm_num) (pow_ne_zero 49 hr0),
      padicValNat.prime_pow, padicValNat.pow, padicValNat.eq_zero_of_not_dvd hr]

/-- Division-free comparison with the actual reconstructed away root. The
two displayed multipliers are seven-units, not necessarily integer units.
This gives more provenance than a matching depth, but does not assert equality
of the factor and the root coordinate. -/
theorem AwayValuationTransferPacket.prescribedSummand_root_unit_comparison
    {c u v : ℕ} (route : AwayValuationTransferPacket u c v)
    (split : SevenAdicPowerSplit c u v) :
    split.a * (split.b * v * (c + v)) =
        Int.natAbs route.normal.root.snd *
          Int.natAbs (seventhPowerSndCore route.normal.root.fst route.normal.root.snd) ∧
      ¬ 7 ∣ split.b * v * (c + v) ∧
      ¬ 7 ∣ Int.natAbs (seventhPowerSndCore route.normal.root.fst route.normal.root.snd) := by
  have h7c := split.sevenAdic.seven_dvd_x
  have hv : ¬ 7 ∣ v := (by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mp
    ((coprime_y_z_of_counterexamplePack route.normal.counterexample).of_dvd_left h7c)
  have hcv : ¬ 7 ∣ c + v := by
    intro h
    have hvdvd : 7 ∣ v := (Nat.dvd_add_iff_right (n := v) h7c).mpr h
    exact hv hvdvd
  have heq : split.a * (split.b * v * (c + v)) =
      Int.natAbs route.normal.root.snd *
        Int.natAbs (seventhPowerSndCore route.normal.root.fst route.normal.root.snd) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 7)
    calc
      _ = c * v * (c + v) := by
        calc
          _ = (7 * split.a * split.b) * v * (c + v) := by ring
          _ = _ := congrArg (fun k => k * v * (c + v)) split.distinguished_eq.symm
      _ = _ := by simpa only [mul_assoc] using away_endpoint_product_load_eq route.normal
  refine ⟨heq, ?_, route.normal.seven_not_dvd_natAbs_sndCore⟩
  intro h
  rcases (by norm_num : Nat.Prime 7).dvd_mul.mp h with h | h
  · rcases (by norm_num : Nat.Prime 7).dvd_mul.mp h with h | h
    · exact split.seven_not_dvd_b h
    · exact hv h
  · exact hcv h

namespace RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

/-- Full source-indexed necessary normal form for the summand branch,
including exact depth and the normalized large-modulus congruence. -/
theorem internalDepthFourSummand_nested_normal_form
    (p : RamifiedSignedRootRoutingPacket) {u v : ℕ}
    (pack : CounterexamplePack u (internalDepthFourCarrier p) v) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ Nat.Coprime r s ∧
      internalDepthFourSeventhCore p = r * s ∧ ¬ 7 ∣ r ∧ ¬ 7 ∣ s ∧
      v - u = 7 ^ 27 * r ^ 49 ∧ GN 7 (v - u) u = 7 * s ^ 49 ∧
      padicValNat 7 (v - u) = 27 ∧
      Nat.ModEq (7 ^ 26 * r ^ 49) (s ^ 49) (u ^ 6) ∧
      Nat.ModEq (7 ^ 27 * r ^ 49) (s ^ 49) (u ^ 6) := by
  have pack' : CounterexamplePack u (7 ^ 4 * internalDepthFourSeventhCore p ^ 7) v := by
    simpa only [internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow] using pack
  rcases pack'.prescribedSummand_nested_split with
    ⟨split, r, s, hr, hs, hcop, ha, hb, hM⟩
  have hr7 : ¬ 7 ∣ r := by
    intro h
    exact internalDepthFourSeventhCore_not_seven_dvd p
      (hM ▸ dvd_mul_of_dvd_left h s)
  have hs7 : ¬ 7 ∣ s := by
    intro h
    exact internalDepthFourSeventhCore_not_seven_dvd p
      (hM ▸ dvd_mul_of_dvd_right h r)
  have hident := split.nested_gap_residual ha hb
  have hGN : GN 7 (7 ^ 27 * r ^ 49) u = 7 * s ^ 49 := by
    rw [← hident.1]; exact hident.2
  exact ⟨r, s, hr, hs, hcop, hM, hr7, hs7, hident.1, hident.2,
    by rw [hident.1]; exact (nestedFactor_exact_depths hr7).2,
    (nestedResidual_normalized_congruence hGN).2,
    nestedResidual_full_gap_congruence hGN⟩

end RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

end DkMath.FLT.Seven
