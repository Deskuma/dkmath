/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimePowerCellSolubility

#print "file: DkMath.FLT.Seven.PrimePowerCellAudit"

namespace DkMath.FLT.Seven

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

private theorem intCast_zero_of_dvd {M : ℕ} {a : ℤ} (h : (M : ℤ) ∣ a) :
    (a : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a M).2 h

private theorem intCast_isUnit_of_not_dvd_natAbs {q e : ℕ} (hq : Nat.Prime q)
    (_he : 0 < e) {a : ℤ} (ha : ¬ q ∣ a.natAbs) : IsUnit (a : ZMod (q ^ e)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  exact (hq.coprime_iff_not_dvd.mpr ha).pow_left e

private theorem prime_not_dvd_second {q a b : ℕ} (hq : Nat.Prime q)
    (hab : Nat.Coprime a b) (ha : q ∣ a) : ¬ q ∣ b := by
  intro hb
  exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hab ha hb)

private theorem modulus_dvd_rootSnd_of_sevenV {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r)
    (hc : p.column = .sevenV) : p.modulus ∣ r.cubic.rootTriple.vPart := by
  have hd := p.modulus_dvd_root
  simp only [hc, rootRoutingFactorNat] at hd
  have hq7 : Nat.Coprime p.q 7 :=
    p.q_prime.coprime_iff_not_dvd.mpr (by
      intro h
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h with h1 | h7
      · exact p.q_prime.ne_one h1
      · exact p.q_ne_seven h7)
  exact (hq7.pow_left p.exponent).dvd_mul_left.mp (by
    simpa [AwayNonSevenPrimeDepthPacket.modulus] using hd)

private theorem endpoint_nondegenerate_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    AwayEndpointPrimePowerNondegenerate p.modulus p.row (y : ZMod p.modulus)
      (z : ZMod p.modulus) := by
  have hq := p.q_dvd_endpoint
  cases hr : p.row
  · simp only [hr, endpointRoutingFactorNat] at hq
    exact isUnit_zmod_primePower_of_not_dvd p.q_prime p.exponent_pos
      (prime_not_dvd_second p.q_prime r.endpoint_y_z_coprime hq)
  · simp only [hr, endpointRoutingFactorNat] at hq
    exact isUnit_zmod_primePower_of_not_dvd p.q_prime p.exponent_pos
      (prime_not_dvd_second p.q_prime r.endpoint_y_z_coprime.symm hq)
  · simp only [hr, endpointRoutingFactorNat] at hq
    exact ⟨isUnit_zmod_primePower_of_not_dvd p.q_prime p.exponent_pos
        (prime_not_dvd_second p.q_prime r.endpoint_y_sum_coprime.symm hq),
      isUnit_zmod_primePower_of_not_dvd p.q_prime p.exponent_pos
        (prime_not_dvd_second p.q_prime r.endpoint_z_sum_coprime.symm hq)⟩

private theorem root_nondegenerate_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    AwayRootPrimePowerNondegenerate p.modulus p.column
      (r.cubic.rootTriple.normal.root.fst : ZMod p.modulus)
      (r.cubic.rootTriple.normal.root.snd : ZMod p.modulus) := by
  have hq := p.q_dvd_root
  cases hc : p.column
  · simp only [hc, rootRoutingFactorNat] at hq
    have hqv : p.q ∣ r.cubic.rootTriple.vPart :=
      (p.q_prime.dvd_mul.mp hq).resolve_left (by
        intro h
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h with h1 | h7
        · exact p.q_prime.ne_one h1
        · exact p.q_ne_seven h7)
    apply intCast_isUnit_of_not_dvd_natAbs p.q_prime p.exponent_pos
    exact prime_not_dvd_second p.q_prime
      r.cubic.rootTriple.normal.root_coordinates_natAbs_coprime.symm (by
        simpa [r.cubic.rootTriple.vPart_eq] using hqv)
  · simp only [hc, rootRoutingFactorNat] at hq
    apply intCast_isUnit_of_not_dvd_natAbs p.q_prime p.exponent_pos
    simpa [← r.cubic.rootTriple.vPart_eq] using
      (prime_not_dvd_second p.q_prime r.cubic.rootTriple.coprime_v_left.symm hq)
  · simp only [hc, rootRoutingFactorNat] at hq
    apply intCast_isUnit_of_not_dvd_natAbs p.q_prime p.exponent_pos
    simpa [← r.cubic.rootTriple.vPart_eq] using
      (prime_not_dvd_second p.q_prime r.cubic.rootTriple.coprime_v_right.symm hq)

private theorem endpoint_equation_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    AwayEndpointPrimePowerEquation p.modulus p.row (y : ZMod p.modulus)
      (z : ZMod p.modulus) := by
  have hd := p.modulus_dvd_endpoint
  cases hr : p.row
  · exact (ZMod.natCast_eq_zero_iff y p.modulus).2 (by
      simpa [hr, endpointRoutingFactorNat] using hd)
  · exact (ZMod.natCast_eq_zero_iff z p.modulus).2 (by
      simpa [hr, endpointRoutingFactorNat] using hd)
  · have hz := (ZMod.natCast_eq_zero_iff (y + z) p.modulus).2 (by
      simpa [hr, endpointRoutingFactorNat] using hd)
    simpa [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation,
      Nat.cast_add] using hz

private theorem root_equation_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    AwayRootPrimePowerEquation p.modulus p.column
      (r.cubic.rootTriple.normal.root.fst : ZMod p.modulus)
      (r.cubic.rootTriple.normal.root.snd : ZMod p.modulus) := by
  cases hc : p.column
  · have hd := modulus_dvd_rootSnd_of_sevenV p hc
    have hi : (p.modulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq] using hd
    exact intCast_zero_of_dvd hi
  · have hd := p.modulus_dvd_root
    simp only [hc, rootRoutingFactorNat] at hd
    have hi : (p.modulus : ℤ) ∣ seventhPowerSndLeftCubic
        r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd := by
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.leftPart_eq] using hd
    simpa [AwayRootPrimePowerEquation, AwayRootLocalEquation, leftCubicZMod,
      seventhPowerSndLeftCubic] using intCast_zero_of_dvd hi
  · have hd := p.modulus_dvd_root
    simp only [hc, rootRoutingFactorNat] at hd
    have hi : (p.modulus : ℤ) ∣ seventhPowerSndRightCubic
        r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd := by
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.rightPart_eq] using hd
    simpa [AwayRootPrimePowerEquation, AwayRootLocalEquation, rightCubicZMod,
      seventhPowerSndRightCubic] using intCast_zero_of_dvd hi

private theorem first_coordinate_dvd_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    (p.modulus : ℤ) ∣ routingFirstCoordinateValue r p.row p.column := by
  rcases nonempty_awayFirstCoordinateRoutingConstraints r with ⟨c⟩
  cases hr : p.row <;> cases hc : p.column
  · have hv := modulus_dvd_rootSnd_of_sevenV p hc
    have hv' : (p.modulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq] using hv
    have hroot := hv'.trans (rootSnd_dvd_fst_sub_u_seven
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
    have hend : p.modulus ∣ y := by
      simpa [hr, endpointRoutingFactorNat] using p.modulus_dvd_endpoint
    have hrow : (p.modulus : ℤ) ∣
        cyclotomicSevenFst (z : ℤ) (y : ℤ) - (z : ℤ) ^ 3 :=
      (Int.natCast_dvd_natCast.mpr hend).trans
        (leftEndpoint_dvd_fst_sub_right_cube (z : ℤ) (y : ℤ))
    rw [r.cubic.rootTriple.normal.fst_eq] at hrow
    simpa [hr, hc, routingFirstCoordinateValue] using hrow.sub hroot
  · exact (Int.natCast_dvd_natCast.mpr p.modulus_dvd_cell).trans (by
      rw [hr, hc]
      change (↑r.routing.c12 : ℤ) ∣
        (↑z : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
          leftFstCorrection r.cubic.rootTriple.normal.root.fst
            r.cubic.rootTriple.normal.root.snd
      exact c.c12_constraint)
  · exact (Int.natCast_dvd_natCast.mpr p.modulus_dvd_cell).trans (by
      rw [hr, hc]
      change (↑r.routing.c13 : ℤ) ∣
        (↑z : ℤ) ^ 3 - 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
          rightFstCorrection r.cubic.rootTriple.normal.root.fst
            r.cubic.rootTriple.normal.root.snd
      exact c.c13_constraint)
  · have hv := modulus_dvd_rootSnd_of_sevenV p hc
    have hv' : (p.modulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq] using hv
    have hroot := hv'.trans (rootSnd_dvd_fst_sub_u_seven
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
    have hend : p.modulus ∣ z := by
      simpa [hr, endpointRoutingFactorNat] using p.modulus_dvd_endpoint
    have hrow : (p.modulus : ℤ) ∣
        cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
      (Int.natCast_dvd_natCast.mpr hend).trans
        (rightEndpoint_dvd_fst_add_left_cube (z : ℤ) (y : ℤ))
    rw [r.cubic.rootTriple.normal.fst_eq] at hrow
    convert hrow.sub hroot using 1
    all_goals first | rfl | (simp only [routingFirstCoordinateValue] <;> ring)
  · exact (Int.natCast_dvd_natCast.mpr p.modulus_dvd_cell).trans (by
      rw [hr, hc]
      change (↑r.routing.c22 : ℤ) ∣
        49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
            leftFstCorrection r.cubic.rootTriple.normal.root.fst
              r.cubic.rootTriple.normal.root.snd - (↑y : ℤ) ^ 3
      exact c.c22_constraint)
  · exact (Int.natCast_dvd_natCast.mpr p.modulus_dvd_cell).trans (by
      rw [hr, hc]
      change (↑r.routing.c23 : ℤ) ∣
        (↑y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
          rightFstCorrection r.cubic.rootTriple.normal.root.fst
            r.cubic.rootTriple.normal.root.snd
      exact c.c23_constraint)
  · have hv := modulus_dvd_rootSnd_of_sevenV p hc
    have hv' : (p.modulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq] using hv
    have hroot := hv'.trans (rootSnd_dvd_fst_sub_u_seven
      r.cubic.rootTriple.normal.root.fst r.cubic.rootTriple.normal.root.snd)
    have hend : p.modulus ∣ y + z := by
      simpa [hr, endpointRoutingFactorNat] using p.modulus_dvd_endpoint
    have hrow : (p.modulus : ℤ) ∣
        cyclotomicSevenFst (z : ℤ) (y : ℤ) + (y : ℤ) ^ 3 :=
      (Int.natCast_dvd_natCast.mpr hend).trans (by
        convert endpointSum_dvd_fst_add_left_cube (z : ℤ) (y : ℤ) using 1
        all_goals first | rfl | ring_nf
        norm_num
        ring)
    rw [r.cubic.rootTriple.normal.fst_eq] at hrow
    convert hrow.sub hroot using 1
    all_goals first | rfl | (simp only [routingFirstCoordinateValue] <;> ring)
  · exact (Int.natCast_dvd_natCast.mpr p.modulus_dvd_cell).trans (by
      rw [hr, hc]
      dsimp [routingCell, routingFirstCoordinateValue]
      change (↑r.routing.c32 : ℤ) ∣
        49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
            leftFstCorrection r.cubic.rootTriple.normal.root.fst
              r.cubic.rootTriple.normal.root.snd - (↑y : ℤ) ^ 3
      exact c.c32_constraint)
  · exact (Int.natCast_dvd_natCast.mpr p.modulus_dvd_cell).trans (by
      rw [hr, hc]
      dsimp [routingCell, routingFirstCoordinateValue]
      change (↑r.routing.c33 : ℤ) ∣
        (↑y : ℤ) ^ 3 + 49 * r.cubic.rootTriple.normal.root.snd ^ 5 *
          rightFstCorrection r.cubic.rootTriple.normal.root.fst
            r.cubic.rootTriple.normal.root.snd
      exact c.c33_constraint)

private theorem first_coordinate_equation_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    AwayFirstCoordinatePrimePowerEquation p.modulus p.row p.column
      (r.cubic.rootTriple.normal.root.fst : ZMod p.modulus)
      (r.cubic.rootTriple.normal.root.snd : ZMod p.modulus)
      (y : ZMod p.modulus) (z : ZMod p.modulus) := by
  have hz := intCast_zero_of_dvd (first_coordinate_dvd_actual p)
  cases hr : p.row <;> cases hc : p.column <;>
    simp only [hr, hc, routingFirstCoordinateValue] at hz <;>
    simpa [hr, hc, AwayFirstCoordinatePrimePowerEquation,
      AwayFirstCoordinateLocalEquation, leftCorrectionZMod, rightCorrectionZMod,
      leftFstCorrection, rightFstCorrection] using hz

/-- The actual integral coordinates, reduced at the complete addressed depth. -/
def AwayNonSevenPrimeDepthPacket.toPrimePowerSolution {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    AwayRoutingPrimePowerSolution p.modulus p.row p.column where
  u := r.cubic.rootTriple.normal.root.fst
  v := r.cubic.rootTriple.normal.root.snd
  y := y
  z := z
  endpoint_nondegenerate := endpoint_nondegenerate_actual p
  endpoint_equation := endpoint_equation_actual p
  root_nondegenerate := root_nondegenerate_actual p
  root_equation := root_equation_actual p
  first_coordinate_equation := first_coordinate_equation_actual p

theorem left_normalized_root_of_primePowerSolution {M : ℕ}
    {row : EndpointRoutingRow}
    (s : AwayRoutingPrimePowerSolution M row .leftCubic) :
    leftCubicNormalizedZMod (s.u * s.v⁻¹) = 0 := by
  have huv : (s.u * s.v⁻¹) * s.v = s.u := by
    calc
      (s.u * s.v⁻¹) * s.v = s.u * (s.v * s.v⁻¹) := by ring
      _ = s.u := by rw [s.v.mul_inv_of_unit s.root_nondegenerate, mul_one]
  have hid : leftCubicZMod ((s.u * s.v⁻¹) * s.v) s.v =
      s.v ^ 3 * leftCubicNormalizedZMod (s.u * s.v⁻¹) := by
    simp [leftCubicZMod, leftCubicNormalizedZMod]
    ring
  rw [huv, s.root_equation] at hid
  apply (s.root_nondegenerate.pow 3).mul_left_cancel
  simpa using hid.symm

theorem right_normalized_root_of_primePowerSolution {M : ℕ}
    {row : EndpointRoutingRow}
    (s : AwayRoutingPrimePowerSolution M row .rightCubic) :
    rightCubicNormalizedZMod (s.u * s.v⁻¹) = 0 := by
  have huv : (s.u * s.v⁻¹) * s.v = s.u := by
    calc
      (s.u * s.v⁻¹) * s.v = s.u * (s.v * s.v⁻¹) := by ring
      _ = s.u := by rw [s.v.mul_inv_of_unit s.root_nondegenerate, mul_one]
  have hid : rightCubicZMod ((s.u * s.v⁻¹) * s.v) s.v =
      s.v ^ 3 * rightCubicNormalizedZMod (s.u * s.v⁻¹) := by
    simp [rightCubicZMod, rightCubicNormalizedZMod]
    ring
  rw [huv, s.root_equation] at hid
  apply (s.root_nondegenerate.pow 3).mul_left_cancel
  simpa using hid.symm

/-- The three explicit prime-power families; varying the row gives the nine cells. -/
inductive AwayNonSevenPrimePowerSolubilitySource {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    RootRoutingColumn → Type
  | sevenV
      (actual : AwayRoutingPrimePowerSolution p.modulus p.row .sevenV)
      (model : AwayRoutingPrimePowerSolution p.modulus p.row .sevenV) :
      AwayNonSevenPrimePowerSolubilitySource p .sevenV
  | leftCubic (t : ZMod p.modulus) (root : leftCubicNormalizedZMod t = 0)
      (correction_unit : IsUnit (leftCorrectionNormalizedZMod t))
      (actual : AwayRoutingPrimePowerSolution p.modulus p.row .leftCubic)
      (model : AwayRoutingPrimePowerSolution p.modulus p.row .leftCubic) :
      AwayNonSevenPrimePowerSolubilitySource p .leftCubic
  | rightCubic (t : ZMod p.modulus) (root : rightCubicNormalizedZMod t = 0)
      (correction_unit : IsUnit (rightCorrectionNormalizedZMod t))
      (actual : AwayRoutingPrimePowerSolution p.modulus p.row .rightCubic)
      (model : AwayRoutingPrimePowerSolution p.modulus p.row .rightCubic) :
      AwayNonSevenPrimePowerSolubilitySource p .rightCubic

theorem primePowerSolubilitySource_of_depthPacket {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwayNonSevenPrimeDepthPacket r) :
    Nonempty (AwayNonSevenPrimePowerSolubilitySource p p.column) := by
  let actual := p.toPrimePowerSolution
  cases hc : p.column with
  | sevenV =>
      have a : AwayRoutingPrimePowerSolution p.modulus p.row .sevenV := by
        simpa [hc] using actual
      rcases nonempty_primePowerSolution_sevenV p.q_prime p.exponent_pos p.row with ⟨model⟩
      exact ⟨.sevenV a model⟩
  | leftCubic =>
      have a : AwayRoutingPrimePowerSolution p.modulus p.row .leftCubic := by
        simpa [hc] using actual
      let t := a.u * a.v⁻¹
      have ht : leftCubicNormalizedZMod t = 0 :=
        left_normalized_root_of_primePowerSolution a
      have hunit := leftCorrection_isUnit_of_leftCubic_eq_zero_primePower
        p.q_prime p.q_ne_seven p.exponent_pos t ht
      rcases nonempty_primePowerSolution_leftCubic_of_root p.q_prime p.q_ne_seven
        p.exponent_pos t ht p.row with ⟨model⟩
      exact ⟨.leftCubic t ht hunit a model⟩
  | rightCubic =>
      have a : AwayRoutingPrimePowerSolution p.modulus p.row .rightCubic := by
        simpa [hc] using actual
      let t := a.u * a.v⁻¹
      have ht : rightCubicNormalizedZMod t = 0 :=
        right_normalized_root_of_primePowerSolution a
      have hunit := rightCorrection_isUnit_of_rightCubic_eq_zero_primePower
        p.q_prime p.q_ne_seven p.exponent_pos t ht
      rcases nonempty_primePowerSolution_rightCubic_of_root p.q_prime p.q_ne_seven
        p.exponent_pos t ht p.row with ⟨model⟩
      exact ⟨.rightCubic t ht hunit a model⟩

inductive PrimePowerCellAuditResult (x y z : ℕ) : Type
  | ramified (packet : RamifiedCoordinateNormalForm x y z)
  | awayPrimePowerClassified
      (routing : AwayCubicRoutingPacket x y z)
      (constraints : AwayFirstCoordinateRoutingConstraints routing)
      (classification : ∀ p : AwayNonSevenPrimeDepthPacket routing,
        Nonempty (AwayNonSevenPrimePowerSolubilitySource p p.column))

/-- Final checkpoint route: the ramified branch, or complete-depth classification
of every specialized non-seven addressed cell on the away branch. -/
theorem primePowerCellAuditResult_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (PrimePowerCellAuditResult x y z) := by
  rcases coordinateCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | ramified packet => exact ⟨.ramified packet⟩
  | away packet =>
      rcases nonempty_awayCubicRoutingPacket packet with ⟨routing⟩
      rcases nonempty_awayFirstCoordinateRoutingConstraints routing with ⟨constraints⟩
      exact ⟨.awayPrimePowerClassified routing constraints
        (fun p => primePowerSolubilitySource_of_depthPacket p)⟩

end DkMath.FLT.Seven
