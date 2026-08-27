/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenPivotDepthPacket

#print "file: DkMath.FLT.Seven.SevenPivotPrimePowerSystem"

namespace DkMath.FLT.Seven

def sevenRamifiedResidualPolynomial (u v : ℤ) : ℤ :=
  3*u^4 + 2*u^3*v - 7*u^2*v^2 - 2*u*v^3 + v^4

theorem seventhPowerFst_eq_sevenRamifiedCore_add_residual (u v : ℤ) :
    seventhPowerFst u v = u^7 + 4*v^7 -
      14*v^2*(u+v)*sevenRamifiedResidualPolynomial u v := by
  simp [seventhPowerFst, sevenRamifiedResidualPolynomial]
  ring

theorem sevenRamified_residual_dvd {m : ℕ} {u v : ℤ}
    (hv : (7 ^ m : ℤ) ∣ v) :
    (7 ^ (m + 1) : ℤ) ∣ seventhPowerFst u v - (u^7 + 4*v^7) := by
  rcases hv with ⟨c, rfl⟩
  rw [seventhPowerFst_eq_sevenRamifiedCore_add_residual]
  refine ⟨-2 * (7 ^ m * c ^ 2) * (u + 7 ^ m * c) *
    sevenRamifiedResidualPolynomial u (7 ^ m * c), ?_⟩
  rw [pow_succ]
  ring

theorem intCast_zero_of_dvd {M : ℕ} {a : ℤ} (h : (M : ℤ) ∣ a) :
    (a : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd a M).2 h

theorem seven_not_dvd_int_of_modSeven_ne_zero {a : ℤ}
    (h : (a : ZMod 7) ≠ 0) : ¬ (7 : ℤ) ∣ a := by
  exact fun hd => h ((ZMod.intCast_zmod_eq_zero_iff_dvd a 7).2 hd)

theorem intCast_isUnit_zmod_sevenPower {k : ℕ} {a : ℤ}
    (ha : ¬ (7 : ℤ) ∣ a) : IsUnit (a : ZMod (7 ^ k)) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.isCoprime_iff_nat_coprime]
  have haNat : ¬ 7 ∣ a.natAbs := by
    intro h
    exact ha (Int.natCast_dvd.mpr h)
  exact ((by norm_num : Nat.Prime 7).coprime_iff_not_dvd.mpr haNat).pow_left k

def AwaySevenPivotFirstCoordinateEquation (M : ℕ) (row : EndpointRoutingRow)
    (u v y z : ZMod M) : Prop :=
  match row with
  | .y => u^7 + 4*v^7 - z^3 = 0
  | .z => u^7 + 4*v^7 + y^3 = 0
  | .sum => u^7 + 4*v^7 + y^3 = 0

structure AwaySevenPivotPrimePowerSolution
    (k : ℕ) (row : EndpointRoutingRow) : Type where
  u : ZMod (7 ^ k)
  v : ZMod (7 ^ k)
  y : ZMod (7 ^ k)
  z : ZMod (7 ^ k)
  endpoint_nondegenerate :
    AwayEndpointPrimePowerNondegenerate (7 ^ k) row y z
  endpoint_equation : AwayEndpointPrimePowerEquation (7 ^ k) row y z
  rootLinear_isUnit : IsUnit (u + 4*v)
  seven_mul_v_eq_zero : 7*v = 0
  rootSnd_ne_zero : v ≠ 0
  first_coordinate_equation :
    AwaySevenPivotFirstCoordinateEquation (7 ^ k) row u v y z

namespace AwaySevenPivotDepthPacket

private theorem modulus_dvd_endpoint {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    p.upperModulus ∣ endpointRoutingFactorNat y z p.row := by
  have hp := p.upperModulus_dvd_pivot
  rw [p.pivot_eq] at hp
  exact hp.trans
    (routingCell_dvd_endpointRoutingFactorNat r p.row .sevenV)

private theorem endpoint_nondegenerate_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    AwayEndpointPrimePowerNondegenerate p.upperModulus p.row
      (y : ZMod p.upperModulus) (z : ZMod p.upperModulus) := by
  have h7end : 7 ∣ endpointRoutingFactorNat y z p.row :=
    p.seven_dvd_pivot.trans (by
      rw [p.pivot_eq]
      exact routingCell_dvd_endpointRoutingFactorNat r p.row .sevenV)
  cases hr : p.row
  · simp only [hr, endpointRoutingFactorNat] at h7end
    exact isUnit_zmod_primePower_of_not_dvd (by norm_num) p.exponent_pos
      (by
        intro hz
        have h : 7 = 1 :=
          Nat.eq_one_of_dvd_coprimes r.endpoint_y_z_coprime h7end hz
        norm_num at h)
  · simp only [hr, endpointRoutingFactorNat] at h7end
    exact isUnit_zmod_primePower_of_not_dvd (by norm_num) p.exponent_pos
      (by
        intro hy
        have h : 7 = 1 :=
          Nat.eq_one_of_dvd_coprimes r.endpoint_y_z_coprime hy h7end
        norm_num at h)
  · simp only [hr, endpointRoutingFactorNat] at h7end
    exact ⟨isUnit_zmod_primePower_of_not_dvd (by norm_num) p.exponent_pos
        (by
          intro hy
          have h : 7 = 1 :=
            Nat.eq_one_of_dvd_coprimes r.endpoint_y_sum_coprime hy h7end
          norm_num at h),
      isUnit_zmod_primePower_of_not_dvd (by norm_num) p.exponent_pos
        (by
          intro hz
          have h : 7 = 1 :=
            Nat.eq_one_of_dvd_coprimes r.endpoint_z_sum_coprime hz h7end
          norm_num at h)⟩

private theorem endpoint_equation_actual {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    AwayEndpointPrimePowerEquation p.upperModulus p.row
      (y : ZMod p.upperModulus) (z : ZMod p.upperModulus) := by
  have hd := p.modulus_dvd_endpoint
  cases hr : p.row
  · exact (ZMod.natCast_eq_zero_iff y p.upperModulus).2 (by
      simpa [hr, endpointRoutingFactorNat] using hd)
  · exact (ZMod.natCast_eq_zero_iff z p.upperModulus).2 (by
      simpa [hr, endpointRoutingFactorNat] using hd)
  · have hz := (ZMod.natCast_eq_zero_iff (y+z) p.upperModulus).2 (by
      simpa [hr, endpointRoutingFactorNat] using hd)
    simpa [AwayEndpointPrimePowerEquation, AwayEndpointLocalEquation,
      Nat.cast_add] using hz

private theorem core_first_coordinate_dvd {x y z : ℕ}
    {r : AwayCubicRoutingPacket x y z} (p : AwaySevenPivotDepthPacket r) :
    (p.upperModulus : ℤ) ∣ match p.row with
      | .y => r.cubic.rootTriple.normal.root.fst^7 +
          4*r.cubic.rootTriple.normal.root.snd^7 - (z : ℤ)^3
      | .z | .sum => r.cubic.rootTriple.normal.root.fst^7 +
          4*r.cubic.rootTriple.normal.root.snd^7 + (y : ℤ)^3 := by
  have hvNat := p.lowerModulus_dvd_vPart
  have hv : (p.lowerModulus : ℤ) ∣ r.cubic.rootTriple.normal.root.snd := by
    apply intCast_dvd_of_dvd_natAbs
    simpa [← r.cubic.rootTriple.vPart_eq] using hvNat
  have hres0 := sevenRamified_residual_dvd
    (u := r.cubic.rootTriple.normal.root.fst) hv
  have hk : p.exponent - 1 + 1 = p.exponent :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr p.exponent_pos.ne')
  have hres : (p.upperModulus : ℤ) ∣
      seventhPowerFst r.cubic.rootTriple.normal.root.fst
        r.cubic.rootTriple.normal.root.snd -
      (r.cubic.rootTriple.normal.root.fst^7 +
        4*r.cubic.rootTriple.normal.root.snd^7) := by
    simpa [upperModulus, lowerModulus, lowerExponent, hk] using hres0
  have hend := p.modulus_dvd_endpoint
  cases hr : p.row
  · have hy : p.upperModulus ∣ y := by
      simpa [hr, endpointRoutingFactorNat] using hend
    have hrow := (Int.natCast_dvd_natCast.mpr hy).trans
      (leftEndpoint_dvd_fst_sub_right_cube (z : ℤ) (y : ℤ))
    rw [r.cubic.rootTriple.normal.fst_eq] at hrow
    simpa [hr] using hrow.sub hres
  · have hz : p.upperModulus ∣ z := by
      simpa [hr, endpointRoutingFactorNat] using hend
    have hrow := (Int.natCast_dvd_natCast.mpr hz).trans
      (rightEndpoint_dvd_fst_add_left_cube (z : ℤ) (y : ℤ))
    rw [r.cubic.rootTriple.normal.fst_eq] at hrow
    convert hrow.sub hres using 1
    all_goals first | rfl | ring
  · have hs : p.upperModulus ∣ y+z := by
      simpa [hr, endpointRoutingFactorNat] using hend
    have hrow := (Int.natCast_dvd_natCast.mpr hs).trans (by
      convert endpointSum_dvd_fst_add_left_cube (z : ℤ) (y : ℤ) using 1
      all_goals first | rfl | ring_nf
      norm_num
      ring
    )
    rw [r.cubic.rootTriple.normal.fst_eq] at hrow
    convert hrow.sub hres using 1
    all_goals first | rfl | ring

def toPrimePowerSolution {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (p : AwaySevenPivotDepthPacket r) :
    AwaySevenPivotPrimePowerSolution p.exponent p.row where
  u := r.cubic.rootTriple.normal.root.fst
  v := r.cubic.rootTriple.normal.root.snd
  y := y
  z := z
  endpoint_nondegenerate := p.endpoint_nondegenerate_actual
  endpoint_equation := p.endpoint_equation_actual
  rootLinear_isUnit := by
    have hne :
        ((r.cubic.rootTriple.normal.root.fst +
          4*r.cubic.rootTriple.normal.root.snd : ℤ) : ZMod 7) ≠ 0 := by
      simpa [awayRootLinearModSeven] using
        r.cubic.rootTriple.normal.rootLinear_ne_zero
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat] using
      intCast_isUnit_zmod_sevenPower
        (seven_not_dvd_int_of_modSeven_ne_zero hne)
  seven_mul_v_eq_zero := by
    have hz : ((7 * r.cubic.rootTriple.normal.root.snd : ℤ) :
        ZMod p.upperModulus) = 0 := by
      apply intCast_zero_of_dvd
      apply intCast_dvd_of_dvd_natAbs
      simpa [← r.cubic.rootTriple.vPart_eq, Int.natAbs_mul] using
        p.upperModulus_dvd_seven_vPart
    change (7 * (r.cubic.rootTriple.normal.root.snd : ℤ) :
      ZMod (7 ^ p.exponent)) = 0
    norm_num [upperModulus, Int.cast_mul] at hz ⊢
    exact hz
  rootSnd_ne_zero := by
    intro h
    apply p.upperModulus_not_dvd_vPart
    rw [r.cubic.rootTriple.vPart_eq]
    exact Int.natCast_dvd.mp
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
  first_coordinate_equation := by
    have hzero := intCast_zero_of_dvd (p.core_first_coordinate_dvd)
    cases hr : p.row
    · simp only [AwaySevenPivotFirstCoordinateEquation]
      rw [hr] at hzero
      simp only at hzero
      exact_mod_cast hzero
    · simp only [AwaySevenPivotFirstCoordinateEquation]
      rw [hr] at hzero
      simp only at hzero
      exact_mod_cast hzero
    · simp only [AwaySevenPivotFirstCoordinateEquation]
      rw [hr] at hzero
      simp only at hzero
      exact_mod_cast hzero

end AwaySevenPivotDepthPacket

end DkMath.FLT.Seven
