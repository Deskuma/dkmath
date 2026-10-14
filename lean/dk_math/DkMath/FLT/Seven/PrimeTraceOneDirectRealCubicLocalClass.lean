/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTwistClass

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicLocalClass"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt

set_option linter.style.longLine false
set_option linter.style.setOption false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Coordinate annihilation at the third theta power -/

theorem theta_local_coords_zero_of_axis_cube_dvd
    (x : SevenRealCubicInt) (hx : eisensteinAxis ^ 3 ∣ x) :
    thetaConstModSeven x = 0 ∧
      thetaLinearModSeven x = 0 ∧
        thetaSquareModSeven x = 0 := by
  rcases hx with ⟨y, rfl⟩
  have haxis : thetaConstModSeven eisensteinAxis = 0 := by
    norm_num [thetaConstModSeven, eisensteinAxis]
  have haxislin : thetaLinearModSeven (eisensteinAxis ^ 3) = 0 := by
    simp only [show eisensteinAxis ^ 3 =
      eisensteinAxis * eisensteinAxis * eisensteinAxis by ring,
      thetaLinearModSeven_mul, thetaConstModSeven_mul]
    norm_num [thetaConstModSeven, thetaLinearModSeven, eisensteinAxis]
  have haxissq : thetaSquareModSeven (eisensteinAxis ^ 3) = 0 := by
    simp only [show eisensteinAxis ^ 3 =
      eisensteinAxis * eisensteinAxis * eisensteinAxis by ring,
      thetaSquareModSeven_mul, thetaLinearModSeven_mul,
      thetaConstModSeven_mul]
    norm_num [thetaConstModSeven, thetaLinearModSeven,
      thetaSquareModSeven, eisensteinAxis]
  have haxisconst : thetaConstModSeven (eisensteinAxis ^ 3) = 0 := by
    rw [thetaConstModSeven_pow, haxis]
    simp
  constructor
  · rw [thetaConstModSeven_mul, haxisconst]
    simp
  constructor
  · rw [thetaLinearModSeven_mul, haxislin, haxisconst]
    simp
  · rw [thetaSquareModSeven_mul, haxissq, haxislin, haxisconst]
    simp

theorem theta_local_coords_zero_of_axis_pow_dvd
    {n : ℕ} (hn : 3 ≤ n) (x : SevenRealCubicInt)
    (hx : eisensteinAxis ^ n ∣ x) :
    thetaConstModSeven x = 0 ∧
      thetaLinearModSeven x = 0 ∧
        thetaSquareModSeven x = 0 := by
  obtain ⟨m, hm⟩ := hx
  have hpow : eisensteinAxis ^ 3 ∣ eisensteinAxis ^ n := by
    refine ⟨eisensteinAxis ^ (n - 3), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  exact theta_local_coords_zero_of_axis_cube_dvd x
    (dvd_trans hpow ⟨m, hm⟩)

/-! ## A generic local extraction formula -/

theorem projectiveLog_eq_normalized_theta_coords_of_unit_mul_pow_seven
    (x : SevenRealCubicInt) (hx : thetaResidue x ≠ 0)
    (u : SevenRealCubicIntˣ) (root : SevenRealCubicInt)
    (hsource : x = (u : SevenRealCubicInt) * root ^ 7) :
    projectiveLog (Additive.ofMul u) =
      (thetaLinearModSeven x / thetaConstModSeven x,
        thetaSquareModSeven x / thetaConstModSeven x -
          (thetaLinearModSeven x / thetaConstModSeven x) ^ 2 / 2) := by
  have hconst : thetaConstModSeven x ≠ 0 := by
    simpa [thetaResidue] using hx
  have hroot : thetaConstModSeven root ≠ 0 := by
    intro hroot
    apply hconst
    rw [hsource, thetaConstModSeven_mul, thetaConstModSeven_pow, hroot]
    simp
  have hlinpow : thetaLinearModSeven (root ^ 7) = 0 :=
    thetaLinearModSeven_pow_seven root
  have hsqpow : thetaSquareModSeven (root ^ 7) = 0 :=
    thetaSquareModSeven_pow_seven root
  have hlin :
      thetaLinearModSeven x =
        thetaLinearModSeven (u : SevenRealCubicInt) *
          thetaConstModSeven root ^ 7 := by
    rw [hsource, thetaLinearModSeven_mul, hlinpow,
      thetaConstModSeven_pow]
    ring
  have hconsteq :
      thetaConstModSeven x =
        thetaConstModSeven (u : SevenRealCubicInt) *
          thetaConstModSeven root ^ 7 := by
    rw [hsource, thetaConstModSeven_mul, thetaConstModSeven_pow]
  have hsq :
      thetaSquareModSeven x =
        thetaSquareModSeven (u : SevenRealCubicInt) *
          thetaConstModSeven root ^ 7 := by
    rw [hsource, thetaSquareModSeven_mul, hsqpow,
      hlinpow, thetaConstModSeven_pow]
    ring
  have hunit : thetaConstModSeven (u : SevenRealCubicInt) ≠ 0 :=
    thetaConstModSeven_unit_ne_zero u
  rw [projectiveLog_apply]
  apply Prod.ext
  · unfold unitNilpotentX
    rw [hlin, hconsteq]
    field_simp [hconst, hunit, hroot]
  · unfold unitNilpotentX unitNilpotentY
    rw [hlin, hsq, hconsteq]
    field_simp [hconst, hunit, hroot]

/-! ## The canonical quotient core and its uniqueness -/

def directOrbitQuotientCoreCanonical
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) (d : SevenRealCubicInt) :
    SevenRealCubicInt :=
    thetaSevenUnit * p.rho ^ 6 +
      3 * thetaSevenUnit * eisensteinAxis * d * p.rho ^ 5 +
      5 * thetaSevenUnit * eisensteinAxis ^ 2 * d ^ 2 * p.rho ^ 4 +
      5 * thetaSevenUnit * eisensteinAxis ^ 3 * d ^ 3 * p.rho ^ 3 +
      3 * thetaSevenUnit * eisensteinAxis ^ 4 * d ^ 4 * p.rho ^ 2 +
      thetaSevenUnit * eisensteinAxis ^ 5 * d ^ 5 * p.rho +
      eisensteinAxis ^ 3 * d ^ 6

theorem directOrbitQuotient_eq_axis_cube_mul_canonical
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) (d : SevenRealCubicInt)
    (hd : rotateEquiv p.rho - p.rho = eisensteinAxis * d) :
    directOrbitQuotient p =
      eisensteinAxis ^ 3 * directOrbitQuotientCoreCanonical p d := by
  rw [directOrbitQuotient, show rotateEquiv p.rho = p.rho + eisensteinAxis * d by
    rw [sub_eq_iff_eq_add] at hd; simpa [add_comm] using hd,
    seventhQuotient_add_gap,
    show (21 : SevenRealCubicInt) = 3 * 7 by norm_num,
    show (35 : SevenRealCubicInt) = 5 * 7 by norm_num,
    seven_eq_eisensteinAxis_cube_mul_unit]
  unfold directOrbitQuotientCoreCanonical
  ring

theorem directOrbitQuotientCore_unique
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r)
    (q₁ q₂ : SevenRealCubicInt)
    (h₁ : directOrbitQuotient p = eisensteinAxis ^ 3 * q₁)
    (h₂ : directOrbitQuotient p = eisensteinAxis ^ 3 * q₂) :
    q₁ = q₂ := by
  apply mul_left_cancel₀ (pow_ne_zero 3 eisensteinAxis_prime.ne_zero)
  exact h₁.symm.trans h₂

theorem directOrbit_root_theta_nilpotent_coords_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    thetaLinearModSeven p.rho = 0 ∧
      thetaSquareModSeven p.rho = 0 := by
  have hgap := theta_local_coords_zero_of_axis_pow_dvd (n := 32)
    (by norm_num : 3 ≤ 32) (directOrbitGap p)
    (directOrbit_gap_axis_pow32_dvd p)
  have hlin_gap := hgap.2.1
  have hsq_gap := hgap.2.2
  have hlin : thetaLinearModSeven p.rho = 0 := by
    change thetaLinearModSeven (rotateEquiv p.rho - p.rho) = 0 at hlin_gap
    simp only [thetaLinearModSeven, rotateEquiv, rotateHom, Int.reduceNeg, neg_mul,
      RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, OneHom.toFun_eq_coe, OneHom.coe_mk,
      RingHom.coe_mk, MonoidHom.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, snd_sub, thd_sub,
      add_sub_cancel_right, Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul,
      Int.cast_ofNat] at hlin_gap
    have hlincoord :
        (p.rho.snd : ZMod 7) + 6 * (p.rho.thd : ZMod 7) = 0 := by
      have hseven : (7 : ZMod 7) = 0 := by decide
      linear_combination (5 : ZMod 7) * hlin_gap +
        -2 * (p.rho.snd : ZMod 7) * hseven +
        3 * (p.rho.thd : ZMod 7) * hseven
    simpa [thetaLinearModSeven] using hlincoord
  have hsq : thetaSquareModSeven p.rho = 0 := by
    change thetaSquareModSeven (rotateEquiv p.rho - p.rho) = 0 at hsq_gap
    simp only [thetaSquareModSeven, rotateEquiv, rotateHom, Int.reduceNeg, neg_mul,
      RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, OneHom.toFun_eq_coe, OneHom.coe_mk,
      RingHom.coe_mk, MonoidHom.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, thd_sub,
      add_sub_cancel_right] at hsq_gap
    have hsnd : (p.rho.snd : ZMod 7) = 0 := by
      change (p.rho.snd : ZMod 7) = 0 at hsq_gap
      exact hsq_gap
    have hlincoord :
        (p.rho.snd : ZMod 7) + 6 * (p.rho.thd : ZMod 7) = 0 := by
      simpa [thetaLinearModSeven] using hlin
    have hsqcoord : (p.rho.thd : ZMod 7) = 0 := by
      have hseven : (7 : ZMod 7) = 0 := by decide
      linear_combination 6 * hlincoord - 6 * hsnd +
        -5 * (p.rho.thd : ZMod 7) * hseven
    simpa [thetaSquareModSeven] using hsqcoord
  exact ⟨hlin, hsq⟩

theorem directOrbitPowerSplit_quotientCore_eq_canonical
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ∃ d : SevenRealCubicInt,
      s.quotientCore = directOrbitQuotientCoreCanonical p d := by
  rcases directOrbit_gap_axis_pow32_dvd p with ⟨t, ht⟩
  let d := eisensteinAxis ^ 31 * t
  have hd : directOrbitGap p = eisensteinAxis * d := by
    dsimp [d]
    rw [ht]
    ring
  have hcanonical := directOrbitQuotient_eq_axis_cube_mul_canonical p d hd
  refine ⟨d, ?_⟩
  exact directOrbitQuotientCore_unique p s.quotientCore
    (directOrbitQuotientCoreCanonical p d) s.quotient_eq hcanonical

theorem directOrbitPowerSplit_quotientCore_eq_canonical_axis3
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ∃ d : SevenRealCubicInt,
      eisensteinAxis ^ 3 ∣ d ∧
        s.quotientCore = directOrbitQuotientCoreCanonical p d := by
  rcases directOrbit_gap_axis_pow32_dvd p with ⟨t, ht⟩
  let d := eisensteinAxis ^ 31 * t
  have hd : eisensteinAxis ^ 3 ∣ d := by
    refine ⟨eisensteinAxis ^ 28 * t, ?_⟩
    dsimp [d]
    calc
      eisensteinAxis ^ 31 * t = eisensteinAxis ^ (3 + 28) * t := by norm_num
      _ = (eisensteinAxis ^ 3 * eisensteinAxis ^ 28) * t := by
        rw [pow_add]
      _ = eisensteinAxis ^ 3 * (eisensteinAxis ^ 28 * t) := by ring
  have hgap : directOrbitGap p = eisensteinAxis * d := by
    dsimp [d]
    rw [ht]
    ring
  have hcanonical := directOrbitQuotient_eq_axis_cube_mul_canonical p d hgap
  refine ⟨d, hd, ?_⟩
  exact directOrbitQuotientCore_unique p s.quotientCore
    (directOrbitQuotientCoreCanonical p d) s.quotient_eq hcanonical

theorem directOrbitQuotientCoreCanonical_theta_coords
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) (d : SevenRealCubicInt)
    (hd : eisensteinAxis ^ 3 ∣ d) :
    thetaConstModSeven
        (directOrbitQuotientCoreCanonical p d) =
        thetaConstModSeven thetaSevenUnit *
          thetaResidue p.rho ^ 6 ∧
      thetaLinearModSeven
          (directOrbitQuotientCoreCanonical p d) =
        thetaLinearModSeven thetaSevenUnit *
          thetaResidue p.rho ^ 6 ∧
      thetaSquareModSeven
          (directOrbitQuotientCoreCanonical p d) =
        thetaSquareModSeven thetaSevenUnit *
          thetaResidue p.rho ^ 6 := by
  rcases hd with ⟨e, he⟩
  have h₁ : eisensteinAxis ^ 3 ∣
      3 * thetaSevenUnit * eisensteinAxis * d * p.rho ^ 5 := by
    refine ⟨3 * thetaSevenUnit * eisensteinAxis * e * p.rho ^ 5, ?_⟩
    rw [he]
    ring
  have h₂ : eisensteinAxis ^ 3 ∣
      5 * thetaSevenUnit * eisensteinAxis ^ 2 * d ^ 2 * p.rho ^ 4 := by
    refine ⟨5 * thetaSevenUnit * eisensteinAxis ^ 5 * e ^ 2 * p.rho ^ 4, ?_⟩
    rw [he]
    ring
  have h₃ : eisensteinAxis ^ 3 ∣
      5 * thetaSevenUnit * eisensteinAxis ^ 3 * d ^ 3 * p.rho ^ 3 := by
    refine ⟨5 * thetaSevenUnit * eisensteinAxis ^ 9 * e ^ 3 * p.rho ^ 3, ?_⟩
    rw [he]
    ring
  have h₄ : eisensteinAxis ^ 3 ∣
      3 * thetaSevenUnit * eisensteinAxis ^ 4 * d ^ 4 * p.rho ^ 2 := by
    refine ⟨3 * thetaSevenUnit * eisensteinAxis ^ 13 * e ^ 4 * p.rho ^ 2, ?_⟩
    rw [he]
    ring
  have h₅ : eisensteinAxis ^ 3 ∣
      thetaSevenUnit * eisensteinAxis ^ 5 * d ^ 5 * p.rho := by
    refine ⟨thetaSevenUnit * eisensteinAxis ^ 17 * e ^ 5 * p.rho, ?_⟩
    rw [he]
    ring
  have h₆ : eisensteinAxis ^ 3 ∣ eisensteinAxis ^ 3 * d ^ 6 := by
    exact dvd_mul_right _ _
  have hrem : eisensteinAxis ^ 3 ∣
      directOrbitQuotientCoreCanonical p d - thetaSevenUnit * p.rho ^ 6 := by
    rw [show directOrbitQuotientCoreCanonical p d -
        thetaSevenUnit * p.rho ^ 6 =
        (3 * thetaSevenUnit * eisensteinAxis * d * p.rho ^ 5) +
        (5 * thetaSevenUnit * eisensteinAxis ^ 2 * d ^ 2 * p.rho ^ 4) +
        (5 * thetaSevenUnit * eisensteinAxis ^ 3 * d ^ 3 * p.rho ^ 3) +
        (3 * thetaSevenUnit * eisensteinAxis ^ 4 * d ^ 4 * p.rho ^ 2) +
        (thetaSevenUnit * eisensteinAxis ^ 5 * d ^ 5 * p.rho) +
        eisensteinAxis ^ 3 * d ^ 6 by
          unfold directOrbitQuotientCoreCanonical
          ring]
    exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_add h₁ h₂) h₃) h₄) h₅) h₆
  have hz := theta_local_coords_zero_of_axis_cube_dvd _ hrem
  have hroot := directOrbit_root_theta_nilpotent_coords_zero p
  have hpow :
      thetaLinearModSeven (p.rho ^ 6) = 0 ∧
        thetaSquareModSeven (p.rho ^ 6) = 0 := by
    induction 6 with
    | zero => simp
    | succ n ih =>
      constructor
      · rw [pow_succ, thetaLinearModSeven_mul]
        simp [ih, hroot]
      · rw [pow_succ, thetaSquareModSeven_mul]
        simp [ih, hroot]
  have hfirstConst :
      thetaConstModSeven (thetaSevenUnit * p.rho ^ 6) =
        thetaConstModSeven thetaSevenUnit * thetaResidue p.rho ^ 6 := by
    rw [thetaConstModSeven_mul, thetaConstModSeven_pow]
    rfl
  have hfirstLinear :
      thetaLinearModSeven (thetaSevenUnit * p.rho ^ 6) =
        thetaLinearModSeven thetaSevenUnit * thetaResidue p.rho ^ 6 := by
    rw [thetaLinearModSeven_mul, hpow.1, thetaConstModSeven_pow]
    simp [thetaResidue]
  have hfirstSquare :
      thetaSquareModSeven (thetaSevenUnit * p.rho ^ 6) =
        thetaSquareModSeven thetaSevenUnit * thetaResidue p.rho ^ 6 := by
    rw [thetaSquareModSeven_mul, hpow.2, hpow.1,
      thetaConstModSeven_pow]
    simp [thetaResidue]
  constructor
  · have hz' :
        thetaConstModSeven (directOrbitQuotientCoreCanonical p d) -
          thetaConstModSeven (thetaSevenUnit * p.rho ^ 6) = 0 := by
      convert hz.1 using 1; simp [thetaConstModSeven]; ring
    exact (sub_eq_zero.mp hz').trans hfirstConst
  constructor
  · have hz' :
        thetaLinearModSeven (directOrbitQuotientCoreCanonical p d) -
          thetaLinearModSeven (thetaSevenUnit * p.rho ^ 6) = 0 := by
      convert hz.2.1 using 1; simp [thetaLinearModSeven]; ring
    exact (sub_eq_zero.mp hz').trans hfirstLinear
  · have hz' :
        thetaSquareModSeven (directOrbitQuotientCoreCanonical p d) -
          thetaSquareModSeven (thetaSevenUnit * p.rho ^ 6) = 0 := by
      convert hz.2.2 using 1; simp [thetaSquareModSeven]
    exact (sub_eq_zero.mp hz').trans hfirstSquare

theorem directOrbitPowerSplit_quotientCore_theta_coords
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    thetaConstModSeven s.quotientCore =
        thetaConstModSeven thetaSevenUnit * thetaResidue p.rho ^ 6 ∧
      thetaLinearModSeven s.quotientCore =
        thetaLinearModSeven thetaSevenUnit * thetaResidue p.rho ^ 6 ∧
      thetaSquareModSeven s.quotientCore =
        thetaSquareModSeven thetaSevenUnit * thetaResidue p.rho ^ 6 := by
  rcases directOrbitPowerSplit_quotientCore_eq_canonical_axis3 s with
    ⟨d, hd, hcore⟩
  rw [hcore]
  exact directOrbitQuotientCoreCanonical_theta_coords p d hd

theorem thetaSevenUnit_projectiveLog :
    projectiveLog (Additive.ofMul thetaSevenUnit_isUnit.unit) = (5, 1) := by
  have hinv2 : (2 : ZMod 7)⁻¹ = 4 := by
    exact ZMod.inv_eq_of_mul_eq_one 7 2 4 (by decide)
  have hinv29 : (29 : ZMod 7)⁻¹ = 1 := by
    exact ZMod.inv_eq_of_mul_eq_one 7 29 1 (by decide)
  rw [projectiveLog_apply]
  simp only [unitNilpotentX, unitNilpotentY]
  rw [thetaSevenUnit_isUnit.unit_spec]
  norm_num [thetaSevenUnit, eisensteinAxisUnitInv,
    eisensteinAxisUnit, eisensteinAxis, alpha, mul, pow_two,
    thetaConstModSeven, thetaLinearModSeven, thetaSquareModSeven,
    hinv2, hinv29, div_eq_mul_inv]
  decide

theorem directOrbitPowerSplit_quotientUnit_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    projectiveLog (Additive.ofMul s.quotientUnit) = (5, 1) := by
  have hres : thetaResidue s.quotientCore ≠ 0 := by
    intro hz
    apply s.quotientCore_not_axis_dvd
    exact (eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero _).mpr hz
  have hlog := projectiveLog_eq_normalized_theta_coords_of_unit_mul_pow_seven
    s.quotientCore hres s.quotientUnit s.quotientRoot s.quotientCore_eq
  have hcoords := directOrbitPowerSplit_quotientCore_theta_coords s
  have hA : thetaResidue p.rho ≠ 0 := p.thetaResidue_ne_zero
  have hU : thetaConstModSeven thetaSevenUnit ≠ 0 := by
    exact thetaConstModSeven_unit_ne_zero thetaSevenUnit_isUnit.unit
  rw [projectiveLog_apply]
  rw [projectiveLog_apply] at hlog
  rw [hcoords.1, hcoords.2.1, hcoords.2.2] at hlog
  rw [hlog]
  have htheta := thetaSevenUnit_projectiveLog
  rw [projectiveLog_apply] at htheta
  simp only [unitNilpotentX, unitNilpotentY,
    thetaSevenUnit_isUnit.unit_spec] at htheta
  calc
    (thetaSevenUnit.thetaLinearModSeven * thetaResidue p.rho ^ 6 /
        (thetaSevenUnit.thetaConstModSeven * thetaResidue p.rho ^ 6),
      thetaSevenUnit.thetaSquareModSeven * thetaResidue p.rho ^ 6 /
          (thetaSevenUnit.thetaConstModSeven * thetaResidue p.rho ^ 6) -
        (thetaSevenUnit.thetaLinearModSeven * thetaResidue p.rho ^ 6 /
            (thetaSevenUnit.thetaConstModSeven * thetaResidue p.rho ^ 6)) ^ 2 /
          2) =
        (thetaLinearModSeven thetaSevenUnit /
          thetaConstModSeven thetaSevenUnit,
          thetaSquareModSeven thetaSevenUnit /
            thetaConstModSeven thetaSevenUnit -
              (thetaLinearModSeven thetaSevenUnit /
                thetaConstModSeven thetaSevenUnit) ^ 2 / 2) := by
      apply Prod.ext
      · field_simp [hA, hU]
      · field_simp [hA, hU]
    _ = (5, 1) := htheta

theorem directOrbitPowerSplit_gapUnit_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    projectiveLog (Additive.ofMul s.gapUnit) = (2, 4) := by
  have hgapConst : thetaConstModSeven s.gapCore ≠ 0 := by
    intro hz
    apply s.gapCore_not_axis_dvd
    exact (eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero _).mpr hz
  have hquotConst : thetaConstModSeven s.quotientCore ≠ 0 := by
    intro hz
    apply s.quotientCore_not_axis_dvd
    exact (eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero _).mpr hz
  have hprodRes : thetaResidue (s.gapCore * s.quotientCore) ≠ 0 := by
    change thetaConstModSeven (s.gapCore * s.quotientCore) ≠ 0
    rw [thetaConstModSeven_mul]
    exact mul_ne_zero hgapConst hquotConst
  have hsource₁ : s.gapCore * s.quotientCore =
      (s.gapUnit * s.quotientUnit : SevenRealCubicInt) *
        (s.gapRoot * s.quotientRoot) ^ 7 := by
    rw [s.gapCore_eq, s.quotientCore_eq]
    ring
  have hlog₁ := projectiveLog_eq_normalized_theta_coords_of_unit_mul_pow_seven
    (s.gapCore * s.quotientCore) hprodRes
      (s.gapUnit * s.quotientUnit) (s.gapRoot * s.quotientRoot) hsource₁
  let w : SevenRealCubicInt :=
    thetaSevenUnit ^ (1 + 2 * s.gapSplit.k) *
      (s.gapSplit.a : SevenRealCubicInt) ^ 2
  have hsource₂ : s.gapCore * s.quotientCore =
      (orbitUnit01Unit : SevenRealCubicInt) * w ^ 7 := by
    simpa [w, orbitUnit01Unit_val] using s.cores_product_eq
  have hlog₂ := projectiveLog_eq_normalized_theta_coords_of_unit_mul_pow_seven
    (s.gapCore * s.quotientCore) hprodRes orbitUnit01Unit w hsource₂
  have hsum :
      projectiveLog (Additive.ofMul s.gapUnit) +
          projectiveLog (Additive.ofMul s.quotientUnit) =
        projectiveLog (Additive.ofMul orbitUnit01Unit) := by
    have hsum0 := hlog₁.trans hlog₂.symm
    rw [ofMul_mul, map_add] at hsum0
    exact hsum0
  have hsum' := hsum
  rw [directOrbitPowerSplit_quotientUnit_projectiveLog s,
    orbitUnit01_projectiveLog] at hsum'
  exact (eq_sub_of_add_eq hsum').trans (by decide)

theorem directOrbit_twistedCoeff_projectiveLog_unconditional
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    projectiveLog (Additive.ofMul (directOrbitTwistedCoeff0 s)) = (2, 4) ∧
      projectiveLog (Additive.ofMul (directOrbitTwistedCoeff1 s)) = (2, 2) ∧
      projectiveLog (Additive.ofMul (directOrbitTwistedCoeff2 s)) = (2, 5) := by
  have hgap := directOrbitPowerSplit_gapUnit_projectiveLog s
  exact ⟨directOrbit_twistedCoeff0_projectiveLog_of_gapClass s hgap,
    directOrbit_twistedCoeff1_projectiveLog_of_gapClass s hgap,
    directOrbit_twistedCoeff2_projectiveLog_of_gapClass s hgap⟩

theorem directOrbit_twistedCoeff_ratio_classes_unconditional
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff1 s * (directOrbitTwistedCoeff0 s)⁻¹)) = (0, 5) ∧
    projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff2 s * (directOrbitTwistedCoeff1 s)⁻¹)) = (0, 3) ∧
    projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff0 s * (directOrbitTwistedCoeff2 s)⁻¹)) = (0, 6) := by
  exact directOrbit_twistedCoeff_ratio_classes_of_gapClass s
    (directOrbitPowerSplit_gapUnit_projectiveLog s)

end
end DkMath.FLT.Seven
