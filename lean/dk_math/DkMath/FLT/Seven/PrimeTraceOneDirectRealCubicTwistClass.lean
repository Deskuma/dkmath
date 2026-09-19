/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSuccessorAudit

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTwistClass"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt

set_option linter.style.longLine false
set_option linter.style.setOption false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## The rotation action on the projective unit class -/

def directOrbitRotateProjectiveLog :
    (ZMod 7 × ZMod 7) →+ (ZMod 7 × ZMod 7) :=
  { toFun := fun c => (4 * c.1, c.1 + 2 * c.2)
    map_zero' := by ext <;> simp
    map_add' := by
      intro a b
      ext <;> simp <;> ring }

@[simp] theorem directOrbitRotateProjectiveLog_apply
    (c : ZMod 7 × ZMod 7) :
    directOrbitRotateProjectiveLog c = (4 * c.1, c.1 + 2 * c.2) := rfl

theorem directOrbitRotateProjectiveLog_order_three
    (c : ZMod 7 × ZMod 7) :
    directOrbitRotateProjectiveLog
        (directOrbitRotateProjectiveLog
          (directOrbitRotateProjectiveLog c)) = c := by
  revert c
  decide

theorem directOrbitRotateProjectiveLog_norm_zero
    (c : ZMod 7 × ZMod 7) :
    c + directOrbitRotateProjectiveLog c +
        directOrbitRotateProjectiveLog (directOrbitRotateProjectiveLog c) = 0 := by
  revert c
  decide

theorem directOrbit_projectiveLog_rotate
    (u : SevenRealCubicIntˣ) :
    projectiveLog (Additive.ofMul (directOrbitRotateUnit u)) =
      directOrbitRotateProjectiveLog
        (projectiveLog (Additive.ofMul u)) := by
  have hlinear (x : SevenRealCubicInt) :
      thetaLinearModSeven (rotateEquiv x) =
        4 * thetaLinearModSeven x := by
    simp [thetaLinearModSeven, rotateEquiv, rotateHom]
    have h7 : (7 : ZMod 7) = 0 := by decide
    linear_combination -(3 * (x.thd : ZMod 7)) * h7
  have hsquare (x : SevenRealCubicInt) :
      thetaSquareModSeven (rotateEquiv x) =
        thetaLinearModSeven x + 2 * thetaSquareModSeven x := by
    simp [thetaSquareModSeven, thetaLinearModSeven, rotateEquiv, rotateHom]
    have h7 : (7 : ZMod 7) = 0 := by decide
    linear_combination -(x.thd : ZMod 7) * h7
  have hx : unitNilpotentX (directOrbitRotateUnit u) =
      4 * unitNilpotentX u := by
    unfold unitNilpotentX
    rw [directOrbitRotateUnit_val, hlinear]
    change _ / thetaResidue (rotateEquiv (u : SevenRealCubicInt)) = _
    rw [thetaResidue_rotateEquiv]
    dsimp [thetaResidue]
    ring
  have hy : unitNilpotentY (directOrbitRotateUnit u) =
      unitNilpotentX u + 2 * unitNilpotentY u := by
    unfold unitNilpotentX unitNilpotentY
    rw [directOrbitRotateUnit_val, hsquare]
    change _ / thetaResidue (rotateEquiv (u : SevenRealCubicInt)) = _
    rw [thetaResidue_rotateEquiv]
    dsimp [thetaResidue]
    ring
  rw [projectiveLog_apply, projectiveLog_apply, hx, hy]
  apply Prod.ext
  · rfl
  · change _ = unitNilpotentX u +
      2 * (unitNilpotentY u - unitNilpotentX u ^ 2 / 2)
    have hi : (2 : ZMod 7)⁻¹ = 4 :=
      ZMod.inv_eq_of_mul_eq_one 7 2 4 (by decide)
    simp only [div_eq_mul_inv, hi]
    have h7 : (7 : ZMod 7) = 0 := by decide
    linear_combination -(8 * unitNilpotentX u ^ 2) * h7

/-! ## Fixed classes and the exponent -/

theorem directOrbit_pairAxisUnitOne_projectiveLog :
    projectiveLog (Additive.ofMul directOrbitPairAxisUnitOne) = (2, 5) := by
  unfold directOrbitPairAxisUnitOne
  exact projectiveLog_alphaAddOne

theorem directOrbit_twistedExponent_mod_seven (k : ℕ) :
    ((32 + 42 * k : ℕ) : ZMod 7) = 4 := by
  norm_num [Nat.cast_add, Nat.cast_mul,
    show (42 : ZMod 7) = 0 by decide]
  rw [show (42 : ZMod 7) = 0 by decide, zero_mul]
  decide

theorem directOrbit_projectiveLog_pow
    (u : SevenRealCubicIntˣ) (n : ℕ) :
    projectiveLog (Additive.ofMul (u ^ n)) =
      n • projectiveLog (Additive.ofMul u) := by
  rw [ofMul_pow, map_nsmul]

/-! ## Coefficient-class formulas, conditional on the missing local bridge -/

theorem directOrbit_twistedCoeff0_projectiveLog_of_gapClass
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p)
    (hgap : projectiveLog (Additive.ofMul s.gapUnit) = (2, 4)) :
    projectiveLog (Additive.ofMul (directOrbitTwistedCoeff0 s)) = (2, 4) := by
  simpa only [directOrbitTwistedCoeff0] using hgap

theorem directOrbit_twistedCoeff1_projectiveLog_of_gapClass
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p)
    (hgap : projectiveLog (Additive.ofMul s.gapUnit) = (2, 4)) :
    projectiveLog (Additive.ofMul (directOrbitTwistedCoeff1 s)) = (2, 2) := by
  rw [directOrbitTwistedCoeff1, ofMul_mul, map_add,
    directOrbit_projectiveLog_pow, nsmul_eq_mul,
    directOrbit_pairAxisUnitOne_projectiveLog, directOrbit_projectiveLog_rotate,
    directOrbitRotateProjectiveLog_apply, hgap]
  norm_num [Nat.cast_add, Nat.cast_mul,
    show (42 : ZMod 7) = 0 by decide]
  rw [show (42 : ZMod 7 × ZMod 7) = 0 by decide, zero_mul]
  decide

theorem directOrbit_twistedCoeff2_projectiveLog_of_gapClass
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p)
    (hgap : projectiveLog (Additive.ofMul s.gapUnit) = (2, 4)) :
    projectiveLog (Additive.ofMul (directOrbitTwistedCoeff2 s)) = (2, 5) := by
  rw [directOrbitTwistedCoeff2, ofMul_mul, map_add,
    directOrbit_projectiveLog_pow, nsmul_eq_mul,
    directOrbit_pairAxisUnitOne_projectiveLog,
    directOrbit_projectiveLog_rotate,
    directOrbitRotateProjectiveLog_apply]
  rw [directOrbit_twistedCoeff1_projectiveLog_of_gapClass s hgap]
  norm_num [Nat.cast_add, Nat.cast_mul,
    show (42 : ZMod 7) = 0 by decide]
  rw [show (42 : ZMod 7 × ZMod 7) = 0 by decide, zero_mul]
  decide

theorem directOrbit_twistedCoeff_ratio_classes_of_gapClass
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p)
    (hgap : projectiveLog (Additive.ofMul s.gapUnit) = (2, 4)) :
    projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff1 s * (directOrbitTwistedCoeff0 s)⁻¹)) = (0, 5) ∧
    projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff2 s * (directOrbitTwistedCoeff1 s)⁻¹)) = (0, 3) ∧
    projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff0 s * (directOrbitTwistedCoeff2 s)⁻¹)) = (0, 6) := by
  have h0 := directOrbit_twistedCoeff0_projectiveLog_of_gapClass s hgap
  have h1 := directOrbit_twistedCoeff1_projectiveLog_of_gapClass s hgap
  have h2 := directOrbit_twistedCoeff2_projectiveLog_of_gapClass s hgap
  constructor
  · rw [ofMul_mul, map_add, ofMul_inv, map_neg, h1, h0]
    decide
  constructor
  · rw [ofMul_mul, map_add, ofMul_inv, map_neg, h2, h1]
    decide
  · rw [ofMul_mul, map_add, ofMul_inv, map_neg, h0, h2]
    decide

theorem directOrbit_twistedCoeff_ratios_not_seventhPower_of_gapClass
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p)
    (hgap : projectiveLog (Additive.ofMul s.gapUnit) = (2, 4)) :
    (¬ ∃ v : SevenRealCubicIntˣ,
        directOrbitTwistedCoeff1 s = directOrbitTwistedCoeff0 s * v ^ 7) ∧
    (¬ ∃ v : SevenRealCubicIntˣ,
        directOrbitTwistedCoeff2 s = directOrbitTwistedCoeff1 s * v ^ 7) ∧
    (¬ ∃ v : SevenRealCubicIntˣ,
        directOrbitTwistedCoeff0 s = directOrbitTwistedCoeff2 s * v ^ 7) := by
  have hr := directOrbit_twistedCoeff_ratio_classes_of_gapClass s hgap
  constructor
  · rintro ⟨v, hv⟩
    have hlog := projectiveLog_pow_seven v
    have hzero : projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff1 s * (directOrbitTwistedCoeff0 s)⁻¹)) = 0 := by
      rw [hv, ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_mul, map_add,
        hlog]
      simp
    rw [hr.1] at hzero
    have hne := congrArg Prod.snd hzero
    exact (by decide : (5 : ZMod 7) ≠ 0) hne
  constructor
  · rintro ⟨v, hv⟩
    have hlog := projectiveLog_pow_seven v
    have hzero : projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff2 s * (directOrbitTwistedCoeff1 s)⁻¹)) = 0 := by
      rw [hv, ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_mul, map_add,
        hlog]
      simp
    rw [hr.2.1] at hzero
    have hne := congrArg Prod.snd hzero
    exact (by decide : (3 : ZMod 7) ≠ 0) hne
  · rintro ⟨v, hv⟩
    have hlog := projectiveLog_pow_seven v
    have hzero : projectiveLog (Additive.ofMul
        (directOrbitTwistedCoeff0 s * (directOrbitTwistedCoeff2 s)⁻¹)) = 0 := by
      rw [hv, ofMul_mul, map_add, ofMul_inv, map_neg, ofMul_mul, map_add,
        hlog]
      simp
    rw [hr.2.2] at hzero
    have hne := congrArg Prod.snd hzero
    exact (by decide : (6 : ZMod 7) ≠ 0) hne

/-! ## The weighted two-term remainder -/

theorem weighted_seventh_difference_remainder
    (u v : SevenRealCubicIntˣ) (x y : SevenRealCubicInt) :
    (u : SevenRealCubicInt) * x ^ 7 - (v : SevenRealCubicInt) * y ^ 7 =
      (u : SevenRealCubicInt) * (x ^ 7 - y ^ 7) +
        ((u : SevenRealCubicInt) - (v : SevenRealCubicInt)) * y ^ 7 := by
  ring

/-! ## Transport data inherited by the current constructor -/

structure DirectRealCubicTransportedTwistedState
    extends DirectRealCubicTwistedSeventhState where
  k : ℕ
  exponent : ℕ
  exponent_eq : exponent = 32 + 42 * k
  coeff1_transport :
    coeff1 = directOrbitPairAxisUnitOne ^ exponent *
      directOrbitRotateUnit coeff0
  coeff2_transport :
    coeff2 = directOrbitPairAxisUnitOne ^ exponent *
      directOrbitRotateUnit coeff1
  root_not_axis_dvd : ¬eisensteinAxis ∣ root

theorem directOrbit_gapRoot_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (s : DirectOrbitPowerSplitPacket p) :
    ¬eisensteinAxis ∣ s.gapRoot := by
  intro hroot
  apply s.gapCore_not_axis_dvd
  rw [s.gapCore_eq]
  exact dvd_mul_of_dvd_right
    (hroot.trans (dvd_pow_self s.gapRoot (by decide : 7 ≠ 0))) _

noncomputable def directOrbitTransportedTwistedState
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r} :
    DirectRealCubicTransportedTwistedState := by
  let s := directOrbitPowerSplit p
  let base := directOrbitTwistedState p
  let e := 32 + 42 * s.gapSplit.k
  exact {
    toDirectRealCubicTwistedSeventhState := base
    k := s.gapSplit.k
    exponent := e
    exponent_eq := rfl
    coeff1_transport := by
      change directOrbitTwistedCoeff1 s = _
      rfl
    coeff2_transport := by
      change directOrbitTwistedCoeff2 s = _
      rfl
    root_not_axis_dvd := by
      exact directOrbit_gapRoot_not_axis_dvd s }

end
end DkMath.FLT.Seven
