/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareRefinement

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 200000

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem squareTwist_realEval_injective : Function.Injective realEval := by
  intro a b hab
  have hfield :
      algebraMap (𝓞 SevenRealCubic.Field) SevenRealCubic.Field
          (SevenRealCubic.modelToRingOfIntegers a) =
        algebraMap (𝓞 SevenRealCubic.Field) SevenRealCubic.Field
          (SevenRealCubic.modelToRingOfIntegers b) := by
    apply realEmbedding.injective
    exact hab
  apply SevenRealCubic.modelToRingOfIntegers_injective
  exact NumberField.RingOfIntegers.coe_injective hfield

/-! ## The square-refined twisted coefficients -/

def directOrbitSquareTwistCoeff0
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  directOrbitTwistedCoeff0 t.powerSplit * t.gapSquareUnit ^ 7

def directOrbitSquareTwistCoeff1
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  directOrbitTwistedCoeff1 t.powerSplit *
    (directOrbitRotateUnit t.gapSquareUnit) ^ 7

def directOrbitSquareTwistCoeff2
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  directOrbitTwistedCoeff2 t.powerSplit *
    (directOrbitRotateUnit (directOrbitRotateUnit t.gapSquareUnit)) ^ 7

/-! ## Exact square-weighted cyclic identity -/

theorem directOrbit_squareTwist_twisted_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
          (t.gapSquareRoot ^ 7) ^ 2 +
        (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) *
          ((rotateEquiv t.gapSquareRoot) ^ 7) ^ 2 +
        (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) *
          ((rotateEquiv (rotateEquiv t.gapSquareRoot)) ^ 7) ^ 2 = 0 := by
  let s := t.powerSplit
  have h := directOrbit_twisted_eq s
  rw [t.gapRoot_eq] at h
  simp only [map_mul, map_pow] at h
  dsimp [s] at h
  simp only [directOrbitSquareTwistCoeff0, directOrbitSquareTwistCoeff1,
    directOrbitSquareTwistCoeff2, Units.val_mul, Units.val_pow_eq_pow_val]
  ring_nf at h ⊢
  exact h

/-! ## Even exponent and coefficient transport -/

theorem directOrbit_squareTwist_exponent_even
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Even (32 + 42 * t.powerSplit.gapSplit.k) := by
  refine ⟨16 + 21 * t.powerSplit.gapSplit.k, ?_⟩
  omega

def directOrbitSquareTwistExponentHalf
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : ℕ :=
  16 + 21 * t.powerSplit.gapSplit.k

theorem directOrbit_squareTwist_exponent_eq_two_mul_half
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    32 + 42 * t.powerSplit.gapSplit.k =
      2 * directOrbitSquareTwistExponentHalf t := by
  simp [directOrbitSquareTwistExponentHalf]
  ring

theorem directOrbit_squareTwist_axis_pow_is_square
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
        (32 + 42 * t.powerSplit.gapSplit.k) =
      ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
        directOrbitSquareTwistExponentHalf t) ^ 2 := by
  rw [directOrbit_squareTwist_exponent_eq_two_mul_half]
  calc
    (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
        (2 * directOrbitSquareTwistExponentHalf t) =
        (directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
          (directOrbitSquareTwistExponentHalf t * 2) := by
            congr 1
            omega
    _ = ((directOrbitPairAxisUnitOne : SevenRealCubicInt) ^
        directOrbitSquareTwistExponentHalf t) ^ 2 := by
          rw [pow_mul]

theorem directOrbit_squareTwist_coeff1_transport
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitSquareTwistCoeff1 t =
      directOrbitPairAxisUnitOne ^
          (32 + 42 * t.powerSplit.gapSplit.k) *
        directOrbitRotateUnit (directOrbitSquareTwistCoeff0 t) := by
  apply Units.ext
  dsimp [directOrbitSquareTwistCoeff1, directOrbitSquareTwistCoeff0,
    directOrbitTwistedCoeff1, directOrbitTwistedCoeff0]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    directOrbitRotateUnit_val, map_mul, map_pow]
  ring

theorem directOrbit_squareTwist_coeff2_transport
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitSquareTwistCoeff2 t =
      directOrbitPairAxisUnitOne ^
          (32 + 42 * t.powerSplit.gapSplit.k) *
        directOrbitRotateUnit (directOrbitSquareTwistCoeff1 t) := by
  apply Units.ext
  dsimp [directOrbitSquareTwistCoeff2, directOrbitSquareTwistCoeff1,
    directOrbitTwistedCoeff2, directOrbitTwistedCoeff1]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val,
    directOrbitRotateUnit_val, map_mul, map_pow]
  ring

/-! ## Projective classes survive the square refinement -/

theorem directOrbit_squareTwist_coeff_projectiveLog
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    projectiveLog (Additive.ofMul (directOrbitSquareTwistCoeff0 t)) = (2, 4) ∧
      projectiveLog (Additive.ofMul (directOrbitSquareTwistCoeff1 t)) = (2, 2) ∧
      projectiveLog (Additive.ofMul (directOrbitSquareTwistCoeff2 t)) = (2, 5) := by
  have h := directOrbit_twistedCoeff_projectiveLog_unconditional t.powerSplit
  have hsq0 := projectiveLog_pow_seven t.gapSquareUnit
  have hsq1 := projectiveLog_pow_seven (directOrbitRotateUnit t.gapSquareUnit)
  have hsq2 := projectiveLog_pow_seven
    (directOrbitRotateUnit (directOrbitRotateUnit t.gapSquareUnit))
  constructor
  · rw [directOrbitSquareTwistCoeff0, ofMul_mul, map_add, h.1, hsq0]
    simp
  constructor
  · rw [directOrbitSquareTwistCoeff1, ofMul_mul, map_add, h.2.1, hsq1]
    simp
  · rw [directOrbitSquareTwistCoeff2, ofMul_mul, map_add, h.2.2, hsq2]
    simp

/-! ## The square roots are nonzero, including their two rotations -/

theorem directOrbit_squareTwist_squareRoot_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    t.gapSquareRoot ≠ 0 := by
  intro hz
  have hpos := directOrbitSquareRefinement_gap_square_norm_pos t
  rw [hz] at hpos
  norm_num [SevenRealCubicInt.norm] at hpos

theorem directOrbit_squareTwist_rotatedSquareRoot_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    rotateEquiv t.gapSquareRoot ≠ 0 := by
  intro hz
  apply directOrbit_squareTwist_squareRoot_ne_zero t
  apply rotateEquiv.injective
  simpa only [map_zero] using hz

theorem directOrbit_squareTwist_twiceRotatedSquareRoot_ne_zero
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    rotateEquiv (rotateEquiv t.gapSquareRoot) ≠ 0 := by
  intro hz
  apply directOrbit_squareTwist_squareRoot_ne_zero t
  apply rotateEquiv.injective
  apply rotateEquiv.injective
  simpa using hz

/-! ## A conditional square-unit contradiction -/

theorem directOrbit_squareTwist_coeff0_not_square
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬ ∃ v : SevenRealCubicIntˣ,
        directOrbitSquareTwistCoeff0 t = v ^ 2 := by
  rintro ⟨v, hv⟩
  let P : SevenRealCubicIntˣ := directOrbitPairAxisUnitOne
  let half := directOrbitSquareTwistExponentHalf t
  have hP :
      (P : SevenRealCubicInt) ^
          (32 + 42 * t.powerSplit.gapSplit.k) =
        ((P : SevenRealCubicInt) ^ half) ^ 2 := by
    exact directOrbit_squareTwist_axis_pow_is_square t
  have hPu :
      directOrbitPairAxisUnitOne ^
          (32 + 42 * t.powerSplit.gapSplit.k) =
        (directOrbitPairAxisUnitOne ^ half) ^ 2 := by
    apply Units.ext
    exact hP
  have hc1 := directOrbit_squareTwist_coeff1_transport t
  have hc2 := directOrbit_squareTwist_coeff2_transport t
  have hs1 : directOrbitSquareTwistCoeff1 t =
      (directOrbitPairAxisUnitOne ^ half *
        directOrbitRotateUnit v) ^ 2 := by
    rw [hc1, hv, hPu]
    apply Units.ext
    simp only [directOrbitRotateUnit_val, map_pow, Units.val_mul,
      Units.val_pow_eq_pow_val]
    ring
  have hs2 : directOrbitSquareTwistCoeff2 t =
      (directOrbitPairAxisUnitOne ^ half *
        directOrbitRotateUnit (directOrbitPairAxisUnitOne ^ half *
          directOrbitRotateUnit v)) ^ 2 := by
    rw [hc2, hs1, hPu]
    apply Units.ext
    simp only [directOrbitRotateUnit_val, map_pow, Units.val_mul,
      Units.val_pow_eq_pow_val]
    ring
  have hroot0 : realEval (t.gapSquareRoot ^ 7) ≠ 0 := by
    intro hz
    apply pow_ne_zero 7 (directOrbit_squareTwist_squareRoot_ne_zero t)
    apply squareTwist_realEval_injective
    simpa only [map_pow, map_zero] using hz
  have hroot1 : realEval ((rotateEquiv t.gapSquareRoot) ^ 7) ≠ 0 := by
    intro hz
    apply pow_ne_zero 7 (directOrbit_squareTwist_rotatedSquareRoot_ne_zero t)
    apply squareTwist_realEval_injective
    simpa only [map_pow, map_zero] using hz
  have hroot2 : realEval ((rotateEquiv (rotateEquiv t.gapSquareRoot)) ^ 7) ≠ 0 := by
    intro hz
    apply pow_ne_zero 7
      (directOrbit_squareTwist_twiceRotatedSquareRoot_ne_zero t)
    apply squareTwist_realEval_injective
    simpa only [map_pow, map_zero] using hz
  have hc0pos : 0 < realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) := by
    rw [hv]
    simp only [map_pow, Units.val_pow_eq_pow_val]
    exact sq_pos_of_ne_zero (by
      intro hzero
      exact v.isUnit.ne_zero
        (squareTwist_realEval_injective (by simpa using hzero)))
  have hc1pos : 0 < realEval (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) := by
    rw [hs1]
    simp only [map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    exact sq_pos_of_ne_zero (by
      intro hzero
      exact (directOrbitPairAxisUnitOne ^ half * directOrbitRotateUnit v).isUnit.ne_zero
        (squareTwist_realEval_injective (by simpa using hzero)))
  have hc2pos : 0 < realEval (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) := by
    rw [hs2]
    simp only [map_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    exact sq_pos_of_ne_zero (by
      intro hzero
      exact (directOrbitPairAxisUnitOne ^ half *
        directOrbitRotateUnit (directOrbitPairAxisUnitOne ^ half *
          directOrbitRotateUnit v)).isUnit.ne_zero
        (squareTwist_realEval_injective (by simpa using hzero)))
  have h := congrArg realEval (directOrbit_squareTwist_twisted_eq t)
  simp only [map_add, map_mul, map_pow, map_zero] at h
  have h0sq : 0 <
      realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
        (realEval (t.gapSquareRoot ^ 7)) ^ 2 :=
    mul_pos hc0pos (sq_pos_of_ne_zero hroot0)
  have h1sq : 0 <
      realEval (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) *
        (realEval ((rotateEquiv t.gapSquareRoot) ^ 7)) ^ 2 :=
    mul_pos hc1pos (sq_pos_of_ne_zero hroot1)
  have h2sq : 0 <
      realEval (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) *
        (realEval ((rotateEquiv (rotateEquiv t.gapSquareRoot)) ^ 7)) ^ 2 :=
    mul_pos hc2pos (sq_pos_of_ne_zero hroot2)
  have h0sq' : 0 <
      realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
        (realEval t.gapSquareRoot ^ 7) ^ 2 := by
    simpa only [map_pow] using h0sq
  have h1sq' : 0 <
      realEval (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) *
        (realEval (rotateEquiv t.gapSquareRoot) ^ 7) ^ 2 := by
    simpa only [map_pow] using h1sq
  have h2sq' : 0 <
      realEval (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) *
        (realEval (rotateEquiv (rotateEquiv t.gapSquareRoot)) ^ 7) ^ 2 := by
    simpa only [map_pow] using h2sq
  nlinarith

/-! ## The signed norm and the real sign obstruction -/

theorem directOrbit_squareTwist_coeff0_norm_eq_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    SevenRealCubicInt.norm
      (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) = 1 := by
  let s := t.powerSplit
  let e := 32 + 42 * s.gapSplit.k
  let r0 := t.gapSquareRoot
  have he : e = 2 * directOrbitSquareTwistExponentHalf t := by
    dsimp [e]
    exact directOrbit_squareTwist_exponent_eq_two_mul_half t
  have haxis : 0 < SevenRealCubicInt.norm (eisensteinAxis ^ e) := by
    rw [he, SevenRealCubicInt.norm_pow, pow_mul, norm_eisensteinAxis]
    positivity
  have hr0 : SevenRealCubicInt.norm r0 ≠ 0 := by
    intro hz
    have hpos := directOrbitSquareRefinement_gap_square_norm_pos t
    rw [hz] at hpos
    change 0 < Int.natAbs (0 : ℤ) at hpos
    simp at hpos
  have hrpow : 0 < SevenRealCubicInt.norm (r0 ^ 14) := by
    rw [SevenRealCubicInt.norm_pow]
    rw [show (14 : ℕ) = 7 * 2 by norm_num, pow_mul]
    exact sq_pos_of_ne_zero (pow_ne_zero _ hr0)
  have hfactor :
      SevenRealCubicInt.norm (directOrbitGap p) =
        SevenRealCubicInt.norm (eisensteinAxis ^ e) *
          SevenRealCubicInt.norm
            (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
          SevenRealCubicInt.norm (r0 ^ 14) := by
    have h := directOrbit_gap_split_eq s
    rw [t.gapRoot_eq] at h
    have hn := congrArg SevenRealCubicInt.norm h
    simp only [SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow] at hn
    dsimp [directOrbitSquareTwistCoeff0] at ⊢
    simp only [SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow]
    dsimp [s, e, r0] at hn ⊢
    ring_nf at hn ⊢
    exact hn
  have hgap : 0 < SevenRealCubicInt.norm (directOrbitGap p) :=
    directOrbit_norms_pos p |>.1
  have hcpos : 0 < SevenRealCubicInt.norm
      (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) := by
    by_contra hc
    have hc' : SevenRealCubicInt.norm
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) ≤ 0 := le_of_not_gt hc
    have hleft : SevenRealCubicInt.norm (eisensteinAxis ^ e) *
        SevenRealCubicInt.norm
          (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt haxis) hc'
    have hright : SevenRealCubicInt.norm (eisensteinAxis ^ e) *
        SevenRealCubicInt.norm
          (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
        SevenRealCubicInt.norm (r0 ^ 14) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hleft (le_of_lt hrpow)
    rw [← hfactor] at hright
    linarith
  have habs : Int.natAbs (SevenRealCubicInt.norm
      (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) = 1 :=
    gapHeight_natAbs_norm_unit (directOrbitSquareTwistCoeff0 t)
  have hcast :
      (Int.natAbs (SevenRealCubicInt.norm
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) : ℤ) =
        SevenRealCubicInt.norm
          (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) :=
    Int.natAbs_of_nonneg (le_of_lt hcpos)
  calc
    SevenRealCubicInt.norm
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) =
        (Int.natAbs (SevenRealCubicInt.norm
          (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) : ℤ) :=
      hcast.symm
    _ = 1 := by rw [habs]; norm_num


theorem directOrbit_squareTwist_coeff0_not_all_real_positive
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬ (0 < realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) ∧
      0 < realEval (rotateEquiv
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) ∧
      0 < realEval (rotateEquiv (rotateEquiv
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)))) := by
  rintro ⟨h0, h1, h2⟩
  have hPu :
      directOrbitPairAxisUnitOne ^
          (32 + 42 * t.powerSplit.gapSplit.k) =
        (directOrbitPairAxisUnitOne ^ directOrbitSquareTwistExponentHalf t) ^ 2 := by
    apply Units.ext
    exact directOrbit_squareTwist_axis_pow_is_square t
  have hPpos : 0 < realEval
      (directOrbitPairAxisUnitOne ^
        (32 + 42 * t.powerSplit.gapSplit.k) : SevenRealCubicInt) := by
    rw [directOrbit_squareTwist_axis_pow_is_square t]
    simp only [map_pow]
    exact sq_pos_of_ne_zero (pow_ne_zero _ (by
      intro hz
      exact directOrbitPairAxisUnitOne.isUnit.ne_zero
        (squareTwist_realEval_injective (by simpa using hz))))
  have hc1 := directOrbit_squareTwist_coeff1_transport t
  have hc2 := directOrbit_squareTwist_coeff2_transport t
  have hc1pos : 0 < realEval
      (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) := by
    rw [hc1]
    simp only [Units.val_mul, map_mul, directOrbitRotateUnit_val]
    exact mul_pos hPpos h1
  have hP1pos : 0 < realEval (rotateEquiv
      (directOrbitPairAxisUnitOne ^
        (32 + 42 * t.powerSplit.gapSplit.k) : SevenRealCubicInt)) := by
    rw [directOrbit_squareTwist_axis_pow_is_square t]
    simp only [map_pow]
    exact sq_pos_of_ne_zero (pow_ne_zero _ (by
      intro hz
      exact (directOrbitRotateUnit directOrbitPairAxisUnitOne).isUnit.ne_zero
        (squareTwist_realEval_injective (by simpa using hz))))
  have hrotc1pos : 0 < realEval (rotateEquiv
      (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt)) := by
    rw [hc1]
    simp only [Units.val_mul, map_mul, directOrbitRotateUnit_val]
    exact mul_pos hP1pos h2
  have hc2pos : 0 < realEval
      (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) := by
    rw [hc2]
    simp only [Units.val_mul, map_mul, directOrbitRotateUnit_val]
    exact mul_pos hPpos hrotc1pos
  have hr0 : realEval (t.gapSquareRoot ^ 7) ≠ 0 := by
    intro hz
    apply pow_ne_zero 7 (directOrbit_squareTwist_squareRoot_ne_zero t)
    apply squareTwist_realEval_injective
    simpa only [map_pow, map_zero] using hz
  have hr1 : realEval ((rotateEquiv t.gapSquareRoot) ^ 7) ≠ 0 := by
    intro hz
    apply pow_ne_zero 7 (directOrbit_squareTwist_rotatedSquareRoot_ne_zero t)
    apply squareTwist_realEval_injective
    simpa only [map_pow, map_zero] using hz
  have hr2 : realEval ((rotateEquiv (rotateEquiv t.gapSquareRoot)) ^ 7) ≠ 0 := by
    intro hz
    apply pow_ne_zero 7
      (directOrbit_squareTwist_twiceRotatedSquareRoot_ne_zero t)
    apply squareTwist_realEval_injective
    simpa only [map_pow, map_zero] using hz
  have h := congrArg realEval (directOrbit_squareTwist_twisted_eq t)
  simp only [map_add, map_mul, map_pow, map_zero] at h
  have h0sq := mul_pos h0 (sq_pos_of_ne_zero hr0)
  have h1sq := mul_pos hc1pos (sq_pos_of_ne_zero hr1)
  have h2sq := mul_pos hc2pos (sq_pos_of_ne_zero hr2)
  have h0sq' : 0 < realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
      (realEval t.gapSquareRoot ^ 7) ^ 2 := by simpa only [map_pow] using h0sq
  have h1sq' : 0 < realEval (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) *
      (realEval (rotateEquiv t.gapSquareRoot) ^ 7) ^ 2 := by simpa only [map_pow] using h1sq
  have h2sq' : 0 < realEval (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) *
      (realEval (rotateEquiv (rotateEquiv t.gapSquareRoot)) ^ 7) ^ 2 := by
    simpa only [map_pow] using h2sq
  nlinarith

theorem directOrbit_squareTwist_coeff0_not_all_real_negative
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬ (realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) < 0 ∧
      realEval (rotateEquiv
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) < 0 ∧
      realEval (rotateEquiv (rotateEquiv
        (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt))) < 0) := by
  rintro ⟨h0, h1, h2⟩
  have hnorm := directOrbit_squareTwist_coeff0_norm_eq_one t
  have hcyc := realEval_cyclic_norm
    (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)
  have hprod :
      realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
          realEval (rotateEquiv
            (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) *
          realEval (rotateEquiv (rotateEquiv
            (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt))) = 1 := by
    rw [hcyc, hnorm]
    norm_num
  have h01 : 0 <
      realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
        realEval (rotateEquiv
          (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) :=
    mul_pos_of_neg_of_neg h0 h1
  have hprodneg :
      realEval (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt) *
          realEval (rotateEquiv
            (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)) *
          realEval (rotateEquiv (rotateEquiv
            (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt))) < 0 :=
    mul_neg_of_pos_of_neg h01 h2
  nlinarith

end
end DkMath.FLT.Seven
