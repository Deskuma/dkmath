/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentCoefficientRatios
import DkMath.FLT.Seven.SevenRealCubicCurrentOrientedGapTransport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentCoefficientPhaseCollapse"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

/-! ## Current coefficient-ratio packet -/

def currentCoefficientRatio0OfSquareRefinement
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  currentCoefficientRatio0 (directOrbitSquareTwistCoeff0 t)
    (directOrbitSquareTwistCoeff1 t) (directOrbitSquareTwistCoeff2 t)

def currentCoefficientRatio1OfSquareRefinement
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  currentCoefficientRatio1 (directOrbitSquareTwistCoeff0 t)
    (directOrbitSquareTwistCoeff1 t) (directOrbitSquareTwistCoeff2 t)

def currentCoefficientRatio2OfSquareRefinement
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) : SevenRealCubicIntˣ :=
  currentCoefficientRatio2 (directOrbitSquareTwistCoeff0 t)
    (directOrbitSquareTwistCoeff1 t) (directOrbitSquareTwistCoeff2 t)

theorem currentCoefficientRatio_squareRefinement_product
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    currentCoefficientRatio0OfSquareRefinement t *
        currentCoefficientRatio1OfSquareRefinement t *
        currentCoefficientRatio2OfSquareRefinement t = -1 := by
  exact currentCoefficientRatio_product _ _ _

theorem currentCoefficientRatio0_squareRefinement_eq_twistRatio21
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    currentCoefficientRatio0OfSquareRefinement t =
      directOrbitCommonPrimeTwistRatio21 t := by
  simp [currentCoefficientRatio0OfSquareRefinement,
    currentCoefficientRatio0, directOrbitCommonPrimeTwistRatio21,
    div_eq_mul_inv]

/-! ## The exact cyclic norm of the transport unit -/

theorem current_pairAxisUnitOne_cyclic_norm :
    directOrbitPairAxisUnitOne *
        directOrbitRotateUnit directOrbitPairAxisUnitOne *
        directOrbitRotateUnit (directOrbitRotateUnit
          directOrbitPairAxisUnitOne) = 1 := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_one, directOrbitPairAxisUnitOne_val,
    directOrbitRotateUnit_val]
  ext <;>
    norm_num [pairAxisUnit_one, alpha, rotateEquiv, rotateHom, mul, pow_two]

theorem current_directOrbitRotateUnit_mul
    (u v : SevenRealCubicIntˣ) :
    directOrbitRotateUnit (u * v) =
      directOrbitRotateUnit u * directOrbitRotateUnit v := by
  apply Units.ext
  simp [directOrbitRotateUnit]

theorem current_directOrbitRotateUnit_pow
    (u : SevenRealCubicIntˣ) (n : ℕ) :
    directOrbitRotateUnit (u ^ n) =
      directOrbitRotateUnit u ^ n := by
  apply Units.ext
  simp [directOrbitRotateUnit]

theorem current_directOrbitRotateUnit_twice_mul
    (u v : SevenRealCubicIntˣ) :
    directOrbitRotateUnit (directOrbitRotateUnit (u * v)) =
      directOrbitRotateUnit (directOrbitRotateUnit u) *
        directOrbitRotateUnit (directOrbitRotateUnit v) := by
  rw [current_directOrbitRotateUnit_mul,
    current_directOrbitRotateUnit_mul]

theorem current_directOrbitRotateUnit_three
    (u : SevenRealCubicIntˣ) :
    directOrbitRotateUnit (directOrbitRotateUnit
      (directOrbitRotateUnit u)) = u := by
  apply Units.ext
  change rotateEquiv (rotateEquiv (rotateEquiv
    (u : SevenRealCubicInt))) = (u : SevenRealCubicInt)
  exact SevenRealCubicInt.rotateEquiv_three (u : SevenRealCubicInt)

theorem current_transport_axis_cyclic_norm
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    let A : SevenRealCubicIntˣ := directOrbitPairAxisUnitOne ^
      (32 + 42 * t.powerSplit.gapSplit.k)
    A * directOrbitRotateUnit A *
        directOrbitRotateUnit (directOrbitRotateUnit A) = 1 := by
  dsimp
  rw [current_directOrbitRotateUnit_pow,
    current_directOrbitRotateUnit_pow]
  calc
    directOrbitPairAxisUnitOne ^ (32 + 42 *
        t.powerSplit.gapSplit.k) *
        directOrbitRotateUnit directOrbitPairAxisUnitOne ^
          (32 + 42 * t.powerSplit.gapSplit.k) *
        directOrbitRotateUnit (directOrbitRotateUnit
          directOrbitPairAxisUnitOne) ^
          (32 + 42 * t.powerSplit.gapSplit.k) =
        (directOrbitPairAxisUnitOne ^ (32 + 42 *
          t.powerSplit.gapSplit.k) *
          directOrbitRotateUnit directOrbitPairAxisUnitOne ^
            (32 + 42 * t.powerSplit.gapSplit.k)) *
          directOrbitRotateUnit (directOrbitRotateUnit
            directOrbitPairAxisUnitOne) ^
            (32 + 42 * t.powerSplit.gapSplit.k) := by rfl
    _ = (directOrbitPairAxisUnitOne *
          directOrbitRotateUnit directOrbitPairAxisUnitOne) ^
            (32 + 42 * t.powerSplit.gapSplit.k) *
          directOrbitRotateUnit (directOrbitRotateUnit
            directOrbitPairAxisUnitOne) ^
            (32 + 42 * t.powerSplit.gapSplit.k) := by
          rw [← mul_pow]
    _ = ((directOrbitPairAxisUnitOne *
          directOrbitRotateUnit directOrbitPairAxisUnitOne) *
          directOrbitRotateUnit (directOrbitRotateUnit
            directOrbitPairAxisUnitOne)) ^
            (32 + 42 * t.powerSplit.gapSplit.k) := by
          rw [← mul_pow]
    _ = 1 := by rw [current_pairAxisUnitOne_cyclic_norm]; simp

/-! ## The third coefficient transport and cyclic ratio laws -/

theorem current_transport_rotate_coeff0
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitRotateUnit (directOrbitSquareTwistCoeff0 t) =
      (directOrbitPairAxisUnitOne ^
        (32 + 42 * t.powerSplit.gapSplit.k))⁻¹ *
        directOrbitSquareTwistCoeff1 t := by
  rw [directOrbit_squareTwist_coeff1_transport t]
  group

theorem current_transport_rotate_coeff1
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitRotateUnit (directOrbitSquareTwistCoeff1 t) =
      (directOrbitPairAxisUnitOne ^
        (32 + 42 * t.powerSplit.gapSplit.k))⁻¹ *
        directOrbitSquareTwistCoeff2 t := by
  rw [directOrbit_squareTwist_coeff2_transport t]
  group

theorem current_transport_rotate_coeff2
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitRotateUnit (directOrbitSquareTwistCoeff2 t) =
      (directOrbitPairAxisUnitOne ^
        (32 + 42 * t.powerSplit.gapSplit.k))⁻¹ *
        directOrbitSquareTwistCoeff0 t := by
  let A : SevenRealCubicIntˣ := directOrbitPairAxisUnitOne ^
    (32 + 42 * t.powerSplit.gapSplit.k)
  have hnorm : A * directOrbitRotateUnit A *
      directOrbitRotateUnit (directOrbitRotateUnit A) = 1 :=
    current_transport_axis_cyclic_norm t
  calc
    directOrbitRotateUnit (directOrbitSquareTwistCoeff2 t) =
        directOrbitRotateUnit (A *
          directOrbitRotateUnit (directOrbitSquareTwistCoeff1 t)) := by
      rw [directOrbit_squareTwist_coeff2_transport t]
    _ = directOrbitRotateUnit A *
          directOrbitRotateUnit (directOrbitRotateUnit
            (directOrbitSquareTwistCoeff1 t)) := by
      rw [current_directOrbitRotateUnit_mul]
    _ = directOrbitRotateUnit A *
          (directOrbitRotateUnit (directOrbitRotateUnit A) *
            directOrbitSquareTwistCoeff0 t) := by
      rw [directOrbit_squareTwist_coeff1_transport t,
        current_directOrbitRotateUnit_twice_mul,
        current_directOrbitRotateUnit_three]
    _ = (directOrbitRotateUnit A *
          directOrbitRotateUnit (directOrbitRotateUnit A)) *
            directOrbitSquareTwistCoeff0 t := by rw [mul_assoc]
    _ = A⁻¹ * directOrbitSquareTwistCoeff0 t := by
      have hcancel : directOrbitRotateUnit A *
          directOrbitRotateUnit (directOrbitRotateUnit A) = A⁻¹ := by
        calc
          directOrbitRotateUnit A *
              directOrbitRotateUnit (directOrbitRotateUnit A) =
              A⁻¹ * (A * directOrbitRotateUnit A *
                directOrbitRotateUnit (directOrbitRotateUnit A)) := by
                  group
          _ = A⁻¹ := by rw [hnorm]; simp
      rw [hcancel]

theorem current_directOrbitRotateUnit_neg
    (u : SevenRealCubicIntˣ) :
    directOrbitRotateUnit (-u) = -directOrbitRotateUnit u := by
  apply Units.ext
  simp [directOrbitRotateUnit]

theorem current_directOrbitRotateUnit_div
    (u v : SevenRealCubicIntˣ) :
    directOrbitRotateUnit (u / v) =
      directOrbitRotateUnit u / directOrbitRotateUnit v := by
  apply Units.ext
  simp [directOrbitRotateUnit]

theorem currentCoefficientRatio0_squareRefinement_rotate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitRotateUnit (currentCoefficientRatio0OfSquareRefinement t) =
      currentCoefficientRatio1OfSquareRefinement t := by
  change directOrbitRotateUnit (-directOrbitSquareTwistCoeff2 t /
      directOrbitSquareTwistCoeff1 t) =
    -directOrbitSquareTwistCoeff0 t / directOrbitSquareTwistCoeff2 t
  let A : SevenRealCubicIntˣ := directOrbitPairAxisUnitOne ^
    (32 + 42 * t.powerSplit.gapSplit.k)
  have h2 : directOrbitRotateUnit (directOrbitSquareTwistCoeff2 t) =
      A⁻¹ * directOrbitSquareTwistCoeff0 t := by
    simpa [A] using current_transport_rotate_coeff2 t
  have h1 : directOrbitRotateUnit (directOrbitSquareTwistCoeff1 t) =
      A⁻¹ * directOrbitSquareTwistCoeff2 t := by
    simpa [A] using current_transport_rotate_coeff1 t
  rw [current_directOrbitRotateUnit_div,
    current_directOrbitRotateUnit_neg,
    h2, h1]
  simp only [div_eq_mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem currentCoefficientRatio1_squareRefinement_rotate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitRotateUnit (currentCoefficientRatio1OfSquareRefinement t) =
      currentCoefficientRatio2OfSquareRefinement t := by
  change directOrbitRotateUnit (-directOrbitSquareTwistCoeff0 t /
      directOrbitSquareTwistCoeff2 t) =
    -directOrbitSquareTwistCoeff1 t / directOrbitSquareTwistCoeff0 t
  let A : SevenRealCubicIntˣ := directOrbitPairAxisUnitOne ^
    (32 + 42 * t.powerSplit.gapSplit.k)
  have h0 : directOrbitRotateUnit (directOrbitSquareTwistCoeff0 t) =
      A⁻¹ * directOrbitSquareTwistCoeff1 t := by
    simpa [A] using current_transport_rotate_coeff0 t
  have h2 : directOrbitRotateUnit (directOrbitSquareTwistCoeff2 t) =
      A⁻¹ * directOrbitSquareTwistCoeff0 t := by
    simpa [A] using current_transport_rotate_coeff2 t
  rw [current_directOrbitRotateUnit_div,
    current_directOrbitRotateUnit_neg,
    h0, h2]
  simp only [div_eq_mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem currentCoefficientRatio2_squareRefinement_rotate
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    directOrbitRotateUnit (currentCoefficientRatio2OfSquareRefinement t) =
      currentCoefficientRatio0OfSquareRefinement t := by
  change directOrbitRotateUnit (-directOrbitSquareTwistCoeff1 t /
      directOrbitSquareTwistCoeff0 t) =
    -directOrbitSquareTwistCoeff2 t / directOrbitSquareTwistCoeff1 t
  let A : SevenRealCubicIntˣ := directOrbitPairAxisUnitOne ^
    (32 + 42 * t.powerSplit.gapSplit.k)
  have h1 : directOrbitRotateUnit (directOrbitSquareTwistCoeff1 t) =
      A⁻¹ * directOrbitSquareTwistCoeff2 t := by
    simpa [A] using current_transport_rotate_coeff1 t
  have h0 : directOrbitRotateUnit (directOrbitSquareTwistCoeff0 t) =
      A⁻¹ * directOrbitSquareTwistCoeff1 t := by
    simpa [A] using current_transport_rotate_coeff0 t
  rw [current_directOrbitRotateUnit_div,
    current_directOrbitRotateUnit_neg,
    h1, h0]
  simp only [div_eq_mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

/-! ## The current fourteen-power packet -/

theorem currentOrientedGap_fourteen_equation
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    let c0 := a.f0 (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt)
    let c1 := a.f0 (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt)
    let c2 := a.f0 (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt)
    let r0 := a.f0 h.squareRefinement.gapSquareRoot
    let r1 := a.f0 (rotateEquiv h.squareRefinement.gapSquareRoot)
    let r2 := a.f0 (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))
    c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0 := by
  dsimp
  have hh := congrArg a.f0
    (directOrbit_squareTwist_twisted_eq h.squareRefinement)
  simpa [map_add, map_mul, map_pow, ← pow_mul] using hh

theorem currentOrientedGap_fourteen_witnesses
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    ∃ u0 u1 u2 : ZMod q,
      u0 ≠ 0 ∧ u1 ≠ 0 ∧ u2 ≠ 0 ∧
      u0 ^ 14 = a.f0
        (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) ∧
      u1 ^ 14 = a.f1
        (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) ∧
      u2 ^ 14 = a.f2
        (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) := by
  letI : Fact q.Prime := ⟨a.q_prime⟩
  let c0 : ZMod q := a.f0
    (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt)
  let c1 : ZMod q := a.f0
    (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt)
  let c2 : ZMod q := a.f0
    (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt)
  let r0 : ZMod q := a.f0 h.squareRefinement.gapSquareRoot
  let r1 : ZMod q := a.f0 (rotateEquiv h.squareRefinement.gapSquareRoot)
  let r2 : ZMod q := a.f0
    (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))
  let d0 : ZMod q := a.f1
    (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt)
  let d1 : ZMod q := a.f1
    (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt)
  let d2 : ZMod q := a.f1
    (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt)
  let s0 : ZMod q := a.f1 h.squareRefinement.gapSquareRoot
  let s1 : ZMod q := a.f1 (rotateEquiv h.squareRefinement.gapSquareRoot)
  let s2 : ZMod q := a.f1
    (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))
  let e0 : ZMod q := a.f2
    (directOrbitSquareTwistCoeff0 h.squareRefinement : SevenRealCubicInt)
  let e1 : ZMod q := a.f2
    (directOrbitSquareTwistCoeff1 h.squareRefinement : SevenRealCubicInt)
  let e2 : ZMod q := a.f2
    (directOrbitSquareTwistCoeff2 h.squareRefinement : SevenRealCubicInt)
  let v0 : ZMod q := a.f2 h.squareRefinement.gapSquareRoot
  let v1 : ZMod q := a.f2 (rotateEquiv h.squareRefinement.gapSquareRoot)
  let v2 : ZMod q := a.f2
    (rotateEquiv (rotateEquiv h.squareRefinement.gapSquareRoot))
  have hc0 : c0 ≠ 0 := by
    dsimp [c0]
    exact (IsUnit.map a.f0
      (directOrbitSquareTwistCoeff0 h.squareRefinement).isUnit).ne_zero
  have hc1 : c1 ≠ 0 := by
    dsimp [c1]
    exact (IsUnit.map a.f0
      (directOrbitSquareTwistCoeff1 h.squareRefinement).isUnit).ne_zero
  have hc2 : c2 ≠ 0 := by
    dsimp [c2]
    exact (IsUnit.map a.f0
      (directOrbitSquareTwistCoeff2 h.squareRefinement).isUnit).ne_zero
  have hEq : c0 * r0 ^ 14 + c1 * r1 ^ 14 + c2 * r2 ^ 14 = 0 := by
    simpa [c0, c1, c2, r0, r1, r2] using
      currentOrientedGap_fourteen_equation a
  have hEq1 : d0 * s0 ^ 14 + d1 * s1 ^ 14 + d2 * s2 ^ 14 = 0 := by
    have hh := congrArg a.f1
      (directOrbit_squareTwist_twisted_eq h.squareRefinement)
    simpa [d0, d1, d2, s0, s1, s2, map_add, map_mul, map_pow,
      ← pow_mul] using hh
  have hEq2 : e0 * v0 ^ 14 + e1 * v1 ^ 14 + e2 * v2 ^ 14 = 0 := by
    have hh := congrArg a.f2
      (directOrbit_squareTwist_twisted_eq h.squareRefinement)
    simpa [e0, e1, e2, v0, v1, v2, map_add, map_mul, map_pow,
      ← pow_mul] using hh
  have h0 := three_zero_index_fourteen_zero hc1
    (by simpa [r2] using a.rotate2_gap_ne_zero)
    hEq (by simpa [r0] using a.gap_zero)
  have hd0 : d0 ≠ 0 := by
    dsimp [d0]
    exact (IsUnit.map a.f1
      (directOrbitSquareTwistCoeff0 h.squareRefinement).isUnit).ne_zero
  have hd2 : d2 ≠ 0 := by
    dsimp [d2]
    exact (IsUnit.map a.f1
      (directOrbitSquareTwistCoeff2 h.squareRefinement).isUnit).ne_zero
  have he0 : e0 ≠ 0 := by
    dsimp [e0]
    exact (IsUnit.map a.f2
      (directOrbitSquareTwistCoeff0 h.squareRefinement).isUnit).ne_zero
  have he1 : e1 ≠ 0 := by
    dsimp [e1]
    exact (IsUnit.map a.f2
      (directOrbitSquareTwistCoeff1 h.squareRefinement).isUnit).ne_zero
  have h1 := three_zero_index_fourteen_one hd2
    (by simpa [s0] using a.f1_gap_zero_ne_zero)
    hEq1 (by simpa [s1] using a.f1_gap_rotate_zero)
  have h2 := three_zero_index_fourteen_two he0
    (by simpa [v1] using a.f2_gap_rotate_ne_zero)
    hEq2 (by simpa [v2] using a.f2_gap_rotate2_zero)
  have hR0 : a.f0
      (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) = -c2 / c1 := by
    simp [currentCoefficientRatio0OfSquareRefinement,
      currentCoefficientRatio0, c1, c2, div_eq_mul_inv]
  have hR1 : a.f0
      (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) = -c0 / c2 := by
    simp [currentCoefficientRatio1OfSquareRefinement,
      currentCoefficientRatio1, c0, c2, div_eq_mul_inv]
  have hR2 : a.f0
      (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) = -c1 / c0 := by
    simp [currentCoefficientRatio2OfSquareRefinement,
      currentCoefficientRatio2, c0, c1, div_eq_mul_inv]
  have hS1 : a.f1
      (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) = -d0 / d2 := by
    simp [currentCoefficientRatio1OfSquareRefinement,
      currentCoefficientRatio1, d0, d2, div_eq_mul_inv]
  have hS2 : a.f2
      (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) = -e1 / e0 := by
    simp [currentCoefficientRatio2OfSquareRefinement,
      currentCoefficientRatio2, e0, e1, div_eq_mul_inv]
  refine ⟨r1 / r2, s2 / s0, v0 / v1,
    div_ne_zero (by simpa [r1] using a.rotate_gap_ne_zero)
      (by simpa [r2] using a.rotate2_gap_ne_zero),
    div_ne_zero (by simpa [s2] using a.f1_gap_rotate2_ne_zero)
      (by simpa [s0] using a.f1_gap_zero_ne_zero),
    div_ne_zero (by simpa [v0] using a.f2_gap_zero_ne_zero)
      (by simpa [v1] using a.f2_gap_rotate_ne_zero), ?_, ?_, ?_⟩
  · calc
      (r1 / r2) ^ 14 = -c2 / c1 := h0
      _ = a.f0
        (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) := hR0.symm
  · calc
      (s2 / s0) ^ 14 = -d0 / d2 := h1
      _ = a.f1
        (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) := hS1.symm
  · calc
      (v0 / v1) ^ 14 = -e1 / e0 := h2
      _ = a.f2
        (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) := hS2.symm

theorem currentCommonPrime_fourteen_phase_collapse
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f1 (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) =
        a.f0 (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) ∧
      a.f2 (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) =
        a.f0 (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) := by
  have hR0 := currentCoefficientRatio0_squareRefinement_rotate
    h.squareRefinement
  have hR1 := currentCoefficientRatio1_squareRefinement_rotate
    h.squareRefinement
  have hR0' : (currentCoefficientRatio1OfSquareRefinement
      h.squareRefinement : SevenRealCubicInt) =
      rotateEquiv (currentCoefficientRatio0OfSquareRefinement
        h.squareRefinement : SevenRealCubicInt) := by
    exact (congrArg Units.val hR0).symm
  have hR1' : (currentCoefficientRatio2OfSquareRefinement
      h.squareRefinement : SevenRealCubicInt) =
      rotateEquiv (currentCoefficientRatio1OfSquareRefinement
        h.squareRefinement : SevenRealCubicInt) := by
    exact (congrArg Units.val hR1).symm
  constructor
  · rw [hR0']
    exact a.f1_rotate _
  · calc
      a.f2 (currentCoefficientRatio2OfSquareRefinement
          h.squareRefinement : SevenRealCubicInt) =
          a.f2 (rotateEquiv (currentCoefficientRatio1OfSquareRefinement
            h.squareRefinement : SevenRealCubicInt)) :=
        congrArg a.f2 hR1'
      _ = a.f2 (rotateEquiv (rotateEquiv
          (currentCoefficientRatio0OfSquareRefinement
            h.squareRefinement : SevenRealCubicInt))) := by rw [hR0']
      _ = a.f0 (currentCoefficientRatio0OfSquareRefinement
          h.squareRefinement : SevenRealCubicInt) := a.f2_rotate_twice _

theorem currentCommonPrime_transported_rhs_product
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentOrientedGapPrimeTransport h q) :
    a.f0 (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) *
        a.f1 (currentCoefficientRatio1OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) *
        a.f2 (currentCoefficientRatio2OfSquareRefinement h.squareRefinement :
          SevenRealCubicInt) =
      a.f0 (currentCoefficientRatio0OfSquareRefinement h.squareRefinement :
        SevenRealCubicInt) ^ 3 := by
  rcases currentCommonPrime_fourteen_phase_collapse a with ⟨h1, h2⟩
  rw [h1, h2]
  ring

end SevenRealCubic
end
end DkMath.FLT.Seven
