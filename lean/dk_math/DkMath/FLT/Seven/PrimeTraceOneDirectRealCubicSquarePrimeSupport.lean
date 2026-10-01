/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareTwistObstruction

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 500000

/-! ## Square-root coprimality and scalar support -/

theorem directOrbitSquareRefinement_squareRoots_isCoprime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    IsCoprime t.gapSquareRoot t.quotientSquareRoot := by
  have hroots :
      IsCoprime
        ((t.gapSquareUnit : SevenRealCubicInt) * t.gapSquareRoot ^ 2)
        ((t.quotientSquareUnit : SevenRealCubicInt) *
          t.quotientSquareRoot ^ 2) := by
    simpa [t.gapRoot_eq, t.quotientRoot_eq] using t.roots_isCoprime
  have hpow :
      IsCoprime (t.gapSquareRoot ^ 2) (t.quotientSquareRoot ^ 2) :=
    (isCoprime_mul_units_left t.gapSquareUnit.isUnit
      t.quotientSquareUnit.isUnit
      (t.gapSquareRoot ^ 2) (t.quotientSquareRoot ^ 2)).mp hroots
  exact
    (IsCoprime.pow_iff (m := 2) (n := 2)
      (by norm_num) (by norm_num)).mp hpow

theorem directOrbitSquareRefinement_squareRoots_associated_scalar
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Associated
      (t.gapSquareRoot * t.quotientSquareRoot)
      (t.powerSplit.gapSplit.a : SevenRealCubicInt) := by
  let uSquares : SevenRealCubicIntˣ :=
    t.gapSquareUnit * t.quotientSquareUnit
  have hsquare :
      (uSquares : SevenRealCubicInt) *
          (t.gapSquareRoot * t.quotientSquareRoot) ^ 2 =
        (t.rootProductUnit : SevenRealCubicInt) *
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) ^ 2 := by
    calc
      (uSquares : SevenRealCubicInt) *
          (t.gapSquareRoot * t.quotientSquareRoot) ^ 2 =
          t.powerSplit.gapRoot * t.powerSplit.quotientRoot := by
            rw [t.gapRoot_eq, t.quotientRoot_eq]
            dsimp [uSquares]
            ring
      _ = (t.rootProductUnit : SevenRealCubicInt) *
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) ^ 2 :=
        t.rootProduct_eq
  have hsquare_assoc :
      Associated
        ((t.gapSquareRoot * t.quotientSquareRoot) ^ 2)
        ((t.powerSplit.gapSplit.a : SevenRealCubicInt) ^ 2) := by
    exact
      (associated_unit_mul_left
          ((t.gapSquareRoot * t.quotientSquareRoot) ^ 2)
          (uSquares : SevenRealCubicInt) uSquares.isUnit).symm |>.trans
        ((Associated.of_eq hsquare).trans
          (associated_unit_mul_left
            ((t.powerSplit.gapSplit.a : SevenRealCubicInt) ^ 2)
            (t.rootProductUnit : SevenRealCubicInt)
            t.rootProductUnit.isUnit))
  exact
    (Associated.pow_iff (n := 2) (by norm_num)).mp hsquare_assoc

theorem directOrbitSquareRefinement_squareRoots_unit_split
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ∃ u : SevenRealCubicIntˣ,
      t.gapSquareRoot * t.quotientSquareRoot =
        (u : SevenRealCubicInt) *
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) := by
  rcases directOrbitSquareRefinement_squareRoots_associated_scalar t with
    ⟨u, hu⟩
  refine ⟨u⁻¹, ?_⟩
  have hunit :
      (u : SevenRealCubicInt) *
          ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) = 1 := by
    rw [← Units.val_mul]
    simp
  calc
    t.gapSquareRoot * t.quotientSquareRoot =
        (t.gapSquareRoot * t.quotientSquareRoot) * 1 := by simp
    _ = (t.gapSquareRoot * t.quotientSquareRoot) *
          ((u : SevenRealCubicInt) *
            ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)) := by
            rw [hunit]
    _ = (t.gapSquareRoot * t.quotientSquareRoot *
          (u : SevenRealCubicInt)) *
          ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) := by ring
    _ = (t.powerSplit.gapSplit.a : SevenRealCubicInt) *
          ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) := by rw [hu]
    _ = ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt) *
          (t.powerSplit.gapSplit.a : SevenRealCubicInt) := by rw [mul_comm]

/-! ## Norm compatibility and the positive second factor -/

theorem directOrbitSquareRefinement_squareRoots_norm_product
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Int.natAbs (norm t.gapSquareRoot) *
        Int.natAbs (norm t.quotientSquareRoot) =
      t.powerSplit.gapSplit.a ^ 3 :=
  directOrbitSquareRefinement_squareRoots_norm_mul_eq_cube t

theorem directOrbitSquareRefinement_quotient_square_norm_pos
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    0 < Int.natAbs (norm t.quotientSquareRoot) := by
  have hprod :
      0 < Int.natAbs (norm t.gapSquareRoot) *
        Int.natAbs (norm t.quotientSquareRoot) := by
    rw [directOrbitSquareRefinement_squareRoots_norm_product t]
    exact pow_pos t.powerSplit.gapSplit.a_pos 3
  by_contra hs
  have hs0 : Int.natAbs (norm t.quotientSquareRoot) = 0 :=
    Nat.eq_zero_of_not_pos hs
  rw [hs0, Nat.mul_zero] at hprod
  omega

/-! ## The ramified axis is absent from both square roots -/

theorem directOrbitSquareRefinement_gapSquareRoot_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬eisensteinAxis ∣ t.gapSquareRoot := by
  intro h
  apply directOrbit_gapRoot_not_axis_dvd t.powerSplit
  rw [t.gapRoot_eq]
  exact dvd_mul_of_dvd_right
    (h.trans (dvd_pow_self t.gapSquareRoot (by norm_num))) _

private theorem not_axis_dvd_of_unit_pow_square
    {root square core : SevenRealCubicInt}
    (u v : SevenRealCubicIntˣ)
    (hcore : ¬eisensteinAxis ∣ core)
    (hcore_eq : core = (u : SevenRealCubicInt) * root ^ 7)
    (hroot_eq : root = (v : SevenRealCubicInt) * square ^ 2) :
    ¬eisensteinAxis ∣ square := by
  intro h
  apply hcore
  rw [hcore_eq, hroot_eq]
  rw [mul_pow]
  have hpow : eisensteinAxis ∣ square ^ (2 * 7) :=
    h.trans (dvd_pow_self square (by decide : 2 * 7 ≠ 0))
  rw [← pow_mul]
  exact dvd_mul_of_dvd_right
    (dvd_mul_of_dvd_right hpow _) _

theorem directOrbitSquareRefinement_quotientSquareRoot_not_axis_dvd
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    ¬eisensteinAxis ∣ t.quotientSquareRoot :=
  not_axis_dvd_of_unit_pow_square
    t.powerSplit.quotientUnit t.quotientSquareUnit
    t.powerSplit.quotientCore_not_axis_dvd
    t.powerSplit.quotientCore_eq t.quotientRoot_eq

end
end DkMath.FLT.Seven
