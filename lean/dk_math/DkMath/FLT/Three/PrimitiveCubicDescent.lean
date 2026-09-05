/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Three.EisensteinDescentFactors

#print "file: DkMath.FLT.Three.PrimitiveCubicDescent"

namespace DkMath.FLT.Three

/-!
# Positive strict descent for primitive cubic solutions

This module reconstructs the positive primitive cubic solution carried by the
signed Eisenstein factors.  It stops at the strict product decrease; the
well-founded closure is the responsibility of the following checkpoint.
-/

/-- A positive primitive solution of the cubic equation. -/
structure PrimitiveCubicPack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  coprime_xy : Nat.Coprime x y
  equation : x ^ 3 + y ^ 3 = z ^ 3

/-- Package the hypotheses used by the Eisenstein descent tower. -/
theorem primitiveCubicPack_of_hypotheses
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hEq : a ^ 3 + b ^ 3 = c ^ 3) :
    PrimitiveCubicPack a b c :=
  { hx := ha
    hy := hb
    hz := hc
    coprime_xy := hab
    equation := hEq }

/-- The product measure used by the strict descent. -/
def primitiveCubicMeasure
    {x y z : ℕ} (_ : PrimitiveCubicPack x y z) : ℕ :=
  x * y * z

/-- Recover the signed cube from its natural absolute value. -/
theorem int_eq_cube_or_neg_cube_of_natAbs_eq
    {x : ℤ} {n : ℕ} (h : x.natAbs = n ^ 3) :
    x = (n : ℤ) ^ 3 ∨ x = -((n : ℤ) ^ 3) := by
  by_cases hx : 0 ≤ x
  · left
    calc
      x = (x.natAbs : ℤ) := Int.eq_natAbs_of_nonneg hx
      _ = ((n ^ 3 : ℕ) : ℤ) := by rw [h]
      _ = (n : ℤ) ^ 3 := by rw [Nat.cast_pow]
  · right
    have hxle : x ≤ 0 := le_of_not_ge hx
    have hnat : (x.natAbs : ℤ) = -x :=
      Int.ofNat_natAbs_of_nonpos hxle
    calc
      x = -(x.natAbs : ℤ) := by linarith
      _ = -((n ^ 3 : ℕ) : ℤ) := by rw [h]
      _ = -((n : ℤ) ^ 3) := by rw [Nat.cast_pow]

private theorem int_eq_pos_cube_of_natAbs_eq
    {x : ℤ} {n : ℕ} (hx : 0 < x) (h : x.natAbs = n ^ 3) :
    x = (n : ℤ) ^ 3 := by
  rcases int_eq_cube_or_neg_cube_of_natAbs_eq h with hpos | hneg
  · exact hpos
  · have hnonneg : 0 ≤ (n : ℤ) ^ 3 := by positivity
    linarith

private theorem int_eq_neg_cube_of_natAbs_eq
    {x : ℤ} {n : ℕ} (hx : x < 0) (h : x.natAbs = n ^ 3) :
    x = -((n : ℤ) ^ 3) := by
  rcases int_eq_cube_or_neg_cube_of_natAbs_eq h with hpos | hneg
  · have hnonneg : 0 ≤ (n : ℤ) ^ 3 := by positivity
    linarith
  · exact hneg

private theorem signed_cube_roots_route_of_factors
    {a b c : ℕ} (p : EisensteinSignedCubeFactors a b c) :
    (p.R ^ 3 + p.S ^ 3 = p.T ^ 3) ∨
      (p.R ^ 3 + p.T ^ 3 = p.S ^ 3) ∨
        (p.S ^ 3 + p.T ^ 3 = p.R ^ 3) := by
  have hprod : 0 < p.source.r * p.source.s * (p.source.r + p.source.s) := by
    rw [p.source.product_eq]
    exact_mod_cast (pow_pos p.source.A_pos 3)
  have hr : 0 < p.source.r ∨ p.source.r < 0 :=
    lt_or_gt_of_ne (Ne.symm p.source.r_ne_zero)
  have hs : 0 < p.source.s ∨ p.source.s < 0 :=
    lt_or_gt_of_ne (Ne.symm p.source.s_ne_zero)
  rcases hr with hrpos | hrneg
  · rcases hs with hspos | hsneg
    · left
      have hsumpos : 0 < p.source.r + p.source.s := add_pos hrpos hspos
      have hR : p.source.r = (p.R : ℤ) ^ 3 :=
        int_eq_pos_cube_of_natAbs_eq hrpos p.abs_r_eq
      have hS : p.source.s = (p.S : ℤ) ^ 3 :=
        int_eq_pos_cube_of_natAbs_eq hspos p.abs_s_eq
      have hT : p.source.r + p.source.s = (p.T : ℤ) ^ 3 := by
        exact int_eq_pos_cube_of_natAbs_eq hsumpos p.abs_sum_eq
      have hEq : (p.R : ℤ) ^ 3 + (p.S : ℤ) ^ 3 = (p.T : ℤ) ^ 3 := by
        linarith [hR, hS, hT]
      exact_mod_cast hEq
    · right
      left
      have hsumneg : p.source.r + p.source.s < 0 := by
        rcases lt_or_gt_of_ne p.source.sum_ne_zero with hneg | hpos
        · exact hneg
        · have hrs : p.source.r * p.source.s < 0 :=
            mul_neg_of_pos_of_neg hrpos hsneg
          have hbad : p.source.r * p.source.s *
              (p.source.r + p.source.s) < 0 :=
            mul_neg_of_neg_of_pos hrs hpos
          linarith
      have hR : p.source.r = (p.R : ℤ) ^ 3 :=
        int_eq_pos_cube_of_natAbs_eq hrpos p.abs_r_eq
      have hS : p.source.s = -((p.S : ℤ) ^ 3) :=
        int_eq_neg_cube_of_natAbs_eq hsneg p.abs_s_eq
      have hT : p.source.r + p.source.s = -((p.T : ℤ) ^ 3) := by
        exact int_eq_neg_cube_of_natAbs_eq hsumneg p.abs_sum_eq
      have hEq : (p.R : ℤ) ^ 3 + (p.T : ℤ) ^ 3 = (p.S : ℤ) ^ 3 := by
        linarith [hR, hS, hT]
      exact_mod_cast hEq
  · rcases hs with hspos | hsneg
    · right
      right
      have hsumneg : p.source.r + p.source.s < 0 := by
        rcases lt_or_gt_of_ne p.source.sum_ne_zero with hneg | hpos
        · exact hneg
        · have hrs : p.source.r * p.source.s < 0 :=
            mul_neg_of_neg_of_pos hrneg hspos
          have hbad : p.source.r * p.source.s *
              (p.source.r + p.source.s) < 0 :=
            mul_neg_of_neg_of_pos hrs hpos
          linarith
      have hR : p.source.r = -((p.R : ℤ) ^ 3) :=
        int_eq_neg_cube_of_natAbs_eq hrneg p.abs_r_eq
      have hS : p.source.s = (p.S : ℤ) ^ 3 :=
        int_eq_pos_cube_of_natAbs_eq hspos p.abs_s_eq
      have hT : p.source.r + p.source.s = -((p.T : ℤ) ^ 3) := by
        exact int_eq_neg_cube_of_natAbs_eq hsumneg p.abs_sum_eq
      have hEq : (p.S : ℤ) ^ 3 + (p.T : ℤ) ^ 3 = (p.R : ℤ) ^ 3 := by
        linarith [hR, hS, hT]
      exact_mod_cast hEq
    · have hsumneg : p.source.r + p.source.s < 0 := add_neg hrneg hsneg
      have hrs : 0 < p.source.r * p.source.s :=
        mul_pos_of_neg_of_neg hrneg hsneg
      have hbad : p.source.r * p.source.s *
          (p.source.r + p.source.s) < 0 :=
        mul_neg_of_pos_of_neg hrs hsumneg
      linarith

/-- The three positive cube equations forced by the signed factors. -/
theorem signed_cube_roots_route
    {a b c : ℕ} (p : EisensteinSignedCubeFactors a b c) :
    (p.R ^ 3 + p.S ^ 3 = p.T ^ 3) ∨
      (p.R ^ 3 + p.T ^ 3 = p.S ^ 3) ∨
        (p.S ^ 3 + p.T ^ 3 = p.R ^ 3) :=
  signed_cube_roots_route_of_factors p

/-- A strict descent packet retaining the source and its same-source factors. -/
structure PrimitiveCubicStrictDescent (a b c : ℕ) : Type where
  source : PrimitiveCubicPack a b c
  factors : EisensteinSignedCubeFactors a b c
  x : ℕ
  y : ℕ
  z : ℕ
  next : PrimitiveCubicPack x y z
  next_product_eq : x * y * z = factors.source.A
  measure_lt : x * y * z < a * b * c

private theorem primitiveCubicStrictDescent_nonempty
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    Nonempty (PrimitiveCubicStrictDescent a b c) := by
  let factors := eisensteinSignedCubeFactors_of_primitive_solution
    source.hx source.hy source.hz source.coprime_xy source.equation
  rcases signed_cube_roots_route factors with hP | hL | hR
  · let next : PrimitiveCubicPack factors.R factors.S factors.T :=
      { hx := factors.R_pos
        hy := factors.S_pos
        hz := factors.T_pos
        coprime_xy := factors.coprime_RS
        equation := hP }
    exact ⟨{
      source := source
      factors := factors
      x := factors.R
      y := factors.S
      z := factors.T
      next := next
      next_product_eq := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          factors.root_product_eq
      measure_lt := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          factors.strict_product_lt source.hx source.hy source.hz }⟩
  · let next : PrimitiveCubicPack factors.R factors.T factors.S :=
      { hx := factors.R_pos
        hy := factors.T_pos
        hz := factors.S_pos
        coprime_xy := factors.coprime_RT
        equation := hL }
    exact ⟨{
      source := source
      factors := factors
      x := factors.R
      y := factors.T
      z := factors.S
      next := next
      next_product_eq := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          factors.root_product_eq
      measure_lt := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          factors.strict_product_lt source.hx source.hy source.hz }⟩
  · let next : PrimitiveCubicPack factors.S factors.T factors.R :=
      { hx := factors.S_pos
        hy := factors.T_pos
        hz := factors.R_pos
        coprime_xy := factors.coprime_ST
        equation := hR }
    exact ⟨{
      source := source
      factors := factors
      x := factors.S
      y := factors.T
      z := factors.R
      next := next
      next_product_eq := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          factors.root_product_eq
      measure_lt := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          factors.strict_product_lt source.hx source.hy source.hz }⟩

/-- Choose the strict descent packet produced from one primitive source. -/
noncomputable def primitiveCubicStrictDescent
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    PrimitiveCubicStrictDescent a b c :=
  Classical.choice (primitiveCubicStrictDescent_nonempty source)

/-- Every primitive positive cubic solution has a smaller one in product measure. -/
theorem exists_smaller_primitiveCubicPack
    {a b c : ℕ} (source : PrimitiveCubicPack a b c) :
    ∃ x y z : ℕ,
      PrimitiveCubicPack x y z ∧ x * y * z < a * b * c := by
  let descent := primitiveCubicStrictDescent source
  exact ⟨descent.x, descent.y, descent.z, descent.next, descent.measure_lt⟩

end DkMath.FLT.Three
