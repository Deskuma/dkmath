/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.Lib.NumberTheory.FreyLocalValuationSubring
import DkMath.Lib.NumberTheory.ValuationRationalPrimeSupport
import DkMath.Lib.NumberTheory.EllipticSmoothReduction
import DkMath.Lib.NumberTheory.EllipticBaseChangeTorsion
import DkMath.Lib.NumberTheory.WeierstrassVariableChangeGalois

#print "file: DkMath.Lib.NumberTheory.EllipticRationalLocalTransport"

/-!
# Rational zero-component conditions at extension valuations

All valuations above a fixed rational prime agree on membership of rational
numbers: the reduced denominator detects integrality.  Nonunit membership
follows from `r = 0 ∨ r⁻¹ ∉ A`.  Applied to the two partial derivatives of
the same integer Weierstrass model, these facts preserve and reflect smooth
reduction of a rational point under base change.

This is a transport theorem, independent of finite-residue point counts.
In particular the algebraic-closure residue field is never identified with
`ZMod q`.
-/

namespace DkMath.Lib.NumberTheory.EllipticRationalLocalTransport

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory
open EllipticGoodReductionSeparation EllipticTorsionRepresentation
noncomputable section

variable {K : Type*} [Field K] [CharZero K]
omit [CharZero K] in
/-- For coordinates satisfying the generic equation, smooth reduction is
precisely the failure of both partial derivatives to lie in the maximal ideal.
The nonintegral-coordinate branches stay vacuous as in `SmoothCoordinates`. -/
theorem smoothCoordinates_iff_partials {A : ValuationSubring K}
    (W : WeierstrassCurve A) {x y : K}
    (he : (W.map A.subtype).toAffine.Equation x y) :
    SmoothCoordinates W x y ↔ ∀ (_ : x ∈ A) (_ : y ∈ A),
      (W.a₁ : K) * y - (3 * x ^ 2 + 2 * (W.a₂ : K) * x + (W.a₄ : K)) ∉ A.nonunits ∨
        2 * y + (W.a₁ : K) * x + (W.a₃ : K) ∉ A.nonunits := by
  unfold SmoothCoordinates
  apply forall_congr'
  intro hx
  apply forall_congr'
  intro hy
  rw [nonsingular_iff']
  have hred := equation_residue W (x := ⟨x,hx⟩) (y := ⟨y,hy⟩) he
  rw [and_iff_right hred]
  have hfx : residue A (W.a₁ * ⟨y,hy⟩ -
      (3 * (⟨x,hx⟩ : A) ^ 2 + 2 * W.a₂ * ⟨x,hx⟩ + W.a₄)) =
      (W.map (residue A)).a₁ * residue A ⟨y,hy⟩ -
        (3 * residue A (⟨x,hx⟩ : A) ^ 2 + 2 * (W.map (residue A)).a₂ *
          residue A ⟨x,hx⟩ + (W.map (residue A)).a₄) := by
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_a₁, map_a₂, map_a₄]
  have hfy : residue A (2 * (⟨y,hy⟩ : A) + W.a₁ * ⟨x,hx⟩ + W.a₃) =
      2 * residue A (⟨y,hy⟩ : A) + (W.map (residue A)).a₁ *
        residue A ⟨x,hx⟩ + (W.map (residue A)).a₃ := by
    simp only [map_add, map_mul, map_ofNat, map_a₁, map_a₃]
  change ((W.map (residue A)).a₁ * residue A ⟨y,hy⟩ -
    (3 * residue A (⟨x,hx⟩ : A) ^ 2 + 2 * (W.map (residue A)).a₂ *
      residue A ⟨x,hx⟩ + (W.map (residue A)).a₄) ≠ 0 ∨
    2 * residue A (⟨y,hy⟩ : A) + (W.map (residue A)).a₁ *
      residue A ⟨x,hx⟩ + (W.map (residue A)).a₃ ≠ 0) ↔ _
  rw [← hfx, ← hfy]
  have hx0 (a : A) : residue A a = 0 ↔ (a : K) ∈ A.nonunits := by
    rw [residue_eq_zero_iff, ValuationSubring.coe_mem_nonunits_iff]
  simp only [ne_eq, hx0]
  rfl

/-- Nonunit membership of a rational number is independent of the chosen
extension valuation above a fixed rational prime.  Only rational integrality
and the inverse criterion for a valuation ring are used. -/
theorem ratCast_nonunits_iff (A : ValuationSubring K) (B : ValuationSubring ℚ)
    {q : ℕ} (hq : q.Prime) (hA : ValuationInertia.LiesOverPrime A q)
    (hB : ValuationInertia.LiesOverPrime B q) (r : ℚ) :
    (r : K) ∈ A.nonunits ↔ r ∈ B.nonunits := by
  have hm : r⁻¹ ∈ B ↔ ¬ q ∣ r⁻¹.den := by
    simpa using ValuationRationalPrimeSupport.ratCast_mem_iff B hq
      ((ValuationSubring.mem_nonunits_iff B).mp hB) r⁻¹
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ← Rat.cast_inv,
    ValuationRationalPrimeSupport.ratCast_mem_iff A hq ((ValuationSubring.mem_nonunits_iff A).mp hA),
    hm]
  simp only [Rat.cast_eq_zero]

/-- Smooth coordinates on an integer model are preserved and reflected by
extension to any valuation ring over the same rational prime. -/
theorem smoothCoordinates_integer_baseChange_iff
    (W : WeierstrassCurve ℤ) (B : ValuationSubring ℚ)
    (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hB : ValuationInertia.LiesOverPrime B q) (hA : ValuationInertia.LiesOverPrime A q)
    {x y : ℚ} (he : (W.map (Int.castRingHom ℚ)).toAffine.Equation x y) :
    SmoothCoordinates (W.map (Int.castRingHom A)) (x : K) (y : K) ↔
      SmoothCoordinates (W.map (Int.castRingHom B)) x y := by
  have hAB (r : ℚ) : (r : K) ∈ A ↔ r ∈ B := by
    have h := ValuationRationalPrimeSupport.ratCast_mem_iff B hq
      ((ValuationSubring.mem_nonunits_iff B).mp hB) r
    simpa only [Rat.cast_id] using
      (ValuationRationalPrimeSupport.ratCast_mem_iff A hq
        ((ValuationSubring.mem_nonunits_iff A).mp hA) r).trans h.symm
  have heB : ((W.map (Int.castRingHom B)).map B.subtype).toAffine.Equation x y := by
    simpa only [equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      Int.coe_castRingHom, map_intCast] using (show _ from (equation_iff x y).mp he)
  have heA : ((W.map (Int.castRingHom A)).map A.subtype).toAffine.Equation (x:K) (y:K) := by
    have hm := he.map (Rat.castHom K)
    simpa only [equation_iff, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      RingHom.coe_comp, Function.comp_apply, Int.coe_castRingHom, Rat.cast_intCast,
      map_intCast, Rat.coe_castHom] using (show _ from (equation_iff (x:K) (y:K)).mp hm)
  rw [smoothCoordinates_iff_partials _ heA, smoothCoordinates_iff_partials _ heB]
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, Int.coe_castRingHom,
    SubringClass.coe_intCast]
  have hfx : (W.a₁ : K) * (y : K) -
      (3 * (x : K) ^ 2 + 2 * (W.a₂ : K) * (x : K) + (W.a₄ : K)) =
      (((W.a₁ : ℚ) * y - (3 * x ^ 2 + 2 * (W.a₂ : ℚ) * x + (W.a₄ : ℚ)) : ℚ) : K) := by
    push_cast
    rfl
  have hfy : 2 * (y : K) + (W.a₁ : K) * (x : K) + (W.a₃ : K) =
      ((2 * y + (W.a₁ : ℚ) * x + (W.a₃ : ℚ) : ℚ) : K) := by
    push_cast
    rfl
  rw [hfx, hfy]
  simp only [hAB, ratCast_nonunits_iff A B hq hA hB]

/-- A rational point has smooth reduction exactly when its base change does
at any extension valuation above the same prime.  No finiteness of the
extension residue field is asserted or used. -/
theorem hasSmoothReduction_integer_baseChange_iff
    (W : WeierstrassCurve ℤ) (B : ValuationSubring ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hB : ValuationInertia.LiesOverPrime B q) (hA : ValuationInertia.LiesOverPrime A q)
    (P : (W.map (Int.castRingHom ℚ)).toAffine.Point) :
    HasSmoothReduction (W.map (Int.castRingHom A))
        (baseChangePoint (W.map (Int.castRingHom ℚ)) P) ↔
      HasSmoothReduction (W.map (Int.castRingHom B)) P := by
  cases P with
  | zero => exact iff_of_true (hasSmoothReduction_zero _ _) (hasSmoothReduction_zero _ _)
  | some x y h =>
    have hbar := ((W.map (Int.castRingHom ℚ)).toAffine.baseChange_nonsingular
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
      (algebraMap ℚ (AlgebraicClosure ℚ)).injective x y).mpr h
    have hp : baseChangePoint (W.map (Int.castRingHom ℚ)) (.some x y h) =
        .some (x : AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ) hbar := rfl
    rw [hp]
    exact (hasSmoothReduction_some_iff _ hbar).trans
      ((smoothCoordinates_integer_baseChange_iff W B A hq hB hA h.1).trans
        (hasSmoothReduction_some_iff _ h).symm)

/-- Changing the generic model by an equality leaves smooth reduction
unchanged: the point transport preserves the coordinates. -/
theorem hasSmoothReduction_pointEquivOfModelEq
    {F : Type*} [Field F] [DecidableEq F] {A : ValuationSubring F}
    (W : WeierstrassCurve A) {U V : WeierstrassCurve F} (h : U = V)
    (P : U.toAffine.Point) :
    HasSmoothReduction W (WeierstrassVariableChange.pointEquivOfModelEq h P) ↔
      HasSmoothReduction W P := by
  subst V
  rfl

/-- The smooth-reduction predicate has the explicit zero-or-affine formula
used by the external `InZeroComponentAt` API.  Integrality of `y` follows from
the same integral equation when `x` is integral, including in residue
characteristics two and three. -/
theorem hasSmoothReduction_iff_zero_or_exists
    {F : Type*} [Field F] {A : ValuationSubring F}
    (W : WeierstrassCurve A) (E : WeierstrassCurve F) (hmodel : W.map A.subtype = E)
    (P : E.toAffine.Point) :
    HasSmoothReduction W P ↔ P = 0 ∨
      ∃ (x y : F) (h : E.toAffine.Nonsingular x y),
        P = .some x y h ∧ (x ∉ A ∨ ∃ (hx : x ∈ A) (hy : y ∈ A),
          (W.map (residue A)).toAffine.Nonsingular
            (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)) := by
  classical
  cases P with
  | zero => exact iff_of_true (hasSmoothReduction_zero W E) (Or.inl rfl)
  | some x y h =>
    constructor
    · intro hs
      refine Or.inr ⟨x, y, h, rfl, ?_⟩
      by_cases hx : x ∈ A
      · have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W E hmodel h.1 hx
        exact Or.inr ⟨hx, hy, (hasSmoothReduction_some_iff W h).mp hs hx hy⟩
      · exact Or.inl hx
    · rintro (hz | ⟨x', y', h', heq, hs⟩)
      · exact (Point.some_ne_zero h hz).elim
      · obtain ⟨rfl, rfl⟩ := Point.some.inj heq
        apply (hasSmoothReduction_some_iff W h).mpr
        intro hx hy
        rcases hs with hn | ⟨hx', hy', hns⟩
        · exact (hn hx).elim
        · exact hns

omit [CharZero K] in
/-- Residue invariants of the integer model at a prime address are exactly
the corresponding integer divisibility conditions. -/
theorem integer_residue_invariants_iff
    (W : WeierstrassCurve ℤ) (A : ValuationSubring K) {q : ℕ} (hq : q.Prime)
    (hA : ValuationInertia.LiesOverPrime A q) :
    (((W.map (Int.castRingHom A)).map (residue A)).Δ = 0 ∧
      ((W.map (Int.castRingHom A)).map (residue A)).c₄ ≠ 0) ↔
      (q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄ := by
  let : CharP (ResidueField A) q := ValuationPrimeSupport.charP_residueField A hq hA
  simp only [map_Δ, map_c₄, Int.coe_castRingHom, map_intCast,
    ne_eq, CharP.intCast_eq_zero_iff (ResidueField A) q]

/-- The concrete rational valuation subring supplies the base address
internally.  This is the local-input transport used at both `2` and `3`. -/
theorem hasSmoothReduction_localValuationSubring_baseChange_iff
    (W : WeierstrassCurve ℤ) {q : ℕ} [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ValuationInertia.LiesOverPrime A q)
    (P : (W.map (Int.castRingHom ℚ)).toAffine.Point) :
    HasSmoothReduction (W.map (Int.castRingHom A))
        (baseChangePoint (W.map (Int.castRingHom ℚ)) P) ↔
      HasSmoothReduction (W.map (Int.castRingHom (FreyLocalReduction.localValuationSubring q)))
        P :=
  hasSmoothReduction_integer_baseChange_iff W _ A (Fact.out : q.Prime)
    (FreyLocalReduction.localValuationSubring_liesOverPrime q) hA P

end
end DkMath.Lib.NumberTheory.EllipticRationalLocalTransport
