/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNProductDegree
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

#print "file: DkMath.NumberTheory.GapFocusing.Phase"

/-!
# The focused cyclotomic phase factors

An integral domain containing a primitive `d`th root supplies all `d`
distinct phases. Focusing translates their linear factors to
`x + (1 - ζ) * u`. The phase `ζ = 1` is characterized by independence
from the parameter `u`; this is a universal statement, not a claim
about accidental equality at a single value such as `u = 0`.
-/

namespace DkMath.NumberTheory.GapFocusing

open scoped BigOperators Polynomial

/-- Universal independence of `u` singles out exactly the trivial phase. -/
theorem phaseFactor_eq_gap_forall_iff {R : Type*} [CommRing R] (x ζ : R) :
    (∀ u : R, x + (1 - ζ) * u = x) ↔ ζ = 1 := by
  constructor
  · intro h
    have hzero : 1 - ζ = 0 := by
      simpa only [mul_one, add_eq_left] using h 1
    exact (sub_eq_zero.mp hzero).symm
  · rintro rfl
    intro u
    simp

/-- Polynomial dependence on the parameter gives the same criterion. -/
theorem phaseFactor_polynomial_eq_gap_iff {R : Type*} [CommRing R] (x ζ : R) :
    (Polynomial.C x + Polynomial.C (1 - ζ) * Polynomial.X : R[X]) =
      Polynomial.C x ↔ ζ = 1 := by
  constructor
  · intro h
    have hzero := congrArg (fun P : R[X] => P.coeff 1) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero,
      ↓reduceIte, Polynomial.coeff_C_mul_X, zero_add] at hzero
    exact (sub_eq_zero.mp hzero).symm
  · rintro rfl
    simp

section SplitPhases

variable {R : Type*} [CommRing R] [IsDomain R] {d : ℕ} {ζ : R}

/-- The full, distinct phase product after Gap focusing. -/
theorem focused_pow_sub_pow_eq_prod (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (x u : R) :
    (x + u) ^ d - u ^ d =
      ∏ ξ ∈ Polynomial.nthRootsFinset d (1 : R), (x + (1 - ξ) * u) := by
  classical
  rw [hζ.pow_sub_pow_eq_prod_sub_mul (x + u) u hd]
  apply Finset.prod_congr rfl
  intro ξ hξ
  ring

open Classical in
/-- Powers of a primitive root enumerate exactly the full phase carrier. -/
theorem nthRootsFinset_eq_powers (hζ : IsPrimitiveRoot ζ d) :
    Polynomial.nthRootsFinset d (1 : R) =
      (Finset.range d).image (fun i => ζ ^ i) := by
  classical
  simp only [Polynomial.nthRootsFinset, hζ.nthRoots_eq (one_pow d), mul_one,
    Multiset.toFinset_map, Multiset.toFinset_range]

/-- A primitive-root enumeration version of the focused factorization. -/
theorem focused_pow_sub_pow_eq_prod_range (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (x u : R) :
    (x + u) ^ d - u ^ d =
      ∏ i ∈ Finset.range d, (x + (1 - ζ ^ i) * u) := by
  classical
  rw [focused_pow_sub_pow_eq_prod hd hζ, nthRootsFinset_eq_powers hζ,
    Finset.prod_image]
  intro i hi j hj hij
  exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij

/-- The finite phase enumeration has exactly `d` factors. -/
theorem focused_pow_sub_pow_eq_prod_fin (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (x u : R) :
    (x + u) ^ d - u ^ d = ∏ i : Fin d, (x + (1 - ζ ^ (i : ℕ)) * u) := by
  calc
    _ = ∏ i ∈ Finset.range d, (x + (1 - ζ ^ i) * u) :=
      focused_pow_sub_pow_eq_prod_range hd hζ x u
    _ = _ := (Fin.prod_univ_eq_prod_range (fun i => x + (1 - ζ ^ i) * u) d).symm

omit [IsDomain R] in
/-- Among the enumerated phases, precisely index zero forgets `u`. -/
theorem indexed_phase_eq_gap_forall_iff (hζ : IsPrimitiveRoot ζ d) (x : R)
    (i : Fin d) :
    (∀ u : R, x + (1 - ζ ^ (i : ℕ)) * u = x) ↔ (i : ℕ) = 0 := by
  rw [phaseFactor_eq_gap_forall_iff]
  constructor
  · intro h
    exact Nat.eq_zero_of_dvd_of_lt (hζ.dvd_of_pow_eq_one _ h) i.isLt
  · intro hi
    simp [hi]

/-- At a nonzero parameter in a domain the same uniqueness holds pointwise. -/
theorem phaseFactor_eq_gap_iff_of_ne_zero (x ξ u : R) (hu : u ≠ 0) :
    x + (1 - ξ) * u = x ↔ ξ = 1 := by
  rw [add_eq_left, mul_eq_zero, or_iff_left hu, sub_eq_zero, eq_comm]

/-- Removing the trivial phase gives precisely the existing `GN` kernel.
The identity holds also at zero gap: cancellation is performed in `R[X]`
before evaluation, never at the value `x`. -/
theorem GN_eq_nontrivial_phase_prod_range (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (x u : R) :
    DkMath.CosmicFormula.GTail d 1 x u =
      ∏ i ∈ (Finset.range d).erase 0, (x + (1 - ζ ^ i) * u) := by
  classical
  have hC : IsPrimitiveRoot (Polynomial.C ζ : R[X]) d :=
    hζ.map_of_injective Polynomial.C_injective
  have hfull := focused_pow_sub_pow_eq_prod_range hd hC
    (Polynomial.X : R[X]) (Polynomial.C u)
  rw [← Finset.mul_prod_erase (Finset.range d)
    (fun i => Polynomial.X + (1 - Polynomial.C ζ ^ i) * Polynomial.C u)
    (Finset.mem_range.mpr hd)] at hfull
  simp only [pow_zero, sub_self, zero_mul, add_zero] at hfull
  have hGN := DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap d
    (Polynomial.X : R[X]) (Polynomial.C u)
  have hmul : Polynomial.X *
      DkMath.CosmicFormula.GTail d 1 Polynomial.X (Polynomial.C u) =
      Polynomial.X * ∏ i ∈ (Finset.range d).erase 0,
        (Polynomial.X + (1 - Polynomial.C ζ ^ i) * Polynomial.C u) := by
    calc
      _ = (Polynomial.X + Polynomial.C u) ^ d - Polynomial.C u ^ d := by
        rw [hGN, add_sub_cancel_right]
      _ = _ := hfull
  have hpol := mul_left_cancel₀ (Polynomial.X_ne_zero (R := R)) hmul
  have heval := congrArg (Polynomial.evalRingHom x) hpol
  simpa [DkMath.CosmicFormula.map_GN] using heval

open Classical in
/-- Removing the trivial root agrees with removing index zero from the enumeration. -/
theorem nontrivialRootsFinset_eq_powers (hζ : IsPrimitiveRoot ζ d) :
    (Polynomial.nthRootsFinset d (1 : R)).erase 1 =
      ((Finset.range d).erase 0).image (fun i => ζ ^ i) := by
  classical
  rw [nthRootsFinset_eq_powers hζ]
  ext ξ
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hne, i, hi, rfl⟩
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    intro hi0
    apply hne
    simp [hi0]
  · rintro ⟨i, ⟨hi0, hi⟩, rfl⟩
    exact ⟨hζ.pow_ne_one_of_pos_of_lt hi0 (Finset.mem_range.mp hi), i, hi, rfl⟩

open Classical in
/-- `GN` retains every nontrivial phase. Its product description uses the
intrinsic root set and is independent of the chosen primitive generator. -/
theorem GN_eq_nontrivial_phase_prod (hd : 0 < d) (hζ : IsPrimitiveRoot ζ d)
    (x u : R) :
    DkMath.CosmicFormula.GTail d 1 x u =
      ∏ ξ ∈ (Polynomial.nthRootsFinset d (1 : R)).erase 1,
        (x + (1 - ξ) * u) := by
  classical
  rw [GN_eq_nontrivial_phase_prod_range hd hζ,
    nontrivialRootsFinset_eq_powers hζ, Finset.prod_image]
  intro i hi j hj hij
  exact hζ.pow_inj (Finset.mem_range.mp (Finset.mem_erase.mp hi).2)
    (Finset.mem_range.mp (Finset.mem_erase.mp hj).2) hij

end SplitPhases

end DkMath.NumberTheory.GapFocusing
