/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.CoreNested
import DkMath.Lib.Cosmic.GNPhaseFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

#print "file: DkMath.Lib.NumberTheory.RamifiedGNPhaseBridge"

/-!
# Ramified depth in one phase

The packet records a primitive root, a prime `λ = 1 - ζ`, and a residue map
with kernel `(λ)` and `ζ ↦ 1`. It contains no FLT equation, class-group condition,
or descent assumption. Slopes are negative geometric sums, so phase zero is
included without dividing in the ring. All depth statements use divisibility
and remain valid when the power difference or a quotient is zero.
-/

open scoped BigOperators

namespace DkMath.Lib.NumberTheory

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Cancel the fixed ramified power and every factor away from the prime.
The selected factor is allowed to be zero. -/
theorem prime_pow_dvd_scaled_prod_iff {ι : Type*}
    {π : R} (hπ : Prime π) (s : Finset ι) (Q : ι → R) (i₀ : ι)
    (hi₀ : i₀ ∈ s) (haway : ∀ i ∈ s, i ≠ i₀ → ¬ π ∣ Q i) (n k : ℕ) :
    π ^ (n + k) ∣ π ^ n * ∏ i ∈ s, Q i ↔ π ^ k ∣ Q i₀ := by
  classical
  have hrest : ¬ π ∣ ∏ i ∈ s.erase i₀, Q i := by
    intro hd
    obtain ⟨i, hi, hd⟩ := (hπ.dvd_finsetProd_iff _).mp hd
    exact haway i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1 hd
  rw [pow_add, mul_dvd_mul_iff_left (pow_ne_zero n hπ.ne_zero),
    ← Finset.mul_prod_erase s Q hi₀]
  exact ⟨hπ.pow_dvd_of_dvd_mul_right k hrest, fun h => dvd_mul_of_dvd_left h _⟩

/-- Minimal ramified phase data, with all arithmetic providers explicit. -/
structure RamifiedPhasePacket (R : Type*) [CommRing R] [IsDomain R]
    (p : ℕ) [Fact p.Prime] where
  zeta : R
  primitive : IsPrimitiveRoot zeta p
  lambda : R
  lambda_eq : lambda = 1 - zeta
  lambda_prime : Prime lambda
  residue : R →+* ZMod p
  residue_zero_iff : ∀ a, residue a = 0 ↔ lambda ∣ a
  residue_zeta : residue zeta = 1

namespace RamifiedPhasePacket

variable {p : ℕ} [hp : Fact p.Prime] (P : RamifiedPhasePacket R p)

/-- Negative geometric sum; phase zero has slope zero. -/
def slope (i : Fin p) : R := -(∑ k ∈ Finset.range i.val, P.zeta ^ k)

@[simp] theorem slope_zero : P.slope ⟨0, hp.out.pos⟩ = 0 := by simp [slope]

/-- Slopes are integral witnesses for the phase difference. -/
theorem slope_spec (i : Fin p) : P.slope i * P.lambda = P.zeta ^ i.val - 1 := by
  rw [slope, P.lambda_eq, neg_mul, geom_sum_mul_neg, neg_sub]

/-- Phase indices survive after removing one ramified factor. -/
theorem slope_residue (i : Fin p) : P.residue (P.slope i) = -(i.val : ZMod p) := by
  simp [slope, map_sum, P.residue_zeta]

/-- All normalized factors share one center and one second endpoint. -/
def quotient (q y : R) (i : Fin p) : R := q + P.slope i * y

/-- Recover every original linear factor from the same center. -/
theorem quotient_spec (q y : R) (i : Fin p) :
    (P.lambda * q - y) + P.zeta ^ i.val * y = P.lambda * P.quotient q y i := by
  have hs := P.slope_spec i
  unfold quotient
  linear_combination -hs * y

/-- The unique index where the normalized factor has zero residue. -/
def distinguished (q y : R) : Fin p :=
  ⟨(P.residue q / P.residue y).val, ZMod.val_lt _⟩

/-- Uniqueness follows from a linear residue equation, without a finite search. -/
theorem quotient_dvd_iff (q y : R) (hy : ¬ P.lambda ∣ y) (i : Fin p) :
    P.lambda ∣ P.quotient q y i ↔ i = P.distinguished q y := by
  have hn : P.residue y ≠ 0 := fun h => hy ((P.residue_zero_iff y).mp h)
  constructor
  · intro hd
    have hz := (P.residue_zero_iff _).mpr hd
    simp only [quotient, map_add, map_mul, slope_residue] at hz
    have he : (i.val : ZMod p) = P.residue q / P.residue y := by
      apply (eq_div_iff hn).mpr
      linear_combination -hz
    apply Fin.ext
    change i.val = (P.residue q / P.residue y).val
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] using hv
  · rintro rfl
    apply (P.residue_zero_iff _).mp
    simp only [quotient, map_add, map_mul, slope_residue, distinguished,
      ZMod.natCast_zmod_val]
    field_simp
    ring

/-- Full phase product, including the Gap phase. -/
theorem powerCore_eq_product (q y : R) :
    DkMath.Lib.Cosmic.powerCore p (-y) (P.lambda * q) =
      P.lambda ^ p * ∏ i : Fin p, P.quotient q y i := by
  have hf := DkMath.NumberTheory.GapFocusing.focused_pow_sub_pow_eq_prod_fin
    hp.out.pos P.primitive (P.lambda * q) (-y)
  change _ - _ = _
  rw [add_comm (-y), hf]
  calc
    _ = ∏ i : Fin p, (P.lambda * P.quotient q y i) := by
      apply Finset.prod_congr rfl
      intro i _
      have hs := P.quotient_spec q y i
      linear_combination hs
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- R1: every extra ramified power belongs to the single distinguished phase. -/
theorem powerCore_dvd_iff (q y : R) (hy : ¬ P.lambda ∣ y) (k : ℕ) :
    P.lambda ^ (p + k) ∣ DkMath.Lib.Cosmic.powerCore p (-y) (P.lambda * q) ↔
      P.lambda ^ k ∣ P.quotient q y (P.distinguished q y) := by
  rw [P.powerCore_eq_product]
  exact prime_pow_dvd_scaled_prod_iff P.lambda_prime Finset.univ _
    (P.distinguished q y) (Finset.mem_univ _) (fun i _ hi hd =>
      hi ((P.quotient_dvd_iff q y hy i).mp hd)) p k

/-- Odd-power-sum form of R1, requiring only the shared center relation. -/
theorem sum_dvd_iff (hodd : Odd p) (x y q : R) (hcenter : x + y = P.lambda * q)
    (hy : ¬ P.lambda ∣ y) (k : ℕ) :
    P.lambda ^ (p + k) ∣ x ^ p + y ^ p ↔
      P.lambda ^ k ∣ P.quotient q y (P.distinguished q y) := by
  rw [← DkMath.Lib.Cosmic.powerCore_neg_sum hodd, hcenter]
  exact P.powerCore_dvd_iff q y hy k

/-- Removing phase zero preserves GN even when `q = 0`: no evaluated Gap is cancelled. -/
theorem gtail_eq_product (q y : R) :
    DkMath.CosmicFormula.GTail p 1 (P.lambda * q) (-y) =
      P.lambda ^ (p - 1) * ∏ i ∈ (Finset.univ.erase (⟨0, hp.out.pos⟩ : Fin p)),
        P.quotient q y i := by
  classical
  rw [DkMath.NumberTheory.GapFocusing.GN_eq_nontrivial_phase_prod_range hp.out.pos
    P.primitive]
  have hprod : (∏ j ∈ (Finset.range p).erase 0,
      (P.lambda * q + (1 - P.zeta ^ j) * -y)) =
      ∏ i ∈ (Finset.univ.erase (⟨0, hp.out.pos⟩ : Fin p)),
        (P.lambda * P.quotient q y i) := by
    symm
    apply Finset.prod_bij (fun (i : Fin p) _ => i.val)
    · intro i hi
      simpa only [Finset.mem_erase, Finset.mem_range, Finset.mem_univ, and_true,
        ne_eq, Fin.ext_iff] using And.intro (Finset.mem_erase.mp hi).1 i.isLt
    · intro i _ j _ hij
      exact Fin.ext hij
    · intro j hj
      refine ⟨⟨j, (Finset.mem_range.mp (Finset.mem_erase.mp hj).2)⟩, ?_, rfl⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
      exact (Finset.mem_erase.mp hj).1
    · intro i _
      have hs := P.quotient_spec q y i
      linear_combination -hs
  rw [hprod, Finset.prod_mul_distrib]
  simp

/-- When phase zero is selected, its entire extra depth is stored in the Gap.
This is cancellation of the fixed `λ`, including the case `q = 0`. -/
theorem gap_dvd_iff_of_distinguished_zero (q y : R)
    (hzero : P.distinguished q y = ⟨0, hp.out.pos⟩) (k : ℕ) :
    P.lambda ^ (1 + k) ∣ P.lambda * q ↔
      P.lambda ^ k ∣ P.quotient q y (P.distinguished q y) := by
  rw [hzero]
  simp only [quotient, slope_zero, zero_mul, add_zero, pow_add, pow_one]
  exact mul_dvd_mul_iff_left P.lambda_prime.ne_zero

/-- If phase zero is distinguished, GN has no extra ramified factor. -/
theorem not_dvd_gtail_of_distinguished_zero (q y : R) (hy : ¬ P.lambda ∣ y)
    (hzero : P.distinguished q y = ⟨0, hp.out.pos⟩) :
    ¬ P.lambda ^ p ∣ DkMath.CosmicFormula.GTail p 1 (P.lambda * q) (-y) := by
  classical
  have hrest : ¬ P.lambda ∣ ∏ i ∈ (Finset.univ.erase (⟨0, hp.out.pos⟩ : Fin p)),
      P.quotient q y i := by
    intro hd
    obtain ⟨i, hi, hd⟩ := (P.lambda_prime.dvd_finsetProd_iff _).mp hd
    exact (Finset.mem_erase.mp hi).1 ((P.quotient_dvd_iff q y hy i).mp hd |>.trans hzero)
  rw [P.gtail_eq_product]
  have hexp : p = (p - 1) + 1 := by have := hp.out.pos; omega
  have hpow : P.lambda ^ p = P.lambda ^ (p - 1) * P.lambda := by
    calc
      _ = P.lambda ^ (p - 1 + 1) := congrArg (fun n : ℕ => P.lambda ^ n) hexp
      _ = _ := by rw [pow_add, pow_one]
  rw [hpow]
  rw [mul_dvd_mul_iff_left (pow_ne_zero _ P.lambda_prime.ne_zero)]
  exact hrest

/-- If a nonzero phase is distinguished, all extra depth is carried by GN. -/
theorem gtail_dvd_iff_of_distinguished_ne_zero (q y : R) (hy : ¬ P.lambda ∣ y)
    (hne : P.distinguished q y ≠ ⟨0, hp.out.pos⟩) (k : ℕ) :
    P.lambda ^ (p - 1 + k) ∣ DkMath.CosmicFormula.GTail p 1 (P.lambda * q) (-y) ↔
      P.lambda ^ k ∣ P.quotient q y (P.distinguished q y) := by
  classical
  rw [P.gtail_eq_product]
  exact prime_pow_dvd_scaled_prod_iff P.lambda_prime _ _ (P.distinguished q y)
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
    (fun i _ hi hd => hi ((P.quotient_dvd_iff q y hy i).mp hd)) (p - 1) k

end RamifiedPhasePacket
end DkMath.Lib.NumberTheory
