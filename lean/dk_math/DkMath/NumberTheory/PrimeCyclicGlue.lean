/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.AKSBridge
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Tactic.Ring

/-!
# Integral prime cyclic gluing

The existing AKS cyclic quotient is reconstructed from an integer augmentation
and an integral cyclotomic quotient component agreeing in `ZMod p`. Existence
is stated with polynomial representatives; uniqueness is in the AKS quotient.
The power endpoint glues genuine powers, with no unit factors.
-/

namespace DkMath.NumberTheory

open Polynomial

/-- Evaluation at the trivial character gives the common residue of the
integral cyclotomic quotient. -/
noncomputable def primeCyclotomicResidue (p : ℕ) [Fact p.Prime] :
    AdjoinRoot (cyclotomic p ℤ) →+* ZMod p :=
  AdjoinRoot.lift (Int.castRingHom (ZMod p)) 1 (by
    rw [eval₂_one_cyclotomic_prime]
    exact ZMod.natCast_self p)

theorem primeCyclotomicResidue_mk (p : ℕ) [Fact p.Prime] (f : ℤ[X]) :
    primeCyclotomicResidue p (AdjoinRoot.mk (cyclotomic p ℤ) f) =
      ((f.eval (1 : ℤ) : ℤ) : ZMod p) := by
  rw [primeCyclotomicResidue, AdjoinRoot.lift_mk]
  simpa only [map_one, Int.coe_castRingHom] using
    (eval₂_at_apply (Int.castRingHom (ZMod p)) (1 : ℤ) (p := f))

/-- Integral polynomial reconstruction is exactly compatibility modulo the prime. -/
theorem exists_polynomial_prime_glue_iff (p : ℕ) [Fact p.Prime]
    (a : ℤ) (q : ℤ[X]) :
    (∃ f : ℤ[X], f.eval 1 = a ∧ cyclotomic p ℤ ∣ f - q) ↔
      (p : ℤ) ∣ a - q.eval 1 := by
  constructor
  · rintro ⟨f, hf, t, ht⟩
    refine ⟨t.eval 1, ?_⟩
    have h := congrArg (eval 1) ht
    simpa only [eval_sub, eval_mul, eval_one_cyclotomic_prime, hf] using h
  · rintro ⟨k, hk⟩
    refine ⟨q + cyclotomic p ℤ * C k, ?_, ?_⟩
    · simp only [eval_add, eval_mul, eval_one_cyclotomic_prime, eval_C]
      rw [← hk]
      ring
    · refine ⟨C k, ?_⟩
      ring

/-- Equal trivial and cyclotomic components determine the same integral cyclic class. -/
theorem cyclic_dvd_sub_iff_components (p : ℕ) [Fact p.Prime] (f g : ℤ[X]) :
    (X ^ p - 1 : ℤ[X]) ∣ f - g ↔
      f.eval 1 = g.eval 1 ∧ cyclotomic p ℤ ∣ f - g := by
  constructor
  · rintro ⟨t, ht⟩
    constructor
    · have h := congrArg (eval 1) ht
      simp only [eval_sub, eval_mul, eval_pow, eval_X, one_pow, eval_one,
        sub_self, zero_mul] at h
      exact sub_eq_zero.mp h
    · rw [ht, ← cyclotomic_prime_mul_X_sub_one ℤ p]
      exact dvd_mul_right _ _ |>.trans (dvd_mul_right _ _)
  · rintro ⟨he, t, ht⟩
    have hz : t.eval 1 = 0 := by
      have h := congrArg (eval 1) ht
      simp only [eval_sub, eval_mul, eval_one_cyclotomic_prime, he, sub_self] at h
      exact (mul_eq_zero.mp h.symm).resolve_left
        (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    have hd : (X - 1 : ℤ[X]) ∣ t := by
      change X - C (1 : ℤ) ∣ t
      exact dvd_iff_isRoot.mpr hz
    rcases hd with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [ht, hs, ← mul_assoc, cyclotomic_prime_mul_X_sub_one]

/-- A cyclotomic component and an integer component have a common integral
representative precisely when their residues agree in `ZMod p`. -/
theorem exists_prime_cyclic_glue_iff (p : ℕ) [Fact p.Prime]
    (a : ℤ) (b : AdjoinRoot (cyclotomic p ℤ)) :
    (∃ f : ℤ[X], f.eval 1 = a ∧ AdjoinRoot.mk (cyclotomic p ℤ) f = b) ↔
      (a : ZMod p) = primeCyclotomicResidue p b := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [primeCyclotomicResidue_mk]
  simp only [AdjoinRoot.mk_eq_mk]
  rw [exists_polynomial_prime_glue_iff]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, sub_eq_zero]

/-- The uniqueness statement uses the existing AKS cyclic quotient, not a new carrier. -/
theorem aks_prime_cyclic_glue_eq_iff (p : ℕ) [Fact p.Prime] (f g : ℤ[X]) :
    aksQuotientMap ℤ p f = aksQuotientMap ℤ p g ↔
      f.eval 1 = g.eval 1 ∧
        AdjoinRoot.mk (cyclotomic p ℤ) f = AdjoinRoot.mk (cyclotomic p ℤ) g := by
  rw [aksQuotientMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [aksCyclicIdeal, Ideal.mem_span_singleton, AdjoinRoot.mk_eq_mk]
  exact cyclic_dvd_sub_iff_components p f g

/-- If both components of a cyclic class are genuine p-th powers, the class
is a genuine p-th power. Frobenius over `ZMod p` forces compatibility of the roots. -/
theorem aks_prime_cyclic_is_pow_of_components (p : ℕ) [Fact p.Prime]
    (f : ℤ[X]) (a : ℤ) (b : AdjoinRoot (cyclotomic p ℤ))
    (ha : f.eval 1 = a ^ p)
    (hb : AdjoinRoot.mk (cyclotomic p ℤ) f = b ^ p) :
    ∃ q : AKSCyclicQuotient ℤ p, aksQuotientMap ℤ p f = q ^ p := by
  have hc : (a : ZMod p) = primeCyclotomicResidue p b := by
    have h := primeCyclotomicResidue_mk p f
    rw [hb, ha, map_pow, Int.cast_pow] at h
    simpa only [ZMod.pow_card] using h.symm
  obtain ⟨q, hqa, hqb⟩ := (exists_prime_cyclic_glue_iff p a b).mpr hc
  refine ⟨aksQuotientMap ℤ p q, ?_⟩
  rw [← map_pow]
  apply (aks_prime_cyclic_glue_eq_iff p f (q ^ p)).mpr
  constructor
  · rw [eval_pow, hqa, ha]
  · rw [map_pow, hqb, hb]

end DkMath.NumberTheory
