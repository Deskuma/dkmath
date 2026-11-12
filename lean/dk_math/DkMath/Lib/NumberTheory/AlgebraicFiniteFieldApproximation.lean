/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
import Mathlib.FieldTheory.Finite.Extension

#print "file: DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation"

/-! # 有限体上の代数拡大での有限個の値の Frobenius 近似
有限集合の生成する有限中間体に両自己同型を制限する。 -/
namespace DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F] [Algebra k F] [Algebra.IsAlgebraic k F]

/-- 有限個の値では、任意の k 自己同型は一つの Frobenius 冪と一致する。 -/
theorem finite_values_pow (σ : F ≃ₐ[k] F) (s : Finset F) :
    ∃ m : ℕ, ∀ x ∈ s, σ x = x ^ (Fintype.card k ^ m) := by
  classical
  let E := IntermediateField.adjoin k (s : Set F)
  let : Finite (s : Set F) := s.finite_toSet.to_subtype
  let : FiniteDimensional k E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  let : Finite E := Module.finite_of_finite k
  let : Fintype E := Fintype.ofFinite E
  let : Normal k E := by infer_instance
  let σE : E ≃ₐ[k] E := σ.restrictNormal E
  obtain ⟨m, _, hm⟩ := FiniteFieldFrobeniusImage.exists_bounded_power k E σE
  refine ⟨m, ?_⟩
  intro x hx
  let xE : E := ⟨x, IntermediateField.subset_adjoin k (s : Set F) hx⟩
  have h := congrArg (fun f : E ≃ₐ[k] E => (f xE : F)) hm
  have hpow : ((FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ m) xE : F) =
      x ^ (Fintype.card k ^ m) := by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    rfl
  rw [hpow] at h
  simpa [σE, xE, AlgEquiv.restrictNormal_apply] using h.symm

/-- 同じ Frobenius 自己同型の冪として、有限個の値を同時に近似できる。 -/
theorem finite_values_frobenius (σ φ : F ≃ₐ[k] F)
    (hφ : ∀ x : F, φ x = x ^ Fintype.card k) (s : Finset F) :
    ∃ m : ℕ, ∀ x ∈ s, σ x = (φ ^ m) x := by
  have hφeq : φ = FiniteField.frobeniusAlgEquivOfAlgebraic k F := by
    ext x
    exact hφ x
  obtain ⟨m, hm⟩ := finite_values_pow k F σ s
  refine ⟨m, fun x hx => ?_⟩
  rw [hφeq, AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  exact hm x hx

end
end DkMath.Lib.NumberTheory.AlgebraicFiniteFieldApproximation
