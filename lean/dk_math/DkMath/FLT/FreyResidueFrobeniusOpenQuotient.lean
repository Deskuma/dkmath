/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueOpenKernelDetection

#print "file: DkMath.FLT.FreyResidueFrobeniusOpenQuotient"

/-! # 実際の局所 Frobenius による開商の生成
有限剰余値近似とコンパクト性から、慣性を含む任意の開部分群 modulo の冪表示を得る。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section

/-- 慣性を含む任意の開部分群 modulo で、任意の D 元は同じ局所 Frobenius の冪。 -/
theorem exists_frobenius_power_mod_open (A : ValuationSubring (AlgebraicClosure ℚ))
    {q : ℕ} [Fact q.Prime] (hA : LiesOverPrime A q)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (N : Subgroup (A.decompositionSubgroup ℚ))
    (hN : IsOpen (N : Set (A.decompositionSubgroup ℚ)))
    (hI : A.inertiaSubgroup ℚ ≤ N) (σ : A.decompositionSubgroup ℚ) :
    ∃ m : ℕ, (φ ^ m)⁻¹ * σ ∈ N := by
  obtain ⟨s, hs⟩ := exists_finite_residue_detection A N hN hI
  obtain ⟨m, hm⟩ := residueFinite_frobenius_approx A hA φ hφ σ s
  refine ⟨m, hs _ ?_⟩
  intro x hx
  rw [mul_smul, hm x hx, inv_smul_smul]

variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の有限 K 作用像の各元は、実際の Frobenius 像の自然数冪である。 -/
theorem ResidualCyclicStage.finiteDecomposition_power_of_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (σ : A.decompositionSubgroup ℚ) :
    ∃ m : ℕ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ =
      (T.finiteDecompositionProjection A hp5 hq hqp haddr hA φ) ^ m := by
  let : Fact q.Prime := ⟨hq⟩
  let π := T.finiteDecompositionProjection A hp5 hq hqp haddr hA
  have hker : IsOpen (π.ker : Set (A.decompositionSubgroup ℚ)) := by
    change IsOpen (((QuotientGroup.mk' (T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker).ker :
      Subgroup (A.decompositionSubgroup ℚ)) : Set (A.decompositionSubgroup ℚ))
    rw [QuotientGroup.ker_mk']
    exact T.kernelDecompositionUnits_kernel_isOpen A hp5 hq hqp haddr hA
  obtain ⟨m, hm⟩ := exists_frobenius_power_mod_open A hA φ hφ π.ker hker
    (T.inertia_le_finiteDecompositionProjection_kernel A hp5 hq hqp haddr hA) σ
  change π ((φ ^ m)⁻¹ * σ) = 1 at hm
  rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at hm
  exact ⟨m, hm.symm⟩

/-- 元の住所から、以前は明示入力だった有限像生成性 `himage` を供給する。 -/
theorem ResidualCyclicStage.finiteDecomposition_generated_of_frobenius
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    ∀ σ : A.decompositionSubgroup ℚ,
      (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈
        Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) := by
  intro σ
  obtain ⟨m, hm⟩ := T.finiteDecomposition_power_of_frobenius A hp5 hq hqp haddr hA φ hφ σ
  rw [hm]
  exact Subgroup.npow_mem_zpowers _ _

end
end DkMath.FLT.Frey.Source
