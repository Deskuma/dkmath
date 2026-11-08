/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalFiniteDetection

#print "file: DkMath.FLT.FreyRadicalKernelClosure"

/-! # 有限段検出を指定した n+3 段まで引き下ろす
同じ全段原始生成元と元の共通商の指数を用い、有限段根核の包含を証明する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 指定した有限段の根核が、同じ実際の共通射影核に含まれる。 -/
theorem ResidualCyclicStage.radical_kernel_le_commonProjection_kernel :
    (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker := by
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp hq hqp.symm A hA
  obtain ⟨M, hM⟩ := T.exists_radical_kernel_le_common A hp5 hq hqp haddr hA
  let d := M + n + 3
  have hdeep : (InertiaRadical.character hp hq hqp.symm A hA (d + 1)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker :=
    (InertiaRadical.character_kernel_antitone hp hq hqp.symm A hA (by dsimp [d]; omega)).trans hM
  intro σ hs
  obtain ⟨j, _, ε, he, hε, _⟩ := InertiaRadical.correction_of_primitive hp hq hqp.symm A hA d γ
    (InertiaRadical.generator_primitive hp hq hqp.symm A hA d) σ
  have hεlow : InertiaRadical.character hp hq hqp.symm A hA (n + 3) ε = 1 :=
    InertiaRadical.character_kernel_antitone hp hq hqp.symm A hA (by dsimp [d]; omega) hε
  have hj : p ^ (n + 3) ∣ j := by
    have hσ := hs
    change InertiaRadical.character hp hq hqp.symm A hA (n + 3) σ = 1 at hσ
    rw [he, map_mul, map_pow, hεlow, mul_one] at hσ
    have hpow := congrArg Units.val hσ
    exact (InertiaRadical.generator_primitive hp hq hqp.symm A hA (n + 2)).pow_eq_one_iff_dvd j |>.mp hpow
  change T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ = 1
  rw [he, map_mul, map_pow, show T.fixedKernelCommonProjection A hp5 hq hqp haddr hA ε = 1 from hdeep hε, mul_one]
  obtain ⟨t, rfl⟩ := hj
  rw [pow_mul, T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA, one_pow]

/-- 有限一段を固定する元の全係数核の評価も零となる。 -/
theorem ResidualCyclicStage.radical_fixed_evaluations_eq_zero (σ : inertiaSubgroupIn A ℚ)
    (hs : σ.val (InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3)) =
      InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3))
    (k : T.fixedH1CoefficientKernel A) : T.fixedKernelEvaluation A σ k = 0 :=
  (T.radical_kernel_comparison_iff_evaluations A hp5 hq hqp haddr hA).mp
    (T.radical_kernel_le_commonProjection_kernel A hp5 hq hqp haddr hA) σ hs k
end
end DkMath.FLT.Frey.Source

