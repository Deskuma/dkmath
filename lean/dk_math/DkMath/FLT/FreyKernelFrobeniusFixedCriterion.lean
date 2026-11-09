/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFrobeniusCovariance

#print "file: DkMath.FLT.FreyKernelFrobeniusFixedCriterion"

/-! # 同じ具体的生成元による Frobenius 不変性の判定
非零性の保存と不変性を同一視しない。q 倍の消去には元の p 冪周期を使う。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の F 上の q 倍は単射。剰余標数が p と異なるという元の条件を消費する。 -/
theorem ResidualCyclicStage.fixed_q_nsmul_injective :
    Function.Injective (fun z : T.inertiaFixedUpperQuotient A => q • z) := by
  have hd : Nat.card (T.inertiaFixedUpperQuotient A) ∣ p ^ (n + 3) := by
    refine ⟨Nat.card (T.fixedH1CoefficientKernel A), ?_⟩
    rw [mul_comm]
    exact (T.fixedKernel_card_mul_fixed A hp5 hq hqp haddr hA).symm
  have hcop : Nat.Coprime q (Nat.card (T.inertiaFixedUpperQuotient A)) :=
    ((Nat.coprime_primes hq (Fact.out : p.Prime)).mpr hqp).pow_right (n + 3) |>.of_dvd_right hd
  have hc : (Nat.card (Multiplicative (T.inertiaFixedUpperQuotient A))).Coprime q := by
    rw [Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (T.inertiaFixedUpperQuotient A) ≃ T.inertiaFixedUpperQuotient A)]
    exact hcop.symm
  intro x y he
  apply Multiplicative.ofAdd.injective
  exact (powCoprime hc).injective (congrArg Multiplicative.ofAdd he)

/-- 同じ γ での値が F の Frobenius q 固有値条件を満たすことと、元の核元の不変性は同値。 -/
theorem ResidualCyclicStage.kernelFrobenius_fixed_iff
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k := by
  have he := T.kernelFrobenius_evaluation_relation A hp5 hq hqp haddr hA φ hφ
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k
  constructor
  · intro hk
    rw [hk] at he
    exact he.symm
  · intro hk
    rw [hk] at he
    apply T.generator_evaluation_injective A hp5 hq hqp haddr hA
    exact T.fixed_q_nsmul_injective A hp5 hq hqp haddr hA he
end
end DkMath.FLT.Frey.Source

