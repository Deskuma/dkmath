/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeOrderGeneratorValue

#print "file: DkMath.FLT.FreyResonantFrobeniusSigns"

/-! # 実際の位数 p の障害値に限った共鳴符号
F 全体の作用や Frobenius 固有値を決定したとは主張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- q≡1 mod p なら同じ障害値の q 倍は元の値。 -/
theorem NarrowAbsorptionObstruction.generatorValue_q_smul_plus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hq1 : (q : ZMod p) = 1) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    q • v = v := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hmod : q % p = 1 := by
    have hv := congrArg ZMod.val hq1
    simpa only [ZMod.val_natCast, ZMod.val_one, Nat.mod_eq_of_lt hp] using hv
  exact (h.generatorValue_nsmul_mod hp5 q).trans
    ((congrArg (fun m : ℕ => m • T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)) hmod).trans (one_nsmul _))

/-- q≡-1 mod p なら同じ障害値の q 倍は負の値。 -/
theorem NarrowAbsorptionObstruction.generatorValue_q_smul_minus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hqneg : (q : ZMod p) = -1) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    q • v = -v := by
  let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
    (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)
  have hmod : (q + 1) % p = 0 := by
    have hz : ((q + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [hqneg]; simp
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  have hz : (q + 1) • v = 0 := by
    rw [h.generatorValue_nsmul_mod hp5 (q + 1), hmod, zero_nsmul]
  rw [add_nsmul, one_nsmul] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- 同じ障害値の Frobenius 固定性を、元の二つの共鳴枝で正確に判定する。 -/
theorem NarrowAbsorptionObstruction.frobenius_fixed_resonant_signs
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    ((q : ZMod p) = 1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
      T.fixedDecompositionAction A φ v = v)) ∨
    ((q : ZMod p) = -1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
      T.fixedDecompositionAction A φ v = -v)) := by
  have he := h.frobenius_fixed_criterion hp5 φ hφ
  rcases h.resonance with hq1 | hqneg
  · refine Or.inl ⟨hq1, ?_⟩
    simpa only [h.generatorValue_q_smul_plus hp5 hq1] using he
  · refine Or.inr ⟨hqneg, ?_⟩
    simpa only [h.generatorValue_q_smul_minus hp5 hqneg] using he
end
end DkMath.FLT.Frey.Source

