/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameStructureCertificate
import DkMath.Lib.NumberTheory.InertiaRadicalCorrection

#print "file: DkMath.FLT.FreyRadicalGeneratorCertificate"

/-!
# 実際の根の塔の生成元と、同じ Frey 慣性元の可視な補正

根拡大の有限核商 C は実際に巡回となる。以前の Frey 共通商 H とは区別する。
補正 ε は指定した根を固定するが、同じ H で消えることは今回まだ証明していない。
評価式の ε 項を残し、未証明の野生性・冪分解・巡回性を入力にしない。
-/
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

/-- 実際に構成した同じ根の生成元と補正を、元の同じ共通商へ射影する。 -/
theorem ResidualCyclicStage.radical_generator_stage_correction (τ : inertiaSubgroupIn A ℚ) :
    let hp : p.Prime := Fact.out
    let γ := InertiaRadical.generator hp hq hqp.symm A hA
    ∃ j < p ^ (n + 3), ∃ ε : inertiaSubgroupIn A ℚ, τ = γ ^ j * ε ∧
      ε ∈ (InertiaRadical.character hp hq hqp.symm A hA (n + 3)).ker ∧
      ε.val (InertiaRadical.radical p q hp (n + 3)) = InertiaRadical.radical p q hp (n + 3) ∧
      T.fixedKernelCommonProjection A hp5 hq hqp haddr hA τ =
        T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ ^ j *
          T.fixedKernelCommonProjection A hp5 hq hqp haddr hA ε := by
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp hq hqp.symm A hA
  have hg := InertiaRadical.generator_primitive hp hq hqp.symm A hA (n + 2)
  obtain ⟨j, hj, ε, he, hker, hfix⟩ := InertiaRadical.correction_of_primitive hp hq hqp.symm A hA (n + 2) γ hg τ
  exact ⟨j, hj, ε, he, hker, hfix, by rw [he, map_mul, map_pow]⟩

end

noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害元の評価を、実際の根の生成元の寄与と、消していない補正の寄与へ分ける。 -/
theorem NarrowAbsorptionObstruction.radical_generator_error
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let hp : p.Prime := Fact.out
    let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ∃ j < p ^ (n + 3), ∃ ε : inertiaSubgroupIn A ℚ, ⟨τ, h.inertia⟩ = γ ^ j * ε ∧
      ε ∈ (InertiaRadical.character hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 3)).ker ∧
      ε.val (InertiaRadical.radical p q hp (n + 3)) = InertiaRadical.radical p q hp (n + 3) ∧
      T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩ =
        T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over γ ^ j *
          T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ε ∧
      h.fixedDifference hp5 = j • T.fixedKernelEvaluation A γ k + T.fixedKernelEvaluation A ε k := by
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
  let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  obtain ⟨j, hj, ε, he, hker, hfix, hproj⟩ := T.radical_generator_stage_correction A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩
  refine ⟨j, hj, ε, he, hker, hfix, hproj, ?_⟩
  calc
    h.fixedDifference hp5 = T.fixedKernelEvaluation A ⟨τ, h.inertia⟩ k :=
      (h.fixedKernelEvaluation_obstruction hp5).symm
    _ = Multiplicative.toAdd (T.fixedKernelCharacter A k (γ ^ j * ε)) := by rw [he]; rfl
    _ = j • T.fixedKernelEvaluation A γ k + T.fixedKernelEvaluation A ε k := by rw [map_mul, map_pow]; rfl

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 元の同じ算術証明書へ、実際の根の生成元・巡回核商・消していない補正評価を接続する。 -/
theorem residual_exists_radical_generator_error
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let hp : p.Prime := Fact.out
      let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
      let χ := InertiaRadical.character hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 3)
      let C := (inertiaSubgroupIn A ℚ) ⧸ χ.ker
      let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      IsPrimitiveRoot (χ γ : AlgebraicClosure ℚ) (p ^ (n + 3)) ∧ Nat.card C = p ^ (n + 3) ∧ IsCyclic C ∧
      ∃ j < p ^ (n + 3), ∃ ε : inertiaSubgroupIn A ℚ, ⟨τ, h.inertia⟩ = γ ^ j * ε ∧
        ε ∈ χ.ker ∧ ε.val (InertiaRadical.radical p q hp (n + 3)) = InertiaRadical.radical p q hp (n + 3) ∧
        T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩ =
          T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over γ ^ j *
            T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ε ∧
        h.fixedDifference hp5 = j • T.fixedKernelEvaluation A γ k + T.fixedKernelEvaluation A ε k := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
  have hg := InertiaRadical.generator_primitive hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 2)
  exact ⟨n, T, q, A, τ, y, h, hg,
    InertiaRadical.quotient_card_of_primitive hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 2) γ hg,
    InertiaRadical.quotient_isCyclic_of_primitive hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 2) γ hg,
    h.radical_generator_error hp5⟩

end
end DkMath.FLT.Frey.Source
