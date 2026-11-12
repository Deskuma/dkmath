/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalExactRoots
import DkMath.Lib.NumberTheory.KummerPrimeQuotientExclusion
import DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots

#print "file: DkMath.Lib.NumberTheory.InertiaTailGaloisRoots"

/-! # 同じ tail 体を固定する実際の慣性元の p 冪根
Kummer 有限商排除と副有限コンパクト性を、実際の体内根で内部充足する。
単一有限段の根の固定から全根の固定は結論しない。 -/
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open ValuationInertia IntermediateField

/-- tail 体上の中間体を ℚ 上へ制限し、前回の正確な根定理を適用する。 -/
theorem tailIntermediate_exact_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (F : IntermediateField (tailField A p q) (AlgebraicClosure ℚ))
    (a : F) (ha : a ≠ 0) : ∃ b : F, b ^ p = a := by
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := F.restrictScalars ℚ
  have hE : tailField A p q ≤ E := fun x hx => F.algebraMap_mem ⟨x, hx⟩
  exact tailOverfield_exact_pRoot hp hq hpq A hA E hE a ha

/-- 同じ tail 体に原始 p 乗根の1が実在する。 -/
theorem tailField_primitiveRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    ∃ ζ : tailField A p q, IsPrimitiveRoot ζ p := by
  let : NeZero (p : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hfix : ζ ∈ fixedField A := by
    rw [fixedField, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    apply InertiaRadical.inertia_fixes_primePower_root hp hq hpq A hA ⟨σ, hσ⟩ 1 ζ
    simpa using hζ.pow_eq_one
  exact ⟨⟨ζ, fixedField_le_tailField A p q hfix⟩,
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (tailField A p q) (AlgebraicClosure ℚ))
      hζ (algebraMap (tailField A p q) (AlgebraicClosure ℚ)).injective⟩

/-- 実際の tail Galois 群の各開正規部分群の指数は p と素。 -/
theorem tailGalois_index_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (N : OpenNormalSubgroup (AlgebraicClosure ℚ ≃ₐ[tailField A p q] AlgebraicClosure ℚ)) :
    N.toSubgroup.index.Coprime p := by
  obtain ⟨ζ, hζ⟩ := tailField_primitiveRoot hp hq hpq A hA
  exact KummerPrimeQuotient.index_coprime_of_forall_pow_surjective hp hζ
    (fun F _ a ha => tailIntermediate_exact_pRoot hp hq hpq A hA F a ha) N

/-- tail を固定する自己同型の p 冪根は、同じ tail 固定群かつ元の慣性群に属する。 -/
theorem tailFixing_inertia_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (n : ℕ) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hg : g ∈ (tailField A p q).fixingSubgroup) :
    ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      w ∈ inertiaSubgroupIn A ℚ ∧ w ∈ (tailField A p q).fixingSubgroup ∧ w ^ (p ^ n) = g := by
  let E := tailField A p q
  let g' : AlgebraicClosure ℚ ≃ₐ[E] AlgebraicClosure ℚ := fixingSubgroupEquiv E ⟨g, hg⟩
  let : T2Space (AlgebraicClosure ℚ ≃ₐ[E] AlgebraicClosure ℚ) := krullTopology_t2
  obtain ⟨w', hw'⟩ := ProfiniteCoprimeRoots.exists_pow_pow_eq
    (tailGalois_index_coprime hp hq hpq A hA) g' n
  let w : E.fixingSubgroup := (fixingSubgroupEquiv E).symm w'
  have hwI : (w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ inertiaSubgroupIn A ℚ := by
    have hf := IntermediateField.fixingSubgroup_le (fixedField_le_tailField A p q) w.2
    rw [fixedField, InertiaClosed.fixingSubgroup_fixedField_inertia] at hf
    exact hf
  refine ⟨w, hwI, w.2, ?_⟩
  have he : (fixingSubgroupEquiv E).symm (w' ^ (p ^ n)) = w ^ (p ^ n) := map_pow _ _ _
  rw [hw', show (fixingSubgroupEquiv E).symm g' = ⟨g, hg⟩ from MulEquiv.symm_apply_apply _ _] at he
  exact (congrArg (fun x : E.fixingSubgroup => (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) he).symm

/-- 慣性元が tail を固定することと、同じ q の全 p 冪根を固定することは同値。 -/
theorem mem_tailFixing_iff_all_radicals {p q : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ)) (g : inertiaSubgroupIn A ℚ) :
    g.val ∈ (tailField A p q).fixingSubgroup ↔
      ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α := by
  constructor
  · intro hg α k hk
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg α (radical_mem_tailField A hk)
  · intro hr
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hs : tailField A p q ≤ IntermediateField.fixedField (Subgroup.zpowers g.val) := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro α hα
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hfix : g.val α = α := by
        rcases hα with hα | ⟨k, hk⟩
        · exact (IntermediateField.mem_fixedField_iff _ _).mp hα g.val g.property
        · exact hr α k hk
      have hle : Subgroup.zpowers g.val ≤ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) α := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hfix
      exact hle hσ
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hs hx) g.val (Subgroup.mem_zpowers _)

/-- 同じ全根を固定する慣性元は、元の慣性群内に任意の有限深さの冪根を持つ。 -/
theorem allRadicals_inertia_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (n : ℕ) (g : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α) :
    ∃ w : inertiaSubgroupIn A ℚ, w ^ (p ^ n) = g := by
  obtain ⟨w, hwI, _, hw⟩ := tailFixing_inertia_pRoot hp hq hpq A hA n g.val
    ((mem_tailFixing_iff_all_radicals A g).mpr hr)
  exact ⟨⟨w, hwI⟩, Subtype.ext hw⟩

/-- 任意の一様 p 冪指数の商は、同じ全根を固定する慣性元を消す。 -/
theorem allRadicals_map_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {H : Type*} [Group H] (f : inertiaSubgroupIn A ℚ →* H)
    (n : ℕ) (hexp : ∀ h : H, h ^ (p ^ n) = 1) (g : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α) :
    f g = 1 := by
  obtain ⟨w, hw⟩ := allRadicals_inertia_pRoot hp hq hpq A hA n g hr
  rw [← hw, map_pow]
  exact hexp _
end
end DkMath.Lib.NumberTheory.InertiaResidue

