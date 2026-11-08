/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual finite radical quotients, bounded powers and visible fixed-root correction.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalGenerator

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalCorrection"

/-!
# 実際の有限根拡大を生成する慣性元と、同じ根を固定する補正元

生成元の存在を内部構成する。補正元が固定するのは指定した根の段であり、
野生合同部分群への所属や慣性内での p 冪根の存在は結論しない。
-/
namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 指標の核は、元の同じ根を固定する実際の慣性元からなる。 -/
theorem character_eq_one_iff_root_fixed (n : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    character hp hq hpq A hA n σ = 1 ↔ σ.val (radical p q hp n) = radical p q hp n := by
  constructor
  · intro he
    exact (ratio_eq_one_iff hp hq σ.val n).mp (congrArg Units.val he)
  · intro he
    apply Units.ext
    exact (ratio_eq_one_iff hp hq σ.val n).mpr he

/-- 原始的な同じ指標値の有界な冪で、任意の同じ慣性値を表す。 -/
theorem image_eq_pow_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)))
    (τ : inertiaSubgroupIn A ℚ) :
    ∃ j < p ^ (n + 1), character hp hq hpq A hA (n + 1) τ = character hp hq hpq A hA (n + 1) γ ^ j := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨j, hj, he⟩ := hprimitive.eq_pow_of_pow_eq_one (character_pow hp hq hpq A hA (n + 1) τ)
  exact ⟨j, hj, Units.ext he.symm⟩

/-- 同じ γ の冪からの補正は、同じ実際の慣性群に属し、指定した根を固定する。 -/
theorem correction_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)))
    (τ : inertiaSubgroupIn A ℚ) :
    ∃ j < p ^ (n + 1), ∃ ε : inertiaSubgroupIn A ℚ, τ = γ ^ j * ε ∧
      ε ∈ (character hp hq hpq A hA (n + 1)).ker ∧
      ε.val (radical p q hp (n + 1)) = radical p q hp (n + 1) := by
  obtain ⟨j, hj, he⟩ := image_eq_pow_of_primitive hp hq hpq A hA n γ hprimitive τ
  let ε := (γ ^ j)⁻¹ * τ
  have hε : character hp hq hpq A hA (n + 1) ε = 1 := by
    change character hp hq hpq A hA (n + 1) ((γ ^ j)⁻¹ * τ) = 1
    rw [map_mul, map_inv, map_pow, he, inv_mul_cancel]
  exact ⟨j, hj, ε, by simp [ε], hε, (character_eq_one_iff_root_fixed hp hq hpq A hA (n + 1) ε).mp hε⟩

/-- 実際の指標像は、同じ原始的な指標値が生成する巡回部分群。 -/
theorem range_eq_zpowers_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1))) :
    (character hp hq hpq A hA (n + 1)).range = Subgroup.zpowers (character hp hq hpq A hA (n + 1) γ) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨τ, rfl⟩ := hz
    obtain ⟨j, _, he⟩ := image_eq_pow_of_primitive hp hq hpq A hA n γ hprimitive τ
    exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), (zpow_natCast _ j).trans he.symm⟩
  · exact Subgroup.zpowers_le.mpr ⟨γ, rfl⟩

/-- 同じ有限根拡大の慣性核商の濃度は、正確に p^(n+1)。 -/
theorem quotient_card_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1))) :
    Nat.card ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) = p ^ (n + 1) := by
  have hc := Nat.card_congr (QuotientGroup.quotientKerEquivRange (character hp hq hpq A hA (n + 1))).toEquiv
  rw [range_eq_zpowers_of_primitive hp hq hpq A hA n γ hprimitive, Nat.card_zpowers] at hc
  exact hc.trans (orderOf_units.symm.trans hprimitive.eq_orderOf.symm)

/-- 同じ実際の根の段の慣性核商は巡回。 -/
theorem quotient_isCyclic_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1))) :
    IsCyclic ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) := by
  have hc : IsCyclic (character hp hq hpq A hA (n + 1)).range := by
    rw [range_eq_zpowers_of_primitive hp hq hpq A hA n γ hprimitive]
    infer_instance
  let := hc
  exact (QuotientGroup.quotientKerEquivRange (character hp hq hpq A hA (n + 1))).isCyclic.mpr inferInstance

/-- 一つの実際の γ が全正段の根拡大を生成し、全ての慣性元に有界な補正分解を与える。 -/
theorem exists_generator_corrections :
    ∃ γ : inertiaSubgroupIn A ℚ, ∀ n : ℕ,
      IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)) ∧
      Nat.card ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) = p ^ (n + 1) ∧
      IsCyclic ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) ∧
      ∀ τ : inertiaSubgroupIn A ℚ, ∃ j < p ^ (n + 1), ∃ ε : inertiaSubgroupIn A ℚ, τ = γ ^ j * ε ∧
        ε ∈ (character hp hq hpq A hA (n + 1)).ker ∧
        ε.val (radical p q hp (n + 1)) = radical p q hp (n + 1) := by
  let γ := generator hp hq hpq A hA
  have hg := generator_primitive hp hq hpq A hA
  exact ⟨γ, fun n => ⟨hg n, quotient_card_of_primitive hp hq hpq A hA n γ (hg n),
    quotient_isCyclic_of_primitive hp hq hpq A hA n γ (hg n),
    correction_of_primitive hp hq hpq A hA n γ (hg n)⟩⟩

end
end DkMath.Lib.NumberTheory.InertiaRadical
