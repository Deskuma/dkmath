/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual DkMath Kummer inertia supplies first-stage movement; no tail-root hypothesis.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalCharacter
import DkMath.Lib.NumberTheory.KummerInertia
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalGenerator"

/-!
# 全ての正の根の段で原始的に作用する、実際の同じ慣性元

第1段の根を動かす元を既存の有限分岐計算から構成する。その同じ元は塔の互換性により
全段で原始的な Kummer 比を持つ。共通 Frey 商の生成性や tail の冪根存在はまだ主張しない。
-/
namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia PrimeRadicalTower
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 追加の生成元入力なしで、同じ慣性元が全ての正の根の段に原始的に作用する。 -/
theorem exists_primitive_generator :
    ∃ γ : inertiaSubgroupIn A ℚ, ∀ n : ℕ,
      IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : radical p q hp 1 ^ p = (q : AlgebraicClosure ℚ) ^ 1 := by
    simpa only [tower_zero, pow_one] using tower_succ_pow p hp.pos (q : AlgebraicClosure ℚ) 0
  have hm : ¬ p ∣ 1 := fun hd => hp.ne_one (Nat.dvd_one.mp hd)
  obtain ⟨τ, hτ, hmove⟩ := KummerInertia.exists_inertia_ne_of_pow_eq A hA hq hp hpq hm hs
  let γ : inertiaSubgroupIn A ℚ := ⟨τ, hτ⟩
  refine ⟨γ, ?_⟩
  intro n
  induction n with
  | zero =>
    have hne : (character hp hq hpq A hA 1 γ : AlgebraicClosure ℚ) ≠ 1 := by
      intro he
      exact hmove ((ratio_eq_one_iff hp hq τ 1).mp he)
    have hpow : (character hp hq hpq A hA 1 γ : AlgebraicClosure ℚ) ^ p = 1 := by
      simpa only [pow_one] using character_pow hp hq hpq A hA 1 γ
    have ho := orderOf_eq_prime hpow hne
    have hz := IsPrimitiveRoot.orderOf (character hp hq hpq A hA 1 γ : AlgebraicClosure ℚ)
    rw [ho] at hz
    simpa only [Nat.zero_add, pow_one] using hz
  | succ n ih =>
    have hc := ratio_compat hp (q := q) τ (n + 1) 1
    rw [pow_one] at hc
    change (character hp hq hpq A hA (n + 1 + 1) γ : AlgebraicClosure ℚ) ^ p =
      (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) at hc
    have hfin := character_pow hp hq hpq A hA (n + 1 + 1) γ
    have hnot : ¬ (character hp hq hpq A hA (n + 1 + 1) γ : AlgebraicClosure ℚ) ^ (p ^ (n + 1)) = 1 := by
      intro he
      rw [pow_succ' p n, pow_mul, hc] at he
      have hd := (ih.pow_eq_one_iff_dvd (p ^ n)).mp he
      have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
      omega
    have ho := orderOf_eq_prime_pow hnot hfin
    have hz := IsPrimitiveRoot.orderOf (character hp hq hpq A hA (n + 1 + 1) γ : AlgebraicClosure ℚ)
    rwa [ho] at hz

/-- 証明済みの存在定理から選ぶ、全段で同じ実際の慣性元。 -/
def generator : inertiaSubgroupIn A ℚ := Classical.choose (exists_primitive_generator hp hq hpq A hA)

/-- 選んだ同じ元は全ての正の根の段で原始的に作用する。 -/
theorem generator_primitive (n : ℕ) :
    IsPrimitiveRoot (character hp hq hpq A hA (n + 1) (generator hp hq hpq A hA) : AlgebraicClosure ℚ)
      (p ^ (n + 1)) := Classical.choose_spec (exists_primitive_generator hp hq hpq A hA) n

end
end DkMath.Lib.NumberTheory.InertiaRadical
