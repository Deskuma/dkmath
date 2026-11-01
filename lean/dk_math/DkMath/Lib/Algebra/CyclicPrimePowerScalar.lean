/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card

#print "file: DkMath.Lib.Algebra.CyclicPrimePowerScalar"

/-!
# 巡回 `p` 群の底と最上商で同じスカラーを読む

位数 `p^m` の有限巡回群では `pK = K[p^(m-1)]`。この等式を倍写像の像と核の
濃度から証明する。従って自己準同型が `K[p]` 上で `c` 倍なら、`K/pK` 上でも
`c` 倍となる。元の群 `K` 全体で `c` 倍であるとは主張しない。

この区別により、捩れ塔の第一段だけの `pK=0` を全段へ誤用せずに済む。
巡回性と `m≥1` は証明の必須条件である。
-/

namespace DkMath.Lib.Algebra.CyclicPrimePowerScalar

variable {K : Type*} [AddCommGroup K] [Finite K] [IsAddCyclic K]

/-- 有限巡回 `p^m` 群の `p` 倍像は、`p^(m-1)` 倍写像の核そのもの。 -/
theorem range_nsmul_eq_ker {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hcard : Nat.card K = p ^ m) :
    (nsmulAddMonoidHom p : K →+ K).range =
      (nsmulAddMonoidHom (p ^ (m - 1)) : K →+ K).ker := by
  have hexp (x : K) : p ^ m • x = 0 := hcard ▸ card_nsmul_eq_zero' (x := x)
  have hle : (nsmulAddMonoidHom p : K →+ K).range ≤
      (nsmulAddMonoidHom (p ^ (m - 1)) : K →+ K).ker := by
    rintro _ ⟨x, rfl⟩
    change p ^ (m - 1) • (p • x) = 0
    rw [← mul_nsmul', ← pow_succ, Nat.sub_add_cancel hm]
    exact hexp x
  have hrange : Nat.card (nsmulAddMonoidHom p : K →+ K).range = p ^ (m - 1) := by
    rw [IsAddCyclic.card_nsmulAddMonoidHom_range, hcard,
      Nat.gcd_eq_right (dvd_pow_self p (by omega : m ≠ 0))]
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  have hker : Nat.card (nsmulAddMonoidHom (p ^ (m - 1)) : K →+ K).ker = p ^ (m - 1) := by
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, hcard,
      Nat.gcd_eq_right (pow_dvd_pow p (by omega : m - 1 ≤ m))]
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, SetLike.coe_sort_coe, hrange, hker]

/-- 底の `p` 捩れ上のスカラー作用から、最上商 `K/pK` 上の作用を得る。
結論は差が `p` 倍像に入ることであり、`K` 全体でのスカラー性ではない。 -/
theorem sub_nsmul_mem_range_of_socle {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (hcard : Nat.card K = p ^ m) (f : K →+ K) (c : ℕ)
    (hsocle : ∀ x : K, p • x = 0 → f x = c • x) (x : K) :
    f x - c • x ∈ (nsmulAddMonoidHom p : K →+ K).range := by
  rw [range_nsmul_eq_ker hp hm hcard]
  change p ^ (m - 1) • (f x - c • x) = 0
  have hx : p • (p ^ (m - 1) • x) = 0 := by
    rw [← mul_nsmul', ← pow_succ', Nat.sub_add_cancel hm]
    exact hcard ▸ card_nsmul_eq_zero' (x := x)
  rw [nsmul_sub, ← map_nsmul, hsocle _ hx, smul_comm (p ^ (m - 1)) c, sub_self]

/-- 巡回塔の `p` 捩れは、含まれる位数 `p` の底部分群そのもの。
底への包含を段ごとの追加 provider にせず、巡回性から取り出す。 -/
theorem socle_mem_of_prime_subgroup {G : Type*} [AddCommGroup G]
    {p m : ℕ} (_hp : p.Prime) (hm : 1 ≤ m)
    (K B : AddSubgroup G) [Finite K] [IsAddCyclic K]
    (hcard : Nat.card K = p ^ m) (hBK : B ≤ K) (hBcard : Nat.card B = p)
    (hBkill : ∀ x ∈ B, p • x = 0) {x : G} (hx : x ∈ K) (hpx : p • x = 0) :
    x ∈ B := by
  let f : B → (nsmulAddMonoidHom p : K →+ K).ker := fun b =>
    ⟨⟨b.val, hBK b.property⟩, Subtype.ext (hBkill b.val b.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : (nsmulAddMonoidHom p : K →+ K).ker => z.val.val) hab)
  have hker : Nat.card (nsmulAddMonoidHom p : K →+ K).ker = p := by
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, hcard,
      Nat.gcd_eq_right (dvd_pow_self p (by omega : m ≠ 0))]
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hBcard.trans hker.symm⟩).2
  obtain ⟨b, hb⟩ := hsurj ⟨⟨x, hx⟩, Subtype.ext hpx⟩
  have heq : b.val = x :=
    congrArg (fun z : (nsmulAddMonoidHom p : K →+ K).ker => z.val.val) hb
  exact heq ▸ b.property

end DkMath.Lib.Algebra.CyclicPrimePowerScalar
