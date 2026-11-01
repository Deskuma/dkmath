/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean,
blob 487cb23e86902f431d7cebdd9211b5c40653f0a7;
private pow_smul_eq_zero_of_kill and the two-anchor argument in core.
Modified: arbitrary additive groups and finite subgroups; explicit specialization
hypotheses; no modular-curve imports or unproved arithmetic providers.
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.Lib.Algebra.MazurStepThreeTwoAnchor"

/-!
# Mazur Step Three の二アンカー群論

この章は任意の可換加法群 `G` と、その有限部分群 `H` についての完成した群論。
実際のモジュラー曲線・Jacobian・Eisenstein 商は構成しない。

証明を三段階に分ける。

1. specialization `s` が `q` と素な位数の捩れ上で単射なら、`s z = 0` を満たす
   有限位数の `z` は `q` 冪で消える。`ord z = q^a*m`, `q ∤ m` と分解し、
   `q^a*z` に単射性を使う。`s` 自体の大域単射性は不要。
2. 互いに素な二つの冪で消える元は零。特に `2^a*z = 3^b*z = 0` なら `z=0`。
3. 二アンカーで `y=0` と分かった後、別住所で `s(y+c)=0` を仮定すると
   `s c=0`。`q` 冪捩れ上の追加単射性から `c=0` となり、`c ≠ 0` と矛盾する。

未実装の大域数学は、有限部分群 `H`、生き残る cusp 類 `c`、実際の各
specialization とその二種類の単射性を構成する工程である。これらの入力を
仮定から隠さず、群論を証明したことと Frey の一般 hno を区別する。
-/

namespace DkMath.Lib.Algebra.MazurStepThreeTwoAnchor

variable {G : Type*} [AddCommGroup G]

/-- 有限部分群の元は有限位数を持つ。周囲の群 `G` の有限性は不要。 -/
theorem addOrderOf_pos_of_mem_finite (H : AddSubgroup G) [Finite H]
    {z : G} (hz : z ∈ H) : 0 < addOrderOf z := by
  have h := (isOfFinAddOrder_of_finite (⟨z, hz⟩ : H)).addOrderOf_pos
  rw [← AddSubgroup.addOrderOf_coe] at h
  exact h

/-- specialization の核に入る有限有理部分群の元は、剰余素数 `q` の冪で消える。
`q` と素な位数の捩れについてだけ核が自明であれば十分である。 -/
theorem exists_prime_power_nsmul_eq_zero_of_specialization_zero
    (H : AddSubgroup G) [Finite H] {q : ℕ} (hq : q.Prime)
    {T : Type*} [AddCommGroup T] (s : G →+ T)
    (hprimeTo : ∀ z ∈ H, (∃ m : ℕ, ¬ q ∣ m ∧ m • z = 0) → s z = 0 → z = 0)
    {z : G} (hz : z ∈ H) (hs : s z = 0) :
    ∃ a : ℕ, q ^ a • z = 0 := by
  have hn : addOrderOf z ≠ 0 := (addOrderOf_pos_of_mem_finite H hz).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn q hq.ne_one
  refine ⟨a, hprimeTo (q ^ a • z) (H.nsmul_mem hz _) ⟨m, hm, ?_⟩ ?_⟩
  · rw [← mul_nsmul', mul_comm, ← hnm]
    exact addOrderOf_nsmul_eq_zero z
  · rw [map_nsmul, hs, nsmul_zero]

/-- 互いに素な二整数が同じ元を消せば、その元は零。
有限性を仮定せず、元の位数が二整数の gcd を割ることから示す。 -/
theorem eq_zero_of_coprime_nsmul {m n : ℕ} (hcop : m.Coprime n)
    {z : G} (hm : m • z = 0) (hn : n • z = 0) : z = 0 := by
  have hd : addOrderOf z ∣ 1 := by
    have h := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm)
      (addOrderOf_dvd_of_nsmul_eq_zero hn)
    simpa only [hcop.gcd_eq_one] using h
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

/-- 二つの異なる素数に限らず、互いに素な底の二冪での消滅から零を得る。 -/
theorem eq_zero_of_coprime_power_nsmul {r s : ℕ} (hrs : r.Coprime s)
    {z : G} (hr : ∃ a : ℕ, r ^ a • z = 0) (hs : ∃ b : ℕ, s ^ b • z = 0) :
    z = 0 := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  exact eq_zero_of_coprime_nsmul (hrs.pow a b) ha hb

/-- 有限部分群における2進・3進 specialization の共通核は自明。
ここで必要なのはそれぞれ prime-to-2 と prime-to-3 捩れ上の単射性だけ。 -/
theorem eq_zero_of_two_three_specializations
    (H : AddSubgroup G) [Finite H]
    {T₂ T₃ : Type*} [AddCommGroup T₂] [AddCommGroup T₃]
    (s₂ : G →+ T₂) (s₃ : G →+ T₃)
    (h₂ : ∀ z ∈ H, (∃ m : ℕ, ¬ 2 ∣ m ∧ m • z = 0) → s₂ z = 0 → z = 0)
    (h₃ : ∀ z ∈ H, (∃ m : ℕ, ¬ 3 ∣ m ∧ m • z = 0) → s₃ z = 0 → z = 0)
    {y : G} (hy : y ∈ H) (hy₂ : s₂ y = 0) (hy₃ : s₃ y = 0) : y = 0 := by
  exact eq_zero_of_coprime_power_nsmul (by decide : Nat.Coprime 2 3)
    (exists_prime_power_nsmul_eq_zero_of_specialization_zero H Nat.prime_two s₂ h₂ hy hy₂)
    (exists_prime_power_nsmul_eq_zero_of_specialization_zero H Nat.prime_three s₃ h₃ hy hy₃)

/-- Step Three の cusp 反証の全群論。
二アンカーの元 `y` が零となった後、`s(y+c)=0` は非零 cusp 類 `c` を消す。
prime-to-`q` 単射性で `c` を `q` 冪捩れへ制限し、`q` 冪捩れ上の単射性で排除する。
実際の `s₂,s₃,s` と `c` の供給は、利用側のモジュラー曲線の定理である。 -/
theorem nonzero_cusp_not_killed_after_two_anchors
    (H : AddSubgroup G) [Finite H]
    {T₂ T₃ T : Type*} [AddCommGroup T₂] [AddCommGroup T₃] [AddCommGroup T]
    (s₂ : G →+ T₂) (s₃ : G →+ T₃) (s : G →+ T)
    (h₂ : ∀ z ∈ H, (∃ m : ℕ, ¬ 2 ∣ m ∧ m • z = 0) → s₂ z = 0 → z = 0)
    (h₃ : ∀ z ∈ H, (∃ m : ℕ, ¬ 3 ∣ m ∧ m • z = 0) → s₃ z = 0 → z = 0)
    {q : ℕ} (hq : q.Prime)
    (hprimeTo : ∀ z ∈ H, (∃ m : ℕ, ¬ q ∣ m ∧ m • z = 0) → s z = 0 → z = 0)
    (hprimary : ∀ z ∈ H, (∃ a : ℕ, q ^ a • z = 0) → s z = 0 → z = 0)
    {y c : G} (hy : y ∈ H) (hc : c ∈ H) (hc0 : c ≠ 0)
    (hy₂ : s₂ y = 0) (hy₃ : s₃ y = 0) : s (y + c) ≠ 0 := by
  have hy0 := eq_zero_of_two_three_specializations H s₂ s₃ h₂ h₃ hy hy₂ hy₃
  intro hkill
  have hsc : s c = 0 := by simpa only [hy0, zero_add] using hkill
  have hpow := exists_prime_power_nsmul_eq_zero_of_specialization_zero H hq s hprimeTo hc hsc
  exact hc0 (hprimary c hc hpow hsc)

end DkMath.Lib.Algebra.MazurStepThreeTwoAnchor
