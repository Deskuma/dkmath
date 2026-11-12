/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow.lean,
blob f822d78971d75cb0036dcd0474e0f36b234ef36a.
Modified: DkMath namespace, focused imports, textbook explanation, and a reusable
finite p-group criterion for the cyclicity invariant of lifted torsion towers.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.Lib.Algebra.PrimePowerCyclicCriterion"

/-!
# 次段の捩れ部分群でも巡回性を保持する

位数 `p^m` と捩れ指数の冪だけでは巡回性は従わない。必要なのは
`p` 倍で消える元が高々 `p` 個であるという条件である。

まず倍写像の像と核を数えて、全ての `p^k` 捩れの濃度を `p^k` 以下に抑える。
任意の `n` 捩れは、群を消す `p^m` と `n` の gcd による捩れと一致する。
従って全ての `n` で `#G[n]≤n` となり、Mathlib の有限巡回群判定を適用できる。
この補題により、補直線から持ち上げた次段も巡回であると証明し、塔の帰納不変量を保つ。
-/

namespace DkMath.Lib.Algebra.PrimePowerCyclicCriterion

private lemma torsion_card_step {G : Type*} [AddCommGroup G] [Finite G] (p k : ℕ)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p)
    (ih : Nat.card {x : G // p ^ k • x = 0} ≤ p ^ k) :
    Nat.card {x : G // p ^ (k + 1) • x = 0} ≤ p ^ (k + 1) := by
  let K : AddSubgroup G := (nsmulAddMonoidHom (α := G) (p ^ (k + 1))).ker
  let φ : K →+ G := (nsmulAddMonoidHom (α := G) (p ^ k)).domRestrict K
  have hKmem : ∀ x : G, x ∈ K ↔ p ^ (k + 1) • x = 0 := fun x => AddMonoidHom.mem_ker
  have hφapp : ∀ x : K, φ x = p ^ k • (x : G) := fun x => rfl
  have key : Nat.card K = Nat.card φ.range * Nat.card φ.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
  have hrange : Nat.card φ.range ≤ p := by
    have hmap : ∀ y : φ.range, p • (y : G) = 0 := by
      rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
      change p • φ x = 0
      rw [hφapp x, ← mul_nsmul', ← pow_succ']
      exact (hKmem (x : G)).mp x.2
    exact le_trans
      (Nat.card_le_card_of_injective (fun y => ⟨(y : G), hmap y⟩)
        (fun a b hab => by
          have h1 := Subtype.ext_iff.mp hab
          exact Subtype.ext h1)) hsocle
  have hker : Nat.card φ.ker ≤ p ^ k := by
    have hmem : ∀ y : φ.ker, p ^ k • ((y : K) : G) = 0 := by
      rintro ⟨y, hy⟩
      have h0 : φ y = 0 := AddMonoidHom.mem_ker.mp hy
      rw [hφapp y] at h0
      exact h0
    exact le_trans
      (Nat.card_le_card_of_injective (fun y => ⟨((y : K) : G), hmem y⟩)
        (fun a b hab => by
          have h1 := Subtype.ext_iff.mp hab
          exact Subtype.ext (Subtype.ext h1))) ih
  calc Nat.card {x : G // p ^ (k + 1) • x = 0}
      = Nat.card K := Nat.card_congr (Equiv.subtypeEquivRight fun x => (hKmem x).symm)
    _ = Nat.card φ.range * Nat.card φ.ker := key
    _ ≤ p * p ^ k := Nat.mul_le_mul hrange hker
    _ = p ^ (k + 1) := (pow_succ' p k).symm

private lemma nsmul_torsion_card_le {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ}
    (hp : p.Prime) {m : ℕ} (hexp : ∀ x : G, p ^ m • x = 0)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p) {n : ℕ} (hn : 0 < n) :
    Nat.card {x : G // n • x = 0} ≤ n := by
  have tower : ∀ k : ℕ, Nat.card {x : G // p ^ k • x = 0} ≤ p ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact torsion_card_step p k hsocle ih
  obtain ⟨j, hjm, hdj⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n (p ^ m))
  have hpj_dvd_n : p ^ j ∣ n := hdj ▸ Nat.gcd_dvd_left n (p ^ m)
  have hiff : ∀ x : G, n • x = 0 ↔ p ^ j • x = 0 := by
    intro x
    constructor
    · intro hx
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp
        (hdj ▸ Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hx)
          (addOrderOf_dvd_of_nsmul_eq_zero (hexp x)))
    · intro hx
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mp
        ((addOrderOf_dvd_of_nsmul_eq_zero hx).trans hpj_dvd_n)
  calc Nat.card {x : G // n • x = 0}
      = Nat.card {x : G // p ^ j • x = 0} := Nat.card_congr (Equiv.subtypeEquivRight hiff)
    _ ≤ p ^ j := tower j
    _ ≤ n := Nat.le_of_dvd hn hpj_dvd_n

/-- 有限 `p` 群で `p` 捩れが高々 `p` 個なら巡回であり、群の位数は指定した冪を割る。
`p` 捩れ濃度の条件を落とすと、二次元の `p` 捩れ群が反例になる。 -/
theorem isAddCyclic_and_card_dvd_of_prime_power_exponent
    {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (m : ℕ)
    (hexp : ∀ x : G, p ^ m • x = 0)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p) :
    IsAddCyclic G ∧ Nat.card G ∣ p ^ m := by
  have hcyc : IsAddCyclic G := by
    cases nonempty_fintype G
    classical
    refine isAddCyclic_of_card_nsmul_eq_zero_le fun n hn => ?_
    have h := nsmul_torsion_card_le hp hexp hsocle hn
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  refine ⟨hcyc, ?_⟩
  have : IsAddCyclic G := hcyc
  rw [← IsAddCyclic.exponent_eq_card]
  exact AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero hexp


end DkMath.Lib.Algebra.PrimePowerCyclicCriterion
