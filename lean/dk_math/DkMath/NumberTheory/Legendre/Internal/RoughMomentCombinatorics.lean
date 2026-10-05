/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.Internal.PairCombinatorics
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

#print "file: DkMath.NumberTheory.Legendre.Internal.RoughMomentCombinatorics"

namespace DkMath.NumberTheory
open scoped BigOperators

theorem zero_pair_triple_balance {k : ℕ} (hk : k ≤ 3) :
    (if k = 0 then 1 else 0) + k + Nat.choose k 3 = 1 + Nat.choose k 2 := by
  interval_cases k <;> decide

theorem excess_pair_triple_balance {k : ℕ} (hk : k ≤ 3) :
    (k - 1) + Nat.choose k 3 = Nat.choose k 2 := by
  interval_cases k <;> decide

/-- Increasing triples are unique representatives of unordered three-element subsets. -/
def upperTriples (t : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (t.product (t.product t)).filter (fun a => a.1 < a.2.1 ∧ a.2.1 < a.2.2)

@[simp] theorem mem_upperTriples {t : Finset ℕ} {p q s : ℕ} :
    (p, q, s) ∈ upperTriples t ↔ p ∈ t ∧ q ∈ t ∧ s ∈ t ∧ p < q ∧ q < s := by
  simp [upperTriples, and_assoc]

theorem exists_ordered_triple_of_card_three {t : Finset ℕ} (ht : t.card = 3) :
    ∃ p q s, p < q ∧ q < s ∧ t = {p, q, s} := by
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp ht
  subst t
  by_cases h₁ : a < b
  · by_cases h₂ : b < c
    · exact ⟨a, b, c, h₁, h₂, rfl⟩
    · by_cases h₃ : a < c
      · exact ⟨a, c, b, h₃, by omega, by ext x; simp; tauto⟩
      · exact ⟨c, a, b, by omega, h₁, by ext x; simp; tauto⟩
  · by_cases h₂ : a < c
    · exact ⟨b, a, c, by omega, h₂, by ext x; simp; tauto⟩
    · by_cases h₃ : b < c
      · exact ⟨b, c, a, h₃, by omega, by ext x; simp; tauto⟩
      · exact ⟨c, b, a, by omega, by omega, by ext x; simp; tauto⟩

theorem upperTriples_three {p q s : ℕ} (hpq : p < q) (hqs : q < s) :
    upperTriples {p, q, s} = {(p, q, s)} := by
  ext a
  rcases a with ⟨a, b, c⟩
  simp only [mem_upperTriples, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- Only the bounded local version is needed; the outer prime universe is unrestricted. -/
theorem card_upperTriples_eq_choose_of_le_three {t : Finset ℕ} (ht : t.card ≤ 3) :
    (upperTriples t).card = Nat.choose t.card 3 := by
  by_cases he : t.card = 3
  · obtain ⟨p, q, s, hpq, hqs, rfl⟩ := exists_ordered_triple_of_card_three he
    rw [upperTriples_three hpq hqs]
    simpa only [Finset.card_singleton, he] using (show 1 = Nat.choose 3 3 by decide)
  · have hh : (upperTriples t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      rcases a with ⟨p, q, s⟩
      obtain ⟨hp, hq, hs, hpq, hqs⟩ := mem_upperTriples.mp ha
      have hsub : ({p, q, s}:Finset ℕ) ⊆ t := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hc : ({p, q, s}:Finset ℕ).card = 3 := by
        simp [hpq.ne, hqs.ne, (hpq.trans hqs).ne]
      have := Finset.card_le_card hsub
      omega
    rw [hh, Finset.card_empty, Nat.choose_eq_zero_of_lt (by omega)]

/-- Counting an existing finite seat/label relation in the seat direction. -/
theorem card_product_filter_mem {α β : Type*} [DecidableEq β]
    (R : Finset α) (A : Finset β) (f : α → Finset β)
    (hf : ∀ r ∈ R, f r ⊆ A) :
    ((R.product A).filter (fun i => i.2 ∈ f i.1)).card = ∑ r ∈ R, (f r).card := by
  classical
  rw [Finset.card_filter]
  trans ∑ r ∈ R, ∑ a ∈ A, if a ∈ f r then (1 : ℕ) else 0
  · exact Finset.sum_product' R A (fun r a => if a ∈ f r then (1 : ℕ) else 0)
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_boole]
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hf r hr h, h⟩⟩

end DkMath.NumberTheory
