/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_sum_eq_zero_of_forall_mem_iff_smul_eq_zero.lean.
Upstream blob: 9ef7b6e7a069030c8f12e05baf7d44cb9e9983c4
Modified for DkMath: isolate group theory; supply actual two-torsion cardinality separately.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Parity

#print "file: DkMath.Lib.Algebra.FiniteTorsionSum"

/-!
# 有限なねじれ点の総和と、四元2-torsionの役割

逆元の異なる点P,−Pは打ち消し合い、総和には2P=0の点だけが残る。
奇数nの核ではその点も零。偶数nの核では2-torsion全体が残る。
2-torsionが四元なら0,A,B,A+Bであり、その総和も零になる。
この議論は一般可換群の補題であり、楕円曲線の幾何学を仮定しない。
-/
namespace DkMath.Lib.Algebra.FiniteTorsionSum

/-- 四元の2-torsionは0,A,B,A+Bであり、総和は2A+2B=0である。
位数2の群では総和が非零なので、四元という条件は省略できない。 -/
theorem sum_eq_zero_of_two_torsion_card_four {M : Type*} [AddCommGroup M]
    (T : Finset M) (hT : ∀ P, P ∈ T ↔ 2 • P = 0) (hcard : T.card = 4) : ∑ P ∈ T, P = 0 := by
  classical
  obtain ⟨A, hA, hA0⟩ : ∃ A ∈ T, A ≠ 0 := by
    by_contra! hall
    have hsub : T ⊆ {0} := fun P hP => Finset.mem_singleton.mpr (hall P hP)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨B, hB, hB0, hBA⟩ : ∃ B ∈ T, B ≠ 0 ∧ B ≠ A := by
    by_contra! hall
    have hsub : T ⊆ {0, A} := fun P hP => by
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases hP0 : P = 0
      · exact Or.inl hP0
      · exact Or.inr (hall P hP hP0)
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  have h2A : 2 • A = 0 := (hT A).mp hA
  have h2B : 2 • B = 0 := (hT B).mp hB
  have hAB : A + B ∈ T := (hT _).mpr (by rw [nsmul_add, h2A, h2B, add_zero])
  have hAB0 : A + B ≠ 0 := fun h => hBA <| by
    rw [two_nsmul] at h2A
    calc B = -A := eq_neg_of_add_eq_zero_right h
      _ = A := neg_eq_of_add_eq_zero_left h2A
  have hABA : A + B ≠ A := fun h => hB0 (add_eq_left.mp h)
  have hABB : A + B ≠ B := fun h => hA0 (add_eq_right.mp h)
  have h0 : (0 : M) ∈ T := (hT 0).mpr (nsmul_zero 2)
  have hsub : ({0, A, B, A + B} : Finset M) ⊆ T := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : ({0, A, B, A + B} : Finset M).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hABB.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hBA.symm, hABA.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hA0.symm, hB0.symm, hAB0.symm⟩
  have heq : ({0, A, B, A + B} : Finset M) = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard4])
  rw [← heq, Finset.sum_insert, Finset.sum_insert, Finset.sum_pair hABB.symm]
  · have : (0 : M) + (A + (B + (A + B))) = 2 • A + 2 • B := by abel
    rw [this, h2A, h2B, add_zero]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hBA.symm, hABA.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hA0.symm, hB0.symm, hAB0.symm⟩

/-- n倍写像の核の総和。逆元で相殺した後、偶奇で残る2-torsionを分類する。
四元性は2倍写像の核についてのみ必要であり、nの核の位数n²はここでは仮定しない。 -/
theorem sum_kernel_eq_zero {G : Type*} [AddCommGroup G]
    (hcard2 : Nat.card {P : G // 2 • P = 0} = 4)
    (n : ℕ) (s : Finset G) (hs : ∀ P, P ∈ s ↔ n • P = 0) : ∑ P ∈ s, P = 0 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not s (fun P => 2 • P = 0)]
  -- 非固定点は逆元と対にして相殺する。
  have hrest : ∑ P ∈ s.filter (fun P => ¬2 • P = 0), P = 0 := by
    refine Finset.sum_involution (fun P _ => -P) (fun P _ => add_neg_cancel P)
      (fun P hP _ => ?_) (fun P hP => ?_) (fun P _ => neg_neg P)
    · rw [Finset.mem_filter] at hP
      intro h
      apply hP.2
      rw [two_nsmul]
      nth_rw 1 [← h]
      exact neg_add_cancel P
    · rw [Finset.mem_filter] at hP ⊢
      refine ⟨(hs _).mpr ?_, ?_⟩
      · rw [smul_neg, (hs _).mp hP.1, _root_.neg_zero]
      · rw [smul_neg, neg_eq_zero]
        exact hP.2
  rw [hrest, add_zero]
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · set T := s.filter (fun P => 2 • P = 0) with hTdef
    have hT : ∀ P, P ∈ T ↔ 2 • P = 0 := fun P => by
      rw [hTdef, Finset.mem_filter, and_iff_right_iff_imp]
      intro h2P
      rw [hs, ← two_mul, mul_nsmul, h2P, nsmul_zero]
    have hcard : T.card = 4 := by
      rw [← Nat.card_eq_finsetCard, ← hcard2]
      exact Nat.card_congr (Equiv.subtypeEquivRight hT)
    exact sum_eq_zero_of_two_torsion_card_four T hT hcard
  · refine Finset.sum_eq_zero fun P hP => ?_
    rw [Finset.mem_filter] at hP
    obtain ⟨hPs, h2P⟩ := hP
    have hnP := (hs P).mp hPs
    rwa [add_nsmul, one_nsmul, mul_nsmul, h2P, nsmul_zero, zero_add] at hnP


end DkMath.Lib.Algebra.FiniteTorsionSum
