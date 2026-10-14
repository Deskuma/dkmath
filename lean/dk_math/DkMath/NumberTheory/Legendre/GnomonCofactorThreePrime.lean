/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonCofactorSemiprime
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Sort

#print "file: DkMath.NumberTheory.Legendre.GnomonCofactorThreePrime"

/-! A bounded ordered three-prime witness, without a factor-depth hierarchy. -/

namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Quotient endpoints enumerate ordered prime triples, with repetitions allowed. -/
def gnomonCofactorThreePrimeTriples (n k : ℕ) (S : Finset ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 2 (Nat.sqrt ((n ^ 2 + 2 * n) / k))).filter
    (fun r => r.Prime ∧ Nat.Coprime r (finitePrimeBasisProduct S) ∧
      r ^ 3 ≤ (n ^ 2 + 2 * n) / k)).biUnion (fun r =>
    ((Finset.Icc r (Nat.sqrt (((n ^ 2 + 2 * n) / k) / r))).filter
      (fun s => s.Prime ∧ Nat.Coprime s (finitePrimeBasisProduct S))).biUnion (fun s =>
        ((Finset.Icc (max s (max (n ^ 2 / k) (2 * n) / (r * s) + 1))
          (((n ^ 2 + 2 * n) / k) / (r * s))).filter
          (fun t => t.Prime ∧ Nat.Coprime t (finitePrimeBasisProduct S))).image
            (fun t => (r, s, t))))

private theorem triple_facts {n k : ℕ} {S : Finset ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ gnomonCofactorThreePrimeTriples n k S) :
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧
      p.1 * p.2.1 * p.2.2 ∈ gnomonCofactorSieveCandidates n k S := by
  obtain ⟨r, hr, hrest⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨s, hsMem, htRest⟩ := Finset.mem_biUnion.mp hrest
  obtain ⟨t, htMem, he⟩ := Finset.mem_image.mp htRest
  subst p
  obtain ⟨hrI, hrP, hrC, _⟩ := Finset.mem_filter.mp hr
  obtain ⟨hsI, hsP, hsC⟩ := Finset.mem_filter.mp hsMem
  obtain ⟨htI, htP, htC⟩ := Finset.mem_filter.mp htMem
  have hrs := (Finset.mem_Icc.mp hsI).1
  obtain ⟨htlo, hthi⟩ := Finset.mem_Icc.mp htI
  have hst := (le_max_left _ _).trans htlo
  have hlo : max (n ^ 2 / k) (2 * n) / (r * s) < t := by
    have := (le_max_right _ _).trans htlo
    omega
  have hA := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hrP.pos hsP.pos)).mp hlo
  have hB := (Nat.le_div_iff_mul_le (Nat.mul_pos hrP.pos hsP.pos)).mp hthi
  rw [Nat.mul_comm t (r * s)] at hA hB
  refine ⟨hrP, hsP, htP, hrs, hst, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hA, hB⟩
  · exact (hrC.mul_left hsC).mul_left htC

private theorem prime_list_perm {l m : List ℕ}
    (hl : ∀ p ∈ l, p.Prime) (hm : ∀ p ∈ m, p.Prime) (he : l.prod = m.prod) :
    l.Perm m :=
  (Nat.primeFactorsList_unique he hl).trans (Nat.primeFactorsList_unique rfl hm).symm

/-- Sorting and unique prime factorization handle repeated factors as well. -/
theorem gnomonCofactorThreePrime_product_injective {n k : ℕ} {S : Finset ℕ} :
    Set.InjOn (fun p : ℕ × ℕ × ℕ => p.1 * p.2.1 * p.2.2)
      (↑(gnomonCofactorThreePrimeTriples n k S)) := by
  intro a ha b hb he
  obtain ⟨ha1, ha2, ha3, ha12, ha23, _⟩ := triple_facts ha
  obtain ⟨hb1, hb2, hb3, hb12, hb23, _⟩ := triple_facts hb
  have hp : [a.1, a.2.1, a.2.2].Perm [b.1, b.2.1, b.2.2] :=
    prime_list_perm (by simp; tauto) (by simp; tauto) (by simpa [mul_assoc] using he)
  have heq := hp.eq_of_pairwise'
    (by simp [List.pairwise_cons]; omega : List.Pairwise (· ≤ ·) [a.1, a.2.1, a.2.2])
    (by simp [List.pairwise_cons]; omega : List.Pairwise (· ≤ ·) [b.1, b.2.1, b.2.2])
  simp only [List.cons.injEq, and_true] at heq
  exact Prod.ext heq.1 (Prod.ext heq.2.1 heq.2.2)

def gnomonCofactorThreePrimeWitnesses (n k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (gnomonCofactorThreePrimeTriples n k S).image (fun p => p.1 * p.2.1 * p.2.2)

/-- Prime-factor list lengths distinguish two factors from three. -/
theorem gnomonCofactorSemiprime_threePrime_disjoint (n k : ℕ) (S : Finset ℕ) :
    Disjoint (gnomonCofactorSemiprimeWitnesses n k S)
      (gnomonCofactorThreePrimeWitnesses n k S) := by
  apply Finset.disjoint_left.mpr
  intro q hq ht
  obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp hq
  obtain ⟨b, hb, hqb⟩ := Finset.mem_image.mp ht
  obtain ⟨hb1, hb2, hb3, _, _, _⟩ := triple_facts hb
  obtain ⟨hc, ha2⟩ := Finset.mem_filter.mp ha
  have ha1 : a.1.Prime := by
    obtain ⟨r, hr, hm⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨m, _, he⟩ := Finset.mem_image.mp hm
    subst a
    exact (Finset.mem_filter.mp hr).2.1
  have hp : [a.1, a.2].Perm [b.1, b.2.1, b.2.2] :=
    prime_list_perm (by simp; tauto) (by simp; tauto)
      (by simpa [mul_assoc] using hqa.trans hqb.symm)
  have hlen := hp.length_eq
  simp at hlen

/-- Combined distinct products, rather than a sum with possible double charging. -/
def gnomonCofactorThreePrimeCombinedWitnesses (n k : ℕ) (S : Finset ℕ) : Finset ℕ :=
  gnomonCofactorSemiprimeWitnesses n k S ∪ gnomonCofactorThreePrimeWitnesses n k S

noncomputable def gnomonCofactorThreePrimeCombinedMass (n : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (n - 1), ∑ q ∈ gnomonCofactorThreePrimeCombinedWitnesses n k S,
    Real.log (q : ℝ)

/-- Each newly admitted product is certainly composite and survives the wheel. -/
theorem gnomonCofactorThreePrimeCombined_subset_error (n k : ℕ) (S : Finset ℕ) :
    gnomonCofactorThreePrimeCombinedWitnesses n k S ⊆
      (gnomonCofactorSieveCandidates n k S).filter (fun q => ¬ q.Prime) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hs | ht
  · exact gnomonCofactorSemiprimeWitnesses_subset_error n k S hs
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hr, hs, ht, _, _, hc⟩ := triple_facts hp
    refine Finset.mem_filter.mpr ⟨hc, Nat.not_prime_mul ?_ ht.ne_one⟩
    have hmul := Nat.mul_le_mul hr.two_le hs.two_le
    omega

/-- Both weights are counted exactly once; the triple pair sum uses injectivity. -/
theorem gnomonCofactorThreePrimeCombinedMass_eq (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorThreePrimeCombinedMass n S = gnomonCofactorSemiprimeMass n S +
      ∑ k ∈ Finset.Icc 2 (n - 1), ∑ p ∈ gnomonCofactorThreePrimeTriples n k S,
        Real.log ((p.1 * p.2.1 * p.2.2 : ℕ) : ℝ) := by
  unfold gnomonCofactorThreePrimeCombinedMass gnomonCofactorSemiprimeMass
    gnomonCofactorThreePrimeCombinedWitnesses
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_union (gnomonCofactorSemiprime_threePrime_disjoint n k S)]
  unfold gnomonCofactorThreePrimeWitnesses
  rw [Finset.sum_image gnomonCofactorThreePrime_product_injective]

theorem gnomonCofactorThreePrimeCombinedMass_le_error (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorThreePrimeCombinedMass n S ≤ gnomonCofactorSieveCompositeError n S := by
  apply Finset.sum_le_sum
  intro k _
  apply Finset.sum_le_sum_of_subset_of_nonneg (gnomonCofactorThreePrimeCombined_subset_error n k S)
  intro q hq _
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))

noncomputable def gnomonCofactorThreePrimeBudget (n : ℕ) (S : Finset ℕ) : ℝ :=
  min (gnomonCofactorSemiprimeBudget n S)
    (gnomonCofactorSieveMass n S - gnomonCofactorThreePrimeCombinedMass n S)

theorem gnomonCofactorWindowMass_le_threePrimeBudget {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorWindowMass n ≤ gnomonCofactorThreePrimeBudget n S := by
  apply le_min (gnomonCofactorWindowMass_le_semiprimeBudget hn hS hbound)
  have he := gnomonCofactorSieveMass_eq_window_add_error hS hbound
  have hd := gnomonCofactorThreePrimeCombinedMass_le_error n S
  linarith

theorem gnomonCofactorThreePrimeBudget_le_semiprimeBudget (n : ℕ) (S : Finset ℕ) :
    gnomonCofactorThreePrimeBudget n S ≤ gnomonCofactorSemiprimeBudget n S := min_le_left _ _

theorem gnomonCofactorThreePrimeBudget_excess {n : ℕ} {S : Finset ℕ}
    (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n) :
    gnomonCofactorThreePrimeBudget n S - gnomonCofactorWindowMass n =
      min (gnomonCofactorSemiprimeBudget n S - gnomonCofactorWindowMass n)
        (gnomonCofactorSieveCompositeError n S - gnomonCofactorThreePrimeCombinedMass n S) := by
  unfold gnomonCofactorThreePrimeBudget
  rw [gnomonCofactorSieveMass_eq_window_add_error hS hbound, ← min_sub_sub_right]
  congr 1
  ring

theorem gnomonPascalOldLogBudget_threePrime_excess {n : ℕ} (hn : 3 ≤ n) (S : Finset ℕ) :
    gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorThreePrimeBudget n S + gnomonPascalShellHigherPrimePowerMass n =
    gnomonPascalOldLogBudget n +
      (gnomonCofactorThreePrimeBudget n S - gnomonCofactorWindowMass n) := by
  have h := gnomonPascalOldLogBudget_cofactor_excess hn
  linarith

theorem exists_prime_squareCell_of_threePrimeBudget_lt {n : ℕ} {S : Finset ℕ}
    (hn : 3 ≤ n) (hS : IsFinitePrimeBasis S) (hbound : ∀ q ∈ S, q ≤ 2 * n)
    (hstrict : gnomonPascalSmallCarryMass n + gnomonRepeatedCarryMass n +
      gnomonCofactorThreePrimeBudget n S + gnomonPascalShellHigherPrimePowerMass n <
        Real.log (GnomonPascalCell n : ℝ)) : ∃ p, p.Prime ∧ SquareCell n p := by
  apply (gnomonPascalOldLogBudget_lt_iff hn).mp
  have hb := gnomonCofactorWindowMass_le_threePrimeBudget hn hS hbound
  rw [gnomonPascalOldLogBudget_threePrime_excess hn S] at hstrict
  linarith

end DkMath.NumberTheory.Legendre
