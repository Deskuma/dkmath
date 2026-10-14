import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree

namespace DkMathTest

open scoped BigOperators

def support (R S : ℕ) : Finset ℕ := R.primeFactors ∪ S.primeFactors

def d1 (R S : ℕ) : ℕ :=
  ∏ q ∈ (support R S).filter (fun q => R.factorization q % 3 = 1), q

def d2 (R S : ℕ) : ℕ :=
  ∏ q ∈ (support R S).filter (fun q => R.factorization q % 3 = 2), q

def cubePart (R S : ℕ) : ℕ :=
  ∏ q ∈ support R S, q ^ (R.factorization q / 3)

def cubePartS (R S : ℕ) : ℕ :=
  ∏ q ∈ support R S, q ^ (S.factorization q / 3)

lemma exponent_mod_three (e : ℕ) :
    e = (if e % 3 = 1 then 1 else 0) +
        2 * (if e % 3 = 2 then 1 else 0) + 3 * (e / 3) := by
  by_cases h1 : e % 3 = 1 <;> by_cases h2 : e % 3 = 2 <;>
    simp [h1, h2] <;>
    omega

lemma complementary_exponent (eR eS ea : ℕ) (h : eR + eS = 3 * ea) :
    eS = 2 * (if eR % 3 = 1 then 1 else 0) +
        (if eR % 3 = 2 then 1 else 0) + 3 * (eS / 3) := by
  by_cases h1 : eR % 3 = 1 <;> by_cases h2 : eR % 3 = 2
  all_goals
    simp [h1, h2]
    omega

lemma prime_product_pow_mod_three (_T : Finset ℕ) (e : ℕ)
    (q : ℕ) :
    q ^ e =
      (if e % 3 = 1 then q else 1) *
        (if e % 3 = 2 then q else 1) ^ 2 *
          (q ^ (e / 3)) ^ 3 := by
  by_cases h1 : e % 3 = 1 <;> by_cases h2 : e % 3 = 2
  all_goals
    first
    | omega
    | (have he : e = (if e % 3 = 1 then 1 else 0) +
          2 * (if e % 3 = 2 then 1 else 0) + 3 * (e / 3) := by
          simp [h1, h2]
          omega
       calc
         q ^ e = q ^ ((if e % 3 = 1 then 1 else 0) +
             2 * (if e % 3 = 2 then 1 else 0) + 3 * (e / 3)) :=
           congrArg (fun n => q ^ n) he
         _ = (if e % 3 = 1 then q else 1) *
             (if e % 3 = 2 then q else 1) ^ 2 *
               (q ^ (e / 3)) ^ 3 := by
           have h12 : ¬(1 : ℕ) = 2 := by omega
           have h21 : ¬(2 : ℕ) = 1 := by omega
           simp only [h1, h2, ite_eq_left, ite_false, pow_zero,
             one_pow, one_mul, mul_one, mul_zero, pow_one, pow_add,
             h12, h21]
           rw [← pow_mul, Nat.mul_comm (e / 3) 3]
           )

lemma complementary_product_pow (eR eS ea q : ℕ)
    (h : eR + eS = 3 * ea) :
    q ^ eS = (if eR % 3 = 1 then q else 1) ^ 2 *
        (if eR % 3 = 2 then q else 1) * (q ^ (eS / 3)) ^ 3 := by
  by_cases h1 : eR % 3 = 1 <;> by_cases h2 : eR % 3 = 2
  all_goals
    first
    | omega
    | (have he := complementary_exponent eR eS ea h
       calc
         q ^ eS = q ^ (2 * (if eR % 3 = 1 then 1 else 0) +
             (if eR % 3 = 2 then 1 else 0) + 3 * (eS / 3)) :=
           congrArg (fun n => q ^ n) he
         _ = (if eR % 3 = 1 then q else 1) ^ 2 *
             (if eR % 3 = 2 then q else 1) * (q ^ (eS / 3)) ^ 3 := by
           have h12 : ¬(1 : ℕ) = 2 := by omega
           have h21 : ¬(2 : ℕ) = 1 := by omega
           simp only [h1, h2, ite_eq_left, ite_false, pow_zero,
             one_pow, one_mul, mul_one, mul_zero, pow_one, pow_add,
             h12, h21]
           rw [← pow_mul, Nat.mul_comm (eS / 3) 3])

lemma d1_d2_squarefree (R S : ℕ) (hT : ∀ q ∈ support R S, q.Prime) :
    Squarefree (d1 R S) ∧ Squarefree (d2 R S) := by
  constructor
  · unfold d1
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hT p (Finset.mem_filter.mp hp).1)
        (hT q (Finset.mem_filter.mp hq).1)).mpr hpq
    · intro p hp
      exact (hT p (Finset.mem_filter.mp hp).1).squarefree
  · unfold d2
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hT p (Finset.mem_filter.mp hp).1)
        (hT q (Finset.mem_filter.mp hq).1)).mpr hpq
    · intro p hp
      exact (hT p (Finset.mem_filter.mp hp).1).squarefree

lemma support_prime (R S : ℕ) (_hR : R ≠ 0) (_hS : S ≠ 0)
    {q : ℕ} (hq : q ∈ support R S) : q.Prime := by
  rcases Finset.mem_union.mp hq with hq | hq
  · exact Nat.prime_of_mem_primeFactors hq
  · exact Nat.prime_of_mem_primeFactors hq

lemma product_on_support (R S : ℕ) (hR : R ≠ 0) (hS : S ≠ 0)
    (n : ℕ) (hn : n = R) :
    n = ∏ q ∈ support R S, q ^ (R.factorization q) := by
  subst n
  calc
    R = ∏ q ∈ R.primeFactors, q ^ R.factorization q :=
      Nat.prod_primeFactors_pow_factorization hR
    _ = ∏ q ∈ support R S, q ^ R.factorization q := by
      apply Finset.prod_subset_one_on_sdiff
      · exact Finset.subset_union_left
      · intro q hq
        have hqR : q ∉ R.primeFactors := (Finset.mem_sdiff.mp hq).2
        have hqnot : ¬q ∣ R := by
          intro hdiv
          apply hqR
          exact (Nat.mem_primeFactors_of_ne_zero hR).mpr
            ⟨support_prime R S hR hS (Finset.mem_sdiff.mp hq).1, hdiv⟩
        simp [Nat.factorization_eq_zero_of_not_dvd hqnot]
      · intro q hq
        rfl

lemma d1_d2_u_reconstruction (R S : ℕ) (hR : R ≠ 0) (hS : S ≠ 0) :
    R = d1 R S * d2 R S ^ 2 * cubePart R S ^ 3 := by
  calc
    R = ∏ q ∈ support R S, q ^ R.factorization q :=
      product_on_support R S hR hS R rfl
    _ = d1 R S * d2 R S ^ 2 * cubePart R S ^ 3 := by
      unfold d1 d2 cubePart
      rw [Finset.prod_filter, Finset.prod_filter]
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q hq
      exact prime_product_pow_mod_three (support R S) (R.factorization q) q

lemma d1_d2_v_reconstruction (R S a : ℕ) (hR : R ≠ 0) (hS : S ≠ 0)
    (hledger : ∀ q, R.factorization q + S.factorization q =
      3 * a.factorization q) :
    S = d1 R S ^ 2 * d2 R S * cubePartS R S ^ 3 := by
  have hprod : S = ∏ q ∈ support R S, q ^ S.factorization q := by
    simpa [support, Finset.union_comm] using
      (product_on_support S R hS hR S rfl)
  calc
    S = ∏ q ∈ support R S, q ^ S.factorization q := hprod
    _ = d1 R S ^ 2 * d2 R S * cubePartS R S ^ 3 := by
      unfold d1 d2 cubePartS
      rw [Finset.prod_filter, Finset.prod_filter]
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q hq
      exact complementary_product_pow (R.factorization q) (S.factorization q)
        (a.factorization q) q (hledger q)

lemma d1_d2_coprime (R S : ℕ) (hT : ∀ q ∈ support R S, q.Prime) :
    Nat.Coprime (d1 R S) (d2 R S) := by
  let P1 : ℕ → Prop := fun q => R.factorization q % 3 = 1
  let P2 : ℕ → Prop := fun q => R.factorization q % 3 = 2
  have hdis : Disjoint ((support R S).filter P1) ((support R S).filter P2) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have h1 := (Finset.mem_filter.mp hq1).2
    have h2 := (Finset.mem_filter.mp hq2).2
    dsimp [P1, P2] at h1 h2
    omega
  have hunion : (support R S).filter P1 ∪ (support R S).filter P2 =
      (support R S).filter (fun q => P1 q ∨ P2 q) := by
    ext q
    have hp : ((q ∈ support R S ∧ P1 q) ∨ (q ∈ support R S ∧ P2 q)) ↔
        (q ∈ support R S ∧ (P1 q ∨ P2 q)) := by
      constructor
      · rintro (⟨hq, hq1⟩ | ⟨hq, hq2⟩)
        · exact ⟨hq, Or.inl hq1⟩
        · exact ⟨hq, Or.inr hq2⟩
      · rintro ⟨hq, hq12⟩
        rcases hq12 with hq1 | hq2
        · exact Or.inl ⟨hq, hq1⟩
        · exact Or.inr ⟨hq, hq2⟩
    simpa only [Finset.mem_union, Finset.mem_filter] using hp
  have hprod : d1 R S * d2 R S =
      ∏ q ∈ (support R S).filter (fun q => P1 q ∨ P2 q), q := by
    have hprod' :
        (∏ q ∈ (support R S).filter P1, q) *
            ∏ q ∈ (support R S).filter P2, q =
          ∏ q ∈ (support R S).filter (fun q => P1 q ∨ P2 q), q := by
      rw [← Finset.prod_union hdis, hunion]
    simpa [d1, d2, P1, P2] using hprod'
  have hsq : Squarefree (d1 R S * d2 R S) := by
    rw [hprod]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hT p (Finset.mem_filter.mp hp).1)
        (hT q (Finset.mem_filter.mp hq).1)).mpr hpq
    · intro p hp
      exact (hT p (Finset.mem_filter.mp hp).1).squarefree
  exact Nat.coprime_of_squarefree_mul hsq

end DkMathTest
