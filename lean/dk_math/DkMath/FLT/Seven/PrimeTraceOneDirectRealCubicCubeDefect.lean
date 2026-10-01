/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicResidueSupport
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree

namespace DkMath.FLT.Seven

open SevenRealCubicInt
open scoped BigOperators
open scoped NumberField

/-! ## Neutral cube-defect products -/

def cubeDefectSupport (R S : ℕ) : Finset ℕ := R.primeFactors ∪ S.primeFactors

def cubeDefectD1 (R S : ℕ) : ℕ :=
  ∏ q ∈ (cubeDefectSupport R S).filter
    (fun q => R.factorization q % 3 = 1), q

def cubeDefectD2 (R S : ℕ) : ℕ :=
  ∏ q ∈ (cubeDefectSupport R S).filter
    (fun q => R.factorization q % 3 = 2), q

def cubeDefectU (R S : ℕ) : ℕ :=
  ∏ q ∈ cubeDefectSupport R S, q ^ (R.factorization q / 3)

def cubeDefectV (R S : ℕ) : ℕ :=
  ∏ q ∈ cubeDefectSupport R S, q ^ (S.factorization q / 3)

def exceptionalModSeven (q : ℕ) : Prop := q % 7 = 1 ∨ q % 7 = 6

theorem cubeDefect_factorization_ledger
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) (hRS : R * S = a ^ 3)
    (q : ℕ) :
    R.factorization q + S.factorization q = 3 * a.factorization q := by
  have h := congrArg (fun n => n.factorization q) hRS
  rw [Nat.factorization_mul hR hS, Nat.factorization_pow] at h
  simpa [Finsupp.add_apply, Pi.smul_apply] using h

theorem cubeDefect_off_exception
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) (hRS : R * S = a ^ 3)
    (hcommon : ∀ q, q.Prime → q ∣ R → q ∣ S → exceptionalModSeven q)
    {q : ℕ} (hq : q.Prime) (hqe : ¬exceptionalModSeven q) (hqR : q ∣ R) :
    S.factorization q = 0 ∧ 3 ∣ R.factorization q := by
  have hqS : ¬q ∣ S := by
    intro hqS
    exact hqe (hcommon q hq hqR hqS)
  have hledger := cubeDefect_factorization_ledger hR hS hRS q
  have hzero : S.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqS
  refine ⟨hzero, ?_⟩
  refine ⟨a.factorization q, ?_⟩
  omega

theorem cubeDefect_off_exception_symm
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) (hRS : R * S = a ^ 3)
    (hcommon : ∀ q, q.Prime → q ∣ R → q ∣ S → exceptionalModSeven q)
    {q : ℕ} (hq : q.Prime) (hqe : ¬exceptionalModSeven q) (hqS : q ∣ S) :
    R.factorization q = 0 ∧ 3 ∣ S.factorization q := by
  have hqR : ¬q ∣ R := by
    intro hqR
    exact hqe (hcommon q hq hqR hqS)
  have hledger := cubeDefect_factorization_ledger hR hS hRS q
  have hzero : R.factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqR
  refine ⟨hzero, ?_⟩
  refine ⟨a.factorization q, ?_⟩
  omega

private theorem cubeDefect_exponent_mod_three (e : ℕ) :
    e = (if e % 3 = 1 then 1 else 0) +
        2 * (if e % 3 = 2 then 1 else 0) + 3 * (e / 3) := by
  by_cases h1 : e % 3 = 1 <;> by_cases h2 : e % 3 = 2 <;>
    simp [h1, h2] <;>
    omega

private theorem cubeDefect_complementary_exponent
    (eR eS ea : ℕ) (h : eR + eS = 3 * ea) :
    eS = 2 * (if eR % 3 = 1 then 1 else 0) +
        (if eR % 3 = 2 then 1 else 0) + 3 * (eS / 3) := by
  by_cases h1 : eR % 3 = 1 <;> by_cases h2 : eR % 3 = 2
  all_goals
    simp [h1, h2]
    omega

private theorem cubeDefect_prime_product_pow_mod_three
    (e q : ℕ) :
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
           rw [← pow_mul, Nat.mul_comm (e / 3) 3])

private theorem cubeDefect_complementary_product_pow
    (eR eS ea q : ℕ) (h : eR + eS = 3 * ea) :
    q ^ eS = (if eR % 3 = 1 then q else 1) ^ 2 *
        (if eR % 3 = 2 then q else 1) * (q ^ (eS / 3)) ^ 3 := by
  by_cases h1 : eR % 3 = 1 <;> by_cases h2 : eR % 3 = 2
  all_goals
    first
    | omega
    | (have he := cubeDefect_complementary_exponent eR eS ea h
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

private theorem cubeDefect_support_prime
    {R S : ℕ} (_hR : R ≠ 0) (_hS : S ≠ 0)
    {q : ℕ} (hq : q ∈ cubeDefectSupport R S) : q.Prime := by
  rcases Finset.mem_union.mp hq with hq | hq
  · exact Nat.prime_of_mem_primeFactors hq
  · exact Nat.prime_of_mem_primeFactors hq

private theorem cubeDefect_product_on_support
    {R S : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) :
    R = ∏ q ∈ cubeDefectSupport R S, q ^ R.factorization q := by
  calc
    R = ∏ q ∈ R.primeFactors, q ^ R.factorization q :=
      Nat.prod_primeFactors_pow_factorization hR
    _ = ∏ q ∈ cubeDefectSupport R S, q ^ R.factorization q := by
      apply Finset.prod_subset_one_on_sdiff
      · exact Finset.subset_union_left
      · intro q hq
        have hqR : q ∉ R.primeFactors := (Finset.mem_sdiff.mp hq).2
        have hqnot : ¬q ∣ R := by
          intro hdiv
          apply hqR
          exact (Nat.mem_primeFactors_of_ne_zero hR).mpr
            ⟨cubeDefect_support_prime hR hS (Finset.mem_sdiff.mp hq).1, hdiv⟩
        simp [Nat.factorization_eq_zero_of_not_dvd hqnot]
      · intro q hq
        rfl

private theorem cubeDefect_squarefree
    {R S : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) :
    Squarefree (cubeDefectD1 R S) ∧ Squarefree (cubeDefectD2 R S) := by
  have hT : ∀ q ∈ cubeDefectSupport R S, q.Prime :=
    fun q hq => cubeDefect_support_prime hR hS hq
  constructor
  · unfold cubeDefectD1
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hT p (Finset.mem_filter.mp hp).1)
        (hT q (Finset.mem_filter.mp hq).1)).mpr hpq
    · intro p hp
      exact (hT p (Finset.mem_filter.mp hp).1).squarefree
  · unfold cubeDefectD2
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hT p (Finset.mem_filter.mp hp).1)
        (hT q (Finset.mem_filter.mp hq).1)).mpr hpq
    · intro p hp
      exact (hT p (Finset.mem_filter.mp hp).1).squarefree

private theorem cubeDefect_gap_reconstruction
    {R S : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) :
    R = cubeDefectD1 R S * cubeDefectD2 R S ^ 2 * cubeDefectU R S ^ 3 := by
  calc
    R = ∏ q ∈ cubeDefectSupport R S, q ^ R.factorization q :=
      cubeDefect_product_on_support hR hS
    _ = cubeDefectD1 R S * cubeDefectD2 R S ^ 2 * cubeDefectU R S ^ 3 := by
      unfold cubeDefectD1 cubeDefectD2 cubeDefectU
      rw [Finset.prod_filter, Finset.prod_filter]
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q hq
      exact cubeDefect_prime_product_pow_mod_three (R.factorization q) q

private theorem cubeDefect_quotient_reconstruction
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0)
    (hledger : ∀ q, R.factorization q + S.factorization q =
      3 * a.factorization q) :
    S = cubeDefectD1 R S ^ 2 * cubeDefectD2 R S * cubeDefectV R S ^ 3 := by
  have hprod : S = ∏ q ∈ cubeDefectSupport R S, q ^ S.factorization q := by
    simpa [cubeDefectSupport, Finset.union_comm] using
      (cubeDefect_product_on_support (R := S) (S := R) hS hR)
  calc
    S = ∏ q ∈ cubeDefectSupport R S, q ^ S.factorization q := hprod
    _ = cubeDefectD1 R S ^ 2 * cubeDefectD2 R S * cubeDefectV R S ^ 3 := by
      unfold cubeDefectD1 cubeDefectD2 cubeDefectV
      rw [Finset.prod_filter, Finset.prod_filter]
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q hq
      exact cubeDefect_complementary_product_pow
        (R.factorization q) (S.factorization q) (a.factorization q) q
        (hledger q)

private theorem cubeDefect_coprime
    {R S : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) :
    Nat.Coprime (cubeDefectD1 R S) (cubeDefectD2 R S) := by
  let P1 : ℕ → Prop := fun q => R.factorization q % 3 = 1
  let P2 : ℕ → Prop := fun q => R.factorization q % 3 = 2
  have hdis : Disjoint ((cubeDefectSupport R S).filter P1)
      ((cubeDefectSupport R S).filter P2) := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    have h1 := (Finset.mem_filter.mp hq1).2
    have h2 := (Finset.mem_filter.mp hq2).2
    dsimp [P1, P2] at h1 h2
    omega
  have hunion : (cubeDefectSupport R S).filter P1 ∪
      (cubeDefectSupport R S).filter P2 =
      (cubeDefectSupport R S).filter (fun q => P1 q ∨ P2 q) := by
    ext q
    have hp : ((q ∈ cubeDefectSupport R S ∧ P1 q) ∨
        (q ∈ cubeDefectSupport R S ∧ P2 q)) ↔
        (q ∈ cubeDefectSupport R S ∧ (P1 q ∨ P2 q)) := by
      constructor
      · rintro (⟨hq, hq1⟩ | ⟨hq, hq2⟩)
        · exact ⟨hq, Or.inl hq1⟩
        · exact ⟨hq, Or.inr hq2⟩
      · rintro ⟨hq, hq12⟩
        rcases hq12 with hq1 | hq2
        · exact Or.inl ⟨hq, hq1⟩
        · exact Or.inr ⟨hq, hq2⟩
    simpa only [Finset.mem_union, Finset.mem_filter] using hp
  have hprod : cubeDefectD1 R S * cubeDefectD2 R S =
      ∏ q ∈ (cubeDefectSupport R S).filter (fun q => P1 q ∨ P2 q), q := by
    have hprod' :
        (∏ q ∈ (cubeDefectSupport R S).filter P1, q) *
            ∏ q ∈ (cubeDefectSupport R S).filter P2, q =
          ∏ q ∈ (cubeDefectSupport R S).filter (fun q => P1 q ∨ P2 q), q := by
      rw [← Finset.prod_union hdis, hunion]
    simpa [cubeDefectD1, cubeDefectD2, P1, P2] using hprod'
  have hsq : Squarefree (cubeDefectD1 R S * cubeDefectD2 R S) := by
    rw [hprod]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes
        (cubeDefect_support_prime hR hS (Finset.mem_filter.mp hp).1)
        (cubeDefect_support_prime hR hS (Finset.mem_filter.mp hq).1)).mpr hpq
    · intro p hp
      exact (cubeDefect_support_prime hR hS (Finset.mem_filter.mp hp).1).squarefree
  exact Nat.coprime_of_squarefree_mul hsq

private theorem cubeDefect_products_pos
    {R S : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) :
    0 < cubeDefectD1 R S ∧ 0 < cubeDefectD2 R S ∧
      0 < cubeDefectU R S ∧ 0 < cubeDefectV R S := by
  have hT : ∀ q ∈ cubeDefectSupport R S, q.Prime :=
    fun q hq => cubeDefect_support_prime hR hS hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun q hq => (hT q (Finset.mem_filter.mp hq).1).pos
  · exact Finset.prod_pos fun q hq => (hT q (Finset.mem_filter.mp hq).1).pos
  · exact Finset.prod_pos fun q hq =>
      pow_pos (hT q hq).pos _
  · exact Finset.prod_pos fun q hq =>
      pow_pos (hT q hq).pos _

structure CubeDefectNormalForm (R S a : ℕ) where
  D1 : ℕ
  D2 : ℕ
  U : ℕ
  V : ℕ
  D1_pos : 0 < D1
  D2_pos : 0 < D2
  U_pos : 0 < U
  V_pos : 0 < V
  D1_squarefree : Squarefree (R := ℕ) D1
  D2_squarefree : Squarefree (R := ℕ) D2
  D1_D2_coprime : Nat.Coprime D1 D2
  R_eq : R = D1 * D2 ^ 2 * U ^ 3
  S_eq : S = D1 ^ 2 * D2 * V ^ 3
  a_eq : a = D1 * D2 * U * V
  defect_dvd_gcd : D1 * D2 ∣ Nat.gcd R S
  defect_prime_support : ∀ q, q.Prime → q ∣ D1 * D2 → exceptionalModSeven q
  height : D1 * D2 ^ 3 * U ^ 5 < V

theorem exists_cube_defect_normal_form_three
    {R S a : ℕ} (hRpos : 0 < R) (hSpos : 0 < S) (hapos : 0 < a)
    (hRS : R * S = a ^ 3)
    (hcommon : ∀ q, q.Prime → q ∣ R → q ∣ S → exceptionalModSeven q)
    (hheight : R ^ 2 < a) :
    Nonempty (CubeDefectNormalForm R S a) := by
  have hR : R ≠ 0 := Nat.ne_of_gt hRpos
  have hS : S ≠ 0 := Nat.ne_of_gt hSpos
  have ha : a ≠ 0 := Nat.ne_of_gt hapos
  have hledger : ∀ q, R.factorization q + S.factorization q =
      3 * a.factorization q :=
    cubeDefect_factorization_ledger hR hS hRS
  have hR_eq := cubeDefect_gap_reconstruction hR hS
  have hS_eq := cubeDefect_quotient_reconstruction hR hS hledger
  have hsq := cubeDefect_squarefree hR hS
  have hcop := cubeDefect_coprime hR hS
  have hpos := cubeDefect_products_pos hR hS
  have hDvdR : cubeDefectD1 R S * cubeDefectD2 R S ∣ R := by
    refine ⟨cubeDefectD2 R S * cubeDefectU R S ^ 3, ?_⟩
    calc
      R = cubeDefectD1 R S * cubeDefectD2 R S ^ 2 * cubeDefectU R S ^ 3 := hR_eq
      _ = (cubeDefectD1 R S * cubeDefectD2 R S) *
          (cubeDefectD2 R S * cubeDefectU R S ^ 3) := by ring
  have hDvdS : cubeDefectD1 R S * cubeDefectD2 R S ∣ S := by
    refine ⟨cubeDefectD1 R S * cubeDefectV R S ^ 3, ?_⟩
    calc
      S = cubeDefectD1 R S ^ 2 * cubeDefectD2 R S * cubeDefectV R S ^ 3 := hS_eq
      _ = (cubeDefectD1 R S * cubeDefectD2 R S) *
          (cubeDefectD1 R S * cubeDefectV R S ^ 3) := by ring
  have hDvdGcd : cubeDefectD1 R S * cubeDefectD2 R S ∣ Nat.gcd R S :=
    Nat.dvd_gcd hDvdR hDvdS
  have ha_eq : a = cubeDefectD1 R S * cubeDefectD2 R S *
      cubeDefectU R S * cubeDefectV R S := by
    have hcube :
        (cubeDefectD1 R S * cubeDefectD2 R S * cubeDefectU R S *
          cubeDefectV R S) ^ 3 = a ^ 3 := by
      calc
        _ = (cubeDefectD1 R S * cubeDefectD2 R S ^ 2 * cubeDefectU R S ^ 3) *
            (cubeDefectD1 R S ^ 2 * cubeDefectD2 R S * cubeDefectV R S ^ 3) := by ring
        _ = R * S := congrArg₂ (· * ·) hR_eq.symm hS_eq.symm
        _ = a ^ 3 := hRS
    exact (Nat.pow_left_injective (n := 3) (by decide)) hcube.symm
  have hmul :
      (cubeDefectD1 R S * cubeDefectD2 R S * cubeDefectU R S) *
          (cubeDefectD1 R S * cubeDefectD2 R S ^ 3 * cubeDefectU R S ^ 5) <
        (cubeDefectD1 R S * cubeDefectD2 R S * cubeDefectU R S) *
          cubeDefectV R S := by
    calc
      _ = (cubeDefectD1 R S * cubeDefectD2 R S ^ 2 * cubeDefectU R S ^ 3) ^ 2 := by ring
      _ = R ^ 2 := (congrArg (fun n : ℕ => n ^ 2) hR_eq).symm
      _ < a := hheight
      _ = _ := by rw [ha_eq]
  have hCpos : 0 < cubeDefectD1 R S * cubeDefectD2 R S * cubeDefectU R S :=
    Nat.mul_pos (Nat.mul_pos hpos.1 hpos.2.1) hpos.2.2.1
  have hheight' := (Nat.mul_lt_mul_left hCpos).mp hmul
  let c : CubeDefectNormalForm R S a := {
    D1 := cubeDefectD1 R S
    D2 := cubeDefectD2 R S
    U := cubeDefectU R S
    V := cubeDefectV R S
    D1_pos := hpos.1
    D2_pos := hpos.2.1
    U_pos := hpos.2.2.1
    V_pos := hpos.2.2.2
    D1_squarefree := hsq.1
    D2_squarefree := hsq.2
    D1_D2_coprime := hcop
    R_eq := hR_eq
    S_eq := hS_eq
    a_eq := ha_eq
    defect_dvd_gcd := hDvdGcd
    defect_prime_support := by
      intro q hq hqD
      exact hcommon q hq (dvd_trans hqD hDvdR) (dvd_trans hqD hDvdS)
    height := hheight' }
  exact ⟨c⟩

/-! ## Current FLT7 packet -/

structure DirectOrbitCubeDefectPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) where
  squareRefinement : DirectOrbitSquareRefinementPacket p
  D1 : ℕ
  D2 : ℕ
  U : ℕ
  V : ℕ
  D1_pos : 0 < D1
  D2_pos : 0 < D2
  U_pos : 0 < U
  V_pos : 0 < V
  D1_squarefree : Squarefree (R := ℕ) D1
  D2_squarefree : Squarefree (R := ℕ) D2
  D1_D2_coprime : Nat.Coprime D1 D2
  gapNorm_eq : Int.natAbs (norm squareRefinement.gapSquareRoot) = D1 * D2 ^ 2 * U ^ 3
  quotientNorm_eq :
    Int.natAbs (norm squareRefinement.quotientSquareRoot) = D1 ^ 2 * D2 * V ^ 3
  unitPart_eq : squareRefinement.powerSplit.gapSplit.a = D1 * D2 * U * V
  defect_dvd_gcd : D1 * D2 ∣ Nat.gcd
    (Int.natAbs (norm squareRefinement.gapSquareRoot))
    (Int.natAbs (norm squareRefinement.quotientSquareRoot))
  defect_prime_support : ∀ q, q.Prime → q ∣ D1 * D2 → exceptionalModSeven q
  height : D1 * D2 ^ 3 * U ^ 5 < V

theorem directOrbitSquareRefinement_cubeDefect_nonempty
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Nonempty (DirectOrbitCubeDefectPacket p) := by
  let R := Int.natAbs (SevenRealCubicInt.norm t.gapSquareRoot)
  let S := Int.natAbs (SevenRealCubicInt.norm t.quotientSquareRoot)
  let a := t.powerSplit.gapSplit.a
  have hRpos : 0 < R := by
    simpa [R] using directOrbitSquareRefinement_gap_square_norm_pos t
  have hSpos : 0 < S := by
    simpa [S] using directOrbitSquareRefinement_quotient_square_norm_pos t
  have hapos : 0 < a := t.powerSplit.gapSplit.a_pos
  have hRS : R * S = a ^ 3 := by
    simpa [R, S, a] using directOrbitSquareRefinement_squareRoots_norm_mul_eq_cube t
  have hheight : R ^ 2 < a := by
    simpa [R, a] using directOrbitSquareRefinement_gap_square_norm_lt_base t
  have hcommon : ∀ q, q.Prime → q ∣ R → q ∣ S → exceptionalModSeven q := by
    intro q hq hqR hqS
    exact SevenRealCubic.common_norm_prime_mod_seven t hq (by simpa [R] using hqR)
      (by simpa [S] using hqS)
  obtain ⟨c⟩ := exists_cube_defect_normal_form_three hRpos hSpos hapos
    hRS hcommon hheight
  exact ⟨{
    squareRefinement := t
    D1 := c.D1
    D2 := c.D2
    U := c.U
    V := c.V
    D1_pos := c.D1_pos
    D2_pos := c.D2_pos
    U_pos := c.U_pos
    V_pos := c.V_pos
    D1_squarefree := c.D1_squarefree
    D2_squarefree := c.D2_squarefree
    D1_D2_coprime := c.D1_D2_coprime
    gapNorm_eq := c.R_eq
    quotientNorm_eq := c.S_eq
    unitPart_eq := c.a_eq
    defect_dvd_gcd := c.defect_dvd_gcd
    defect_prime_support := c.defect_prime_support
    height := c.height }⟩

end DkMath.FLT.Seven
