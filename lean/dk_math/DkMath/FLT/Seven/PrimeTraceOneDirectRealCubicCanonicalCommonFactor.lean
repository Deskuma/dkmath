/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.RamificationInertia.Ramification

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped BigOperators
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

def directOrbitCanonicalCommonFactor_commonSupport (R S a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun q => q ∣ R ∧ q ∣ S)

def directOrbitCanonicalCommonFactor_gapOnlySupport (R S a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun q => q ∣ R ∧ ¬q ∣ S)

def directOrbitCanonicalCommonFactor_quotientOnlySupport (R S a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun q => ¬q ∣ R ∧ q ∣ S)

def directOrbitCanonicalCommonFactor_commonProduct (R S a : ℕ) : ℕ :=
  ∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
    q ^ a.factorization q

def directOrbitCanonicalCommonFactor_gapRoot (R S a : ℕ) : ℕ :=
  ∏ q ∈ directOrbitCanonicalCommonFactor_gapOnlySupport R S a,
    q ^ a.factorization q

def directOrbitCanonicalCommonFactor_quotientRoot (R S a : ℕ) : ℕ :=
  ∏ q ∈ directOrbitCanonicalCommonFactor_quotientOnlySupport R S a,
    q ^ a.factorization q

structure DirectOrbitCanonicalCommonFactorPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) where
  squareRefinement : DirectOrbitSquareRefinementPacket p
  c : ℕ
  u : ℕ
  v : ℕ
  c_pos : 0 < c
  u_pos : 0 < u
  v_pos : 0 < v
  c_eq_gcd : c = Nat.gcd
    (Int.natAbs (norm squareRefinement.gapSquareRoot))
    (Int.natAbs (norm squareRefinement.quotientSquareRoot))
  c_dvd_a : c ∣ squareRefinement.powerSplit.gapSplit.a
  gapNorm_eq : Int.natAbs (norm squareRefinement.gapSquareRoot) = c * u ^ 3
  quotientNorm_eq :
    Int.natAbs (norm squareRefinement.quotientSquareRoot) = c ^ 2 * v ^ 3
  unitPart_eq : squareRefinement.powerSplit.gapSplit.a = c * u * v
  c_u_coprime : Nat.Coprime c u
  c_v_coprime : Nat.Coprime c v
  u_v_coprime : Nat.Coprime u v
  c_prime_support : ∀ q, q.Prime → q ∣ c → exceptionalModSeven q
  height : c * u ^ 5 < v

namespace SevenRealCubic

private theorem canonicalCommonFactor_support_prime
    {_R _S a : ℕ} {q : ℕ} (hq : q ∈ a.primeFactors) : q.Prime :=
  Nat.prime_of_mem_primeFactors hq

private theorem canonicalCommonFactor_factorization_prime_power
    {p q e : ℕ} (hp : p.Prime) :
    (p ^ e).factorization q = if p = q then e else 0 := by
  rw [Nat.Prime.factorization_pow hp]
  by_cases h : p = q <;> simp [h]

private theorem canonicalCommonFactor_product_factorization
    {_R _S a : ℕ} {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) (q : ℕ) :
    (∏ p ∈ s, p ^ a.factorization p).factorization q =
      if q ∈ s then a.factorization q else 0 := by
  classical
  have hne : ∀ p ∈ s, p ^ a.factorization p ≠ 0 := by
    intro p hp
    exact pow_ne_zero _ (hs p hp).ne_zero
  rw [Nat.factorization_prod_apply hne]
  by_cases hq : q ∈ s
  · rw [Finset.sum_eq_single_of_mem q hq]
    · rw [canonicalCommonFactor_factorization_prime_power (hs q hq)]
      simp [hq]
    · intro b hb hneq
      rw [canonicalCommonFactor_factorization_prime_power (hs b hb)]
      simp [hneq]
  · rw [Finset.sum_eq_zero]
    · simp [hq]
    · intro b hb
      rw [canonicalCommonFactor_factorization_prime_power (hs b hb)]
      have hneq : b ≠ q := by
        intro heq
        apply hq
        simpa [heq] using hb
      simp [hneq]

private theorem canonicalCommonFactor_prime_support_partition
    {R S a : ℕ} (ha : a ≠ 0) (hRS : R * S = a ^ 3)
    {q : ℕ} (hq : q ∈ a.primeFactors) :
    q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a ∨
      q ∈ directOrbitCanonicalCommonFactor_gapOnlySupport R S a ∨
      q ∈ directOrbitCanonicalCommonFactor_quotientOnlySupport R S a := by
  have hqa : q ∣ a :=
    (Nat.mem_primeFactors_of_ne_zero ha).mp hq |>.2
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqprod : q ∣ R * S := by
    rw [hRS]
    exact dvd_pow hqa (by decide)
  rcases hqprime.dvd_mul.mp hqprod with hqR | hqS
  · by_cases hqS' : q ∣ S
    · exact Or.inl (Finset.mem_filter.mpr ⟨hq, hqR, hqS'⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hq, hqR, hqS'⟩))
  · by_cases hqR' : q ∣ R
    · exact Or.inl (Finset.mem_filter.mpr ⟨hq, hqR', hqS⟩)
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hq, hqR', hqS⟩))

private theorem canonicalCommonFactor_prime_support_disjoint
    {R S a : ℕ} :
    Disjoint (directOrbitCanonicalCommonFactor_commonSupport R S a)
        (directOrbitCanonicalCommonFactor_gapOnlySupport R S a) ∧
      Disjoint (directOrbitCanonicalCommonFactor_commonSupport R S a)
        (directOrbitCanonicalCommonFactor_quotientOnlySupport R S a) ∧
      Disjoint (directOrbitCanonicalCommonFactor_gapOnlySupport R S a)
        (directOrbitCanonicalCommonFactor_quotientOnlySupport R S a) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Finset.disjoint_left] <;>
    intro q hq1 hq2
  · exact (Finset.mem_filter.mp hq2).2.2 (Finset.mem_filter.mp hq1).2.2
  · exact (Finset.mem_filter.mp hq2).2.1 (Finset.mem_filter.mp hq1).2.1
  · exact (Finset.mem_filter.mp hq1).2.2 (Finset.mem_filter.mp hq2).2.2

private theorem canonicalCommonFactor_prime_support_equalities
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) (ha : a ≠ 0)
    (hRS : R * S = a ^ 3) :
    R.primeFactors = a.primeFactors.filter (fun q => q ∣ R) ∧
      S.primeFactors = a.primeFactors.filter (fun q => q ∣ S) := by
  have hRpf : R.primeFactors = a.primeFactors.filter (fun q => q ∣ R) := by
    ext q
    simp only [Nat.mem_primeFactors_of_ne_zero hR,
      Nat.mem_primeFactors_of_ne_zero ha, Finset.mem_filter]
    constructor
    · rintro ⟨hqprime, hqR⟩
      have hqpow : q ∣ R * S := dvd_mul_of_dvd_left hqR S
      have hqa : q ∣ a := hqprime.dvd_of_dvd_pow (by simpa [hRS] using hqpow)
      exact ⟨⟨hqprime, hqa⟩, hqR⟩
    · rintro ⟨⟨hqprime, _⟩, hqR⟩
      exact ⟨hqprime, hqR⟩
  have hSpf : S.primeFactors = a.primeFactors.filter (fun q => q ∣ S) := by
    ext q
    simp only [Nat.mem_primeFactors_of_ne_zero hS,
      Nat.mem_primeFactors_of_ne_zero ha, Finset.mem_filter]
    constructor
    · rintro ⟨hqprime, hqS⟩
      have hqpow : q ∣ R * S := dvd_mul_of_dvd_right hqS R
      have hqa : q ∣ a := hqprime.dvd_of_dvd_pow (by simpa [hRS] using hqpow)
      exact ⟨⟨hqprime, hqa⟩, hqS⟩
    · rintro ⟨⟨hqprime, _⟩, hqS⟩
      exact ⟨hqprime, hqS⟩
  exact ⟨hRpf, hSpf⟩

private theorem canonicalCommonFactor_three_case_exponents
    {R S a : ℕ} (hledger : ∀ q, R.factorization q + S.factorization q =
      3 * a.factorization q)
    (hcommon : ∀ {q}, q.Prime → q ∣ R → q ∣ S →
      R.factorization q = a.factorization q ∧
        S.factorization q = 2 * a.factorization q)
    {q : ℕ} (hq : q.Prime) (_hqa : q ∣ a) :
    (q ∣ R ∧ q ∣ S →
      R.factorization q = a.factorization q ∧
        S.factorization q = 2 * a.factorization q) ∧
    (q ∣ R ∧ ¬q ∣ S →
      R.factorization q = 3 * a.factorization q ∧
        S.factorization q = 0) ∧
    (¬q ∣ R ∧ q ∣ S →
      R.factorization q = 0 ∧
        S.factorization q = 3 * a.factorization q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hqRS
    exact hcommon hq hqRS.1 hqRS.2
  · intro hqR
    have hzero : S.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hqR.2
    refine ⟨?_, hzero⟩
    have hsum := hledger q
    rw [hzero] at hsum
    omega
  · intro hqS
    have hzero : R.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hqS.1
    refine ⟨hzero, ?_⟩
    have hsum := hledger q
    rw [hzero] at hsum
    omega

private theorem canonicalCommonFactor_reconstruction
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) (ha : a ≠ 0)
    (hRS : R * S = a ^ 3)
    (htable : ∀ {q}, q.Prime → q ∣ a →
      (q ∣ R ∧ q ∣ S →
        R.factorization q = a.factorization q ∧
          S.factorization q = 2 * a.factorization q) ∧
      (q ∣ R ∧ ¬q ∣ S →
        R.factorization q = 3 * a.factorization q ∧
          S.factorization q = 0) ∧
      (¬q ∣ R ∧ q ∣ S →
        R.factorization q = 0 ∧
          S.factorization q = 3 * a.factorization q)) :
    R = directOrbitCanonicalCommonFactor_commonProduct R S a *
        directOrbitCanonicalCommonFactor_gapRoot R S a ^ 3 ∧
      S = directOrbitCanonicalCommonFactor_commonProduct R S a ^ 2 *
        directOrbitCanonicalCommonFactor_quotientRoot R S a ^ 3 ∧
      a = directOrbitCanonicalCommonFactor_commonProduct R S a *
        directOrbitCanonicalCommonFactor_gapRoot R S a *
        directOrbitCanonicalCommonFactor_quotientRoot R S a := by
  classical
  have hRpf := canonicalCommonFactor_prime_support_equalities hR hS ha hRS |>.1
  have hSpf := canonicalCommonFactor_prime_support_equalities hR hS ha hRS |>.2
  have hcommon_filter :
      (a.primeFactors.filter (fun q => q ∣ R)).filter (fun q => q ∣ S) =
        directOrbitCanonicalCommonFactor_commonSupport R S a := by
    ext q
    simp [directOrbitCanonicalCommonFactor_commonSupport, and_assoc,
      and_left_comm, and_comm]
  have hgap_filter :
      (a.primeFactors.filter (fun q => q ∣ R)).filter (fun q => ¬q ∣ S) =
        directOrbitCanonicalCommonFactor_gapOnlySupport R S a := by
    ext q
    simp [directOrbitCanonicalCommonFactor_gapOnlySupport, and_assoc,
      and_left_comm, and_comm]
  have hRprod :
      R = ∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
        q ^ R.factorization q := by
    rw [← hRpf]
    exact Nat.prod_primeFactors_pow_factorization hR
  have hSprod :
      S = ∏ q ∈ a.primeFactors.filter (fun q => q ∣ S),
        q ^ S.factorization q := by
    rw [← hSpf]
    exact Nat.prod_primeFactors_pow_factorization hS
  have hRsplit :
      (∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
        q ^ R.factorization q) =
        (∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
          q ^ R.factorization q) *
        (∏ q ∈ directOrbitCanonicalCommonFactor_gapOnlySupport R S a,
          q ^ R.factorization q) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (a.primeFactors.filter (fun q => q ∣ R))
      (fun q : ℕ => q ∣ S) (fun q => q ^ R.factorization q)]
    rw [hcommon_filter]
    have hgap_filter' :
        (a.primeFactors.filter (fun q => q ∣ R)).filter (fun q => ¬q ∣ S) =
          directOrbitCanonicalCommonFactor_gapOnlySupport R S a := by
      ext q
      simp [directOrbitCanonicalCommonFactor_gapOnlySupport, and_assoc,
        and_left_comm, and_comm]
    rw [hgap_filter']
  have hSsplit :
      (∏ q ∈ a.primeFactors.filter (fun q => q ∣ S),
        q ^ S.factorization q) =
        (∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
          q ^ S.factorization q) *
        (∏ q ∈ directOrbitCanonicalCommonFactor_quotientOnlySupport R S a,
          q ^ S.factorization q) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (a.primeFactors.filter (fun q => q ∣ S))
      (fun q : ℕ => q ∣ R) (fun q => q ^ S.factorization q)]
    have hcommon_filter' :
        (a.primeFactors.filter (fun q => q ∣ S)).filter (fun q => q ∣ R) =
          directOrbitCanonicalCommonFactor_commonSupport R S a := by
      ext q
      simp [directOrbitCanonicalCommonFactor_commonSupport, and_assoc,
        and_left_comm, and_comm]
    have hquot_filter' :
        (a.primeFactors.filter (fun q => q ∣ S)).filter (fun q => ¬q ∣ R) =
          directOrbitCanonicalCommonFactor_quotientOnlySupport R S a := by
      ext q
      simp [directOrbitCanonicalCommonFactor_quotientOnlySupport, and_assoc,
        and_left_comm, and_comm]
    rw [hcommon_filter', hquot_filter']
  have hRcommon :
      (∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
        q ^ R.factorization q) =
        directOrbitCanonicalCommonFactor_commonProduct R S a := by
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    exact congrArg (fun e => q ^ e)
      (htable hqprime hqa |>.1 hq0.2 |>.1)
  have hRgap :
      (∏ q ∈ directOrbitCanonicalCommonFactor_gapOnlySupport R S a,
        q ^ R.factorization q) =
        directOrbitCanonicalCommonFactor_gapRoot R S a ^ 3 := by
    unfold directOrbitCanonicalCommonFactor_gapRoot
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    rw [htable hqprime hqa |>.2.1 hq0.2 |>.1]
    rw [← pow_mul]
    exact congrArg (fun n => q ^ n) (Nat.mul_comm _ _)
  have hScommon :
      (∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
        q ^ S.factorization q) =
        directOrbitCanonicalCommonFactor_commonProduct R S a ^ 2 := by
    unfold directOrbitCanonicalCommonFactor_commonProduct
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    rw [htable hqprime hqa |>.1 hq0.2 |>.2]
    rw [← pow_mul]
    exact congrArg (fun n => q ^ n) (Nat.mul_comm _ _)
  have hSquoter :
      (∏ q ∈ directOrbitCanonicalCommonFactor_quotientOnlySupport R S a,
        q ^ S.factorization q) =
        directOrbitCanonicalCommonFactor_quotientRoot R S a ^ 3 := by
    unfold directOrbitCanonicalCommonFactor_quotientRoot
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    rw [htable hqprime hqa |>.2.2 hq0.2 |>.2]
    rw [← pow_mul]
    exact congrArg (fun n => q ^ n) (Nat.mul_comm _ _)
  have hR_eq : R = directOrbitCanonicalCommonFactor_commonProduct R S a *
      directOrbitCanonicalCommonFactor_gapRoot R S a ^ 3 := by
    calc
      R = ∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
          q ^ R.factorization q := hRprod
      _ = _ := hRsplit
      _ = _ := by rw [hRcommon, hRgap]
  have hS_eq : S = directOrbitCanonicalCommonFactor_commonProduct R S a ^ 2 *
      directOrbitCanonicalCommonFactor_quotientRoot R S a ^ 3 := by
    calc
      S = ∏ q ∈ a.primeFactors.filter (fun q => q ∣ S),
          q ^ S.factorization q := hSprod
      _ = _ := hSsplit
      _ = _ := by rw [hScommon, hSquoter]
  have hA_Rsplit :
      (∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
        q ^ a.factorization q) *
        (∏ q ∈ directOrbitCanonicalCommonFactor_gapOnlySupport R S a,
          q ^ a.factorization q) =
        ∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
          q ^ a.factorization q := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (a.primeFactors.filter (fun q => q ∣ R))
      (fun q : ℕ => q ∣ S) (fun q => q ^ a.factorization q)]
    rw [hcommon_filter]
    have hgap_filter' :
        (a.primeFactors.filter (fun q => q ∣ R)).filter (fun q => ¬q ∣ S) =
          directOrbitCanonicalCommonFactor_gapOnlySupport R S a := by
      ext q
      simp [directOrbitCanonicalCommonFactor_gapOnlySupport, and_assoc,
        and_left_comm, and_comm]
    rw [hgap_filter']
  have hnotR_filter :
      a.primeFactors.filter (fun q => ¬q ∣ R) =
        directOrbitCanonicalCommonFactor_quotientOnlySupport R S a := by
    ext q
    change q ∈ a.primeFactors.filter (fun q => ¬q ∣ R) ↔
      q ∈ a.primeFactors.filter (fun q => ¬q ∣ R ∧ q ∣ S)
    constructor
    · intro hq
      have hq0 := Finset.mem_filter.mp hq
      have hqprime := Nat.prime_of_mem_primeFactors hq0.1
      have hqprod : q ∣ R * S := by
        have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
        rw [hRS]
        exact dvd_pow hqa (by decide)
      rcases hqprime.dvd_mul.mp hqprod with hqR' | hqS
      · exact (hq0.2 hqR').elim
      · exact Finset.mem_filter.mpr ⟨hq0.1, ⟨hq0.2, hqS⟩⟩
    · intro hq
      have hq0 := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hq0.1, hq0.2.1⟩
  have hApart :
      (∏ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
        q ^ a.factorization q) *
        (∏ q ∈ directOrbitCanonicalCommonFactor_gapOnlySupport R S a,
          q ^ a.factorization q) *
          (∏ q ∈ directOrbitCanonicalCommonFactor_quotientOnlySupport R S a,
            q ^ a.factorization q) =
        ∏ q ∈ a.primeFactors, q ^ a.factorization q := by
    calc
      _ = (∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
          q ^ a.factorization q) *
          (∏ q ∈ a.primeFactors.filter (fun q => ¬q ∣ R),
            q ^ a.factorization q) := by
        rw [hA_Rsplit, hnotR_filter]
      _ = _ := Finset.prod_filter_mul_prod_filter_not
        a.primeFactors (fun q : ℕ => q ∣ R)
        (fun q => q ^ a.factorization q)
  have ha_eq : a = directOrbitCanonicalCommonFactor_commonProduct R S a *
      directOrbitCanonicalCommonFactor_gapRoot R S a *
      directOrbitCanonicalCommonFactor_quotientRoot R S a := by
    calc
      a = ∏ q ∈ a.primeFactors, q ^ a.factorization q :=
        Nat.prod_primeFactors_pow_factorization ha
      _ = _ := by simpa [directOrbitCanonicalCommonFactor_commonProduct,
        directOrbitCanonicalCommonFactor_gapRoot,
        directOrbitCanonicalCommonFactor_quotientRoot] using hApart.symm
  exact ⟨hR_eq, hS_eq, ha_eq⟩

private theorem canonicalCommonFactor_gcd_eq
    {R S a : ℕ} (hR : R ≠ 0) (hS : S ≠ 0) (ha : a ≠ 0)
    (hRS : R * S = a ^ 3)
    (htable : ∀ {q}, q.Prime → q ∣ a →
      (q ∣ R ∧ q ∣ S →
        R.factorization q = a.factorization q ∧
          S.factorization q = 2 * a.factorization q) ∧
      (q ∣ R ∧ ¬q ∣ S →
        R.factorization q = 3 * a.factorization q ∧ S.factorization q = 0) ∧
      (¬q ∣ R ∧ q ∣ S →
        R.factorization q = 0 ∧ S.factorization q = 3 * a.factorization q)) :
    directOrbitCanonicalCommonFactor_commonProduct R S a = Nat.gcd R S := by
  classical
  have hsp : ∀ q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a,
      q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hcp : directOrbitCanonicalCommonFactor_commonProduct R S a ≠ 0 := by
    unfold directOrbitCanonicalCommonFactor_commonProduct
    exact Finset.prod_ne_zero_iff.mpr (fun q hq =>
      pow_ne_zero _ (hsp q hq).ne_zero)
  apply Nat.eq_of_factorization_eq hcp (Nat.gcd_ne_zero_left hR)
  intro q
  by_cases hq : q.Prime
  · unfold directOrbitCanonicalCommonFactor_commonProduct
    rw [canonicalCommonFactor_product_factorization (_R := R) (_S := S) (a := a)
        hsp q,
      Nat.factorization_gcd hR hS]
    by_cases hqC : q ∈ directOrbitCanonicalCommonFactor_commonSupport R S a
    · have hq0 := Finset.mem_filter.mp hqC
      have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
      have htab := htable hq hqa |>.1 hq0.2
      simp [hqC, htab.1, htab.2]
      omega
    · by_cases hqR : q ∣ R
      · have hqS : ¬q ∣ S := by
          intro hqS
          have hqa : q ∣ a := hq.dvd_of_dvd_pow (by
            have : q ∣ R * S := dvd_mul_of_dvd_left hqR S
            simpa [hRS] using this)
          exact hqC (Finset.mem_filter.mpr ⟨
            (Nat.mem_primeFactors_of_ne_zero ha).mpr ⟨hq, hqa⟩, hqR, hqS⟩)
        have hqa : q ∣ a := hq.dvd_of_dvd_pow (by
          have : q ∣ R * S := dvd_mul_of_dvd_left hqR S
          simpa [hRS] using this)
        have htab := htable hq hqa |>.2.1 ⟨hqR, hqS⟩
        simp [hqC, htab.1, htab.2]
      · simp [hqC, Nat.factorization_eq_zero_of_not_dvd hqR]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

private theorem canonicalCommonFactor_pairwise_coprime
    {R S a : ℕ} :
    Nat.Coprime
        (directOrbitCanonicalCommonFactor_commonProduct R S a)
        (directOrbitCanonicalCommonFactor_gapRoot R S a) ∧
      Nat.Coprime
        (directOrbitCanonicalCommonFactor_commonProduct R S a)
        (directOrbitCanonicalCommonFactor_quotientRoot R S a) ∧
      Nat.Coprime
        (directOrbitCanonicalCommonFactor_gapRoot R S a)
        (directOrbitCanonicalCommonFactor_quotientRoot R S a) := by
  classical
  have hsp : ∀ q ∈ a.primeFactors, q.Prime := fun q hq =>
    Nat.prime_of_mem_primeFactors hq
  have hpowcop : ∀ {p q e f : ℕ}, p.Prime → q.Prime → p ≠ q →
      Nat.Coprime (p ^ e) (q ^ f) := by
    intro p q e f hp hq hpq
    exact Nat.coprime_pow_primes e f hp hq hpq
  have hdisj := canonicalCommonFactor_prime_support_disjoint (R := R) (S := S) (a := a)
  refine ⟨?_, ?_, ?_⟩
  · unfold directOrbitCanonicalCommonFactor_commonProduct
    unfold directOrbitCanonicalCommonFactor_gapRoot
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    rw [Nat.coprime_prod_right_iff]
    intro q hq
    have hp0 := Finset.mem_filter.mp hp
    have hq0 := Finset.mem_filter.mp hq
    have hpq : p ≠ q := by
      intro heq
      apply (Finset.disjoint_left.mp hdisj.1) hp
      simpa [heq] using hq
    exact hpowcop (hsp p hp0.1) (hsp q hq0.1) hpq
  · unfold directOrbitCanonicalCommonFactor_commonProduct
    unfold directOrbitCanonicalCommonFactor_quotientRoot
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    rw [Nat.coprime_prod_right_iff]
    intro q hq
    have hp0 := Finset.mem_filter.mp hp
    have hq0 := Finset.mem_filter.mp hq
    have hpq : p ≠ q := by
      intro heq
      apply (Finset.disjoint_left.mp hdisj.2.1) hp
      simpa [heq] using hq
    exact hpowcop (hsp p hp0.1) (hsp q hq0.1) hpq
  · unfold directOrbitCanonicalCommonFactor_gapRoot
    unfold directOrbitCanonicalCommonFactor_quotientRoot
    rw [Nat.coprime_prod_left_iff]
    intro p hp
    rw [Nat.coprime_prod_right_iff]
    intro q hq
    have hp0 := Finset.mem_filter.mp hp
    have hq0 := Finset.mem_filter.mp hq
    have hpq : p ≠ q := by
      intro heq
      apply (Finset.disjoint_left.mp hdisj.2.2) hp
      simpa [heq] using hq
    exact hpowcop (hsp p hp0.1) (hsp q hq0.1) hpq

private theorem canonicalCommonFactor_scalar_ideal_map
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Ideal.map (algebraMap ℤ O)
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) =
      Ideal.span {modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} := by
  simp [Ideal.map_span]

private theorem canonicalCommonFactor_span_model_ne_bot
    {s : SevenRealCubicInt} (hs : s ≠ 0) :
    Ideal.span ({modelEquivRingOfIntegers s} : Set O) ≠ ⊥ := by
  intro h
  have hm : modelEquivRingOfIntegers s ∈ (⊥ : Ideal O) := by
    rw [← h]
    exact Ideal.mem_span_singleton_self _
  have hm0 : modelEquivRingOfIntegers s = 0 := by
    simpa using hm
  apply hs
  apply modelEquivRingOfIntegers.injective
  simpa using hm0

theorem directOrbitCanonicalCommonFactor_prime_absNorm
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    Ideal.absNorm P = q := by
  let : P.IsPrime := hPprime
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hPover
  have hbase0 : Ideal.span {(q : ℤ)} ≠ (⊥ : Ideal ℤ) := by
    simpa using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hinertia : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span {(q : ℤ)}) P Gal(Field / ℚ)]
    exact (common_norm_prime_complete_split t hq hqR hqS).2.2.2
  have hpow := Ideal.natAbs_pow_inertiaDeg (q : ℤ) P
  rw [hinertia, pow_one] at hpow
  exact hpow.symm

theorem directOrbitCanonicalCommonFactor_scalar_ideal_multiplicity
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    multiplicity P (Ideal.span {modelEquivRingOfIntegers
      (t.powerSplit.gapSplit.a : SevenRealCubicInt)}) =
        t.powerSplit.gapSplit.a.factorization q := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hqZ : Prime (q : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hbase : base.IsPrime := by
    dsimp [base]
    exact (Ideal.span_singleton_prime (by
      exact Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero hq))).mpr hqZ
  have hbase0 : base ≠ ⊥ := by
    simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  let : P.IsPrime := hPprime
  have hP0 : P ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  let : P.LiesOver base := by simpa [base] using hPover
  have hscalar0 : Ideal.span {(t.powerSplit.gapSplit.a : ℤ)} ≠ ⊥ := by
    simpa using (Int.ofNat_ne_zero.mpr t.powerSplit.gapSplit.a_pos.ne')
  have hram : (Ideal.span {(q : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hbase0]
    have hcomplete := common_norm_prime_complete_split t hq hqR hqS
    have hri := Ideal.ramificationIdxIn_eq_ramificationIdx
      (Ideal.span {(q : ℤ)}) P (Gal(Field / ℚ))
    rw [← hri, hcomplete.2.2.1]
  have hmult :
      emultiplicity P (Ideal.map (algebraMap ℤ O)
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)})) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
    rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
      hscalar0 (Ideal.prime_of_isPrime hbase0 hbase).irreducible
      (Ideal.prime_of_isPrime hP0 hPprime).irreducible hP0]
    rw [hram]
    simp only [Nat.cast_one, one_mul]
    change emultiplicity base
      (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) = _
    have hfin : FiniteMultiplicity base
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) :=
      FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime hbase0 hbase) hscalar0
    rw [hfin.emultiplicity_eq_multiplicity]
    rw [Ideal.multiplicity_span_eq_multiplicity]
    rw [← Int.multiplicity_natAbs q (t.powerSplit.gapSplit.a : ℤ)]
    simp only [Int.natAbs_natCast, Nat.cast_inj]
    rw [Nat.multiplicity_eq_factorization hq]
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← canonicalCommonFactor_scalar_ideal_map t]
  exact hmult

theorem directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    Xor
      (gapSquareIdeal t ≤ P ∧
        multiplicity P (gapSquareIdeal t) =
          t.powerSplit.gapSplit.a.factorization q ∧
        multiplicity P (quotientSquareIdeal t) = 0)
      (quotientSquareIdeal t ≤ P ∧
        multiplicity P (gapSquareIdeal t) = 0 ∧
        multiplicity P (quotientSquareIdeal t) =
          t.powerSplit.gapSplit.a.factorization q) := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hqZ : Prime (q : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hbase0 : base ≠ ⊥ := by
    simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  have hx := directOrbitSquareRefinement_prime_ideal_allocation_xor
    t hq hqR hqS P hPprime hPover
  have hgap0 : gapSquareIdeal t ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    apply directOrbit_squareTwist_squareRoot_ne_zero t
  have hquotRoot0 : t.quotientSquareRoot ≠ 0 := by
    intro hz
    have hpos := directOrbitSquareRefinement_quotient_square_norm_pos t
    rw [hz] at hpos
    norm_num [SevenRealCubicInt.norm] at hpos
  have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    intro hz
    apply hquotRoot0
    apply modelEquivRingOfIntegers.injective
    simpa using congrArg modelEquivRingOfIntegers hz
  have hscalar0 : Ideal.span
      ({modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} : Set O) ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    intro hz
    have hzO := congrArg modelEquivRingOfIntegers hz
    have hzONat : (t.powerSplit.gapSplit.a : O) = 0 := by
      simpa using hzO
    exact t.powerSplit.gapSplit.a_pos.ne' (by exact_mod_cast hzONat)
  have hPprime' : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  have hscalar_mult := directOrbitCanonicalCommonFactor_scalar_ideal_multiplicity
    t hq hqR hqS P hPprime hPover
  have hscalar_emult : emultiplicity P
      (Ideal.span ({modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} : Set O)) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
    rw [(FiniteMultiplicity.of_prime_left hPprime' hscalar0).emultiplicity_eq_multiplicity,
      hscalar_mult]
  rcases hx with ⟨hgap, hnotquot⟩ | ⟨hquot, hnotgap⟩
  · left
    have hquot_zero : emultiplicity (P : Ideal O) (quotientSquareIdeal t) = 0 := by
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      exact hnotquot (Ideal.dvd_iff_le.mp hdiv)
    have hprod_emult : emultiplicity (P : Ideal O)
        (gapSquareIdeal t * quotientSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      change emultiplicity P
        (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
          Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O)) = _
      rw [directOrbitSquareRefinement_principal_ideal_scalar_split t]
      exact hscalar_emult
    have hgap_emult : emultiplicity (P : Ideal O) (gapSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      rw [emultiplicity_mul hPprime', hquot_zero] at hprod_emult
      simpa using hprod_emult
    exact
      ⟨⟨hgap, multiplicity_eq_of_emultiplicity_eq_some hgap_emult,
          multiplicity_eq_of_emultiplicity_eq_some hquot_zero⟩,
        by intro h; exact hnotquot h.1⟩
  · right
    have hgap_zero : emultiplicity (P : Ideal O) (gapSquareIdeal t) = 0 := by
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      exact hnotgap (Ideal.dvd_iff_le.mp hdiv)
    have hprod_emult : emultiplicity (P : Ideal O)
        (gapSquareIdeal t * quotientSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      change emultiplicity P
        (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
          Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O)) = _
      rw [directOrbitSquareRefinement_principal_ideal_scalar_split t]
      exact hscalar_emult
    have hquot_emult : emultiplicity (P : Ideal O) (quotientSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      rw [emultiplicity_mul hPprime', hgap_zero] at hprod_emult
      simpa using hprod_emult
    exact
      ⟨⟨hquot, multiplicity_eq_of_emultiplicity_eq_some hgap_zero,
          multiplicity_eq_of_emultiplicity_eq_some hquot_emult⟩,
        by intro h; exact hnotgap h.1⟩

theorem directOrbitCanonicalCommonFactor_gap_qPrimary_residual
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    ∃ P J : Ideal O,
      P.IsMaximal ∧
      P.LiesOver (Ideal.span {(q : ℤ)}) ∧
      gapSquareIdeal t =
        P ^ t.powerSplit.gapSplit.a.factorization q * J ∧
      ¬q ∣ Ideal.absNorm J := by
  have hqR' : q ∣ Ideal.absNorm (gapSquareIdeal t) := by
    change q ∣ Ideal.absNorm
      (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O))
    rw [directOrbitSquareRefinement_absNorm_span_model]
    exact hqR
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq (gapSquareIdeal t) hqR'
  have hPover : P.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hPunder.symm⟩
  have hbase0 : Ideal.span {(q : ℤ)} ≠ (⊥ : Ideal ℤ) := by
    simpa using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  have hgap0 : gapSquareIdeal t ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    exact directOrbit_squareTwist_squareRoot_ne_zero t
  have hPprime : P.IsPrime := hPmax.isPrime
  have hPprime' : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  have hfin : FiniteMultiplicity P (gapSquareIdeal t) :=
    FiniteMultiplicity.of_prime_left hPprime' hgap0
  obtain ⟨J, hJ, hJnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hPmem : P ∈
      {Q | Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O ∧
        gapSquareIdeal t ≤ Q} := by
    exact ⟨⟨hPprime, hPover⟩, Ideal.dvd_iff_le.mp hPdiv⟩
  have hPalloc := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
    t hq hqR hqS P hPprime hPover
  have hPmult : multiplicity P (gapSquareIdeal t) =
      t.powerSplit.gapSplit.a.factorization q := by
    rcases hPalloc with ⟨⟨_, hmult, _⟩, _⟩ | ⟨⟨_, hzero, _⟩, _⟩
    · exact hmult
    · have hpos := multiplicity_pos_of_dvd hPdiv hfin
      rw [hzero] at hpos
      exact (Nat.not_lt_zero _ hpos).elim
  have hPcenter : ∀ {Q : Ideal O},
      Q ∈ {Q | Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O ∧
        gapSquareIdeal t ≤ Q} → Q = P := by
    intro Q hQmem
    obtain ⟨P0, hset⟩ := Set.ncard_eq_one.mp
      (directOrbitSquareRefinement_common_prime_gap_ncard t hq hqR hqS)
    have hP0eq : P0 = P := by
      have hmem : P ∈ ({P0} : Set (Ideal O)) := by
        rw [← hset]
        exact hPmem
      simpa using hmem.symm
    have hQ0eq : Q ∈ ({P0} : Set (Ideal O)) := by
      rw [← hset]
      exact hQmem
    have hQP0 : Q = P0 := by simpa using hQ0eq
    exact hQP0.trans hP0eq
  have hqfree : ¬q ∣ Ideal.absNorm J := by
    intro hqJ
    obtain ⟨Q, hQmax, hQunder, hQdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq J hqJ
    have hQover : Q.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hQunder.symm⟩
    have hQprime : Q.IsPrime := hQmax.isPrime
    have hQdivI : Q ∣ gapSquareIdeal t := by
      rw [hJ]
      exact dvd_mul_of_dvd_right hQdiv _
    have hx := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
      t hq hqR hqS Q hQprime hQover
    rcases hx with ⟨⟨hQgap, _, _⟩, _⟩ | ⟨⟨_, hQzero, _⟩, _⟩
    · have hQP : Q = P := hPcenter
        ⟨⟨hQprime, hQover⟩, hQgap⟩
      exact hJnot (by simpa [hQP] using hQdiv)
    · have hQ0 : Q ≠ ⊥ :=
        Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 Q
      have hQprime' : Prime Q := Ideal.prime_of_isPrime hQ0 hQprime
      have hQfin : FiniteMultiplicity Q (gapSquareIdeal t) :=
        FiniteMultiplicity.of_prime_left hQprime' hgap0
      have hQpos := multiplicity_pos_of_dvd hQdivI hQfin
      rw [hQzero] at hQpos
      exact (Nat.not_lt_zero _ hQpos).elim
  exact ⟨P, J, hPmax, hPover, by simpa [hPmult] using hJ, hqfree⟩

theorem directOrbitCanonicalCommonFactor_gap_factorization
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    (Int.natAbs (norm t.gapSquareRoot)).factorization q =
      t.powerSplit.gapSplit.a.factorization q := by
  obtain ⟨P, J, hPmax, hPover, hEq, hqfree⟩ :=
    directOrbitCanonicalCommonFactor_gap_qPrimary_residual
      t hq hqR hqS
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have hgap0 : gapSquareIdeal t ≠ ⊥ := by
      apply canonicalCommonFactor_span_model_ne_bot
      exact directOrbit_squareTwist_squareRoot_ne_zero t
    apply hgap0
    have hzero : gapSquareIdeal t = ⊥ := by
      simpa [hJ] using hEq
    exact hzero
  have hnormJ0 : Ideal.absNorm J ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr hJ0
  have hnormP := directOrbitCanonicalCommonFactor_prime_absNorm
    t hq hqR hqS P hPmax.isPrime hPover
  have hnormI : Ideal.absNorm (gapSquareIdeal t) =
      q ^ t.powerSplit.gapSplit.a.factorization q * Ideal.absNorm J := by
    have h := congrArg Ideal.absNorm hEq
    rw [map_mul, map_pow, hnormP] at h
    exact h
  have hfac : (Ideal.absNorm (gapSquareIdeal t)).factorization q =
      (q ^ t.powerSplit.gapSplit.a.factorization q).factorization q +
        (Ideal.absNorm J).factorization q := by
    rw [hnormI, Nat.factorization_mul
      (pow_ne_zero _ hq.ne_zero) hnormJ0]
    rfl
  have hfacJ : (Ideal.absNorm J).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqfree
  have hfacPow :
      (q ^ t.powerSplit.gapSplit.a.factorization q).factorization q =
        t.powerSplit.gapSplit.a.factorization q :=
    Nat.factorization_pow_self hq
  change (Ideal.absNorm
    (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O))).factorization q = _
    at hfac
  rw [directOrbitSquareRefinement_absNorm_span_model] at hfac
  rw [hfacJ, hfacPow, add_zero] at hfac
  exact hfac

theorem directOrbitCanonicalCommonFactor_quotient_qPrimary_residual
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    ∃ A B J : Ideal O,
      A.IsPrime ∧ B.IsPrime ∧
      A.LiesOver (Ideal.span {(q : ℤ)}) ∧
      B.LiesOver (Ideal.span {(q : ℤ)}) ∧
      A ≠ B ∧
      quotientSquareIdeal t =
        (A ^ t.powerSplit.gapSplit.a.factorization q) *
          (B ^ t.powerSplit.gapSplit.a.factorization q) * J ∧
      ¬q ∣ Ideal.absNorm J := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hbase0 : base ≠ (⊥ : Ideal ℤ) := by
    simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hHcard : ({Q | Q ∈ Ideal.primesOver base O ∧
      quotientSquareIdeal t ≤ Q} : Set (Ideal O)).ncard = 2 := by
    simpa [base] using
      directOrbitSquareRefinement_common_prime_quotient_ncard t hq hqR hqS
  obtain ⟨A, B, hAB, hHset⟩ := Set.ncard_eq_two.mp hHcard
  have hAmem' : A ∈ ({Q | Q ∈ Ideal.primesOver base O ∧
      quotientSquareIdeal t ≤ Q} : Set (Ideal O)) := by
    rw [hHset]
    simp
  have hBmem' : B ∈ ({Q | Q ∈ Ideal.primesOver base O ∧
      quotientSquareIdeal t ≤ Q} : Set (Ideal O)) := by
    rw [hHset]
    simp
  have hAmem : A ∈ Ideal.primesOver base O ∧ quotientSquareIdeal t ≤ A := hAmem'
  have hBmem : B ∈ Ideal.primesOver base O ∧ quotientSquareIdeal t ≤ B := hBmem'
  have hAprime : A.IsPrime := hAmem.1.1
  have hBprime : B.IsPrime := hBmem.1.1
  have hAover : A.LiesOver base := hAmem.1.2
  have hBover : B.LiesOver base := hBmem.1.2
  have hA0 : A ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 A
  have hB0 : B ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 B
  have hquotRoot0 : t.quotientSquareRoot ≠ 0 := by
    intro hz
    have hpos := directOrbitSquareRefinement_quotient_square_norm_pos t
    rw [hz] at hpos
    norm_num [SevenRealCubicInt.norm] at hpos
  have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    intro hz
    apply hquotRoot0
    apply modelEquivRingOfIntegers.injective
    simpa using congrArg modelEquivRingOfIntegers hz
  have hAfin : FiniteMultiplicity A (quotientSquareIdeal t) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime hA0 hAprime) hquot0
  have hBfin : FiniteMultiplicity B (quotientSquareIdeal t) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime hB0 hBprime) hquot0
  have hAmult : multiplicity A (quotientSquareIdeal t) =
      t.powerSplit.gapSplit.a.factorization q := by
    have hx := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
      t hq hqR hqS A hAprime hAover
    rcases hx with ⟨⟨_, _, hzero⟩, _⟩ | ⟨⟨_, _, hmult⟩, _⟩
    · have hpos := multiplicity_pos_of_dvd
        (Ideal.dvd_iff_le.mpr hAmem.2) hAfin
      rw [hzero] at hpos
      exact (Nat.not_lt_zero _ hpos).elim
    · exact hmult
  have hBmult : multiplicity B (quotientSquareIdeal t) =
      t.powerSplit.gapSplit.a.factorization q := by
    have hx := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
      t hq hqR hqS B hBprime hBover
    rcases hx with ⟨⟨_, _, hzero⟩, _⟩ | ⟨⟨_, _, hmult⟩, _⟩
    · have hpos := multiplicity_pos_of_dvd
        (Ideal.dvd_iff_le.mpr hBmem.2) hBfin
      rw [hzero] at hpos
      exact (Nat.not_lt_zero _ hpos).elim
    · exact hmult
  have hAdiv : A ^ t.powerSplit.gapSplit.a.factorization q ∣
      quotientSquareIdeal t := by
    exact pow_dvd_of_le_multiplicity (hAmult ▸ le_rfl)
  have hBdiv : B ^ t.powerSplit.gapSplit.a.factorization q ∣
      quotientSquareIdeal t := by
    exact pow_dvd_of_le_multiplicity (hBmult ▸ le_rfl)
  let : A.IsMaximal := hAprime.isMaximal hA0
  let : B.IsMaximal := hBprime.isMaximal hB0
  have hcop : IsCoprime A B := Ideal.isCoprime_of_isMaximal hAB
  have hcopPow : IsCoprime
      (A ^ t.powerSplit.gapSplit.a.factorization q) B := hcop.pow_left
  have hcopPow' : IsCoprime
      (A ^ t.powerSplit.gapSplit.a.factorization q)
      (B ^ t.powerSplit.gapSplit.a.factorization q) := hcopPow.pow_right
  obtain ⟨J, hJ⟩ := hcopPow'.mul_dvd hAdiv hBdiv
  have hJ0 : J ≠ ⊥ := by
    intro hJ0
    apply hquot0
    simpa [hJ0] using hJ
  have hAnot : ¬A ^ (t.powerSplit.gapSplit.a.factorization q + 1) ∣
      quotientSquareIdeal t := by
    apply hAfin.not_pow_dvd_of_multiplicity_lt
    rw [hAmult]
    exact Nat.lt_succ_self _
  have hBnot : ¬B ^ (t.powerSplit.gapSplit.a.factorization q + 1) ∣
      quotientSquareIdeal t := by
    apply hBfin.not_pow_dvd_of_multiplicity_lt
    rw [hBmult]
    exact Nat.lt_succ_self _
  have hAres : ¬A ∣ J := by
    intro hAJ
    obtain ⟨K, hK⟩ := hAJ
    apply hAnot
    rw [hJ, hK, pow_succ]
    exact ⟨B ^ t.powerSplit.gapSplit.a.factorization q * K, by ac_rfl⟩
  have hBres : ¬B ∣ J := by
    intro hBJ
    obtain ⟨K, hK⟩ := hBJ
    apply hBnot
    rw [hJ, hK, pow_succ]
    exact ⟨A ^ t.powerSplit.gapSplit.a.factorization q * K, by
      simp [mul_assoc, mul_comm, mul_left_comm]⟩
  have hqfree : ¬q ∣ Ideal.absNorm J := by
    intro hqJ
    obtain ⟨Q, hQmax, hQunder, hQdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq J hqJ
    have hQover : Q.LiesOver base := ⟨hQunder.symm⟩
    have hQdivI : Q ∣ quotientSquareIdeal t := by
      rw [hJ]
      exact dvd_mul_of_dvd_right hQdiv _
    have hQmem : Q ∈ ({A, B} : Set (Ideal O)) := by
      have hmem : Q ∈ ({Q | Q ∈ Ideal.primesOver base O ∧
          quotientSquareIdeal t ≤ Q} : Set (Ideal O)) :=
        ⟨⟨hQmax.isPrime, hQover⟩, Ideal.dvd_iff_le.mp hQdivI⟩
      rw [hHset] at hmem
      simpa using hmem
    rcases hQmem with hQA | hQB
    · subst Q
      exact hAres hQdiv
    · subst Q
      exact hBres hQdiv
  exact ⟨A, B, J, hAprime, hBprime, hAover, hBover, hAB, hJ, hqfree⟩

theorem directOrbitCanonicalCommonFactor_quotient_factorization
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    (Int.natAbs (norm t.quotientSquareRoot)).factorization q =
      2 * t.powerSplit.gapSplit.a.factorization q := by
  obtain ⟨A, B, J, hAprime, hBprime, hAover, hBover, hAB, hEq, hqfree⟩ :=
    directOrbitCanonicalCommonFactor_quotient_qPrimary_residual
      t hq hqR hqS
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
      apply canonicalCommonFactor_span_model_ne_bot
      intro hz
      apply directOrbitSquareRefinement_quotient_square_norm_pos t |>.ne'
      have hz0 : t.quotientSquareRoot = 0 := by
        apply modelEquivRingOfIntegers.injective
        simpa using congrArg modelEquivRingOfIntegers hz
      simp [hz0, SevenRealCubicInt.norm]
    apply hquot0
    simpa [hJ] using hEq
  have hnormJ0 : Ideal.absNorm J ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr hJ0
  have hnormA := directOrbitCanonicalCommonFactor_prime_absNorm
    t hq hqR hqS A hAprime hAover
  have hnormB := directOrbitCanonicalCommonFactor_prime_absNorm
    t hq hqR hqS B hBprime hBover
  let m := t.powerSplit.gapSplit.a.factorization q
  have hnormI : Ideal.absNorm (quotientSquareIdeal t) =
      q ^ (2 * m) * Ideal.absNorm J := by
    have h := congrArg Ideal.absNorm hEq
    rw [map_mul, map_mul, map_pow, map_pow, hnormA, hnormB] at h
    calc
      Ideal.absNorm (quotientSquareIdeal t) = q ^ m * q ^ m * Ideal.absNorm J := h
      _ = q ^ (2 * m) * Ideal.absNorm J := by
        rw [← pow_add, two_mul]
  have hfac : (Ideal.absNorm (quotientSquareIdeal t)).factorization q =
      (q ^ (2 * m)).factorization q + (Ideal.absNorm J).factorization q := by
    rw [hnormI, Nat.factorization_mul
      (pow_ne_zero _ hq.ne_zero) hnormJ0]
    rfl
  have hfacJ : (Ideal.absNorm J).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqfree
  have hfacPow : (q ^ (2 * m)).factorization q = 2 * m := by
    exact Nat.factorization_pow_self hq
  change (Ideal.absNorm
    (Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O))).factorization q = _
    at hfac
  rw [directOrbitSquareRefinement_absNorm_span_model] at hfac
  rw [hfacJ, hfacPow, add_zero] at hfac
  exact hfac

theorem directOrbitCanonicalCommonFactor_prime_exponent_table
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqa : q ∣ t.powerSplit.gapSplit.a) :
    (q ∣ Int.natAbs (norm t.gapSquareRoot) ∧
        q ∣ Int.natAbs (norm t.quotientSquareRoot) →
      (Int.natAbs (norm t.gapSquareRoot)).factorization q =
          t.powerSplit.gapSplit.a.factorization q ∧
        (Int.natAbs (norm t.quotientSquareRoot)).factorization q =
          2 * t.powerSplit.gapSplit.a.factorization q) ∧
    (q ∣ Int.natAbs (norm t.gapSquareRoot) ∧
        ¬q ∣ Int.natAbs (norm t.quotientSquareRoot) →
      (Int.natAbs (norm t.gapSquareRoot)).factorization q =
          3 * t.powerSplit.gapSplit.a.factorization q ∧
        (Int.natAbs (norm t.quotientSquareRoot)).factorization q = 0) ∧
    (¬q ∣ Int.natAbs (norm t.gapSquareRoot) ∧
        q ∣ Int.natAbs (norm t.quotientSquareRoot) →
      (Int.natAbs (norm t.gapSquareRoot)).factorization q = 0 ∧
        (Int.natAbs (norm t.quotientSquareRoot)).factorization q =
          3 * t.powerSplit.gapSplit.a.factorization q) := by
  let R := Int.natAbs (norm t.gapSquareRoot)
  let S := Int.natAbs (norm t.quotientSquareRoot)
  let a := t.powerSplit.gapSplit.a
  have hR : R ≠ 0 := by
    simpa [R] using (directOrbitSquareRefinement_gap_square_norm_pos t).ne'
  have hS : S ≠ 0 := by
    simpa [S] using (directOrbitSquareRefinement_quotient_square_norm_pos t).ne'
  have hRS : R * S = a ^ 3 := by
    simpa [R, S, a] using directOrbitSquareRefinement_squareRoots_norm_mul_eq_cube t
  have hledger : ∀ q, R.factorization q + S.factorization q =
      3 * a.factorization q := cubeDefect_factorization_ledger hR hS hRS
  have hcommon : ∀ {q}, q.Prime → q ∣ R → q ∣ S →
      R.factorization q = a.factorization q ∧
        S.factorization q = 2 * a.factorization q := by
    intro q hq hqR hqS
    refine ⟨?_, ?_⟩
    · simpa [R, a] using directOrbitCanonicalCommonFactor_gap_factorization
        t hq (by simpa [R] using hqR) (by simpa [S] using hqS)
    · simpa [S, a] using directOrbitCanonicalCommonFactor_quotient_factorization
        t hq (by simpa [R] using hqR) (by simpa [S] using hqS)
  simpa [R, S, a] using
    canonicalCommonFactor_three_case_exponents hledger hcommon hq
      (by simpa [a] using hqa)

theorem directOrbitSquareRefinement_canonicalCommonFactor_nonempty
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Nonempty (DirectOrbitCanonicalCommonFactorPacket p) := by
  let R := Int.natAbs (norm t.gapSquareRoot)
  let S := Int.natAbs (norm t.quotientSquareRoot)
  let a := t.powerSplit.gapSplit.a
  let C := directOrbitCanonicalCommonFactor_commonProduct R S a
  let U := directOrbitCanonicalCommonFactor_gapRoot R S a
  let V := directOrbitCanonicalCommonFactor_quotientRoot R S a
  have hR : R ≠ 0 := by
    simpa [R] using (directOrbitSquareRefinement_gap_square_norm_pos t).ne'
  have hS : S ≠ 0 := by
    simpa [S] using (directOrbitSquareRefinement_quotient_square_norm_pos t).ne'
  have ha : a ≠ 0 := by
    simpa [a] using t.powerSplit.gapSplit.a_pos.ne'
  have hRS : R * S = a ^ 3 := by
    simpa [R, S, a] using directOrbitSquareRefinement_squareRoots_norm_mul_eq_cube t
  have htable : ∀ {q}, q.Prime → q ∣ a →
      (q ∣ R ∧ q ∣ S →
        R.factorization q = a.factorization q ∧
          S.factorization q = 2 * a.factorization q) ∧
      (q ∣ R ∧ ¬q ∣ S →
        R.factorization q = 3 * a.factorization q ∧ S.factorization q = 0) ∧
      (¬q ∣ R ∧ q ∣ S →
        R.factorization q = 0 ∧ S.factorization q = 3 * a.factorization q) := by
    intro q hq hqa
    simpa [R, S, a] using
      directOrbitCanonicalCommonFactor_prime_exponent_table t hq
        (by simpa [a] using hqa)
  obtain ⟨hR_eq, hS_eq, ha_eq⟩ :=
    canonicalCommonFactor_reconstruction hR hS ha hRS htable
  have hCeq : C = Nat.gcd R S := by
    simpa [C] using canonicalCommonFactor_gcd_eq hR hS ha hRS htable
  have hcop := canonicalCommonFactor_pairwise_coprime (R := R) (S := S) (a := a)
  have hCpos : 0 < C := by
    unfold C directOrbitCanonicalCommonFactor_commonProduct
    exact Finset.prod_pos (fun q hq =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _)
  have hUpos : 0 < U := by
    unfold U directOrbitCanonicalCommonFactor_gapRoot
    exact Finset.prod_pos (fun q hq =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _)
  have hVpos : 0 < V := by
    unfold V directOrbitCanonicalCommonFactor_quotientRoot
    exact Finset.prod_pos (fun q hq =>
      pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos _)
  have hheight0 : R ^ 2 < a := by
    simpa [R, a] using directOrbitSquareRefinement_gap_square_norm_lt_base t
  have hleft : R ^ 2 = (C * U) * (C * U ^ 5) := by
    rw [hR_eq]
    simp only [C, U]
    ring
  have hright : a = (C * U) * V := by
    rw [ha_eq]
  rw [hleft, hright] at hheight0
  have hheight : C * U ^ 5 < V :=
    (Nat.mul_lt_mul_left (mul_pos hCpos hUpos)).mp hheight0
  have hc_dvd_a : C ∣ a := by
    refine ⟨U * V, ?_⟩
    calc
      a = C * U * V := ha_eq
      _ = C * (U * V) := by ring
  have hc_support : ∀ q, q.Prime → q ∣ C → exceptionalModSeven q := by
    intro q hq hqC
    have hqg : q ∣ Nat.gcd R S := by simpa [hCeq] using hqC
    have hqRS : q ∣ R ∧ q ∣ S := Nat.dvd_gcd_iff.mp hqg
    exact common_norm_prime_mod_seven t hq
      (by simpa [R] using hqRS.1) (by simpa [S] using hqRS.2)
  refine ⟨{
    squareRefinement := t
    c := C
    u := U
    v := V
    c_pos := hCpos
    u_pos := hUpos
    v_pos := hVpos
    c_eq_gcd := hCeq
    c_dvd_a := by simpa [C, a] using hc_dvd_a
    gapNorm_eq := by simpa [R, C, U] using hR_eq
    quotientNorm_eq := by simpa [S, C, V] using hS_eq
    unitPart_eq := by simpa [a, C, U, V] using ha_eq
    c_u_coprime := hcop.1
    c_v_coprime := hcop.2.1
    u_v_coprime := hcop.2.2
    c_prime_support := hc_support
    height := hheight
  }⟩

end SevenRealCubic
end
end DkMath.FLT.Seven
