import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin

namespace DkMath.FLT.Seven

open scoped BigOperators

def r37CommonSupport (R S a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun q => q ∣ R ∧ q ∣ S)

def r37GapOnlySupport (R S a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun q => q ∣ R ∧ ¬q ∣ S)

def r37QuotientOnlySupport (R S a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun q => ¬q ∣ R ∧ q ∣ S)

def r37CommonProduct (R S a : ℕ) : ℕ :=
  ∏ q ∈ r37CommonSupport R S a, q ^ a.factorization q

def r37GapRoot (R S a : ℕ) : ℕ :=
  ∏ q ∈ r37GapOnlySupport R S a, q ^ a.factorization q

def r37QuotientRoot (R S a : ℕ) : ℕ :=
  ∏ q ∈ r37QuotientOnlySupport R S a, q ^ a.factorization q

private theorem r37_support_prime
    {_R _S a : ℕ} {q : ℕ} (hq : q ∈ a.primeFactors) : q.Prime :=
  Nat.prime_of_mem_primeFactors hq

private theorem r37_factorization_prime_power
    {p q e : ℕ} (hp : p.Prime) :
    (p ^ e).factorization q = if p = q then e else 0 := by
  rw [Nat.Prime.factorization_pow hp]
  by_cases h : p = q <;> simp [h]

private theorem r37_product_factorization
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
    · rw [r37_factorization_prime_power (hs q hq)]
      simp [hq]
    · intro b hb hneq
      rw [r37_factorization_prime_power (hs b hb)]
      simp [hneq]
  · rw [Finset.sum_eq_zero]
    · simp [hq]
    · intro b hb
      rw [r37_factorization_prime_power (hs b hb)]
      have hneq : b ≠ q := by
        intro heq
        apply hq
        simpa [heq] using hb
      simp [hneq]

private theorem r37_prime_support_partition
    {R S a : ℕ} (ha : a ≠ 0) (hRS : R * S = a ^ 3)
    {q : ℕ} (hq : q ∈ a.primeFactors) :
    q ∈ r37CommonSupport R S a ∨
      q ∈ r37GapOnlySupport R S a ∨
      q ∈ r37QuotientOnlySupport R S a := by
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

private theorem r37_prime_support_disjoint
    {R S a : ℕ} :
    Disjoint (r37CommonSupport R S a) (r37GapOnlySupport R S a) ∧
      Disjoint (r37CommonSupport R S a) (r37QuotientOnlySupport R S a) ∧
      Disjoint (r37GapOnlySupport R S a) (r37QuotientOnlySupport R S a) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Finset.disjoint_left] <;>
    intro q hq1 hq2
  · exact (Finset.mem_filter.mp hq2).2.2 (Finset.mem_filter.mp hq1).2.2
  · exact (Finset.mem_filter.mp hq2).2.1 (Finset.mem_filter.mp hq1).2.1
  · exact (Finset.mem_filter.mp hq1).2.2 (Finset.mem_filter.mp hq2).2.2

private theorem r37_prime_support_equalities
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

private theorem r37_three_case_exponents
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

private theorem r37_canonical_reconstruction
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
    R = r37CommonProduct R S a * r37GapRoot R S a ^ 3 ∧
      S = r37CommonProduct R S a ^ 2 * r37QuotientRoot R S a ^ 3 ∧
      a = r37CommonProduct R S a * r37GapRoot R S a *
        r37QuotientRoot R S a := by
  classical
  have hRpf := r37_prime_support_equalities hR hS ha hRS |>.1
  have hSpf := r37_prime_support_equalities hR hS ha hRS |>.2
  have hcommon_filter :
      (a.primeFactors.filter (fun q => q ∣ R)).filter (fun q => q ∣ S) =
        r37CommonSupport R S a := by
    ext q
    simp [r37CommonSupport, and_assoc, and_left_comm, and_comm]
  have hgap_filter :
      (a.primeFactors.filter (fun q => q ∣ R)).filter (fun q => ¬q ∣ S) =
        r37GapOnlySupport R S a := by
    ext q
    simp [r37GapOnlySupport, and_assoc, and_left_comm, and_comm]
  have hquot_filter :
      (a.primeFactors.filter (fun q => ¬q ∣ R)).filter (fun q => q ∣ S) =
        r37QuotientOnlySupport R S a := by
    ext q
    simp [r37QuotientOnlySupport, and_assoc, and_left_comm, and_comm]
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
        (∏ q ∈ r37CommonSupport R S a, q ^ R.factorization q) *
        (∏ q ∈ r37GapOnlySupport R S a, q ^ R.factorization q) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (a.primeFactors.filter (fun q => q ∣ R))
      (fun q : ℕ => q ∣ S) (fun q => q ^ R.factorization q)]
    rw [hcommon_filter, hgap_filter]
  have hSsplit :
      (∏ q ∈ a.primeFactors.filter (fun q => q ∣ S),
        q ^ S.factorization q) =
        (∏ q ∈ r37CommonSupport R S a, q ^ S.factorization q) *
        (∏ q ∈ r37QuotientOnlySupport R S a, q ^ S.factorization q) := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (a.primeFactors.filter (fun q => q ∣ S))
      (fun q : ℕ => q ∣ R) (fun q => q ^ S.factorization q)]
    have hcommon_filter' :
        (a.primeFactors.filter (fun q => q ∣ S)).filter (fun q => q ∣ R) =
          r37CommonSupport R S a := by
      ext q
      simp [r37CommonSupport, and_assoc, and_left_comm, and_comm]
    have hquot_filter' :
        (a.primeFactors.filter (fun q => q ∣ S)).filter (fun q => ¬q ∣ R) =
          r37QuotientOnlySupport R S a := by
      ext q
      simp [r37QuotientOnlySupport, and_assoc, and_left_comm, and_comm]
    rw [hcommon_filter']
    rw [hquot_filter']
  have hRcommon :
      (∏ q ∈ r37CommonSupport R S a, q ^ R.factorization q) =
        r37CommonProduct R S a := by
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := Nat.prime_of_mem_primeFactors hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    exact congrArg (fun e => q ^ e)
      (htable hqprime hqa |>.1 hq0.2 |>.1)
  have hRgap :
      (∏ q ∈ r37GapOnlySupport R S a, q ^ R.factorization q) =
        r37GapRoot R S a ^ 3 := by
    unfold r37GapRoot
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
      (∏ q ∈ r37CommonSupport R S a, q ^ S.factorization q) =
        r37CommonProduct R S a ^ 2 := by
    unfold r37CommonProduct
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := r37_support_prime (_R := R) (_S := S) (a := a) hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    rw [htable hqprime hqa |>.1 hq0.2 |>.2]
    rw [← pow_mul]
    exact congrArg (fun n => q ^ n) (Nat.mul_comm _ _)
  have hSquoter :
      (∏ q ∈ r37QuotientOnlySupport R S a, q ^ S.factorization q) =
        r37QuotientRoot R S a ^ 3 := by
    unfold r37QuotientRoot
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q hq
    have hq0 := Finset.mem_filter.mp hq
    have hqprime := r37_support_prime (_R := R) (_S := S) (a := a) hq0.1
    have hqa := (Nat.mem_primeFactors_of_ne_zero ha).mp hq0.1 |>.2
    rw [htable hqprime hqa |>.2.2 hq0.2 |>.2]
    rw [← pow_mul]
    exact congrArg (fun n => q ^ n) (Nat.mul_comm _ _)
  have hR_eq : R = r37CommonProduct R S a * r37GapRoot R S a ^ 3 := by
    calc
      R = ∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
          q ^ R.factorization q := hRprod
      _ = (∏ q ∈ r37CommonSupport R S a, q ^ R.factorization q) *
          (∏ q ∈ r37GapOnlySupport R S a, q ^ R.factorization q) := hRsplit
      _ = _ := by rw [hRcommon, hRgap]
  have hS_eq : S = r37CommonProduct R S a ^ 2 *
      r37QuotientRoot R S a ^ 3 := by
    calc
      S = ∏ q ∈ a.primeFactors.filter (fun q => q ∣ S),
          q ^ S.factorization q := hSprod
      _ = (∏ q ∈ r37CommonSupport R S a, q ^ S.factorization q) *
          (∏ q ∈ r37QuotientOnlySupport R S a, q ^ S.factorization q) := hSsplit
      _ = _ := by rw [hScommon, hSquoter]
  have hA_Rsplit :
      (∏ q ∈ r37CommonSupport R S a, q ^ a.factorization q) *
        (∏ q ∈ r37GapOnlySupport R S a, q ^ a.factorization q) =
        ∏ q ∈ a.primeFactors.filter (fun q => q ∣ R),
          q ^ a.factorization q := by
    rw [← Finset.prod_filter_mul_prod_filter_not
      (a.primeFactors.filter (fun q => q ∣ R))
      (fun q : ℕ => q ∣ S) (fun q => q ^ a.factorization q)]
    rw [hcommon_filter, hgap_filter]
  have hnotR_filter :
      a.primeFactors.filter (fun q => ¬q ∣ R) =
        r37QuotientOnlySupport R S a := by
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
      (∏ q ∈ r37CommonSupport R S a, q ^ a.factorization q) *
        (∏ q ∈ r37GapOnlySupport R S a, q ^ a.factorization q) *
          (∏ q ∈ r37QuotientOnlySupport R S a, q ^ a.factorization q) =
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
  have ha_eq : a = r37CommonProduct R S a * r37GapRoot R S a *
      r37QuotientRoot R S a := by
    calc
      a = ∏ q ∈ a.primeFactors, q ^ a.factorization q :=
        Nat.prod_primeFactors_pow_factorization ha
      _ = _ := hApart.symm
  exact ⟨hR_eq, hS_eq, ha_eq⟩

private theorem r37_gcd_test
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
    r37CommonProduct R S a = Nat.gcd R S := by
  classical
  have hsp : ∀ q ∈ r37CommonSupport R S a, q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hcp : r37CommonProduct R S a ≠ 0 := by
    unfold r37CommonProduct
    exact Finset.prod_ne_zero_iff.mpr (fun q hq =>
      pow_ne_zero _ (hsp q hq).ne_zero)
  apply Nat.eq_of_factorization_eq hcp (Nat.gcd_ne_zero_left hR)
  intro q
  by_cases hq : q.Prime
  · unfold r37CommonProduct
    rw [r37_product_factorization (_R := R) (_S := S) (a := a) hsp q,
      Nat.factorization_gcd hR hS]
    by_cases hqC : q ∈ r37CommonSupport R S a
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

end DkMath.FLT.Seven
