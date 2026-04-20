import DkMath.Basic

#print "file: DkMath.ABC.Rad"

namespace DkMath.ABC

/- ============================================================================
     2. rad: definition + basic facts
   ============================================================================ -/

/-- rad(n) := 素因数分解の support 上に現れる素数の積 -/
def rad (n : ℕ) : ℕ :=
  n.factorization.support.prod (fun p => p)

/-- rad(n) の定義を n ≥ 1 に制限したバージョン -/
def rad' (n : ℕ) (hn : n ≥ 1) : ℕ :=
  match n with
  | 0 => 1 -- In the case n = 0: we define rad(0) = 1 for convenience (technically undefined)
  | _ =>   -- For n ≥ 1: rad(n) ≥ 1
    n.factorization.support.prod (fun p => p)

/-- rad(1) = 1 であること -/
lemma rad_one' : rad 1 = 1 := by
  simp only [rad, Nat.factorization_one, Finsupp.support_zero, Finset.prod_empty]

/-- rad(0) = 1 であること -/
lemma rad_zero' : rad 0 = 1 := by
  simp only [rad, Nat.factorization_zero, Finsupp.support_zero, Finset.prod_empty]

/-- rad(0) = 1 であること -/
@[simp] lemma rad_zero : rad 0 = 1 := by rw [rad_zero']
/-- rad(1) = 1 であること -/
@[simp] lemma rad_one : rad 1 = 1 := by rw [rad_one']

/- 小さな補題群の整理：rad に関する再利用可能補題 -/

/-`rad n ∣ n` を切り出しておくと再利用が楽になる（n ≠ 0 の場合）。-/
/--
`rad_dvd_nonzero` は、任意の自然数 `n` が 0 でないとき、その数の radical（`rad n`、すなわち `n` の素因数の積）が `n` を割り切ることを示す補題です。

radical `rad n` は、`n` の素因数全体の積として定義されます。
この補題の証明では、まず `n` の素因数分解を利用して `n = ∏_{p∈s} p^(f p)` という形に書き換えます。
（ここで `s` は `n` の素因数の集合、`f p` は素因数 `p` の指数）
各素因数 `p` について、`p` は `p^(f p)` を割り切ることから、素因数全体の積（radical）は `n` を割り切ることが分かります。

この補題は、整数論において radical の基本的な性質を述べており、例えば square-free な数や、radical を用いた他の性質の証明の基礎となります。
-/
lemma rad_dvd_nonzero (n : ℕ) (hn : n ≠ 0) : rad n ∣ n := by
  classical
  unfold rad
  let f := n.factorization
  let s := f.support
  -- n = ∏_{p∈s} p^(f p)
  have hfac : n = s.prod (fun p => p ^ f p) := Eq.symm (Nat.prod_factorization_pow_eq_self hn)
  -- 各 p ∈ s について p ∣ p^(f p)
  have hpt : ∀ p ∈ s, p ∣ p ^ f p := by
    intro p hp
    -- support 上の要素なので指数は非零
    rw [Finsupp.mem_support_iff] at hp
    have hf : f p ≠ 0 := hp
    exact dvd_pow_self p hf
  have hdiv : s.prod (fun p => p) ∣ s.prod (fun p => p ^ f p) :=
    Finset.prod_dvd_prod_of_dvd (fun p => p) (fun p => p ^ f p) fun p hp => hpt p hp
  rw [Eq.symm hfac] at hdiv
  exact hdiv

/--
`p ∈ n.factorization.support ↔ (n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n)`。

radical kernel の多くの補題で使う、factorization support の基本特徴付け。
-/
lemma mem_support_factorization_iff {n p : ℕ} :
  p ∈ n.factorization.support ↔ (n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n) := by
  classical
  have hsup : n.factorization.support = Nat.primeFactors n := by rfl
  constructor <;> intro h
  · have hpf : p ∈ Nat.primeFactors n := by
      simpa [hsup] using h
    rw [Nat.mem_primeFactors] at hpf
    exact ⟨hpf.2.2, hpf.1, hpf.2.1⟩
  · rcases h with ⟨hn, hp, hpd⟩
    have hpf : p ∈ Nat.primeFactors n := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpd, hn⟩
    simpa [hsup] using hpf

/-- support 上の素数積の対数は、各素数対数の総和に等しい。 -/
theorem support_prod_log_eq_sum_log (n : ℕ) :
    Real.log ((Nat.factorization n).support.prod fun p => (p : ℝ))
      = ∑ p ∈ (Nat.factorization n |>.support), Real.log (p : ℝ) := by
  have h_nz : ∀ p ∈ (Nat.factorization n).support, (p : ℝ) ≠ 0 := by
    intro p hp
    rcases mem_support_factorization_iff.mp hp with ⟨_, hprime, _⟩
    exact_mod_cast Nat.Prime.ne_zero hprime
  simpa using
    (Real.log_prod
      (α := ℕ)
      (s := (Nat.factorization n).support)
      (f := fun p : ℕ => (p : ℝ))
      h_nz)

/-- support 上の素数積の対数は、各素数対数の総和以上である。 -/
lemma support_prod_log_ge_sum_log (n : ℕ) :
    Real.log ((Nat.factorization n).support.prod fun p => (p : ℝ))
      ≥ ∑ p ∈ (Nat.factorization n |>.support), Real.log (p : ℝ) := by
  exact le_of_eq (support_prod_log_eq_sum_log n).symm

/-- radical は factorization support 上の素数積そのものである。 -/
theorem rad_prod (n : ℕ) (_hn : n ≥ 2) :
    rad n = ∏ p ∈ (Nat.factorization n |>.support), p := by
  simp only [rad, Nat.support_factorization]

/-- radical の対数は、support 上の素数対数和に等しい。 -/
theorem rad_log_eq_sum_prime_logs (n : ℕ) (_hn : n ≥ 2) :
    Real.log (rad n) = ∑ p ∈ (Nat.factorization n |>.support), Real.log p := by
  have hprod : (rad n : ℝ) = (Nat.factorization n).support.prod fun p => (p : ℝ) := by
    simp only [rad, Nat.support_factorization, Nat.cast_prod]
  rw [hprod]
  have h_nz : ∀ p ∈ (Nat.factorization n).support, (p : ℝ) ≠ 0 := by
    intro p hp
    rcases mem_support_factorization_iff.mp hp with ⟨_, hprime, _⟩
    exact_mod_cast Nat.Prime.ne_zero hprime
  exact Real.log_prod
      (α := ℕ)
      (s := (Nat.factorization n).support)
      (f := fun p : ℕ => (p : ℝ))
      h_nz

/-- radical の対数は、support 上の素数対数和以上である。 -/
lemma rad_log_ge_sum_prime_logs (n : ℕ) (hn : n ≥ 2) :
    Real.log (rad n) ≥ ∑ p ∈ (Nat.factorization n |>.support), Real.log p := by
  exact le_of_eq (rad_log_eq_sum_prime_logs n hn).symm

/-- 互いに素なら factorization support は交わらない。 -/
lemma disjoint_support_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
  Disjoint a.factorization.support b.factorization.support := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hpA hpB
  have ⟨_, pp, p_div_a⟩ := mem_support_factorization_iff.mp hpA
  have ⟨_, _, p_div_b⟩ := mem_support_factorization_iff.mp hpB
  have hgd := Nat.dvd_gcd p_div_a p_div_b
  rw [h] at hgd
  exact pp.not_dvd_one hgd

/-- 互いに素なら support は単純に和集合になる。 -/
lemma support_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
  (a*b).factorization.support = a.factorization.support ∪ b.factorization.support := by
  classical
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_left] at h
      exact h
    subst hb1
    simp
  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : a = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_right] at h
      exact h
    subst ha1
    simp
  have hfac :
      (a * b).factorization = a.factorization + b.factorization :=
    Nat.factorization_mul ha0 hb0
  rw [hfac]
  ext p
  have add_iff :
      (a.factorization p + b.factorization p ≠ 0) ↔
        (a.factorization p ≠ 0 ∨ b.factorization p ≠ 0) := by
    constructor
    · intro hsum
      by_cases ha' : a.factorization p = 0
      · have hb_non : b.factorization p ≠ 0 := by
          by_contra hb0'
          simp [ha', hb0'] at hsum
        exact Or.inr hb_non
      · exact Or.inl ha'
    · intro h'
      rcases h' with (ha_non | hb_non)
      · by_contra hsum
        exact ha_non (Nat.add_eq_zero_iff.mp hsum).1
      · by_contra hsum
        exact hb_non (Nat.add_eq_zero_iff.mp hsum).2
  rw [Finsupp.mem_support_iff, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  simp [add_iff]

/-- [★] 互いに素での乗法性 `rad(ab) = rad(a) * rad(b)`。 -/
lemma rad_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
  rad (a*b) = rad a * rad b := by
  classical
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_left] at h
      exact h
    subst hb1
    simp
  by_cases hb0 : b = 0
  · subst hb0
    have ha1 : a = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_right] at h
      exact h
    subst ha1
    simp
  have hsup := support_mul_coprime (a := a) (b := b) h
  have hdis := disjoint_support_of_coprime (a := a) (b := b) h
  unfold rad
  rw [hsup]
  exact Finset.prod_union hdis

/-- 単調界：`rad n ≤ n` (`n ≠ 0`)。 -/
lemma rad_le {n : ℕ} (hn : n ≠ 0) : rad n ≤ n := by
  classical
  unfold rad
  let f := n.factorization
  let s := f.support
  have hfac : n = s.prod (fun p => p ^ f p) := by
    exact Eq.symm (Nat.prod_factorization_pow_eq_self hn)
  have hdiv : s.prod (fun p : ℕ => p) ∣ s.prod (fun p => p ^ f p) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    have hf : f p ≠ 0 := by
      rw [Finsupp.mem_support_iff] at hp
      exact hp
    exact dvd_pow_self p hf
  have hrad_dvd_n : s.prod (fun p => p) ∣ n := by
    rw [hfac]
    exact hdiv
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hrad_dvd_n

-- Quick sanity checks (equivalent to the original #eval tests)
-- #eval rad 0 -- 1 (by definition)
-- #eval rad 1 -- 1 (by definition)
-- #eval rad 2 -- 2
-- #eval rad 3 -- 3
-- #eval rad 4 -- 2
-- #eval rad 6 -- 6 = 2 * 3
-- #eval rad 7 -- 7
-- #eval rad 8 -- 2
-- #eval rad 9 -- 3
-- #eval rad 12 -- 6 = 2 * 3
-- #eval rad 123 -- 123 = 3 * 41
-- #eval rad 456 -- 114 = 2 * 3 * 19
-- #eval rad 840 -- 210 = 2 * 3 * 5 * 7
-- #eval rad 1000 -- 10 = 2 * 5

end DkMath.ABC
