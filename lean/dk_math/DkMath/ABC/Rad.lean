import DkMath.Basic

#print "file: DkMath.ABC.Rad"

set_option linter.style.longLine false

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

/-- squarefree なら指数は 0/1 だけなので radical は本体に一致する。 -/
@[simp]
lemma rad_eq_self_of_squarefree {n : ℕ} (hn0 : n ≠ 0) (hsf : Squarefree n) :
    rad n = n := by
  classical
  have hfac : ∀ p ∈ n.factorization.support, n.factorization p = 1 := by
    intro p hp
    have hle := (Nat.squarefree_iff_factorization_le_one hn0).mp hsf p
    have hpos : n.factorization p ≠ 0 := (Finsupp.mem_support_iff).mp hp
    have hpos' : 0 < n.factorization p := Nat.pos_of_ne_zero hpos
    have h1le : 1 ≤ n.factorization p := Nat.succ_le_of_lt hpos'
    exact Nat.le_antisymm hle h1le
  calc
    rad n = n.factorization.support.prod (fun p => p) := rfl
    _ = n.factorization.support.prod (fun p => p ^ n.factorization p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hfac p hp]
      simp
    _ = n := Nat.prod_factorization_pow_eq_self hn0

/-- `rad_eq_self_of_squarefree` の互換別名。 -/
lemma rad_eq_self_of_squarefree' {n : ℕ} (hn0 : n ≠ 0) (hsf : Squarefree n) :
    rad n = n := by
  exact rad_eq_self_of_squarefree hn0 hsf

/-- 有限集合上の素数積の factorization は、各素数に指数 1 を与える。 -/
@[simp]
lemma factorization_prod_primes (q : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    (s.prod (fun p => p)).factorization q = if q ∈ s then 1 else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Finset.prod_empty, Nat.factorization_one]
  | @insert a t ha ih =>
      have ha_prime := hs a (Finset.mem_insert_self a t)
      have ht_primes : ∀ p ∈ t, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      let m := t.prod fun p => p
      have a_ne : a ≠ 0 := Nat.Prime.ne_zero ha_prime
      have m_ne : m ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero (ht_primes p hp)
      have prod_eq : (insert a t).prod (fun p : ℕ => p) = a * m := by
        rw [Finset.prod_insert ha]
      have mul_fac :
          ((insert a t).prod (fun p : ℕ => p)).factorization
        = a.factorization + m.factorization := by
        rw [prod_eq]
        exact Nat.factorization_mul a_ne m_ne
      have ha_fact : a.factorization q = if a = q then 1 else 0 := by
        simp [Nat.Prime.factorization ha_prime, Finsupp.single_apply]
      have ht_fact := ih ht_primes
      have hsum :
          ((insert a t).prod fun p => p).factorization q
        = a.factorization q + m.factorization q := by
        rw [mul_fac]
        rfl
      by_cases hq_a : q = a
      · subst hq_a
        have q_not_in_t : q ∉ t := by intro h; exact ha h
        have q_fact_one : q.factorization q = 1 := by simp [ha_fact]
        have m_fact_zero : m.factorization q = 0 := by
          rw [ht_fact]
          simp [q_not_in_t]
        simp [hsum, q_fact_one, m_fact_zero]
      · by_cases hq_in_t : q ∈ t
        · have a_fact_zero : a.factorization q = 0 := by
            have : a ≠ q := fun H => hq_a H.symm
            simp [ha_fact, this]
          have m_fact_one : m.factorization q = 1 := by
            rw [ht_fact]
            simp [hq_in_t]
          simp [hsum, a_fact_zero, m_fact_one, Finset.mem_insert_of_mem hq_in_t]
        · have a_fact_zero : a.factorization q = 0 := by
            have : a ≠ q := fun H => hq_a H.symm
            simp [ha_fact, this]
          have m_fact_zero : m.factorization q = 0 := by
            rw [ht_fact]
            simp [hq_in_t]
          have q_not_in_insert : q ∉ insert a t := by
            simp [Finset.mem_insert, hq_a, hq_in_t]
          simp [hsum, a_fact_zero, m_fact_zero, q_not_in_insert]

/-- `rad n = n` ならば `n` は squarefree である。 -/
lemma squarefree_of_rad_eq_self {n : ℕ} (hn0 : n ≠ 0) (h : rad n = n) :
    Squarefree n := by
  apply (Nat.squarefree_iff_factorization_le_one hn0).mpr
  intro p
  have hfac := congrArg Nat.factorization h
  rw [← hfac]
  let s := n.factorization.support
  dsimp [rad] at *
  have hs : ∀ r ∈ s, Nat.Prime r := by
    intro r hr
    exact (mem_support_factorization_iff.mp hr).2.1
  have hq := factorization_prod_primes p s hs
  have hrad_eq :
      (∏ p ∈ n.primeFactors, p).factorization p = (s.prod fun p => p).factorization p := by
    rfl
  have hval := Eq.trans hrad_eq hq
  rw [hval]
  by_cases hp : p ∈ s <;> simp [hp]

/-- 正冪は素因数の support を増やさないので radical は不変である。 -/
@[simp]
lemma rad_pow_eq_rad {n k : ℕ} (hk : 0 < k) :
    rad (n ^ k) = rad n := by
  classical
  unfold rad
  have hfac : (n ^ k).factorization = k • n.factorization := by
    exact Nat.factorization_pow n k
  have hs : (n ^ k).factorization.support = n.factorization.support := by
    ext p
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    have hfac_p : (n ^ k).factorization p = (k • n.factorization) p := by
      exact congrArg (fun f => f p) hfac
    rw [hfac_p]
    have : (k • n.factorization) p = k * n.factorization p := by
      simp [Finsupp.smul_apply]
    rw [this]
    constructor
    · intro h
      by_contra hp0
      have : k * n.factorization p = 0 := by simp [hp0]
      have := (Nat.mul_eq_zero.mp this).resolve_left (Nat.pos_iff_ne_zero.mp hk)
      contradiction
    · intro h
      by_contra hkp
      have : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
      have := (Nat.mul_eq_zero.mp hkp).resolve_right (by exact h)
      contradiction
  change (n ^ k).factorization.support.prod (fun p => p) = n.factorization.support.prod (fun p => p)
  rw [hs]

/-- `rad (a * b)` を `rad a`, `rad b`, `rad (gcd a b)` で表す一般公式。 -/
@[simp]
lemma rad_mul_general (a b : ℕ) :
    rad (a * b) = rad a * rad b / rad (Nat.gcd a b) := by
  classical
  by_cases ha0 : a = 0
  · have rb_pos : 0 < rad b := by
      have : ∀ p ∈ b.factorization.support, 0 < p := fun p hp =>
        Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
      exact Finset.prod_pos this
    rw [ha0, zero_mul, rad_zero, Nat.gcd_zero_left, one_mul, Nat.div_self rb_pos]
  by_cases hb0 : b = 0
  · have ra_pos : 0 < rad a := by
      have : ∀ p ∈ a.factorization.support, 0 < p := fun p hp =>
        Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
      exact Finset.prod_pos this
    rw [hb0, mul_zero, rad_zero, Nat.gcd_zero_right, mul_one, Nat.div_self ra_pos]
  have ha_ne : a ≠ 0 := ha0
  have hb_ne : b ≠ 0 := hb0
  let sA := a.factorization.support
  let sB := b.factorization.support
  let sAB := (a * b).factorization.support
  let sG := (Nat.gcd a b).factorization.support
  have hsA : ∀ p ∈ sA, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hsB : ∀ p ∈ sB, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hsAB : ∀ p ∈ sAB, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hsG : ∀ p ∈ sG, Nat.Prime p := by intro p hp; exact (mem_support_factorization_iff.mp hp).2.1
  have hA : ∀ p, (rad a).factorization p = if p ∈ sA then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sA hsA
  have hB : ∀ p, (rad b).factorization p = if p ∈ sB then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sB hsB
  have hAB : ∀ p, (rad (a * b)).factorization p = if p ∈ sAB then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sAB hsAB
  have hG : ∀ p, (rad (Nat.gcd a b)).factorization p = if p ∈ sG then 1 else 0 := by
    intro p
    dsimp [rad]
    exact factorization_prod_primes p sG hsG
  have sAB_eq : sAB = sA ∪ sB := by
    ext p
    constructor
    · intro hp
      rcases mem_support_factorization_iff.mp hp with ⟨_nz, pp, pd⟩
      have hdiv := (Nat.Prime.dvd_mul pp).mp pd
      rcases hdiv with pa | pb
      · exact Finset.mem_union.mpr (Or.inl (mem_support_factorization_iff.mpr ⟨ha_ne, pp, pa⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_support_factorization_iff.mpr ⟨hb_ne, pp, pb⟩))
    · intro hp
      rcases Finset.mem_union.mp hp with hA | hB
      · rcases mem_support_factorization_iff.mp hA with ⟨_, ppA, pdiva⟩
        have pd : p ∣ a * b := dvd_mul_of_dvd_left pdiva b
        exact mem_support_factorization_iff.mpr ⟨mul_ne_zero ha_ne hb_ne, ppA, pd⟩
      · rcases mem_support_factorization_iff.mp hB with ⟨_, ppB, pdivb⟩
        have pd : p ∣ a * b := dvd_mul_of_dvd_right pdivb a
        exact mem_support_factorization_iff.mpr ⟨mul_ne_zero ha_ne hb_ne, ppB, pd⟩
  have gcd_ne0 : Nat.gcd a b ≠ 0 := by
    intro H
    have ha_zero : a = 0 := Nat.eq_zero_of_gcd_eq_zero_left H
    exact ha_ne ha_zero
  have sG_eq : sG = sA ∩ sB := by
    ext p
    constructor
    · intro hp
      rcases mem_support_factorization_iff.mp hp with ⟨_nz, pp, pd⟩
      have pdiva : p ∣ a := dvd_trans pd (Nat.gcd_dvd_left a b)
      have pdivb : p ∣ b := dvd_trans pd (Nat.gcd_dvd_right a b)
      exact Finset.mem_inter.mpr
        ⟨mem_support_factorization_iff.mpr ⟨ha_ne, pp, pdiva⟩,
         mem_support_factorization_iff.mpr ⟨hb_ne, pp, pdivb⟩⟩
    · intro h
      rcases Finset.mem_inter.mp h with ⟨ha, hb⟩
      rcases mem_support_factorization_iff.mp ha with ⟨_, ppA, pdiva⟩
      rcases mem_support_factorization_iff.mp hb with ⟨_, _ppB, pdivb⟩
      have pd : p ∣ Nat.gcd a b := Nat.dvd_gcd pdiva pdivb
      exact mem_support_factorization_iff.mpr ⟨gcd_ne0, ppA, pd⟩
  have hsum :
      (rad a).factorization + (rad b).factorization =
        (rad (a * b)).factorization + (rad (Nat.gcd a b)).factorization := by
    ext p
    have A := hA p
    have B := hB p
    have AB := hAB p
    have G := hG p
    by_cases pprime : Nat.Prime p
    · have memA_iff : p ∈ sA ↔ p ∣ a := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨ha_ne, pprime, pd⟩
      have memB_iff : p ∈ sB ↔ p ∣ b := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨hb_ne, pprime, pd⟩
      have memAB_iff : p ∈ sAB ↔ p ∣ a * b := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨mul_ne_zero ha_ne hb_ne, pprime, pd⟩
      have memG_iff : p ∈ sG ↔ p ∣ Nat.gcd a b := by
        constructor
        · intro h; rcases mem_support_factorization_iff.mp h with ⟨_, _, pd⟩; exact pd
        · intro pd; exact mem_support_factorization_iff.mpr ⟨gcd_ne0, pprime, pd⟩
      rw [Finsupp.add_apply, Finsupp.add_apply, A, B, AB, G]
      simp only [memA_iff, memB_iff, memAB_iff, memG_iff]
      by_cases pa : p ∣ a
      · by_cases pb : p ∣ b
        · have pab := dvd_mul_of_dvd_left pa b
          have pg := Nat.dvd_gcd pa pb
          simp [pa, pb, pab, pg]
        · have pab := dvd_mul_of_dvd_left pa b
          have pg : ¬ p ∣ Nat.gcd a b := by
            rw [Nat.dvd_gcd_iff]
            intro h
            exact pb h.right
          simp [pa, pb, pab, pg]
      · by_cases pb : p ∣ b
        · have pab := dvd_mul_of_dvd_right pb a
          have pg : ¬ p ∣ Nat.gcd a b := by
            rw [Nat.dvd_gcd_iff]
            intro h
            exact pa h.left
          simp [pa, pb, pab, pg]
        · have pab : ¬ p ∣ a * b := by
            intro h
            rw [Nat.Prime.dvd_mul pprime] at h
            cases h with
            | inl ha => exact pa ha
            | inr hb => exact pb hb
          have pg : ¬ p ∣ Nat.gcd a b := by
            rw [Nat.dvd_gcd_iff]
            intro h
            exact pa h.left
          simp [pa, pb, pab, pg]
    · have nA : ¬ p ∈ sA := by
        intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      have nB : ¬ p ∈ sB := by
        intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      have nAB : ¬ p ∈ sAB := by
        intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      have nG : ¬ p ∈ sG := by
        intro h; rcases mem_support_factorization_iff.mp h with ⟨_, pp, _⟩; exact pprime pp
      simp [A, B, AB, G, nA, nB, nAB, nG]
  have rad_a_pos : 0 < rad a := by
    have : ∀ p ∈ sA, 0 < p := fun p hp =>
      Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have rad_b_pos : 0 < rad b := by
    have : ∀ p ∈ sB, 0 < p := fun p hp =>
      Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have rad_ab_pos : 0 < rad (a * b) := by
    have : ∀ p ∈ sAB, 0 < p := fun p hp =>
      Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have rad_g_pos : 0 < rad (Nat.gcd a b) := by
    have : ∀ p ∈ sG, 0 < p := fun p hp =>
      Nat.pos_of_ne_zero (Nat.Prime.ne_zero ((mem_support_factorization_iff.mp hp).2.1))
    exact Finset.prod_pos this
  have Lfac :=
    Nat.factorization_mul (Nat.pos_iff_ne_zero.mp rad_a_pos) (Nat.pos_iff_ne_zero.mp rad_b_pos)
  have Rfac :=
    Nat.factorization_mul (Nat.pos_iff_ne_zero.mp rad_ab_pos) (Nat.pos_iff_ne_zero.mp rad_g_pos)
  have fac_eq : (rad a * rad b).factorization
    = (rad (a * b) * rad (Nat.gcd a b)).factorization := by
    calc
      (rad a * rad b).factorization = (rad a).factorization + (rad b).factorization := Lfac
      _ = (rad (a * b)).factorization + (rad (Nat.gcd a b)).factorization := by simpa using hsum
      _ = (rad (a * b) * rad (Nat.gcd a b)).factorization := Rfac.symm
  have lhs_prod :=
    Nat.prod_factorization_pow_eq_self (Nat.pos_iff_ne_zero.mp (Nat.mul_pos rad_a_pos rad_b_pos))
  have rhs_prod :=
    Nat.prod_factorization_pow_eq_self (Nat.pos_iff_ne_zero.mp (Nat.mul_pos rad_ab_pos rad_g_pos))
  have final_eq : rad a * rad b = rad (a * b) * rad (Nat.gcd a b) := by
    calc
      rad a * rad b =
          (rad a * rad b).factorization.support.prod
            (fun p => p ^ ((rad a * rad b).factorization p)) := lhs_prod.symm
      _ =
          (rad (a * b) * rad (Nat.gcd a b)).factorization.support.prod
            (fun p => p ^ ((rad (a * b) * rad (Nat.gcd a b)).factorization p)) := by
            rw [fac_eq]
      _ = rad (a * b) * rad (Nat.gcd a b) := rhs_prod
  exact
    (Nat.div_eq_of_eq_mul_left rad_g_pos (by simpa [mul_comm] using final_eq)).symm

/-- 互いに素な場合の完全乗法性。既存名との互換用。 -/
@[simp]
lemma rad_mul_coprime' {a b : ℕ} (h : Nat.Coprime a b) :
    rad (a * b) = rad a * rad b := by
  simpa using rad_mul_coprime h

/-- `n ≠ 0` ならば `1 ≤ rad n`。 -/
@[simp]
lemma abc_one_le_rad {n : ℕ} (hn : n ≠ 0) : 1 ≤ rad n := by
  by_cases h1 : n = 1
  · subst h1
    simp
  · have hne1 : n ≠ 1 := h1
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hne1
    have hmem : p ∈ n.factorization.support := by
      rw [mem_support_factorization_iff]
      exact ⟨hn, hp_prime, hp_dvd⟩
    have hpd : p ∣ rad n := Finset.dvd_prod_of_mem (fun q => q) hmem
    have rad_pos_n : 0 < rad n := by
      apply Finset.prod_pos
      intro q hq
      rcases mem_support_factorization_iff.mp hq with ⟨_, hq_prime, _⟩
      exact Nat.pos_of_ne_zero (Nat.Prime.ne_zero hq_prime)
    have h1p : 1 ≤ p := Nat.Prime.one_le hp_prime
    exact Nat.le_trans h1p (Nat.le_of_dvd rad_pos_n hpd)

/-- `n > 0` ならば `rad n > 0`。 -/
@[simp]
lemma rad_pos {n : ℕ} (hn : 0 < n) : 0 < rad n := by
  have : 1 ≤ rad n := abc_one_le_rad (Nat.ne_of_gt hn)
  exact Nat.zero_lt_one.trans_le this

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
