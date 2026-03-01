/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Basic

#print "file: DkMath.ABC.Core"

set_option linter.style.longLine false
set_option linter.style.emptyLine false
set_option linter.style.whitespace false

/-
  RpowExtras.lean
  小さな補題群：Real.rpow に関する nat 乗換えと分母正性補題
  目的：ABCMiddle の幾何和変形を安定化する
-/

namespace RpowExtras

open Real

/-- x > 0 かつ任意の k : ℕ に対して x^{a * k} = (x^a)^k となる補題。 -/
lemma rpow_mul_nat {x a : ℝ} (hx : 0 < x) :
  ∀ k : ℕ, Real.rpow x (a * (k : ℝ)) = (Real.rpow x a) ^ k := by
  intro k; induction k with
  | zero => simp only [CharP.cast_eq_zero, mul_zero, rpow_eq_pow, rpow_zero, pow_zero]
  | succ k ih =>
      have : a * ((k + 1 : ℕ) : ℝ) = a * (k : ℝ) + a := by
        simp [mul_add, Nat.cast_add, Nat.cast_one]
      calc
        Real.rpow x (a * ((k + 1 : ℕ) : ℝ)) = Real.rpow x (a * (k : ℝ) + a) := by rw [this]
        _ = Real.rpow x (a * (k : ℝ)) * Real.rpow x a := by simp [Real.rpow_add hx]
        _ = (Real.rpow x a) ^ (k + 1) := by
          rw [ih]
          rw [pow_succ]

/-- 2^(α+ε) > 1 when α+ε > 0 (helper) -/
lemma one_lt_rpow_two {a : ℝ} (h : 0 < a) : 1 < (2 : ℝ) ^ a := by
  have : (1 : ℝ) < 2 := by norm_num
  exact Real.one_lt_rpow this (by exact_mod_cast h)

/-- (2^a - 1) > 0 when a > 0 -/
lemma denom_pos {a : ℝ} (h : 0 < a) : 0 < (2 : ℝ) ^ a - 1 := by
  have h1 := one_lt_rpow_two (a:=a) h
  linarith

end RpowExtras

-- ------------------------------------------------------------------------------------------------------------------------------------

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- Auxiliary lemma: 3^(X+1) ≥ 2X+1 for all X (帰納法で証明)
lemma three_pow_ge_linear (X : ℕ) : 3 ^ (X + 1) ≥ 2 * X + 1 := by
  induction X with
  | zero =>
      norm_num
  | succ n ih =>
      -- 3^(n+2) = 3 * 3^(n+1) ≥ 3 * (2n+1) = 6n+3 ≥ 2(n+1)+1
      have : (3 : ℕ) ^ (n + 2) = 3 * 3 ^ (n + 1) := by
        rw [Nat.pow_succ]; ring
      calc
        3 ^ (n + 2)
            = 3 * 3 ^ (n + 1) := this
        _ ≥ 3 * (2 * n + 1) := Nat.mul_le_mul_left _ ih
        _ = 6 * n + 3 := by ring
        _ ≥ 2 * (n + 1) + 1 := by omega

-- 補助補題：v_p(n) の分解
lemma padicValNat_split (p n : ℕ) :
    padicValNat p n = min (padicValNat p n) 1 + max (padicValNat p n - 1) 0 := by
  by_cases h : padicValNat p n = 0
  · simp [h]
  · by_cases h1 : padicValNat p n = 1
    · simp [h1]
    · have : padicValNat p n ≥ 2 := by omega
      have : min (padicValNat p n) 1 = 1 := by omega
      have : max (padicValNat p n - 1) 0 = padicValNat p n - 1 := by omega
      omega

/- ============================================================================
     0. Basic helpers & notations
   ============================================================================ -/

-- NOTE: the two definitions below currently have no references (2025/09/07)

/-- squarefull: 任意の素因子 p に対して p^2 ∣ n が成り立つこと -/
def squarefull' (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p^2 ∣ n

/-- squarefree（mathlib の標準定義を本ファイルに鏡像として置く） -/
-- alias to Mathlib's predicate
def squarefree_prop (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ¬ (p^2 ∣ n)

/- ============================================================================
     1. gcd / coprimality lemmas
   ============================================================================ -/

-- ※以下４つはここだけ 2025/09/07  3:37
/-- (n + 1) - n = 1 であること -/
def succ_sub_self (n : ℕ) : (n + 1) - n = 1 := by
  rw [Nat.add_comm, Nat.add_sub_cancel]

/-- n ∣ 1 ↔ n = 1 であること -/
def dvd_one_iff (n : ℕ) : n ∣ 1 ↔ n = 1 := by
  constructor
  · rintro h
    exact Nat.eq_one_of_dvd_one h
  · rintro rfl
    exact ⟨1, rfl⟩

/-- (n, n + 1) が互いに素であること -/
lemma gcd_succ (n : ℕ) : Nat.gcd n (n+1) = 1 := by
  -- standard: gcd n (n+1) = 1
  have h := Nat.dvd_sub (Nat.gcd_dvd_right n (n+1)) (Nat.gcd_dvd_left n (n+1))
  have : Nat.gcd n (n+1) ∣ 1 := by
    rw [succ_sub_self] at h
    exact h
  exact (dvd_one_iff (Nat.gcd n (n+1))).1 this

/-- (n, n + 1) が互いに素であること -/
lemma coprime_succ (n : ℕ) : Nat.Coprime n (n+1) := by
  -- follows from gcd_succ
  rw [Nat.coprime_iff_gcd_eq_one]
  exact gcd_succ n

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
@[simp] lemma rad_one  : rad 1 = 1 := by rw [rad_one']

/- 小さな補題群の整理：rad に関する再利用可能補題 -/

/-`rad n ∣ n` を切り出しておくと再利用が楽になる（n ≠ 0 の場合）。-/
/--
`rad_dvd_nonzero` は、任意の自然数 `n` が 0 でないとき、その数の radical（`rad n`、すなわち `n` の素因数の積）が `n` を割り切ることを示す補題です。

radical `rad n` は、`n` の素因数全体の積として定義されます。
この補題の証明では、まず `n` の素因数分解を利用して `n = ∏_{p∈s} p^(f p)` という形に書き換えます（ここで `s` は `n` の素因数の集合、`f p` は素因数 `p` の指数）。
各素因数 `p` について、`p` は `p^(f p)` を割り切ることから、素因数全体の積（radical）は `n` を割り切ることが分かります。

この補題は、整数論において radical の基本的な性質を述べており、例えば square-free な数や、radical を用いた他の性質の証明の基礎となります。
-/
lemma rad_dvd_nonzero (n : ℕ) (hn : n ≠ 0) : rad n ∣ n := by
  classical
  unfold rad
  let f := n.factorization
  let s := f.support
  -- n = ∏_{p∈s} p^(f p)
  have hfac : n = s.prod (fun p => p ^ f p) := Eq.symm (Nat.factorization_prod_pow_eq_self hn)
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

-- support に素数 p が現れることと「p ∣ n」の同値（片側には素数性が要る）
/--
`p ∈ n.factorization.support ↔ (n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n)` という補題です。

この補題は、自然数 `n` の素因数分解（`factorization`）のサポート（非ゼロの指数を持つ素数の集合）に素数 `p` が含まれることと、
`n` が 0 でなく、`p` が素数であり、かつ `p` が `n` を割り切ることが同値であることを示します。

この性質は、素因数分解のサポート集合の特徴付けや、整数の素因数に関する議論で有用です。
-/
lemma mem_support_factorization_iff {n p : ℕ} :
  p ∈ n.factorization.support ↔ (n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n) := by
  classical
  -- 既存の事実：`p ∈ n.factors ↔ p.Prime ∧ p ∣ n`
  -- と `n.factorization.support = n.factors.toFinset` を使うのが一番楽。
  -- 見つからなければ下の 2 行で代替：
  --   * 「→」: support とは係数 ≠ 0。`n = ∏ p p^(factorization n p)` から `p ∣ n`
  --   * 「←」: p|n かつ p prime → 係数 > 0（素因子分解の一意性）
  -- ここでは simp ラインで通す：
  have hsup : n.factorization.support = Nat.primeFactors n := by rfl
  constructor <;> intro h
  · -- →: support にいる ⇒ primeFactors.toFinset にいる ⇒ list にもいる
    have hpf : p ∈ Nat.primeFactors n := by
      simpa [hsup] using h
    -- primeFactors の定義より
    rw [Nat.mem_primeFactors] at hpf
    exact ⟨hpf.2.2, hpf.1, hpf.2.1⟩
  · -- ←: p が素数で n を割る ⇒ primeFactors の list に入る ⇒ support にいる
    rcases h with ⟨hn, hp, hpd⟩
    -- primeFactors の定義は「p.Prime ∧ p ∣ n ∧ n ≠ 0」
    have hpf : p ∈ Nat.primeFactors n := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpd, hn⟩
    have : p ∈ n.factorization.support := by
      simpa [hsup] using hpf
    exact this

/--
`support_prod_log_eq_sum_log` は、自然数 `n` の素因数分解に現れる素因数の集合（`Nat.factorization n` の `support`）に対して、
それらの素因数の積の自然対数が、各素因数の自然対数の総和に等しいことを示す定理です。

すなわち、
$\log\left(\prod_{p \in \operatorname{supp}(\mathrm{factorization}(n))} p\right) = \sum_{p \in \operatorname{supp}(\mathrm{factorization}(n))} \log p$
が成り立つことを証明します。

この性質は、対数の積に関する基本的な性質 $\log(\prod_i a_i) = \sum_i \log a_i$ に基づいています。
-/
theorem support_prod_log_eq_sum_log (n : ℕ) :
    Real.log ((Nat.factorization n).support.prod fun p => (p : ℝ))
      = ∑ p ∈ (Nat.factorization n |>.support), Real.log (p : ℝ) := by
  have h_nz : ∀ p ∈ (Nat.factorization n).support, (p : ℝ) ≠ 0 := by
    intro p hp
    have h := (mem_support_factorization_iff.mp hp)
    -- h : n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n
    rcases h with ⟨hnz, hprime, hpd⟩
    exact_mod_cast Nat.Prime.ne_zero hprime
  -- use `Real.log_prod` with named implicit parameters to avoid argument order issues
  simpa using
    (Real.log_prod
      (α := ℕ)
      (s := (Nat.factorization n).support)
      (f := fun p : ℕ => (p : ℝ))
      h_nz)

/--
与えられた自然数 `n` に対して、その素因数分解のサポート（現れる素数の集合）の元 `p` について、
サポート上の素数の総積の対数は、各素数の対数の総和以上であることを示す補題です。

具体的には、`Nat.factorization n` で `n` の素因数分解を取得し、そのサポート（現れる素数の集合）上で
素数の積を取り、その対数を計算します。一方、サポート上の各素数の対数の総和も計算します。
この補題は、前者が後者以上であること、すなわち
`log(Π p∈S, p) ≥ Σ p∈S, log p`
が成り立つことを主張しています。

この不等式は、対数関数の性質（積の対数は対数の和）と、サポート集合の性質に基づいています。
-/
lemma support_prod_log_ge_sum_log (n : ℕ) :
    Real.log ((Nat.factorization n).support.prod fun p => (p : ℝ))
      ≥ ∑ p ∈ (Nat.factorization n |>.support), Real.log (p : ℝ) := by
  have h := support_prod_log_eq_sum_log n
  exact le_of_eq (Eq.symm h)

-- lemma about the radical of a number and prime factorization
theorem rad_prod (n : ℕ) (_hn : n ≥ 2) :
    rad n = ∏ p ∈ (Nat.factorization n |>.support), p := by
  -- rad is defined as the product over the factorization support
  simp only [rad, Nat.support_factorization]

-- lemma about the radical of a number and prime logarithms
theorem rad_log_eq_sum_prime_logs (n : ℕ) (_hn : n ≥ 2) :
    Real.log (rad n) = ∑ p ∈ (Nat.factorization n |>.support), Real.log p := by
  -- cast the product to ℝ so the types match Real.log_prod's expectation
  have hprod : (rad n : ℝ) = (Nat.factorization n).support.prod fun p => (p : ℝ) := by
    -- use norm_cast together with the definitional equation of rad
    simp only [rad, Nat.support_factorization, Nat.cast_prod]
  rw [hprod]
  have h_nz : ∀ p ∈ (Nat.factorization n).support, (p : ℝ) ≠ 0 := by
    intro p hp
    rcases (mem_support_factorization_iff.mp hp) with ⟨_, hprime, _⟩
    exact_mod_cast Nat.Prime.ne_zero hprime
  exact Real.log_prod
      (α := ℕ)
      (s := (Nat.factorization n).support)
      (f := fun p : ℕ => (p : ℝ))
      h_nz

-- lemma about the radical of a number and prime logarithms (greater than or equal)
lemma rad_log_ge_sum_prime_logs (n : ℕ) (hn : n ≥ 2) :
    Real.log (rad n) ≥ ∑ p ∈ (Nat.factorization n |>.support), Real.log p := by
  have h := rad_log_eq_sum_prime_logs n hn
  exact le_of_eq (Eq.symm h)


-- 互いに素なら、factorization の support は交わらない
/--
`a`と`b`が互いに素（`Nat.Coprime a b`）であるとき、`a`の素因数分解のサポート（`a.factorization.support`）と`b`の素因数分解のサポート（`b.factorization.support`）は互いに素（`Disjoint`）であることを示す補題。

すなわち、`a`と`b`が共通の素因数を持たないことを形式的に述べている。
-/
lemma disjoint_support_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
  Disjoint a.factorization.support b.factorization.support := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro p hpA hpB
  -- p が両方の support にいる ⇒ p は素で a も b も割る
  have ⟨_, pp, p_div_a⟩ := (mem_support_factorization_iff.mp hpA)
  have ⟨_, _, p_div_b⟩ := (mem_support_factorization_iff.mp hpB)
  -- すると gcd(a,b) に p が割り込むので矛盾
  have hgd := Nat.dvd_gcd p_div_a p_div_b
  -- gcd a b = 1 を h から書き換えて p ∣ 1 となり、素数 p は 1 を割らない
  rw [h] at hgd
  exact pp.not_dvd_one hgd

-- 互いに素なら support は単純に「和集合」になる（ℕ 係数なので 0 の相殺が起きない）
/--
`support_mul_coprime` は、互いに素な自然数 `a` と `b` に対して、`(a * b)` の素因数分解のサポート（現れる素数の集合）は `a` のサポートと `b` のサポートの和集合になることを示す補題です。

数学的には、`gcd(a, b) = 1` のとき、`supp(factorization(a * b)) = supp(factorization(a)) ∪ supp(factorization(b))` が成り立ちます。
-/
lemma support_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
  (a*b).factorization.support = a.factorization.support ∪ b.factorization.support := by
  classical
  -- 0 の場合を分岐しておく（Nat.factorization_mul は両方非零を仮定する）
  by_cases ha0 : a = 0
  · subst ha0
    -- Coprime 0 b ならば b = 1
    have hb1 : b = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_left] at h
      exact h
    subst hb1
    simp
  by_cases hb0 : b = 0
  · subst hb0
    -- Coprime a 0 ならば a = 1
    have ha1 : a = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_right] at h
      exact h
    subst ha1
    simp
  -- 両方非零なので factorization_mul を使える
  -- factorization の加法
  have hfac : (a*b).factorization = a.factorization + b.factorization := Nat.factorization_mul ha0 hb0
  -- 両辺を点ごとに比較する
  rw [hfac]
  ext p
  -- (a.factorization p + b.factorization p ≠ 0) ↔ (a.factorization p ≠ 0 ∨ b.factorization p ≠ 0) をまず示す
  have add_iff : (a.factorization p + b.factorization p ≠ 0) ↔ (a.factorization p ≠ 0 ∨ b.factorization p ≠ 0) := by
    constructor
    · -- (→) 和が非零なら少なくとも一方は非零
      intro hsum
      by_cases ha' : a.factorization p = 0
      · -- a の係数が 0 なら、b の係数は 0 であってはならない
        have hb_non : b.factorization p ≠ 0 := by
          by_contra hb0
          simp [ha', hb0] at hsum
        right; exact hb_non
      · left; exact ha'
    · -- (←) どちらかが非零なら和は非零（Nat.add_eq_zero_iff によりその否定を示す）
      intro h
      rcases h with (ha_non | hb_non)
      · -- a の係数が非零なら和は非零
        by_contra hsum
        have h0 := (Nat.add_eq_zero_iff.mp hsum).1
        exact ha_non h0
      · -- b の係数が非零なら和は非零
        by_contra hsum
        have h0 := (Nat.add_eq_zero_iff.mp hsum).2
        exact hb_non h0
  -- 最後に Finsupp.mem_support_iff と Finset.mem_union を使って support の形に戻す
  have : p ∈ (a.factorization + b.factorization).support ↔ p ∈ a.factorization.support ∪ b.factorization.support := by
    -- Finsupp.mem_support_iff により「p ∈ support ↔ f p ≠ 0」へ書き換え、
    -- Finset.mem_union により和集合のメンバシップは論理和へ書き換え、
    -- それらを一度に simp で解くのじゃ。
    -- 左辺と右辺の両方の "p ∈ ...support" を Finsupp.mem_support_iff で展開してから簡約する
    rw [Finsupp.mem_support_iff, Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    simp [add_iff]
  exact this

/-- [★] 互いに素での乗法性 rad(ab) = rad(a) * rad(b) -/
lemma rad_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
  rad (a*b) = rad a * rad b := by
  classical
  unfold rad
  -- Nat.factorization_mul は両方非零を仮定するので、0 の場合を分岐して扱う
  by_cases ha0 : a = 0
  · subst ha0
    -- Coprime 0 b ならば b = 1
    have hb1 : b = 1 := by
      -- Coprime を gcd = 1 に書き換えてから gcd_zero_left を適用する
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_left] at h
      exact h
    subst hb1
    simp
  by_cases hb0 : b = 0
  · subst hb0
    -- Coprime a 0 ならば a = 1
    have ha1 : a = 1 := by
      rw [Nat.coprime_iff_gcd_eq_one] at h
      rw [Nat.gcd_zero_right] at h
      exact h
    subst ha1
    simp
  -- 両方非零なので factorization_mul を使える
  have hfac : (a*b).factorization = a.factorization + b.factorization :=
    Nat.factorization_mul ha0 hb0
  have hsup := support_mul_coprime (a:=a) (b:=b) h
  have hdis := disjoint_support_of_coprime (a:=a) (b:=b) h
  -- ∪ の積は、disjoint なら prod_union が使える
  -- まず support の和集合に書き換え、その後 Finset.prod_union を適用する
  rw [hsup]
  apply Finset.prod_union hdis

/-- 単調界：rad n ≤ n (n ≠ 0 の場合) -/
lemma rad_le {n : ℕ} (hn : n ≠ 0) : rad n ≤ n := by
  classical
  unfold rad
  let f := n.factorization
  let s := f.support
  -- 素因数分解の積表示: n = ∏ p ∈ s, p ^ (f p)
  have hfac : n = s.prod (fun p => p ^ f p) := by
    exact Eq.symm (Nat.factorization_prod_pow_eq_self hn)
  -- 各 p ∈ s について p ∣ p ^ (f p) が成り立つため，積に関しても成り立つ
  have hdiv : s.prod (fun p : ℕ => p) ∣ s.prod (fun p => p ^ f p) := by
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    -- サポート上の指数は非ゼロなので累乗に p は現れる
    have hf : f p ≠ 0 := by
      rw [Finsupp.mem_support_iff] at hp
      exact hp
    -- p ∣ p ^ (f p)
    exact dvd_pow_self p hf
  -- よって rad n (= s.prod (λ p, p)) は n を割る
  have hrad_dvd_n : s.prod (fun p => p) ∣ n := by
    rw [hfac]
    exact hdiv
  -- 割り切ることから rad n ≤ n を得る
  rcases hrad_dvd_n with ⟨k, hk⟩
  have hk_pos : 0 < k := by
    -- n ≠ 0 かつ n = rad n * k なので k > 0
    have : 0 < n := Nat.pos_of_ne_zero hn
    rw [hk] at this
    exact Nat.pos_of_mul_pos_left this
  -- n = rad n * k かつ k > 0 より rad n ≤ n
  have hn_eq : n = s.prod (fun p => p) * k := hk
  have hrad_le_n : s.prod (fun p => p) ≤ n := by
    rw [hn_eq]
    exact Nat.le_mul_of_pos_right _ hk_pos
  exact hrad_le_n

/- ============================================================================
     3. squarefree / squarefull controls
   ============================================================================ -/


/-- mathlib 標準を ℕ にエイリアス（再利用を最大化） -/
/-
An element of a monoid is squarefree if the only squares that
divide it are the squares of units.

def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x
-/
-- #check Squarefree -- mathlib の定義を確認
-- Squarefree.{u_1} {R : Type u_1} [Monoid R] (r : R) : Prop
abbrev squarefree (n : ℕ) : Prop := Squarefree n

/-- squarefull: すべての素因子が指数 ≥ 2 -/
def squarefull (n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → p^2 ∣ n

-- #eval squarefree 6  -- true
-- #eval squarefree 9  -- false
-- #eval squarefree 12 -- false
-- #eval squarefree 30 -- true

end ABC

-- ------------------------------------------------------------------------------------------------------------------------------------
