import DkMath.Basic
import DkMath.ABC.Rad

#print "file: DkMath.Basic.Nat"

set_option linter.style.longLine false

namespace DkMath.Basic.Nat

open DkMath.ABC.Rad

/- ============================================================================
     1. gcd / coprimality lemmas
   ============================================================================ -/

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
  -- dvd_sub は「a ∣ b → a ∣ c → a ∣ b - c」なので命題型を渡す
  have : Nat.gcd n (n+1) ∣ 1 := by
    rw [succ_sub_self n] at h
    exact h
  exact (dvd_one_iff (Nat.gcd n (n+1))).1 this

/-- (n, n + 1) が互いに素であること -/
lemma coprime_succ (n : ℕ) : Nat.Coprime n (n+1) := by
  -- follows from gcd_succ
  rw [Nat.coprime_iff_gcd_eq_one]
  exact gcd_succ n

/-- n > 1 のとき、0 と n は互いに素でない -/
lemma not_isCoprime_zero_nonzero {n : ℕ} (hn : 1 < n) : ¬ IsCoprime 0 n := by
  -- If n > 1, there are no a,b with a*0 + b*n = 1.
  intro hcop
  rcases hcop with ⟨u, v, h_be_z_out⟩
  -- u * 0 + v * n = 1 so v * n = 1
  have hvn : v * n = 1 := by
    rw [mul_zero, zero_add] at h_be_z_out
    exact h_be_z_out
  -- From v * n = 1 we get n ∣ 1, hence n = 1, contradicting 1 < n
  have hdvd : n ∣ 1 := by
    use v
    rw [mul_comm] at hvn
    exact hvn.symm
  -- from 1 ≤ n and n = 1 we get a contradiction with 1 ≤ n when originally assuming strict >1
  have hn1 : n = 1 := Nat.eq_one_of_dvd_one hdvd
  rw [hn1] at hn
  linarith

/-- n > 1 のとき、n と 0 は互いに素でない(対称性) -/
abbrev not_isCoprime_nonzero_zero {n : ℕ} (hn : 1 < n) := not_isCoprime_zero_nonzero hn

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

-- 互いに素なら、factorization の support は交わらない
/--
`a`と`b`が互いに素（`Nat.Coprime a b`）であるとき、
`a`の素因数分解のサポート（`a.factorization.support`）と
`b`の素因数分解のサポート（`b.factorization.support`）は
互いに素（`Disjoint`）であることを示す補題。

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
`support_mul_coprime` は、互いに素な自然数 `a` と `b` に対して、
`(a * b)` の素因数分解のサポート（現れる素数の集合）は `a` のサポートと `b` のサポートの和集合になることを示す補題です。

数学的には、`gcd(a, b) = 1` のとき、
`supp(factorization(a * b)) = supp(factorization(a)) ∪ supp(factorization(b))` が成り立ちます。
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
  have hfac : (a*b).factorization =
    a.factorization + b.factorization := Nat.factorization_mul ha0 hb0
  -- 両辺を点ごとに比較する
  rw [hfac]
  ext p
  -- (a.factorization p + b.factorization p ≠ 0) ↔ (a.factorization p ≠ 0 ∨ b.factorization p ≠ 0) をまず示す
  have add_iff :
    (a.factorization p + b.factorization p ≠ 0) ↔ (a.factorization p ≠ 0 ∨ b.factorization p ≠ 0) := by
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
    · -- (←) どちらかが非零なら和は非零（Nat.add_eq_zero によりその否定を示す）
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


end DkMath.Basic.Nat
