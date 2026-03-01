/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC010

#print "file: DkMath.ABC.ABC011"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- -------------------------------------------------------------------------------------------------------------------


-- Finite union (Boole) lemma: measure of finite union ≤ sum of measures
/--
有限集合 K に対する有限和の半加法（和に関する上界）を述べる補題。

仮定として Ω は測度空間であり，μ は確率測度（特に有限測度）である．
このとき，任意の集合列 A : ℕ → Set Ω に対して
K に含まれる全ての k についての合併の測度は，各 k に対する測度の和以下である：
μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, μ.real (A k)。
直感的には有限個の集合に対して成り立つ「和の上界」あるいは有限半加性を表している．

証明は Finset に関する帰納法や，測度の単調性と有限可加性／半加法性を使って行うことができる．
また，もし A k が互いに素（互いに交わらない）であれば，上式は等号となる（有限可加性）．
-/
lemma measure_union_over_k
  {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (K : Finset ℕ) (A : ℕ → Set Ω) :
  μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, μ.real (A k) := by
  -- Use the existing mathlib lemma which proves the same statement for finite biUnion
  exact MeasureTheory.measureReal_biUnion_finset_le K A


-- If we have an upper bound B k for each μ.real (A k) on k ∈ K, then the
-- measure of the finite union is bounded by the sum of those upper bounds.
/--
有限なインデックス集合 K にわたる集合族 A の合併の測度は、
各集合の測度に対する上界 B の和で抑えられることを主張する補題の説明。

概要：
- 仮定 h により各 k ∈ K について μ.real (A k) ≤ B k が成り立つ。
- 測度は有限合併に対して部分加法（subadditivity）を満たすので
  μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, μ.real (A k) が成り立つ。
- これに仮定 h を適用して各項を B k で上界すれば、
  μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, B k となる。

備考：
- 仮定 [IsProbabilityMeasure μ] は文脈上用意されているが、
  本補題の結論自体は測度の部分加法性のみから導ける。
- K が有限であることにより有限和を扱える点が重要である。
- 記法として μ.real は実数値に変換した測度を表す。
-/
lemma measure_union_over_k_bound
  {Ω} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  (K : Finset ℕ) (A : ℕ → Set Ω) (B : ℕ → ℝ)
  (h : ∀ k ∈ K, μ.real (A k) ≤ B k) :
  μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, B k := by
  calc
    μ.real (⋃ k ∈ K, A k) ≤ ∑ k ∈ K, μ.real (A k) := MeasureTheory.measureReal_biUnion_finset_le K A
    _ ≤ ∑ k ∈ K, B k := Finset.sum_le_sum (fun k hk => h k hk)


-- 補助: C * exp(-c * 2^k) の可和性（c>0, C≥0）
/--
C ≥ 0 かつ c > 0 のとき、列 k ↦ C * Real.exp (- c * (2 : ℝ) ^ k) は総和可能（Summable）であることを主張する補題。

説明（概略）:
Real.exp (- c * 2^k) = (Real.exp (-c))^(2^k) であり、0 < Real.exp (-c) < 1 であるため,
この項は k に対して超指数的に減衰する。従って適当な 0 < r < 1, A > 0 が存在して
Real.exp (- c * 2^k) ≤ A * r^k と評価でき、幾何級数との比較により総和可能となる。
C ≥ 0 を掛けても総和可能性は保たれる。
-/
lemma summable_exp_neg_two_pow_mul {C c : ℝ} (_hC : 0 ≤ C) (hc : 0 < c) :
  Summable (fun k : ℕ => C * Real.exp (- c * ((2 : ℝ) ^ k))) := by
  -- use the summability proved in MathlibHello.ABC (Prob.summable_exp_neg_two_pow) and multiply by C
  have hsum := Prob.summable_exp_neg_two_pow c hc
  exact Summable.mul_left C hsum


/- Independent-version constants and absorption lemmas -/


/- 中域・独立版の合併確率を吸収する X 非依存定数（C⋆₍indep₎）。 -/
/--
δ : ℝ に対して次を返す非計算的な実数値関数。

midblockCstarIndep δ = 3 + ∑' (k : ℕ), Real.exp (-(δ^2) * 2^k)

説明と基本的性質（直感的説明）:
- 定義は 3 に、指数関数 exp(−(δ^2) 2^k) の k に関する無限和を加えたものです。
- 式は δ^2 にのみ依存するため偶関数です（δ と −δ で同じ値を取ります）。
- |δ| が大きくなると各項は急速に 0 に近づくので、関数値は単調に小さくなり（δ^2 に対して単調）、δ → ∞ のとき 3 に収束します。
- δ = 0 のとき各項が 1 になるため和は発散します（∑ 1 = ∞）。したがって収束を考える際は一般に δ ≠ 0 を想定します。
- δ ≠ 0 の場合は 2^k による二重的な増加により項が超指数的に減少し、和は非常に速く収束します。

実装上の注意:
- 無限和を含むため noncomputable として定義されています。
- 必要に応じて δ ≠ 0 の下での収束性・連続性・単調性などを補題として形式化できます。
- この関数は解析的な見地からは |δ| に対して滑らかであり、特に δ ≠ 0 の領域で良質な性質を持ちます。
- 記法上の ∑' は tsum（可測な無限和）を表します。
-/
noncomputable def midblockCstarIndep (δ : ℝ) : ℝ :=
  (3 : ℝ) + (∑' k : ℕ, Real.exp (-(δ ^ 2) * (2 : ℝ) ^ k))

-- Simple helper: probability-measure の下で任意事象の実数化測度は ≤ 1.
/--
確率測度 μ に対する基本的な評価補題。

任意の可測集合 A に対して μ.real A ≤ 1 が成り立つ。
これは IsProbabilityMeasure の仮定により μ.real univ = 1 であり、
集合 A が univ の部分集合であることと測度の単調性から直ちに従う。

引数:
- `μ` : `Measure Ω` で `IsProbabilityMeasure μ` を満たす確率測度
- `A` : 可測集合

結論: `μ.real A ≤ 1`
-/
lemma prob_real_le_one {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (A : Set Ω) : μ.real A ≤ 1 := by
  have hle := MeasureTheory.measure_mono (μ := μ) (Set.subset_univ A)
  have htop : μ (Set.univ : Set Ω) ≠ ⊤ := by simp [IsProbabilityMeasure.measure_univ]
  have : (μ A).toReal ≤ (μ (Set.univ : Set Ω)).toReal := ENNReal.toReal_mono htop hle
  calc
    μ.real A = (μ A).toReal := rfl
    _ ≤ (μ (Set.univ : Set Ω)).toReal := this
    _ = 1 := by simp [IsProbabilityMeasure.measure_univ]


/- Slice の和恒等式と Markov による重いスライスの個数上界 -/
/--
δ : ℝ, X : ℕ を固定するとき、各スライス b ∈ Finset.range (X+1) における `sliceBadCount δ X b`
（自然数へキャストしたもの）の総和は、全体の `BadCount δ X`（自然数へキャストしたもの）を越えない、という不等式を主張する補助補題。

直観的には、"bad" と見なされる要素は各スライスに対して重複なく（少なくとも一度以上には）数えられるため、各スライスの個別の不良数の和が全体の不良数を上回ることはない、ということを表す。
Finset.range (X+1) は 0,1,…,X を走査するので、スライスインデックスの全体を加算している点に注意する。

証明の方針としては、各要素がどのスライスに属するかを対応づけることにより、スライスごとのカウントの和が全体カウントに対応する写像の逆像の和で抑えられることを示す。
-/
lemma slice_sum_eq_badcount {δ : ℝ} {X : ℕ} :
  (∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℕ)) ≤ (BadCount δ X : ℕ) := by
  exact slice_sum_le_badcount δ X


/--
与えられた実数 `δ`, `η` と自然数 `X` に対して、`η > 0` かつ `X > 0` のとき、
「重いスライス」（すなわち、`sliceBadCount δ X b` が `η * X` 以上となるような `b` の個数）は、
全体の「BadCount」を `η * X` で割った値以下であることを示す補題。

この補題は、マルコフの不等式の応用例であり、あるしきい値以上となる要素の個数を全体の合計値から上界する際に用いられる。
-/
lemma few_heavy_slices {δ η : ℝ} (hη : 0 < η) (X : ℕ) (hXpos : 0 < (X : ℝ)) :
  ((Finset.filter (fun b => (sliceBadCount δ X b : ℝ) ≥ η * (X : ℝ))
      (Finset.range (X+1))).card : ℝ)
    ≤ (BadCount δ X : ℝ) / (η * (X : ℝ)) := by
  -- フィルタされた有限集合を定める
  let F := Finset.filter (fun b => (sliceBadCount δ X b : ℝ) ≥ η * (X : ℝ)) (Finset.range (X+1))
  -- 各要素について sliceBadCount ≥ η * X である
  have h_each : ∀ b ∈ F, (sliceBadCount δ X b : ℝ) ≥ η * (X : ℝ) := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  -- フィルタ上の和は定数和以上
  have h_sum_ge : (F.card : ℝ) * (η * (X : ℝ)) ≤ ∑ b ∈ F, (sliceBadCount δ X b : ℝ) := by
    calc
      (F.card : ℝ) * (η * (X : ℝ)) = ∑ b ∈ F, (η * (X : ℝ)) := by simp [Finset.sum_const]
      _ ≤ ∑ b ∈ F, (sliceBadCount δ X b : ℝ) := Finset.sum_le_sum (fun b hb => (Finset.mem_filter.mp hb).2)
  -- フィルタ上の和は全体範囲の和以下（非負項なので包含により成立）
  have h_subsum : ∑ b ∈ F, (sliceBadCount δ X b : ℝ) ≤ ∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℝ) := by
    -- 0 ≤ sliceBadCount を実数へキャストして与える
    have h_subset : F ⊆ Finset.range (X+1) := Finset.filter_subset _ _
    have h_nonneg : ∀ b ∈ Finset.range (X+1), 0 ≤ (sliceBadCount δ X b : ℝ) := by
      intro b hb
      exact_mod_cast Nat.zero_le (sliceBadCount δ X b)
    have h_nonneg' :
        ∀ b ∈ Finset.range (X+1), b ∉ F → 0 ≤ (sliceBadCount δ X b : ℝ) := by
      intro b hb _
      exact h_nonneg b hb
    simpa using Finset.sum_le_sum_of_subset_of_nonneg h_subset h_nonneg'
  -- 全体和は BadCount に上界される（自然数の和の不等式を実数に持ち上げる）
  have h_total_le_bad : ∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℝ) ≤ (BadCount δ X : ℝ) := by
    exact_mod_cast slice_sum_eq_badcount
  -- 以上をつなげると (F.card) * (η * X) ≤ BadCount
  have mul_le_bad : (F.card : ℝ) * (η * (X : ℝ)) ≤ (BadCount δ X : ℝ) := by
    calc
      (F.card : ℝ) * (η * (X : ℝ)) ≤ ∑ b ∈ F, (sliceBadCount δ X b : ℝ) := h_sum_ge
      _ ≤ ∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℝ) := h_subsum
      _ ≤ (BadCount δ X : ℝ) := h_total_le_bad
  -- 正の数で割って目的の不等式を得る
  have hpos : 0 < η * (X : ℝ) := mul_pos hη hXpos
  exact
    (le_div_iff₀ hpos).mpr mul_le_bad


/-- log の単調性（実数, 1以上で有効） -/
lemma log_mono_on_Ici : MonotoneOn Real.log (Set.Ici (1:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  exact Real.log_le_log hx0 hxy


/-- rad(0)=1 の説明：空積＝1・factorization 仕様 -/
lemma rad_zero_eq_one : (rad 0 : ℕ) = 1 := by
  -- Mathlib の `Nat.factorization` 仕様と `support.prod` の空積
  -- 既に `#eval rad 0 = 1` だった理由を定理化
  simp only [rad_zero]  -- ぬしの定義ブロックに合せて展開（必要に応じて補助補題を追加）


/-- rad の基本：gcd との相互作用と単調 -/
lemma rad_mul_le (a b : ℕ) :
  rad (a * b) ≤ rad a * rad b := by
  -- mathlib 標準：`rad (ab) = rad a * rad b / rad (gcd a b)` から従う
  -- ぬしの環境では既に `rad(ab)=…` を証明済みなのでそれを利用
  -- 例: `have := rad_mul_eq a b; …` として `Nat.div_le_self` で落とす
  classical
  -- 一般公式
  have h := rad_mul_general a b
  -- 分母を捨てる単調性: (x / d) ≤ x
  have hdiv : (rad a * rad b) / rad (Nat.gcd a b) ≤ rad a * rad b := Nat.div_le_self _ _
  simpa [h] using hdiv


/-- rad の下界：`a ≠ 0 → 1 ≤ rad a` -/
lemma one_le_rad_of_ne_zero {a : ℕ} (ha : a ≠ 0) : 1 ≤ rad a := by
  -- squarefree/素因子 support が空でなければ ≥ 2 だが、0/1 の特例に注意
  -- 既存の `rad_pos_of_two_le` 系があればそれを使う
  -- 既に `abc_one_le_rad` が `a ≠ 0 → 1 ≤ rad a` を与えるのでそれを流用
  simpa using abc_one_le_rad ha


/-- `log (rad N)` の正性（`N≥2` で OK） -/
lemma log_rad_pos_of_two_le {N : ℕ} (hN : 2 ≤ N) :
  0 < Real.log ((rad N : ℕ) : ℝ) := by
  -- 方針: N ≥ 2 ならば素数 p ∣ N があり p ≥ 2, support に入るので p ∣ rad N, よって 2 ≤ rad N, 従って log(rad N) > 0
  have hN_ne0 : N ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hN_ne1 : N ≠ 1 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hN)
  -- 素数 p dividing N
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hN_ne1
  -- p は factorization support に現れる
  have hmem : p ∈ (Nat.factorization N).support := by
    exact (mem_support_factorization_iff).2 ⟨hN_ne0, hp_prime, hp_dvd⟩
  -- p ∣ rad N
  have hp_dvd_rad : p ∣ rad N := by
    dsimp [rad]
    exact Finset.dvd_prod_of_mem (fun q => q) hmem
  -- rad N > 0 （support 上の素数の積なので正）
  have hpos : 0 < rad N := by
    dsimp [rad]
    apply Finset.prod_pos
    intro q hq
    rcases (mem_support_factorization_iff).1 hq with ⟨_, qprime, _⟩
    exact Nat.Prime.pos qprime
  -- 2 ≤ p ≤ rad N
  have h2_le_p : 2 ≤ p := hp_prime.two_le
  have hp_le_rad : p ≤ rad N := Nat.le_of_dvd hpos hp_dvd_rad
  have hrad_ge2 : 2 ≤ rad N := le_trans h2_le_p hp_le_rad
  -- 実数へ持ち上げて log 正
  have hgt1 : (1 : ℝ) < (rad N : ℝ) := by
    have : (2 : ℝ) ≤ (rad N : ℝ) := by exact_mod_cast hrad_ge2
    linarith
  exact Real.log_pos hgt1


/-- `piSqRad n = ∏_{p^2 ∣ n} p` :
    `n` の素因数のうち 2 乗以上で現れる素数だけを拾って掛けたもの。 -/
def piSqRad (n : ℕ) : ℕ :=
  (n.factorization.support.filter fun p => 2 ≤ n.factorization p).prod fun p => p


/-- The set of prime factors with multiplicity at least 2 is a subset of all prime factors. -/
lemma piSqRad_subset (n : ℕ) :
  (n.factorization.support.filter fun p => 2 ≤ n.factorization p) ⊆ n.factorization.support := by
  intro p hp; exact (Finset.filter_subset _ _) hp


/-- `piSqRad n` は `rad n` を割り切る（証明は後で埋める）。 -/
lemma piSqRad_dvd_rad (n : ℕ) : piSqRad n ∣ rad n := by
  dsimp [piSqRad]
  let s := n.factorization.support.filter fun p => 2 ≤ n.factorization p
  have hsubset : s ⊆ n.factorization.support := by intro p hp; exact (Finset.mem_filter.1 hp).1
  exact Finset.prod_dvd_prod_of_subset s n.factorization.support (fun p => p) hsubset


/-- とりあえずの実数上界（後で rad との関係で強化する）。 -/
lemma piSqRad_le_rad (n : ℕ) : (piSqRad n : ℝ) ≤ (rad n : ℝ) := by
  have hdiv := piSqRad_dvd_rad n
  -- show rad n > 0 (empty product yields 1, or each prime factor > 0)
  have hrpos : 0 < rad n := by
    dsimp [rad]
    apply Finset.prod_pos
    intro p hp
    have ⟨hnz, hpprime, hpd⟩ := mem_support_factorization_iff.mp hp
    exact Nat.Prime.pos hpprime
  have hle_nat : piSqRad n ≤ rad n := Nat.le_of_dvd hrpos hdiv
  exact_mod_cast hle_nat


/-- `piSqRad n ≤ n` は `rad n ≤ n` から従う（補題は後で埋める）。 -/
lemma piSqRad_le_self {n : ℕ} (hn0 : n ≠ 0) : (piSqRad n : ℝ) ≤ n := by
  have h1 := piSqRad_le_rad n
  have h2 : (rad n : ℝ) ≤ (n : ℝ) := by exact_mod_cast (rad_le hn0)
  linarith [h1, h2]


-- ===== Strong analytic bridge: preparation lemmas =====


-- rad divides monotonicity helpers
/-- If `m` divides `n` and `n ≠ 0`, then `rad m` divides `rad n`. -/
lemma rad_dvd_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) : rad m ∣ rad n := by
  classical
  -- rad m is product of primes appearing in factorization of m; if m|n every such prime also divides n
  -- so support m ⊆ support n, hence product over subset divides product
  dsimp [rad]
  -- Convert divisibility to factorization inclusion on primes with positive exponent
  -- We use the fact that for a prime p, p ∈ support (factorization m) → p ∈ support (factorization n)
  refine Finset.prod_dvd_prod_of_subset (m.factorization.support) (n.factorization.support) (fun p => p) ?subset
  intro p hp
  -- hp : p in support factorization m ⇒ p prime ∧ p|m; with m|n gives p|n ⇒ p in support factorization n
  rcases mem_support_factorization_iff.mp hp with ⟨hm0, pprime, hp_dvd⟩
  have : p ∣ n := dvd_trans hp_dvd h
  exact mem_support_factorization_iff.mpr ⟨hn, pprime, this⟩


/-- If `m` divides `n` and `n ≠ 0`, then the radical of `m` is less than or equal to the radical of `n`. -/
lemma rad_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) : (rad m : ℝ) ≤ (rad n : ℝ) := by
  classical
  have hdiv := rad_dvd_of_dvd hn h
  have hpos : 0 < rad n := by
    dsimp [rad]
    apply Finset.prod_pos
    intro p hp
    rcases mem_support_factorization_iff.mp hp with ⟨_, pprime, _⟩
    exact Nat.Prime.pos pprime
  have hle_nat : rad m ≤ rad n := Nat.le_of_dvd hpos hdiv
  exact_mod_cast hle_nat


-- log of a product (two factors) with positivity side-conditions (wrapper for simp clarity)
/-- `Real.log (x * y) = Real.log x + Real.log y` for positive real numbers `x` and `y`. -/
lemma log_mul_eq (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
  Real.log (x * y) = Real.log x + Real.log y := by
  simp [Real.log_mul hx.ne' hy.ne']


-- positivity of rpow base variant (rad n is positive)
-- existing lemma name clash avoided by renaming to rad_pos_real
/-- `rad_pos_real n` asserts that the radical of a natural number `n`, when cast to the real numbers, is strictly positive. -/
lemma rad_pos_real (n : ℕ) : 0 < (rad n : ℝ) := by
  have : 0 < rad n := by
    dsimp [rad]
    apply Finset.prod_pos
    intro p hp
    rcases mem_support_factorization_iff.mp hp with ⟨_, pprime, _⟩
    exact Nat.Prime.pos pprime
  exact_mod_cast this


-- For any natural n, piSqRad n ≥ 1 hence positive as real
/-- `piSqRad_pos n` asserts that the value of `piSqRad n` is positive when interpreted as a real number. -/
lemma piSqRad_pos (n : ℕ) : 0 < (piSqRad n : ℝ) := by
  -- If empty, value is 1; otherwise product of positive primes.
  simp only [piSqRad]
  have h_nat_pos : 0 < (n.factorization.support.filter fun p => 2 ≤ n.factorization p).prod (fun p => p) := by
    classical
    by_cases hEmpty : (n.factorization.support.filter fun p => 2 ≤ n.factorization p).card = 0
    · -- empty product = 1 > 0
      have : (n.factorization.support.filter fun p => 2 ≤ n.factorization p).prod (fun p => p) = 1 := by
        rw [Finset.card_eq_zero.mp hEmpty]; simp
      rw [this]; norm_num
    · -- nonempty: each p ≥ 2 hence product positive
      apply Finset.prod_pos
      intro p hp
      -- p is in factorization.support, so p is a prime divisor of n
      have hp_in_supp : p ∈ n.factorization.support := Finset.mem_filter.mp hp |>.1
      rcases mem_support_factorization_iff.mp hp_in_supp with ⟨_, pprime, _⟩
      exact pprime.pos
  exact Nat.cast_pos.mpr h_nat_pos


-- Convert rpow log: log(x^t) = t * log x for positive base (wrapper)
/-- `Real.log (x ^ t) = t * Real.log x` for `x > 0`, expressing the logarithm of a power as the product of the exponent and the logarithm. -/
lemma log_rpow_pos {x t : ℝ} (hx : 0 < x) :
  Real.log (x ^ t) = t * Real.log x := by
  simp [Real.log_rpow hx]

end ABC
