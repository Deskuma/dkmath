/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC021

#print "file: DkMath.ABC.ABC022"

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

-- Version: 2025/10/08  2:14: v0

/-
# p‑進 MGF の過剰項の有界性（layer‑cake 法）

このファイルは，主に「layer‑cake」分解を用いて p の冪に関する実数べき乗を評価するための補題群を収録します。
最終的な目的は，p‑進確率母関数（moment generating function, MGF）に現れる余剰項を
別法（layer‑cake 分解）で有界に抑える補題（mgf_padic_excess_bound_pbase_layercake）を与えることにあります。

## 主な内容

- 層ごとの分解（layer‑cake）に基づき，冪和を望ましい形に分割する手法。
- 切り上げ・切り下げ（ceiling / floor）の基本性質を用いたインデックス操作とテレスコーピング。
- 合同式や剰余類を用いた個数評価（ある層に属する項の個数見積もり）。
- 実数べき乗と指数関数の関係から得られる評価の変換（x^a と exp の比較など）。
- 幾何級数の標準的評価による残差項の抑制と定数管理。

## 構成（概観）

1. 基本的な補助評価（切り上げに関する補題，指数・べき変換の補題）。
2. 剰余類による個数評価とそれを用いた層別和の推定。
3. 幾何級数評価とテレスコーピングを組み合わせた主補題の導出。
4. 最終的な補題 mgf_padic_excess_bound_pbase_layercake の定式化と証明。

### 利用上の注意

- 証明は定数の明示的な追跡を行うためやや冗長になる場合がありますが，定数最適化や一般化（例えば p 以外の基底）へは比較的容易に拡張可能です。
- 本ファイルは，数え上げと解析的評価を組み合わせた手法を学ぶための参照としても有用です。

### 参考・備考

- 証明で用いる基本的事実は elementary な数論・実解析に属しますが，Lean の定式化上は数値不等式や剰余類の扱いに注意が必要です。
- 将来的には定数の改善や他の手法（例えば直接の級数評価）との比較を行うとよいでしょう。

## 序文

このファイルは，主に「layer‑cake」分解を用いた冪和（特に p べきの実指数）の評価補題群を収録するものであり，
最終的に p‑進的な確率母関数（MGF）に対する過剰項の有界性（mgf_padic_excess_bound_pbase_layercake）を
別法（layer‑cake）で与える補題を含みます。証明手法としては，級数の望ましい展開（テレスコーピング），
切り上げ操作の基本性質，合同式・剰余クラスによる個数評価，実数べき乗と指数関数の換算，
および幾何級数の評価を組み合わせています。

## 主要定理・補題と役割

- div_le_iff: 正の実数での除算と乗算による不等号の同値変形（簡約規則としても利用）。
- ceil_spec / natCeil_le_add_one_real: 非負実数に対する Nat.ceil の上下界と切り上げの補助不等式。
- sum_Icc_telescope: Icc 上の差分和のテレスコーピング恒等式（有限和の基本補題）。
- exp_layer_cake: 整値値関数 V(n) に対する exp(t V(n)) の layer‑cake 表現と上界（有限区間かつ V の上界仮定つき）。
- rpow_layer_cake: exp_layer_cake の a^x (a>1) 版。log を用いて exp に還元し，結果を戻すことで得る。
- count_powers_dividing_2n1: 奇素数 p と k ≥ 1 に対して，区間 [0,X] 内で p^k が 2n+1 を割る n の個数を
  切り上げ (⌈(X+1)/p^k⌉) で評価する補題（合同式と剰余クラス分割に基づく）。
- mgf_padic_excess_bound_pbase_layercake: exp / rpow の layer‑cake，count_powers_dividing_2n1，幾何級数評価を結合して，
  p‑進評価に関する MGF の余分項を定数 C で抑える存在定理を与える（p は奇素数，t ∈ (0,1/2] などの仮定）。

## 証明の要点

- 各項 e^{t V(n)}（あるいは a^{t V(n) }）を 1 と差分和に分解し，和を入れ替えて k 層ごとに数え上げる（layer‑cake）。
- 剰余クラスの一意性（gcd(2, p^k) = 1）により，p^k | (2n+1) の解は一つの合同類に対応し，区間内での個数はブロック分割で上界を得る。
- 切り上げによる余剰を局所化し，幾何級数の収束（比 < 1）を用いて有限和を定数倍で抑える。
- rpow（a^x） は log を介して exp に還元することで既存の exp の評価を流用する。

## 用途

- p‑進的評価や素数べきの寄与を扱う解析的証明（特に MGF や確率分布の上界）に直接利用できる補題群。
- layer‑cake 技法の具体化例として，他の離散関数の累積的な寄与評価にも応用可能。

## 依存関係と前提

Mathlib の実数・有限集合・Nat の基本補題，padicValNat に関する基本性質，及び実数の rpow/exp に関する性質を用いる。
ファイル内の各補題はそれぞれ明示的な仮定（p.Prime, p ≠ 2, t > 0, t ≤ 1/2, V の有界性 など）を持つ。

## 注意事項

- 証明の一部は議論的注釈（TODO）や細部の簡略化が残っており，ZMod を直接用いることで簡潔化できる箇所がある。
- 定数の最適化や仮定の緩和は別途検討可能であり，ここでは可読性と構造化を優先してやや粗い上界を採用している。
- 日本語での注釈は補助的説明を意図したものであり，形式的証明部分は Lean の記法に従っている。
- ファイル全体は教育的かつ実用的な layer‑cake の実装例として参照できる。
- 主結果は，別証明（テレスコーピング等）と並列して p‑進 MGF の過剰項評価を与えるものである。
- このコメントはファイル全体のハイレベルな案内を目的とする。
-/

-- Layer-cake representation for real power of integer-valued function
-- ∑ a^{t V(n)} ≤ (X+1) + (a^t - 1) * ∑_{k≥1} a^{t(k-1)} * #{n | V(n) ≥ k}
-- Bounded version: assumes V n ≤ X+1 for all n ≤ X
-- This is the rpow analogue of exp_layer_cake, useful for p-adic MGF bounds
/--
rpow に対する「layer‑cake」的な分解に基づく上界。

仮定:
- a > 1, t > 0,
- 自然数 X と写像 V : ℕ → ℕ,
- hVbd : 任意の n ≤ X に対して V n ≤ X + 1（つまり V の値域を有限の層数で切れる）。

主張:
Finset.sum (Finset.Icc 0 X) (fun n => a ^ (t * (V n : ℝ))) が
(X + 1) + (a^t - 1) * ∑_{k=1}^{X+1} a^{t*(k-1)} * card { n ∈ [0, X] | k ≤ V n }
以下である。

解説（直感的な導出）:
任意の自然数 m について a^{t m} を
a^{t m} = 1 + (a^t - 1) * ∑_{k=1}^m a^{t*(k-1)}
と展開できる（等比級数の細分を用いた表現）。これを各 n について適用して
∑_{n=0}^X a^{t V n} = (X+1) + (a^t - 1) * ∑_{n=0}^X ∑_{k=1}^{V n} a^{t*(k-1)}
と書ける。内側の和と外側の和を入れ替え、hVbd により上限を X+1 に制限すると主張される不等式が得られる。
この補題は、値の多い要素を層ごとに数えることで冪和を制御する場面（例えば p‑進解析や組合せ的なカウント手法）で有用である。
-/
lemma rpow_layer_cake
  (a : ℝ) (ha : 1 < a) (X : ℕ) (t : ℝ) (ht : 0 < t) (V : ℕ → ℕ)
  (hVbd : ∀ n ≤ X, V n ≤ X + 1) :
  (Finset.sum (Finset.Icc 0 X) (fun n => a ^ (t * (V n : ℝ))))
    ≤ (X + 1 : ℝ) + (a ^ t - 1) *
        (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
          a ^ (t * ((k : ℝ) - 1)) *
          ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := by
  -- Strategy: Convert a^x = exp(x * log a), apply exp_layer_cake, convert back
  have ha_pos : 0 < a := by linarith
  have hlog_pos : 0 < Real.log a := Real.log_pos ha

  -- Key identity: a^x = exp(x * log a) for a > 0
  have h_rpow_exp : ∀ x : ℝ, a ^ x = Real.exp (x * Real.log a) := by
    intro x
    rw [← Real.exp_log ha_pos, ← Real.exp_mul]
    congr 1
    rw [Real.log_exp]
    ring

  -- Apply exp_layer_cake with t' = t * log a
  let t' := t * Real.log a
  have ht' : 0 < t' := mul_pos ht hlog_pos

  have h_exp := ABC.exp_layer_cake X t' ht' V hVbd

  -- Convert LHS: ∑ a^{t·V(n)} = ∑ exp(t'·V(n))
  have h_lhs : Finset.sum (Finset.Icc 0 X) (fun n => a ^ (t * (V n : ℝ)))
             = Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t' * (V n : ℝ))) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [h_rpow_exp]
    congr 1
    show t * ↑(V n) * Real.log a = t' * ↑(V n)
    rw [show t' = t * Real.log a from rfl]
    ring

  rw [h_lhs]

  -- Convert RHS constants
  have h_at : a ^ t = Real.exp t' := by
    rw [h_rpow_exp, show t' = t * Real.log a from rfl]

  have h_conv_k : ∀ k : ℕ, a ^ (t * ((k : ℝ) - 1)) = Real.exp (t' * ((k : ℝ) - 1)) := by
    intro k
    rw [h_rpow_exp, show t' = t * Real.log a from rfl]
    ring_nf

  -- Apply exp_layer_cake and convert back
  calc Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t' * (V n : ℝ)))
      ≤ (X + 1 : ℝ) + (Real.exp t' - 1) *
          (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
            Real.exp (t' * ((k : ℝ) - 1)) *
            ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := h_exp
    _ = (X + 1 : ℝ) + (a ^ t - 1) *
          (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
            a ^ (t * ((k : ℝ) - 1)) *
            ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := by
        congr 2
        · rw [h_at]
        · refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          rw [h_conv_k]

/--
実数 a, b, c に対して、c が正 (c > 0) の場合に成り立つ不等式の同値変形を示す補題。

直感的には「a を c で割った値が b 以下である」ことは
「a が b に c を掛けた値以下である」ことと同値である、という主張です。
（除算は正の数に関して単調増加なので、この変換が可能になります。）

用途:
- 不等号の形を除算 ⇄ 乗算のどちらかに変形したいときに使います。
- `@[simp]` 属性が付いているため、簡約規則として自動化にも利用されます。

前提:
- c : ℝ, c > 0
- a, b : ℝ
-/
@[simp]
lemma div_le_iff {a b c : ℝ} (hc : 0 < c) :
  a / c ≤ b ↔ a ≤ b * c := by
  -- c > 0 なので両辺に c や 1/c を掛けて不等号を変形する
  have hc_ne : c ≠ 0 := by linarith
  refine Iff.intro ?h1 ?h2
  · -- 右辺へ: a / c ≤ b から a ≤ b * c を示す
    intro h
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hc)
    have eq1 : (a / c) * c = a := by
      field_simp [hc_ne]
    rw [eq1] at hmul
    exact hmul
  · -- 左辺へ: a ≤ b * c から a / c ≤ b を示す
    intro h
    -- 1/c > 0 を得て両辺に掛ける
    have h1c : 0 < (1 : ℝ) / c := div_pos (by norm_num) hc
    have hmul := mul_le_mul_of_nonneg_right h (le_of_lt h1c)
    have eq2 : a * (1 / c) = a / c := by field_simp [hc_ne]
    have eq3 : (b * c) * (1 / c) = b := by field_simp [hc_ne]
    rw [eq2, eq3] at hmul
    exact hmul


/--
y が非負の実数のときの Nat.ceil に関する基本的な性質を示す補題。

主張：
  (Nat.ceil y - 1 : ℝ) < y ∧ y ≤ Nat.ceil y

意味：
  - Nat.ceil y は y 以上の最小の自然数であり（上界性）、
  - そのひとつ下の整数を実数にキャストしたものは y より小さい（厳密不等式）、
  ということを表す。

用途：
  切り上げ（ceil）に関する不等式を扱うときに用いる。特に、実数から自然数への切り上げに伴う上下界の扱いや、離散化・整数近似に関する証明で有用。

備考：
  - 記法 (Nat.ceil y - 1 : ℝ) は Nat.ceil y から 1 を引いた自然数を実数にキャストしたものを指す。
  - 仮定 `hy : 0 ≤ y` はキャストや関連する比較での取り扱いを簡単にするために置かれている。
-/
@[simp]
lemma ceil_spec (y : ℝ) (hy : 0 ≤ y) : (Nat.ceil y - 1 : ℝ) < y ∧ y ≤ Nat.ceil y := by
  constructor
  · -- show (↑⌈y⌉ - 1) < y
    set n := Nat.ceil y
    by_cases hn0 : n = 0
    · -- n = 0: then y ≤ 0, but hy : 0 ≤ y so y = 0, and -1 < 0 = y holds
      have hle : y ≤ (n : ℝ) := Nat.le_ceil y
      have : y ≤ 0 := by simpa [hn0] using hle
      have hy0 : y = 0 := le_antisymm this hy
      have : (n : ℝ) - 1 = (-1 : ℝ) := by simp [hn0]
      rw [hy0, this]; linarith
    · -- n ≥ 1: rewrite ↑n - 1 = ↑(n - 1) and use minimality of ceil
      have hnne : n ≠ 0 := hn0
      have hnpos : 0 < n := Nat.pos_of_ne_zero hnne
      have hn1 : 1 ≤ n := Nat.one_le_of_lt hnpos
      have : (n : ℝ) - 1 = (n - 1 : ℝ) := by norm_cast;
      rw [this]
      by_contra hneg  -- assume ¬(↑(n - 1) < y)
      have hle : y ≤ (n - 1 : ℝ) := (not_lt).mp hneg
      have hceil_le : Nat.ceil y ≤ n - 1 := (Nat.ceil_le).mpr (by exact_mod_cast hle)
      -- but Nat.ceil y = n by definition of n, so n ≤ n - 1, contradiction
      have hn_eq : Nat.ceil y = n := rfl
      have hle : n ≤ n - 1 := by rwa [←hn_eq] at hceil_le
      -- n = (n - 1).succ なので型を合わせて矛盾を導くのじゃ
      have hn_succ : n = (n - 1).succ := Eq.symm (Nat.succ_pred_eq_of_pos hnpos)
      rw [hn_succ] at hle
      exact absurd hle (Nat.not_succ_le_self (n - 1))
  · -- right inequality: y ≤ ⌈y⌉
    exact Nat.le_ceil y


#check ABC.ceil_spec


-- `↑⌈y⌉₊ ≤ y + 1` （`Nat.ceil_spec` と `Int.ceil_le_add_one` から従う）
/--
y ≥ 0 のとき、非負整数としての天井 ⌈y⌉₊ を実数にキャストしたものは y + 1 以下になる、という補題。

直感的には ⌈y⌉₊ は y を上回る最小の非負整数であり、したがって
⌈y⌉₊ - 1 < y ≤ ⌈y⌉₊ が成り立つ。実数にキャストして両辺に 1 を足すことで
↑(⌈y⌉₊) ≤ y + 1 を得る。

用途：実数から自然数への天井を実数に戻して上界を取るような場面での簡単な見積りに用いる。
-/
@[simp]
lemma natCeil_le_add_one_real' {y : ℝ} (hy : 0 ≤ y) :
  (↑(⌈y⌉₊) : ℝ) ≤ y + 1 := by
  -- Nat.ceil_spec より ↑(⌈y⌉₊) < y + 1 が得られるのでこれを用いる
  have h := ABC.ceil_spec y hy
  -- Nat.ceil_spec より ↑⌈y⌉₊ - 1 < y なので、↑⌈y⌉₊ < y + 1 が従う
  linarith [h.left]


-- Basic telescoping lemma: ∑_{k=1}^m (f k - f(k-1)) = f m - f 0
/--
1 から m までの閉区間 Icc に対する和
∑_{k=1}^m (f k - f (k-1)) = f m - f 0
を主張する補題．各項 f k と -f (k-1) が隣接する項と打ち消し合う（テレスコーピング）ため，
内部の項はすべて消え，残るのは端点の差 f m - f 0 だけになる．

注意: k が 1 以上なので k-1 は自然数として定義される．
m = 0 の場合は左辺は空和で 0 となり，右辺も f 0 - f 0 = 0 で一致する．

証明は自然数 m に関する帰納法か，Finset.sum の基本的な性質（区間分割や項の再配置）を用いて簡単に与えられる．
-/
lemma sum_Icc_telescope' (m : ℕ) (f : ℕ → ℝ) :
  Finset.sum (Finset.Icc 1 m) (fun k => f k - f (k-1)) = f m - f 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · -- Direct induction on m
    induction m with
    | zero => simp at hm
    | succ m ihm =>
        by_cases hm0 : m = 0
        · simp [hm0]
        · rw [Finset.sum_Icc_succ_top]
          · rw [ihm hm0]
            simp
          · omega


-- Layer-cake representation for exponential of integer-valued function
-- ∑ e^{t V(n)} ≤ (X+1) + (e^t - 1) * ∑_{k≥1} e^{t(k-1)} * #{n | V(n) ≥ k}
-- Bounded version: assumes V n ≤ X+1 for all n ≤ X
/--
exp_layer_cake の説明（日本語）:

X : ℕ, t : ℝ (0 < t), V : ℕ → ℕ, かつ ∀ n ≤ X, V n ≤ X+1 という仮定の下で，
有限和 ∑_{n=0}^X exp (t * V n) を「層（layer）」ごとに分解して上界を与える補題である。
各自然数 m に対して恒等式
  exp (t * m) = 1 + (exp t - 1) * ∑_{k=1}^m exp (t * (k - 1))
が成り立つことを用い，これを各 n について合計して和の順序を入れ替えると，
k ごとに k ≤ V n を満たす n の個数（すなわち層 k の濃度）が現れる。
仮定 hVbd により k を 1 から X+1 までに制限して評価できるため，結果として次の形の不等式が得られる：
左辺の指数和 ≲ (X+1) + (exp t - 1) * Σ_{k=1}^{X+1} exp(t*(k-1)) * (層 k の要素数) 。

証明の骨子：
  1. 各項に対して上の幾何級数の恒等式を適用する。
  2. n に関する和と k に関する和を入れ替える（layer-cake 技法）。
  3. フィルタを使って「k を満たす n の個数」を数え上げ，hVbd により k の範囲を有限に切り詰める。
  4. 定数因子を整理して所望の右辺の形にする。

補足：
  - (Finset.filter ...).card は実数に写した層の要素数である。
  - t > 0 によって exp t - 1 > 0 となり，評価が単純化される。
  - 場合によっては上記の操作で等号が得られるが，本補題は上界として述べている。
-/
lemma exp_layer_cake'
  (X : ℕ) (t : ℝ) (ht : 0 < t) (V : ℕ → ℕ)
  (hVbd : ∀ n ≤ X, V n ≤ X + 1) :
  (Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t * (V n : ℝ))))
    ≤ (X + 1 : ℝ) + (Real.exp t - 1) *
        (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
          Real.exp (t * ((k : ℝ) - 1)) *
          ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := by
  classical
  -- Step 1: Decompose e^{tV(n)} = 1 + ∑_{k=1}^{V(n)} (e^{tk} - e^{t(k-1)})
  have h_decomp : ∀ n ≤ X, Real.exp (t * (V n : ℝ))
      = 1 + Finset.sum (Finset.Icc 1 (V n)) (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ))) := by
    intro n _
    by_cases hV : V n = 0
    · simp [hV]
    · -- Telescoping sum
      have h_tele : Finset.sum (Finset.Icc 1 (V n)) (fun k => Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))
          = Real.exp (t * (V n : ℝ)) - 1 := by
        have h := sum_Icc_telescope (V n) (fun k => Real.exp (t * (k : ℝ)))
        simp only [Nat.cast_zero, mul_zero, Real.exp_zero] at h
        refine Eq.trans ?_ h
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        norm_cast
      rw [h_tele]
      ring
  -- Step 2: Sum both sides over n
  calc Finset.sum (Finset.Icc 0 X) (fun n => Real.exp (t * (V n : ℝ)))
      = Finset.sum (Finset.Icc 0 X) (fun n =>
          1 + Finset.sum (Finset.Icc 1 (V n)) (fun k =>
            Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Icc] at hn
        exact h_decomp n hn.2
    _ = (X + 1) + Finset.sum (Finset.Icc 0 X) (fun n =>
          Finset.sum (Finset.Icc 1 (V n)) (fun k =>
            Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        have h_card : (Finset.Icc 0 X).card = X + 1 := by rw [Nat.card_Icc]; omega
        rw [h_card]
        simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    _ ≤ (X + 1) + (Real.exp t - 1) *
          Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
            Real.exp (t * ((k : ℝ) - 1)) *
            ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ)) := by
        -- Factor out (e^t - 1) from differences (for k ≥ 1)
        have h_factor : ∀ k : ℕ, 1 ≤ k → Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ))
            = (Real.exp t - 1) * Real.exp (t * ((k-1) : ℝ)) := by
          intro k hk
          have h_eq : (k : ℝ) = ((k-1) : ℝ) + 1 := by simp
          rw [h_eq, mul_add, Real.exp_add]
          ring_nf
        -- Rewrite double sum using factorization
        have h_rewrite : ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
            (Real.exp (t * (k : ℝ)) - Real.exp (t * ((k-1) : ℝ)))
            = (Real.exp t - 1) * ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
                Real.exp (t * ((k-1) : ℝ)) := by
          trans (∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n),
            (Real.exp t - 1) * Real.exp (t * ((k-1) : ℝ)))
          · apply Finset.sum_congr rfl
            intro n _
            apply Finset.sum_congr rfl
            intro k hk
            exact h_factor k (Finset.mem_Icc.mp hk).1
          · simp [Finset.mul_sum]
        rw [h_rewrite]
        -- Key: show (e^t - 1) ≥ 0 for t > 0
        have ht_pos : 0 ≤ Real.exp t - 1 := by
          have : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (le_of_lt ht)
          linarith
        gcongr
        -- Interchange: ∑_n ∑_{k ≤ V(n)} f(k) = ∑_{k ≤ X+1} f(k) * #{n : k ≤ V(n)}
        -- Using boundedness V n ≤ X+1, we can rewrite as equality with indicators
        calc ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (V n), Real.exp (t * ((k-1) : ℝ))
            = ∑ n ∈ Finset.Icc 0 X, ∑ k ∈ Finset.Icc 1 (X+1),
                if k ≤ V n then Real.exp (t * ((k-1) : ℝ)) else 0 := by
              apply Finset.sum_congr rfl
              intro n hn
              -- Use boundedness: V n ≤ X+1 for n ≤ X
              have hV : V n ≤ X+1 := hVbd n (Finset.mem_Icc.mp hn).2
              -- Rewrite Icc 1 (V n) as filter of Icc 1 (X+1)
              rw [← Finset.sum_filter]
              apply Finset.sum_congr
              · ext k
                simp only [Finset.mem_filter, Finset.mem_Icc]
                constructor
                · intro ⟨h1, h2⟩
                  exact ⟨⟨h1, Nat.le_trans h2 hV⟩, h2⟩
                · intro ⟨⟨h1, _⟩, h2⟩
                  exact ⟨h1, h2⟩
              · intro k _; rfl
          _ = ∑ k ∈ Finset.Icc 1 (X+1), ∑ n ∈ Finset.Icc 0 X,
                if k ≤ V n then Real.exp (t * ((k-1) : ℝ)) else 0 := Finset.sum_comm
          _ = ∑ k ∈ Finset.Icc 1 (X+1), Real.exp (t * ((k-1) : ℝ)) *
                (Finset.filter (fun n => k ≤ V n) (Finset.Icc 0 X)).card := by
              apply Finset.sum_congr rfl
              intro k _
              rw [← Finset.sum_filter, Finset.sum_const]
              simp [nsmul_eq_mul, mul_comm]
          _ ≤ ∑ k ∈ Finset.Icc 1 (X+1), Real.exp (t * ((k-1) : ℝ)) *
                (Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card := by
              apply Finset.sum_le_sum
              intro k _
              apply mul_le_mul_of_nonneg_left
              · norm_cast
                apply Finset.card_le_card
                intro n hn
                simp [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
                omega
              · positivity

end ABC
