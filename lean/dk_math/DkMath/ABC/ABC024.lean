/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC023

#print "file: DkMath.ABC.ABC024"

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

#check ABC.div_le_iff

#check ABC.count_powers_dividing_2n1
#check ABC.natCeil_le_add_one_real

#check ABC.rpow_layer_cake


/-
Alternative proof of `mgf_padic_excess_bound_pbase` using layer-cake decomposition.
This proof demonstrates the use of `exp_layer_cake` (from ABC.lean) combined with
`count_powers_dividing_2n1` to achieve the same MGF bound via a different route.

Mathematical Strategy:
1. Apply `exp_layer_cake` to decompose ∑ p^{t·v(n)} into layer-by-layer sums
2. Use `count_powers_dividing_2n1` to bound #{n : v(n) ≥ k} ≤ ⌈(X+1)/p^k⌉
3. Evaluate the resulting geometric series with ratio r = p^{t-1} < 1
4. Factor out p^{-2t} to get the final bound

This approach is pedagogically valuable as it shows how the general layer-cake
technique applies to p-adic valuations, complementing the telescoping approach
used in the main proof above.
-/

/--
p を奇素数、t ∈ (0, 1/2] としたときの有界性を与える補題。

具体的には、奇素数 p と t ∈ (0,1/2] の下で、任意の大きさ X ≥ 1 に対して
平均値 (Finset.sum (Finset.Icc 0 X) (λ n, p ^ (t * (padicValNat p (2*n+1) - 2)))) / (X + 1)
が p, t に依存する定数 C > 0 によって一様に上から抑えられることを主張する。

証明の主要素は層別化（layer-cake）法と p-進付値の性質の利用である。
具体的には v_p(2n+1) の値 k ごとに n を分類し、そのクラスに含まれる項の個数が
おおよそ p^{-(k-1)} に比例することを用いる。一方、各層での寄与は p^{t(k-2)} によって
指数的に減衰するため、層ごとの和は収束し、全体の平均が一定の正の定数で抑えられる。
得られる定数 C は p と t に依存するが、X に依存しない点が重要である。
-/
lemma mgf_padic_excess_bound_pbase_layercake
  (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 1 / 2) :
  ∃ C > 0, ∀ X ≥ 1,
    (Finset.sum (Finset.Icc 0 X)
      (fun n => (p : ℝ) ^ (t * ((padicValNat p (2*n+1) : ℤ) - 2)))) / (X + 1) ≤ C := by
  classical
  -- Step 1: Define V(n) = v_p(2n+1) and establish upper bound V(n) ≤ log_p(2X+1)
  let V : ℕ → ℕ := fun n => padicValNat p (2*n+1)

  -- We need V(n) ≤ some upper bound K for all n ≤ X to apply exp_layer_cake
  -- Since p^{V(n)} | (2n+1) ≤ 2X+1, we have V(n) ≤ log_p(2X+1)
  -- For simplicity, we use V(n) ≤ X+1 (crude but sufficient)
  have hV_bound : ∀ X ≥ 1, ∀ n ≤ X, V n ≤ X + 1 := by
    intro X hX n hn
    -- V(n) ≤ log_p(2n+1) ≤ log_p(2X+1) ≤ X+1 (since p ≥ 3)
    -- More precisely: p^{V(n)} ≤ 2n+1 ≤ 2X+1
    -- So V(n) ≤ log_p(2X+1) = (log(2X+1))/(log p) ≤ (log(2X+1))/(log 3)
    -- For large X: log(2X+1) ~ log(2X) < log(X^2) = 2 log X < X (for X ≥ 3)
    -- For small X ≥ 1: can verify directly
    -- Use padicValNat_le_nat_log and the fact that 2n+1 ≤ 2X+1
    -- V(n) ≤ log_p(2n+1) by padicValNat_le_nat_log
    have h1 : V n ≤ Nat.log p (2*n+1) := padicValNat_le_nat_log (2*n+1)
    -- 2n+1 ≤ 2X+1 from n ≤ X
    have h2 : 2*n+1 ≤ 2*X+1 := by omega
    -- log_p(2n+1) ≤ log_p(2X+1) by monotonicity
    have h3 : Nat.log p (2*n+1) ≤ Nat.log p (2*X+1) := by
      apply Nat.log_mono_right
      exact h2
    -- Need to show: log_p(2X+1) ≤ X+1
    -- This requires showing p^{X+1} ≥ 2X+1 when p ≥ 3, X ≥ 1
    have hp_ge_3 : 3 ≤ p := by
      -- p is prime and p ≠ 2, so p ≥ 3
      have : p ≥ 2 := hp.two_le
      omega
    have h_pow_bound : 2*X+1 ≤ (p : ℕ) ^ (X+1) := by
      -- 3^{X+1} ≥ 2X+1 for X ≥ 1 by induction
      have h_three_pow : ∀ m ≥ 1, 2*m+1 ≤ 3^(m+1) := by
        intro m hm
        -- Prove by strong induction on m
        induction m with
        | zero =>
          -- m = 0: but we have hm : 0 ≥ 1, contradiction
          omega
        | succ k ih =>
          -- m = k+1, need to prove 2(k+1)+1 ≤ 3^{k+2}
          by_cases hk : k = 0
          · -- k = 0, m = 1: need 2·1+1 = 3 ≤ 3^2 = 9
            rw [hk]
            norm_num
          · -- k ≥ 1: use IH for k
            have hk_ge_1 : k ≥ 1 := by omega
            have ih_k := ih hk_ge_1
            -- Now: 2k+1 ≤ 3^{k+1}
            -- Want: 2(k+1)+1 = 2k+3 ≤ 3^{k+2} = 3·3^{k+1}
            calc (2*(k+1)+1 : ℕ)
                = 2*k + 3 := by ring
              _ ≤ 6*k + 3 := by omega
              _ = 3 * (2*k + 1) := by ring
              _ ≤ 3 * (3 ^ (k+1)) := Nat.mul_le_mul_left 3 ih_k
              _ = 3 ^ (k+2) := by ring
      have : 2*X+1 ≤ 3 ^ (X+1) := h_three_pow X hX
      calc (2*X+1 : ℕ)
          ≤ 3 ^ (X+1) := this
        _ ≤ p ^ (X+1) := Nat.pow_le_pow_left hp_ge_3 (X+1)
    -- Therefore log_p(2X+1) ≤ X+1
    have hp_gt_1 : 1 < p := hp.one_lt
    have h4 : Nat.log p (2*X+1) ≤ X + 1 := by
      -- If log p n > k, then n ≥ p^{k+1}, contrapositive of this gives result
      by_contra h_not
      push_neg at h_not
      -- log p (2X+1) > X+1, so log p (2X+1) ≥ X+2
      have : X + 2 ≤ Nat.log p (2*X+1) := by omega
      -- By definition of log: p^{log p n} ≤ n
      have h_pow_le : p ^ Nat.log p (2*X+1) ≤ 2*X+1 := by
        apply Nat.pow_log_le_self
        omega
      -- But X+2 ≤ log p (2X+1) implies p^{X+2} ≤ p^{log p (2X+1)} ≤ 2X+1
      have h_bad : p ^ (X+2) ≤ 2*X+1 := by
        have hp_pos : 0 < p := Nat.Prime.pos hp
        calc p ^ (X+2)
            ≤ p ^ Nat.log p (2*X+1) := Nat.pow_le_pow_right hp_pos this
          _ ≤ 2*X+1 := h_pow_le
      -- But p^{X+1} ≤ 2X+1 by h_pow_bound, and p^{X+2} > p^{X+1} since p > 1
      -- So p^{X+2} > 2X+1, contradiction
      have h_good : 2*X+1 < p ^ (X+2) := by
        calc 2*X+1
            ≤ p ^ (X+1) := h_pow_bound
          _ < p ^ (X+2) := by
            have : (X+1) < (X+2) := by omega
            exact Nat.pow_lt_pow_right hp_gt_1 this
      omega
    omega

  -- Define constant C (will be determined through the proof)
  -- From geometric series: C ~ p^{-2t} * (1 + (p^t - 1) * r/(1-r)) where r = p^{t-1}
  -- Updated: After sum2 correction, we have 1 + 4*p, so C = (1 + 4*p) * p^{-2t}
  let r := (p : ℝ) ^ (t - 1)
  let C := (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t) -- Exact bound matching h_sum_bound

  use C
  constructor
  · -- Show C > 0
    apply mul_pos
    · -- 1 + 4*p > 0
      have : 0 < (p : ℝ) := by norm_cast; exact hp.pos
      linarith
    · apply Real.rpow_pos_of_pos
      norm_cast
      exact hp.pos

  intro X hX

  -- Step 2: Apply rpow_layer_cake decomposition
  -- We want to bound: ∑ p^{t(V(n)-2)} = p^{-2t} * ∑ p^{t·V(n)}
  -- rpow_layer_cake gives: ∑ p^{t·V(n)} ≤ (X+1) + (p^t - 1) * ∑_{k=1}^{X+1} p^{t(k-1)} * #{n : V(n) ≥ k}

  have hp_ge_3 : 3 ≤ p := by
    by_contra h
    push_neg at h
    have hp2 : 2 ≤ p := hp.two_le
    have : p = 2 := by omega
    exact hpodd this

  have hp_pos : 0 < (p : ℝ) := by norm_cast; exact hp.pos
  have hp_ge_one : 1 < (p : ℝ) := by norm_cast; omega

  -- Apply rpow_layer_cake with base p and parameter t
  /-
  有限和 ∑_{n=0}^X (p : ℝ)^(t * V n) に対する「レイヤーケーキ」型の上界。
  仮定として p ≥ 1, t ≥ 0 と V の値域が適切に上に有界であることを用いることで、
  各 n に対する指数関数の寄与をレベル k（1, …, X+1）ごとに分解して評価している。

  具体的には左辺は各 n に対して p^{t·V n} を合計したものであり、
  右辺は次の二つの寄与の和で上から抑えている：
    1. (X+1) : 全ての項が最低でも 1（V n = 0 の寄与）であることによる基底項。
    2. (p^t - 1) * ∑_{k=1}^{X+1} p^{t·(k-1)} * #{ n ∈ [0,X] | V n ≥ k }
       : レベル k 以上にある項が生む追加寄与を、各レベルでの要素数に比例して重み付けして合計したもの。

  右辺のフィルタのカードは「0 ≤ n ≤ X かつ V n ≥ k」を満たす n の個数を表す。
  この不等式は、指数関数の増加をレイヤーごとの累積で制御する標準的な手法（layer-cake／レイヤーケーキ分解）
  を実装したものであり、以降の議論で ∑ p^{t·V n} を個数情報と幾何級数の積で扱う際に用いる。
  -/
  have h_layer : Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (V n : ℝ)))
      ≤ (X + 1 : ℝ) + ((p : ℝ) ^ t - 1) *
          (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
            (p : ℝ) ^ (t * ((k : ℝ) - 1)) *
            ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := by
    exact rpow_layer_cake (p : ℝ) hp_ge_one X t ht0 V (hV_bound X hX)

  -- Step 3: Use count_powers_dividing_2n1 to bound each layer
  -- For each k: #{n ∈ [0,X] : V(n) ≥ k} ≤ count_powers_dividing_2n1 p k X ≤ ⌈(X+1)/p^k⌉

  -- Bound each layer's cardinality (with ceiling slack)
  /-
  任意の k ∈ [1, X+1] に対して，
  区間 0 ≤ n ≤ X の中で p-valuation V n が少なくとも k であるような n の個数（実数として）は上から次の式で評価できる：
  (X + 1) / p^k + 1.

  説明：V n ≥ k であるためには n が p^k の倍数でなければならず（0 を含む），
  0 から X までの整数のうちそのようなものは floor(X / p^k) + 1 個である。
  したがって floor(X / p^k) + 1 ≤ (X + 1) / p^k + 1 が成り立ち，主張が得られる。
  -/
  have h_card_bound_ceil : ∀ k ∈ Finset.Icc 1 (X+1),
      ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ)
        ≤ ((X + 1 : ℝ) / (p : ℝ) ^ k) + 1 := by
    intro k hk_mem
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    -- The key is: #{n ≤ X : V(n) ≥ k} counts n where p^k | (2n+1)
    -- This is bounded by count_powers_dividing_2n1 p k X ≤ ⌈(X+1)/p^k⌉₊
    have h_filter_eq : Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X) =
        Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · intro ⟨h_range, hn, hv⟩
        refine ⟨h_range, hn, ?_⟩
        -- k ≤ padicValNat p (2*n+1) → p^k ∣ (2*n+1)
        have h2n1_ne : 2*n+1 ≠ 0 := by omega
        rw [padicValNat_dvd_iff_le h2n1_ne]
        exact hv
      · intro ⟨h_range, hn, hdiv⟩
        refine ⟨h_range, hn, ?_⟩
        -- p^k ∣ (2*n+1) → k ≤ padicValNat p (2*n+1)
        have h2n1_ne : 2*n+1 ≠ 0 := by omega
        rw [← padicValNat_dvd_iff_le h2n1_ne]
        exact hdiv
    -- Now apply count_powers_dividing_2n1
    have hk_ge_1 : k ≥ 1 := by
      have : k ∈ Finset.Icc 1 (X+1) := hk_mem
      simp only [Finset.mem_Icc] at this
      exact this.1

    /-
    n ∈ [0, X] かつ p^k ∣ (2*n+1) を満たす n の個数は上界 ⌈((X : ℝ) + 1) / (p : ℝ)^k⌉₊ を与えることを述べる補助説明。

    仮定：
    - p は素数 (hp)．
    - p は奇数である (hpodd)、したがって 2 は p^k に関して可逆である。
    - k ≥ 1 (hk_ge_1)．
    - X は有限区間 Finset.Icc 0 X による上界を与える自然数である。

    考え方の要点：
      方程式 2*n+1 ≡ 0 (mod p^k) は 2 が可逆であることから n ≡ c (mod p^k) の形で一意の合同類を定める。
      よって区間 [0, X] に含まれる解の個数は長さ X+1 を周期 p^k で割ったときの天井 ⌈(X+1)/p^k⌉₊ を超えない。
      ここでは既存の補題 ABC.count_powers_dividing_2n1 を用い、最後に ge_iff_le による簡約を行って結論を得る。
    -/
    have h_count_bound : (Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card
        ≤ ⌈((X : ℝ)+1) / ((p : ℝ)^k)⌉₊ := by
      have h := ABC.count_powers_dividing_2n1 p hp hpodd k hk_ge_1 X
      simp only [ge_iff_le]
      exact h
    calc ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ)
        = ((Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card : ℝ) := by
          rw [h_filter_eq]
      _ ≤ (⌈((X : ℝ)+1) / ((p : ℝ)^k)⌉₊ : ℝ) := by
          -- use exact_mod_cast to transport the Nat-inequality h_count_bound to the real cast
          exact_mod_cast h_count_bound
      _ ≤ ((X : ℝ)+1) / ((p : ℝ)^k) + 1 := by
          have hx_pos : ((X : ℝ)+1) / ((p : ℝ)^k) ≥ 0 := by positivity
          exact ABC.natCeil_le_add_one_real hx_pos
      _ = ((X : ℝ) + 1) / (p : ℝ) ^ k + 1 := by ring

  -- Key truncation lemma: when p^k > 2X+1, the cardinality is 0
  -- k が `Finset.Icc 1 (X+1)` に属し、かつ `(p : ℕ)^k > 2*X + 1` であるとき、
  -- 区間 `Icc 0 X` の中で `p^k` が `2*n+1` を割り切るような `n` は存在しない、という主張です。
  -- したがって
  --   (Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card = 0
  -- が成り立ちます。
  --
  -- 証明のアイデア: 任意の `n ∈ Icc 0 X` に対して `0 < 2*n+1 ≤ 2*X+1` であり、
  -- 仮定より `2*X+1 < p^k` なので `2*n+1 < p^k` が成り立ちます。
  -- 正の整数 `2*n+1` が自分より大きな正整数 `p^k` によって割り切れることはないため、
  -- そのような `n` は存在せず、フィルタ後の元数は 0 になります。
  have count_zero_of_large_k : ∀ k ∈ Finset.Icc 1 (X+1),
      (p : ℕ) ^ k > 2*X + 1 →
      (Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card = 0 := by
    intro k hk_mem hpk_gt
    -- show the filter is empty: any n in the filter would give p^k ≤ 2*n+1 ≤ 2*X+1
    have h_empty : Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      -- hn : n ∈ Finset.filter (...) so unpack the filter membership using lemma `Finset.mem_filter`
      have hn_filter := Finset.mem_filter.1 hn
      -- extract pieces: hn_filter.1 : n ∈ Finset.Icc 0 X, hn_filter.2 : n ≤ X ∧ p^k ∣ 2*n+1
      have hnIcc := hn_filter.1
      have hn_leX := hn_filter.2.1
      have hdiv := hn_filter.2.2
      -- from hnIcc get lower/upper bounds 0 ≤ n and n ≤ X
      have ⟨_, hnX⟩ := Finset.mem_Icc.1 hnIcc
      -- bound 2*n+1 ≤ 2*X+1
      have h2n1_le : 2 * n + 1 ≤ 2 * X + 1 := by
        have h := Nat.mul_le_mul_left 2 hnX
        linarith
      -- get witness for divisibility: 2*n+1 = p^k * m
      obtain ⟨m, hm⟩ := hdiv
      -- m cannot be 0 because 2*n+1 > 0, so m ≥ 1
      have m_pos : 1 ≤ m := by
        cases m
        · simp at hm
        · simp
      -- hence p^k ≤ p^k * m = 2*n+1, so p^k ≤ 2*n+1 ≤ 2*X+1
      have hpk_le : (p : ℕ) ^ k ≤ 2 * n + 1 := by
        have m_pos' : 0 < m := by linarith [m_pos]
        calc (p : ℕ) ^ k
            ≤ (p : ℕ) ^ k * m := by apply Nat.le_mul_of_pos_right; exact m_pos'
          _ = 2 * n + 1 := by rw [← hm]
      have : (p : ℕ) ^ k ≤ 2 * X + 1 := Nat.le_trans hpk_le h2n1_le
      -- this contradicts the assumption p^k > 2*X+1
      linarith
    -- card of empty set is 0
    have : (Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X)).card = 0 := by
      rw [h_empty]; simp
    exact this

  -- Refined bound with indicator function: card ≤ (X+1)/p^k + 1_{p^k ≤ 2X+1}
  -- This splits the "+1 ceiling slack" to only k ≤ K = log_p(2X+1)
  have h_card_bound_split :
    ∀ k ∈ Finset.Icc 1 (X+1),
      ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ)
        ≤ ((X + 1 : ℝ) / (p : ℝ) ^ k)
          + (if ( (p : ℕ)^k ≤ 2*X + 1) then (1 : ℝ) else 0) := by
    intro k hk
    by_cases hk_small : (p : ℕ)^k ≤ 2*X + 1
    · -- small: ceiling +1 applies
      have hceil := h_card_bound_ceil k hk
      -- hceil : (card : ℝ) ≤ ((X+1)/p^k) + 1
      simpa [hk_small] using hceil
    · -- large: card = 0
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      have h_filter_eq : Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)
                       = Finset.filter (fun n => n ≤ X ∧ p^k ∣ (2*n+1)) (Finset.Icc 0 X) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro ⟨h_range, hn, hv⟩
          refine ⟨h_range, hn, ?_⟩
          -- k ≤ V n → p^k ∣ (2*n+1)
          have h2n1_ne : 2*n+1 ≠ 0 := by omega
          rw [padicValNat_dvd_iff_le h2n1_ne]
          exact hv
        · intro ⟨h_range, hn, hdiv⟩
          refine ⟨h_range, hn, ?_⟩
          -- p^k ∣ (2*n+1) → k ≤ V n
          have h2n1_ne : 2*n+1 ≠ 0 := by omega
          rw [← padicValNat_dvd_iff_le h2n1_ne]
          exact hdiv
      have hzero := count_zero_of_large_k k hk (lt_of_not_ge hk_small)
      have : ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ) = 0 := by
        rw [h_filter_eq]
        exact_mod_cast hzero
      -- RHS becomes + 0
      simp only [this, hk_small, ↓reduceIte, add_zero, ge_iff_le]
      positivity

  -- Finset.Icc 0 X 上の和を上から抑える補題の説明。
  --
  -- 目的: Finset.Icc 0 X にわたる和
  --   ∑_{n ∈ Icc 0 X} (p : ℝ) ^ (t * (V n : ℝ))
  -- が
  --   (1 + 4 * (p : ℝ)) * (X + 1)
  -- で上から抑えられることを示す。
  --
  -- 証明の骨子:
  -- 各 n ∈ Finset.Icc 0 X について項 (p : ℝ)^(t * (V n : ℝ)) を一様に 1 + 4 * (p : ℝ) で上から評価する。
  -- 区間 Finset.Icc 0 X は 0 から X までの整数を含むので要素数は X + 1 であり、
  -- 各項の上界を足し合わせると総和は (1 + 4 * (p : ℝ)) * (X + 1) を下回る。
  --
  -- 備考: 実際の不等式の成立には p, t, V に関する適切な仮定（符号や値の範囲）が必要になる点に注意する。
  -- また (p : ℝ) や (V n : ℝ) は実数への coercion を表す。
  have h_sum_bound : Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (V n : ℝ)))
      ≤ (1 + 4 * (p : ℝ)) * (X + 1) := by
    -- Strategy: Use h_layer and h_card_bound_split to establish geometric series bound
    -- KEY: Split the "+1 ceiling slack" into conditional form using h_card_bound_split
    calc Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (V n : ℝ)))
        ≤ (X + 1 : ℝ) + ((p : ℝ) ^ t - 1) *
            (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
              (p : ℝ) ^ (t * ((k : ℝ) - 1)) *
              ((Finset.filter (fun n => n ≤ X ∧ k ≤ V n) (Finset.Icc 0 X)).card : ℝ))) := h_layer

      -- Step 1: Replace h_card_bound_ceil with h_card_bound_split
      -- This splits card ≤ (X+1)/p^k + 1 into (X+1)/p^k + indicator{p^k ≤ 2X+1}
      _ ≤ (X + 1 : ℝ) + ((p : ℝ) ^ t - 1) *
            (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
              (p : ℝ) ^ (t * ((k : ℝ) - 1)) *
                (((X + 1 : ℝ) / (p : ℝ) ^ k)
                + (if ( (p : ℕ)^k ≤ 2*X + 1) then (1 : ℝ) else 0)))) := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro k hk
            apply mul_le_mul_of_nonneg_left (h_card_bound_split k hk)
            apply Real.rpow_nonneg
            norm_cast; omega
          · linarith [Real.one_le_rpow (by norm_cast; omega : (1 : ℝ) ≤ (p : ℝ)) ht0.le]

      -- Step 2: Split the sum into two parts: (X+1)/p^k and indicator function
      -- This is the KEY step: separating the "+1 slack" to only k ≤ K
      _ = (X + 1 : ℝ) + ((p : ℝ) ^ t - 1) *
            (Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
              (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ k))
            + Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
              (p : ℝ) ^ (t * ((k : ℝ) - 1)) *
              (if ( (p : ℕ)^k ≤ 2*X + 1) then (1 : ℝ) else 0))) := by
          congr 2
          rw [← Finset.sum_add_distrib]
          congr 1
          ext k
          ring

      _ ≤ (1 + 4 * (p : ℝ)) * (X + 1) := by
          -- [LEVEL 1] Now we have split: sum1 (the (X+1)/p^k part) + sum2 (the indicator part)
          -- Strategy: bound sum1 by existing method, bound (p^t-1)*sum2 by 2(X+1)

          -- [LEVEL 2] Define sum1 and sum2 explicitly
          let sum1 := Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
              (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ k))
          let sum2 := Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
              (p : ℝ) ^ (t * ((k : ℝ) - 1)) *
              (if ( (p : ℕ)^k ≤ 2*X + 1) then (1 : ℝ) else 0))

          -- [LEVEL 2] Goal structure: show LHS ≤ (X+1) + (p^t-1)*(sum1+sum2) ≤ (1+4p)*(X+1)
          have h_goal_expand : (X + 1 : ℝ) + ((p : ℝ) ^ t - 1) * (sum1 + sum2)
              ≤ (1 + 4 * (p : ℝ)) * (X + 1) := by






            -- [LEVEL 3] sum1 bound: use existing proof (geometric series)
            have sum1_bound : Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
                (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ k))
              ≤ (X + 1) * 2 := by
              -- Strategy: sum1 = (X+1) * ∑_{k=1}^{X+1} p^{t(k-1)-k}
              -- Let r = p^{-(1-t)}, then sum = (X+1) * ∑_{k=1}^{X+1} r^k
              -- Since p^{1-t} ≥ 3^{1/2} > 1, we have 0 < r < 1
              -- Geometric series: ∑_{k=1}^n r^k < r/(1-r) ≤ 2 for r = 1/sqrt(3)

              -- First show (X+1) can be factored out
              have h_factor : Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
                  (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1 : ℝ) / (p : ℝ) ^ k))
                = (X + 1) * Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
                    (p : ℝ) ^ (t * ((k : ℝ) - 1) - k)) := by
                rw [Finset.mul_sum]
                congr 1
                ext k
                have h_div : (p : ℝ) ^ k ≠ 0 := by
                  apply pow_ne_zero
                  linarith
                calc (p : ℝ) ^ (t * ((k : ℝ) - 1)) * ((X + 1) / (p : ℝ) ^ k)
                    = (p : ℝ) ^ (t * ((k : ℝ) - 1)) * (X + 1) / (p : ℝ) ^ k := by
                      rw [mul_div_assoc]
                  _ = (X + 1) * (p : ℝ) ^ (t * ((k : ℝ) - 1)) / (p : ℝ) ^ k := by
                      ring
                  _ = (X + 1) * ((p : ℝ) ^ (t * ((k : ℝ) - 1)) / (p : ℝ) ^ k) := by
                      rw [mul_div_assoc]
                  _ = (X + 1) * (p : ℝ) ^ (t * ((k : ℝ) - 1) - k) := by
                      congr 1
                      rw [Real.rpow_sub hp_pos]
                      norm_cast
              rw [h_factor]

              apply mul_le_mul_of_nonneg_left _ (by norm_cast; omega)

              -- Now bound ∑_{k=1}^{X+1} p^{t(k-1)-k} ≤ 2
              -- CORRECT: t(k-1)-k = -t - (1-t)*k, so p^{t(k-1)-k} = p^{-t} * (p^{-(1-t)})^k
              -- Let r = p^{-(1-t)} = 1/p^{1-t}, where p^{1-t} ≥ 3^{1/2} > 1
              -- So 0 < r < 1 and ∑_{k=1}^n r^k ≤ r/(1-r) ≤ 2
              -- Factor out p^{-t}: ∑ p^{t(k-1)-k} = p^{-t} * ∑ r^k

              -- Transform the sum to geometric form with p^{-t} factored out
              have h_exp_geom : ∀ k : ℕ, (p : ℝ) ^ (t * ((k : ℝ) - 1) - k)
                  = (p : ℝ) ^ (-t) * ((p : ℝ) ^ (-(1 - t))) ^ k := by
                intro k
                -- Key algebraic identity: t*(k-1) - k = -t - (1-t)*k
                have hlin : t * ((k : ℝ) - 1) - k = -t - (1 - t) * (k : ℝ) := by ring
                calc (p : ℝ) ^ (t * ((k : ℝ) - 1) - k)
                    = (p : ℝ) ^ (-t - (1 - t) * (k : ℝ)) := by rw [hlin]
                  _ = (p : ℝ) ^ (-t) * (p : ℝ) ^ (-(1 - t) * (k : ℝ)) := by
                    -- rewrite the subtraction as an addition of negatives so `Real.rpow_add` matches
                    have hadd : -t - (1 - t) * (k : ℝ) = (-t) + (-(1 - t) * (k : ℝ)) := by ring
                    rw [hadd, Real.rpow_add hp_pos]
                  _ = (p : ℝ) ^ (-t) * ((p : ℝ) ^ (-(1 - t))) ^ (k : ℝ) := by
                      congr 1
                      rw [Real.rpow_mul hp_pos.le]
                  _ = (p : ℝ) ^ (-t) * ((p : ℝ) ^ (-(1 - t))) ^ k := by
                      rw [Real.rpow_natCast]

              -- Factor out p^{-t} from the sum and apply geometric series bound
              calc Finset.sum (Finset.Icc 1 (X+1)) (fun k => (p : ℝ) ^ (t * ((k : ℝ) - 1) - k))
                  = Finset.sum (Finset.Icc 1 (X+1)) (fun k =>
                      (p : ℝ) ^ (-t) * ((p : ℝ) ^ (-(1 - t))) ^ k) := by
                    congr 1
                    ext k
                    exact h_exp_geom k

                _ = (p : ℝ) ^ (-t) * Finset.sum (Finset.Icc 1 (X+1)) (fun k => ((p : ℝ) ^ (-(1 - t))) ^ k) := by
                    rw [Finset.mul_sum]

                _ ≤ (p : ℝ) ^ (-t) * 2 := by
                    -- Need to show: ∑_{k=1}^{X+1} r^k ≤ 2 where r = p^{-(1-t)}
                    -- Since p ≥ 3 and 1-t ≥ 1/2, we have p^{1-t} ≥ 3^{1/2} > 1
                    -- So 0 < r = 1/p^{1-t} < 1, and ∑ r^k ≤ r/(1-r) ≤ 2

                    have h_sum_le_2 : Finset.sum (Finset.Icc 1 (X+1)) (fun k => ((p : ℝ) ^ (-(1 - t))) ^ k) ≤ 2 := by
                      -- Set r = p^{-(1-t)}
                      let r := (p : ℝ) ^ (-(1 - t))

                      -- Step 1: Show p^{1-t} ≥ 3^{1/2}
                      -- 補助命題 h_p1mt_ge_sqrt3.
                      --
                      -- この行は、変数 p, t に関する既知の仮定を用いて
                      -- 実数のべき乗 (p : ℝ)^(1 - t) が √3 (Real.sqrt 3) 以上であることを主張する補助的な不等式である。
                      -- 典型的には、べき関数の単調性や対数変換を用いて導かれる不等式であり、
                      -- 例えば p と t が次のような関係を満たすときに成り立つことが期待される：
                      --   p ≥ 3^(1/(2*(1 - t))) すなわち (p : ℝ)^(1 - t) ≥ 3^(1/2) = √3.
                      -- 証明では、既存の下界や仮定（p の下界、t の範囲など）を用いてこの不等式を得ており、
                      -- 以降の評価や比較のための下限として利用される。
                      have h_p1mt_ge_sqrt3 : (p : ℝ) ^ (1 - t) ≥ Real.sqrt 3 := by
                        have h_oneminus_t : 1 - t ≥ 1/2 := by linarith
                        calc (p : ℝ) ^ (1 - t)
                            ≥ (p : ℝ) ^ (1/2 : ℝ) := by
                              apply Real.rpow_le_rpow_of_exponent_le
                              · -- 1 ≤ ↑p
                                norm_cast; omega
                              · -- 1/2 ≤ 1 - t
                                linarith
                          _ ≥ (3 : ℝ) ^ (1/2 : ℝ) := by
                              apply Real.rpow_le_rpow <;> norm_num
                              norm_cast
                          _ = Real.sqrt 3 := by
                            rw [Real.sqrt_eq_rpow]

                      -- Step 2: Show 0 < r < 1
                      have hr_pos : 0 < r := by
                        apply Real.rpow_pos_of_pos
                        exact hp_pos
                      have hr_lt_one : r < 1 := by
                        rw [show r = (p : ℝ) ^ (-(1 - t)) from rfl]
                        rw [Real.rpow_neg hp_pos.le]
                        -- Use inv_lt_one for positive reals: inv_lt_one (Real.rpow_pos_of_pos hp_pos (1 - t)) (Real.one_lt_rpow hp_ge_one (by linarith : 0 < 1 - t))
                        have h_rpow_pos : 0 < (p : ℝ) ^ (1 - t) := Real.rpow_pos_of_pos hp_pos (1 - t)
                        have h_one_lt_rpow : 1 < (p : ℝ) ^ (1 - t) := Real.one_lt_rpow hp_ge_one (by linarith : 0 < 1 - t)
                        -- 1 < (p : ℝ) ^ (1 - t) ならば 0 < (p : ℝ) ^ (1 - t) なので inv_lt_one で 1 / (p : ℝ) ^ (1 - t) < 1
                        have h_inv_lt_one : 1 / (p : ℝ) ^ (1 - t) < 1 := by
                          -- 1 < ↑p ^ (1 - t) より 1 / ↑p ^ (1 - t) < 1 が成り立つ
                          rw [div_lt_one h_rpow_pos]
                          exact h_one_lt_rpow
                        -- r = 1 / (p : ℝ) ^ (1 - t)
                        rw [one_div] at h_inv_lt_one
                        exact h_inv_lt_one

                      -- Step 3: Bound the geometric sum ∑_{k=1}^{X+1} r^k ≤ r/(1-r)
                      -- r が 0 ≤ r < 1 で、X が自然数のときの幾何級数の上界に関する補題。
                      --
                      -- Finset.Icc 1 (X + 1) 上の部分和
                      --   ∑_{k=1}^{X+1} r^k
                      -- は無限和の値で上から抑えられ、具体的には
                      --   ∑_{k=1}^{X+1} r^k ≤ ∑_{k=1}^{∞} r^k = r / (1 - r)
                      -- が成り立つ。証明は有限和の公式
                      --   ∑_{k=1}^{n} r^k = r * (1 - r^{n}) / (1 - r)
                      -- から直ちに得られる（0 ≤ r < 1 のとき右辺は r/(1-r) 以下）。
                      -- この不等式は級数の収束や尾部の評価に用いる。
                      have h_geom_bound : ∑ k ∈ Finset.Icc 1 (X + 1), r ^ k ≤ r / (1 - r) := by
                        -- Geometric series sum formula: ∑_{k=1}^n r^k = r(1-r^n)/(1-r) ≤ r/(1-r) for 0 < r < 1
                        have h_oneminus_pos : 0 < 1 - r := by linarith
                        -- ⊢ ∑ k ∈ Finset.Icc 1 (X + 1), r ^ k ≤ r / (1 - r)
                        have h_geom_sum : ∑ k ∈ Finset.Icc 1 (X + 1), r ^ k
                                    = r * (1 - r^(X + 1)) / (1 - r) := by
                                  -- Use geometric series sum formula
                                  have h_r_ne_1 : r ≠ 1 := by linarith
                                  -- Finset.Icc a b = {x | a ≤ x ∧ x ≤ b}
                                  -- Finset.Ico a (b+1) = {x | a ≤ x ∧ x < b+1} = {x | a ≤ x ∧ x ≤ b}
                                  have h_icc_ico : Finset.Icc 1 (X + 1) = Finset.Ico 1 (X + 2) := by
                                    ext k
                                    simp only [Finset.mem_Icc, Finset.mem_Ico]
                                    omega
                                  rw [h_icc_ico]
                                  -- geom_sum_Ico を使って証明する
                                  rw [geom_sum_Ico h_r_ne_1 (by omega : 1 ≤ X + 2)]
                                  -- (r ^ (X + 2) - r ^ 1) / (r - 1) = r * (1 - r ^ (X + 1)) / (1 - r)
                                  have h_neg : (r ^ (X + 2) - r ^ 1) / (r - 1) = - (r - r ^ (X + 2)) / (r - 1) := by ring
                                  rw [h_neg]
                                  have h_neg2 : - (r - r ^ (X + 2)) / (r - 1) = (r - r ^ (X + 2)) / (1 - r) := by
                                    -- r - 1 = -(1 - r) なので分母を -1 倍して分子の符号を反転できる
                                    have h_r_ne_1' : r - 1 ≠ 0 := by linarith
                                    have h_1mr_ne_0 : 1 - r ≠ 0 := by linarith
                                    rw [neg_div, ← div_neg, neg_sub]
                                  rw [h_neg2]
                                  -- r - r ^ (X + 2) = r * (1 - r ^ (X + 1))
                                  have h_factor : r - r ^ (X + 2) = r * (1 - r ^ (X + 1)) := by
                                    rw [pow_succ]
                                    ring
                                  rw [h_factor]

                        rw [h_geom_sum]
                        -- Since 0 < r < 1, we have 0 < r^(X+1) < 1, so 1 - r^(X+1) ≤ 1
                        have h_rpow_bound : 1 - r^(X + 1) ≤ 1 := by
                          have h_rpow_pos : 0 < r ^ (X + 1 : ℝ) := Real.rpow_pos_of_pos hr_pos (X + 1 : ℝ)
                          have h_rpow_lt_1 : r ^ (X + 1 : ℝ) < 1 := by
                            apply Real.rpow_lt_one hr_pos.le hr_lt_one
                            norm_cast
                            omega
                          -- 1 - r^(X+1) ≤ 1 は r^(X+1) ≥ 0 から明らか
                          -- もし 1 < 1 - r^(X+1) なら、r^(X+1) < 0 となり矛盾
                          by_contra h_not
                          push_neg at h_not
                          -- h_not : 1 < 1 - r ^ (X + 1)
                          -- つまり r ^ (X + 1) < 0
                          have h_neg : r ^ (X + 1 : ℝ) < 0 := by
                            have h_gt : 1 - r ^ (X + 1 : ℝ) > 1 := by exact_mod_cast h_not
                            linarith [h_rpow_pos]
                          -- しかし h_rpow_pos : 0 < r ^ (X + 1) なので矛盾
                          linarith

                        -- r * (1 - r ^ (X + 1)) / (1 - r) ≤ r * 1 / (1 - r) = r / (1 - r)
                        have h_div_pos : 0 < 1 / (1 - r) := by positivity
                        calc r * (1 - r ^ (X + 1)) / (1 - r)
                            = (1 - r ^ (X + 1)) * (r / (1 - r)) := by ring

                          _ ≤ 1 * (r / (1 - r)) := by
                              apply mul_le_mul_of_nonneg_right h_rpow_bound
                              positivity

                          _ = r / (1 - r) := by ring

                      -- Step 4: Show r/(1-r) ≤ 2
                      -- r / (1 - r) ≤ 2 を示す補助命題の説明。
                      --
                      -- 前提として 0 ≤ r < 1（したがって 1 - r > 0）および r ≤ 2/3 が与えられているとする。
                      -- 不等式の両辺に正の数 1 - r を掛けて変形すると
                      --   r ≤ 2(1 - r) = 2 - 2r
                      -- となり、これを整理すると
                      --   3r ≤ 2
                      -- すなわち r ≤ 2/3 が得られる。逆に r ≤ 2/3 を仮定すれば元の不等式 r / (1 - r) ≤ 2 が成り立つ。
                      -- したがって、上記の前提の下で r / (1 - r) ≤ 2 を示すことができる。
                      have h_rat_bound : r / (1 - r) ≤ 2 := by
                        -- From p^{1-t} ≥ √3, we have r = 1/p^{1-t} ≤ 1/√3
                        have h_r_bound : r ≤ 1 / Real.sqrt 3 := by
                                rw [show r = (p : ℝ) ^ (-(1 - t)) from rfl]
                                rw [Real.rpow_neg hp_pos.le]
                                rw [one_div]
                                -- √3 ≤ p^(1-t) が成り立つので，その両辺に p^{-(1-t)} ≥ 0 を掛けて
                                -- √3 * p^{-(1-t)} ≤ 1 を得てから，le_div_iff で逆数の不等号に変換する
                                have h_nonneg : 0 ≤ (p : ℝ) ^ (-(1 - t)) := by
                                  apply Real.rpow_nonneg
                                  norm_cast; omega
                                have h_sqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num : 0 < (3 :ℝ))
                                -- h_p1mt_ge_sqrt3 : (p : ℝ) ^ (1 - t) ≥ √3
                                -- より、(p : ℝ) ^ (-(1 - t)) ≤ (√3)⁻¹
                                rw [← one_div]
                                -- r ≤ 1 / Real.sqrt 3 は h_p1mt_ge_sqrt3 から導ける
                                rw [← one_div]
                                -- 逆数の単調性を使って不等式を変換する
                                have h_sqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
                                have hp1mt_pos : 0 < (p : ℝ) ^ (1 - t) := Real.rpow_pos_of_pos hp_pos (1 - t)
                                rw [one_div_le_one_div hp1mt_pos h_sqrt_pos]
                                exact h_p1mt_ge_sqrt3

                        -- For r ≤ 1/√3, show r/(1-r) ≤ 2
                        -- This follows from: r(1-r) ≤ r → 2r ≤ 2(1-r) → 3r ≤ 2
                        have : r ≤ 1 / Real.sqrt 3 := h_r_bound
                        have hsqrt3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
                        have h3r_le_2 : 3 * r ≤ 2 := by
                          calc 3 * r
                              ≤ 3 * (1 / Real.sqrt 3) := by apply mul_le_mul_of_nonneg_left h_r_bound; norm_num
                            _ = 3 / Real.sqrt 3 := by ring
                            _ = Real.sqrt 3 * Real.sqrt 3 / Real.sqrt 3 := by
                                rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
                            _ = Real.sqrt 3 := by field_simp
                            _ ≤ 2 := by
                                have : Real.sqrt 3 < 2 := by
                                  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
                                  norm_num
                                linarith

                        -- From 3r ≤ 2, show r/(1-r) ≤ 2
                        have h_oneminus_pos : 0 < 1 - r := by linarith
                        rw [ABC.div_le_iff h_oneminus_pos]
                        calc r
                            = 3 * r - 2 * r := by ring
                          _ ≤ 2 - 2 * r := by linarith
                          _ = 2 * (1 - r) := by ring

                      -- Final: Combine all bounds to show ∑ r^k ≤ 2
                      -- r = (p : ℝ) ^ (-(1 - t)) なので、式はそのまま進める
                      exact h_geom_bound.trans h_rat_bound
                    -- Apply mul_le_mul_of_nonneg_left with h_sum_le_2
                    exact mul_le_mul_of_nonneg_left h_sum_le_2 (by apply Real.rpow_nonneg; norm_cast; omega)

                _ ≤ 2 := by
                    -- ⊢ ↑p ^ (-t) * 2 ≤ 2
                    -- p^{-t} ≤ 1 since t > 0 and p > 1, so p^{-t} * 2 ≤ 2
                    have hp_gt_one : 1 < (p : ℝ) := hp_ge_one
                    have h_pt_le_one : (p : ℝ) ^ (-t) ≤ 1 := by
                      -- Prove p^{-t} ≤ 1 by multiplying the inequality 1 ≤ p^t on the right by p^{-t} ≥ 0
                      have h1 : 1 ≤ (p : ℝ) ^ t := Real.one_le_rpow (le_of_lt hp_ge_one) ht0.le
                      have hpos : 0 ≤ (p : ℝ) ^ (-t) := by
                        apply Real.rpow_nonneg
                        norm_cast; omega

                      calc (p : ℝ) ^ (-t)
                          = 1 * (p : ℝ) ^ (-t) := by ring
                        _ ≤ (p : ℝ) ^ t * (p : ℝ) ^ (-t) := mul_le_mul_of_nonneg_right h1 hpos
                        _ = (p : ℝ) ^ (t + -t) := by
                          have : 0 < (p : ℝ) := hp_pos
                          rw [Real.rpow_add this]
                        _ = (p : ℝ) ^ 0 := by rw [add_neg_cancel, Real.rpow_zero, pow_zero]
                        _ = 1 := by rw [pow_zero]
                    linarith









            -- [LEVEL 3] sum2_prod_bound: KEY NEW BOUND (p^t-1)*sum2 ≤ 2(X+1)
            have sum2_prod_bound : ((p : ℝ) ^ t - 1) * sum2 ≤ 2 * (X + 1) := by
              -- [LEVEL 4] Define K := log_p(2X+1)
              let K := Nat.log p (2*X+1)
              have hK_bound : (p : ℕ) ^ K ≤ 2*X+1 := by
                exact Nat.pow_log_le_self p (by omega : 2*X+1 ≠ 0)

              -- [LEVEL 4] Key insight: sum2 counts only k where p^k ≤ 2X+1
              -- For k > K, we have p^k > 2X+1, so indicator = 0
              -- Thus sum2 ≤ ∑_{k=1}^K (p^t)^{k-1}

              have h_sum2_le_K : sum2 ≤ Finset.sum (Finset.Icc 1 K)
                (fun k => (p : ℝ) ^ (t * ((k : ℝ) - 1))) := by
                unfold sum2
                -- sum2 = ∑_{k∈Icc 1 (X+1)} p^{t(k-1)} * indicator{p^k ≤ 2X+1}
                -- Key insight: k > K ⇒ p^k > p^K ≥ 2X+1 ⇒ indicator = 0
                -- So sum2 = ∑_{k∈Icc 1 (X+1), k≤K} p^{t(k-1)}
                -- And this ≤ ∑_{k∈Icc 1 K} p^{t(k-1)} since {k ∈ Icc 1 (X+1) | k≤K} ⊆ Icc 1 K
                have h_indicator_zero_large : ∀ k ∈ Finset.Icc 1 (X+1), k > K →
                    ((p : ℝ) ^ (t * ((k : ℝ) - 1)) * (if (p:ℕ)^k ≤ 2*X+1 then 1 else 0) = 0) := by
                  intro k _ hkgt
                  -- Use upper bound: 2*X+1 < p^(K+1)
                  have hK_upper : 2 * X + 1 < (p : ℕ) ^ (K + 1) := by
                    -- By definition of Nat.log, p^K ≤ 2*X+1 < p^(K+1)
                    have hlog_def := Nat.pow_log_le_self p (by omega : 2*X+1 ≠ 0)
                    have hp_gt_1 : 1 < p := hp.one_lt
                    have hlog_lt := Nat.lt_pow_succ_log_self hp_gt_1 (2 * X + 1)
                    exact hlog_lt
                  -- k > K implies K+1 ≤ k
                  have : K + 1 ≤ k := Nat.succ_le_of_lt hkgt
                  -- monotonicity of pow in exponent for base > 1
                  have : (p : ℕ) ^ (K + 1) ≤ (p : ℕ) ^ k := by
                    apply Nat.pow_le_pow_right
                    · exact hp.pos
                    · exact this
                  have : 2 * X + 1 < (p : ℕ) ^ k := Nat.lt_of_lt_of_le hK_upper this
                  simp [Nat.not_le.mpr this]
                -- Now we show sum2 ≤ ∑_{k∈Icc 1 K} p^{t(k-1)}
                calc ∑ k ∈ Finset.Icc 1 (X+1), (p : ℝ) ^ (t * ((k : ℝ) - 1)) * (if (p:ℕ)^k ≤ 2*X+1 then 1 else 0)
                    ≤ ∑ k ∈ Finset.Icc 1 (X+1), (if k ≤ K then (p : ℝ) ^ (t * ((k : ℝ) - 1)) else 0) := by
                      apply Finset.sum_le_sum
                      intro k hk
                      by_cases hkK : k ≤ K
                      · -- k ≤ K: show indicator = 1
                        have : (p:ℕ)^k ≤ (p:ℕ)^K := Nat.pow_le_pow_right (Nat.Prime.pos hp) hkK
                        have : (p:ℕ)^k ≤ 2*X+1 := Nat.le_trans this hK_bound
                        simp [this, hkK]
                      · -- k > K: show indicator = 0
                        have hgt : k > K := Nat.lt_of_not_le hkK
                        have hzero := h_indicator_zero_large k hk hgt
                        simp only [hzero, ge_iff_le]
                        -- ⊢ 0 ≤ if k ≤ K then ↑p ^ (t * (↑k - 1)) else 0
                        positivity
                  _ = ∑ k ∈ Finset.filter (fun k => k ≤ K) (Finset.Icc 1 (X+1)),
                        (p : ℝ) ^ (t * ((k : ℝ) - 1)) := by
                      classical
                      rw [← Finset.sum_filter]
                  _ ≤ ∑ k ∈ Finset.Icc 1 K, (p : ℝ) ^ (t * ((k : ℝ) - 1)) := by
                      apply Finset.sum_le_sum_of_subset_of_nonneg
                      · intro k hk
                        simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
                        exact ⟨hk.1.1, hk.2⟩
                      · intro k _ _
                        apply Real.rpow_nonneg
                        norm_cast
                        exact hp.pos.le

              -- Key observation: sum2 only has nonzero terms for k ≤ min (X+1) K
              have sum2_eq_minK : sum2 = Finset.sum (Finset.Icc 1 (min (X+1) K))
                                          (fun k => (p : ℝ) ^ (t * ((k : ℝ) - 1)) *
                                                    (if p ^ k ≤ 2*X+1 then 1 else 0)) := by
                -- sum2 defined on Icc 1 (X+1), but indicator = 0 for k > K
                -- So nonzero terms are only for k ∈ Icc 1 (min (X+1) K)
                unfold sum2
                -- Use Finset.sum_subset with indicator = 0 for k > min (X+1) K
                symm
                apply Finset.sum_subset
                · -- Icc 1 (min (X+1) K) ⊆ Icc 1 (X+1)
                  intro k hk
                  simp only [Finset.mem_Icc] at hk ⊢
                  constructor
                  · exact hk.1
                  · calc k ≤ min (X+1) K := hk.2
                         _ ≤ X+1 := Nat.min_le_left (X+1) K
                · -- For k ∈ Icc 1 (X+1) \ Icc 1 (min (X+1) K), the term is 0
                  intro k hk_in hk_not_in
                  simp only [Finset.mem_Icc] at hk_in hk_not_in
                  push_neg at hk_not_in
                  -- k > min (X+1) K, so either k > X+1 or k > K
                  -- Since k ∈ Icc 1 (X+1), we have k ≤ X+1, so k > K
                  have hk_gt_K : K < k := by omega





                  -- So p^k > p^(K+1) > 2X+1, thus indicator = 0
                  -- Key: Nat.log definition gives p^K ≤ 2*X+1 < p^(K+1)
                  -- And k > K means k ≥ K+1, so p^k ≥ p^(K+1) > 2*X+1
                  have hK_upper : 2 * X + 1 < (p : ℕ) ^ (K + 1) := by
                    have hp_gt_1 : 1 < p := hp.one_lt
                    exact Nat.lt_pow_succ_log_self hp_gt_1 (2 * X + 1)
                  have hk_ge_succ : K + 1 ≤ k := Nat.succ_le_of_lt hk_gt_K
                  have hpk_ge_psucc : (p : ℕ) ^ (K + 1) ≤ (p : ℕ) ^ k := by
                    apply Nat.pow_le_pow_right (Nat.Prime.pos hp) hk_ge_succ
                  have : 2*X+1 < p ^ k := Nat.lt_of_lt_of_le hK_upper hpk_ge_psucc





                  simp [Nat.not_le.mpr this]

              -- Also show: sum2 ≤ ∑ k ∈ Icc 1 (min (X+1) K), p^{t(k-1)}
              have h_sum2_le_minK : sum2 ≤ Finset.sum (Finset.Icc 1 (min (X+1) K))
                                            (fun k => (p : ℝ) ^ (t * ((k : ℝ) - 1))) := by
                rw [sum2_eq_minK]
                apply Finset.sum_le_sum
                intro k _
                -- p^{t(k-1)} * (if ... then 1 else 0) ≤ p^{t(k-1)}
                by_cases h : p ^ k ≤ 2*X+1
                · simp [h]
                · simp only [h, ↓reduceIte, mul_zero]
                  apply Real.rpow_nonneg
                  norm_cast
                  exact hp.pos.le

              have h_geom_prod : ((p : ℝ) ^ t - 1) *
                    Finset.sum (Finset.Icc 1 (min (X+1) K))
                      (fun k => (p : ℝ) ^ (t * ((k : ℝ) - 1)))
                  = ((p : ℝ) ^ t) ^ (min (X+1) K) - 1 := by
                -- Rewrite p^{t·(k-1)} = (p^t)^{k-1} using rpow_mul
                have h_rewrite : ∀ k : ℕ, (p : ℝ) ^ (t * ((k : ℝ) - 1)) = ((p : ℝ) ^ t) ^ ((k : ℝ) - 1) := by
                  intro k
                  have hp_nonneg : 0 ≤ (p : ℝ) := by norm_cast; exact hp.pos.le
                  exact Real.rpow_mul hp_nonneg t ((k:ℝ) - 1)
                conv_lhs => arg 2; arg 2; ext k; rw [h_rewrite k]
                -- Now use geom_sum formula for ∑_{k=1}^m r^{k-1}
                let m := min (X+1) K
                let r := (p : ℝ) ^ t
                -- Reindex: ∑_{k=1}^m r^{k-1} = ∑_{j=0}^{m-1} r^j
                by_cases hm : m = 0
                · -- m = 0 の場合、両辺とも 0 になるので一致する
                  -- ⊢ (↑p ^ t - 1) * ∑ k ∈ Finset.Icc 1 (min (X + 1) K), (↑p ^ t) ^ (↑k - 1) = (↑p ^ t) ^ min (X + 1) K - 1
                  have : min (X+1) K = 0 := hm
                  rw [this]
                  have : Finset.Icc 1 0 = ∅ := by
                    ext k
                    simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.notMem_empty]
                  -- ⊢ (↑p ^ t - 1) * ∑ k ∈ Finset.Icc 1 0, (↑p ^ t) ^ (↑k - 1) = (↑p ^ t) ^ 0 - 1
                  rw [this]
                  -- ⊢ (↑p ^ t - 1) * ∑ k ∈ ∅, (↑p ^ t) ^ (↑k - 1) = (↑p ^ t) ^ 0 - 1
                  simp only [Finset.sum_empty, mul_zero, pow_zero, sub_self]
                · -- m ≠ 0 の場合、m ≥ 1 なので reindex が可能
                  -- ⊢ (↑p ^ t - 1) * ∑ k ∈ Finset.Icc 1 (min (X + 1) K), (↑p ^ t) ^ (↑k - 1) = (↑p ^ t) ^ min (X + 1) K - 1
                  -- m = min (X+1) K ≥ 1
                  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
                  have h_reindex : Finset.sum (Finset.Icc 1 m) (fun k => r ^ ((k : ℝ) - 1))
                      = Finset.sum (Finset.range m) (fun j => r ^ (j : ℝ)) := by
                    rw [Finset.sum_bij (fun k hk => k - 1) _ _ _ _]
                    · intro k hk
                      simp only [Finset.mem_Icc] at hk
                      simp only [Finset.mem_range]
                      omega
                    · -- 逆写像 j ↦ j + 1
                      -- ⊢ ∀ (a₁ : ℕ)
                      --   (ha₁ : a₁ ∈ Finset.Icc 1 m) (a₂ : ℕ) (ha₂ : a₂ ∈ Finset.Icc 1 m), (fun k hk ↦ k - 1) a₁ ha₁
                      -- = (fun k hk ↦ k - 1) a₂ ha₂ → a₁
                      -- = a₂
                      intro k hk
                      -- ⊢ ∀ (a₂ : ℕ) (ha₂ : a₂ ∈ Finset.Icc 1 m), (fun k hk ↦ k - 1) k hk = (fun k hk ↦ k - 1) a₂ ha₂ → k = a₂
                      simp only [Finset.mem_Icc] at hk
                      simp only [Finset.mem_Icc, and_imp]
                      -- ⊢ ∀ (a₂ : ℕ), 1 ≤ a₂ → a₂ ≤ m → k - 1 = a₂ - 1 → k = a₂
                      intro j hj heq
                      -- ⊢ k - 1 = j - 1 → k = j
                      -- k, j ∈ Icc 1 m より k ≥ 1, j ≥ 1 なので，両辺に 1 を足して差を消す
                      have hk1 : 1 ≤ k := hk.1
                      have hj1 : 1 ≤ j := hj
                      intro hkj
                      -- k - 1 = j - 1 → k = j は両辺に 1 を足して示す
                      have : k = j := by
                        calc
                          k = (k - 1) + 1 := Eq.symm (Nat.sub_add_cancel hk1)
                          _ = (j - 1) + 1 := by rw [hkj]
                          _ = j := Nat.sub_add_cancel hj1
                      exact this

                    · -- 全射性: ∀ j ∈ range m, ∃ k ∈ Icc 1 m, j = k - 1
                      -- ⊢ ∀ b ∈ Finset.range m, ∃ a, ∃ (ha : a ∈ Finset.Icc 1 m), (fun k hk ↦ k - 1) a ha = b
                      intro j hj
                      simp only [Finset.mem_range] at hj
                      use j + 1
                      constructor
                      · simp only [add_tsub_cancel_right]
                      · -- 証明: ⊢ j + 1 ∈ Finset.Icc 1 m
                        simp only [Finset.mem_Icc]
                        constructor
                        · omega
                        · have : j < m := hj
                          have : j + 1 ≤ m := Nat.succ_le_of_lt this
                          exact this
                    · -- ⊢ ∀ (a : ℕ) (ha : a ∈ Finset.Icc 1 m), r ^ (↑a - 1) = r ^ ↑((fun k hk ↦ k - 1) a ha)
                      intro j hj
                      simp only [Finset.mem_Icc] at hj
                      -- ⊢ r ^ (↑j - 1) = r ^ ↑((fun k hk ↦ k - 1) j hj)
                      -- hj : 1 ≤ j ∧ j ≤ m
                      -- hj✝ : j ∈ Finset.Icc 1 m
                      have hj1 : (fun k hk ↦ k - 1) j hj = j - 1 := rfl
                      rw [hj1]
                      -- ↑j - 1 = ↑(j - 1) を示す
                      rw [Nat.cast_sub hj.1]
                      ring_nf

                  -- Now apply geometric sum formula
                  -- this : (↑p ^ t - 1) * ∑ j ∈ Finset.range m, r ^ j                                 =      (↑p ^ t) ^ min (X + 1) K - 1
                  -- ⊢       ↑p ^ t      * ∑ j ∈ Finset.range m, r ^ ↑j - ∑ j ∈ Finset.range m, r ^ ↑j = -1 + (↑p ^ t) ^ min (1 + X) K

                  rw [h_reindex]
                  have hr_ne : r ≠ 1 := by
                    have : 1 < r := Real.one_lt_rpow (by norm_cast; omega) ht0
                    linarith
                  -- ⊢ (r - 1) * ∑ j ∈ range m, r^↑j = r^m - 1
                  -- Simplify cast: r^↑j = r^j for j : ℕ
                  conv_lhs => arg 2; arg 2; ext j; rw [show r ^ (j : ℝ) = r ^ j by norm_cast]
                  -- Use geom_sum_eq: ∑ i ∈ range n, x^i = (x^n - 1)/(x - 1)
                  have h_geom := geom_sum_eq hr_ne m
                  rw [h_geom]
                  -- ⊢ (r - 1) * ((r^m - 1)/(r - 1)) = r^m - 1
                  have hr_minus_ne : r - 1 ≠ 0 := by
                    have : 1 < r := Real.one_lt_rpow (by norm_cast; omega) ht0
                    linarith
                  field_simp [hr_minus_ne]
                  ring

              -- [LEVEL 4] Final chain: (p^t)^min ≤ (p^t)^K ≤ (p^K)^t ≤ (2X+1)^t ≤ 2(X+1)
              have h_le_pK : ((p : ℝ) ^ t) ^ (min (X+1) K) ≤ ((p : ℝ) ^ t) ^ K := by
                have hr_gt_one : 1 < (p : ℝ) ^ t := by
                  have : 1 < (p : ℝ) := by norm_cast; omega
                  exact Real.one_lt_rpow this ht0
                -- Use calc mode to make intermediate coercions explicit
                calc ((p : ℝ) ^ t) ^ (min (X+1) K)
                    = ((p : ℝ) ^ t) ^ ((min (X+1) K) : ℝ) := by norm_cast
                  _ ≤ ((p : ℝ) ^ t) ^ ((K) : ℝ) := by
                      apply Real.rpow_le_rpow_of_exponent_le hr_gt_one.le
                      norm_cast
                      exact Nat.min_le_right (X+1) K
                  _ = ((p : ℝ) ^ t) ^ K := by norm_cast

              have h_le_2X1t : ((p : ℝ) ^ t) ^ K ≤ (2*X+1 : ℝ) ^ t := by
                -- (p^t)^K = (p^K)^t by rpow_pow_comm
                have : ((p : ℝ) ^ t) ^ K = ((p : ℝ) ^ K) ^ t := by
                  exact Real.rpow_pow_comm (by norm_cast; exact hp.pos.le) t K
                rw [this]
                have hK_real : (p : ℝ) ^ K ≤ (2*X+1 : ℝ) := by exact_mod_cast hK_bound
                apply Real.rpow_le_rpow
                · positivity
                · exact hK_real
                · exact ht0.le

              have h_2X1_bound : (2*X+1 : ℝ) ^ t ≤ 2 * (X + 1) := by
                -- (2X+1)^t ≤ (2(X+1))^t = 2^t (X+1)^t ≤ 2 (X+1) since t ≤ 1
                have h1 : (2*X+1 : ℝ) ≤ 2*(X+1) := by norm_cast; omega
                have h2 : (2*X+1 : ℝ) ^ t ≤ (2*(X+1) : ℝ) ^ t := by
                  apply Real.rpow_le_rpow
                  · norm_cast; omega
                  · exact h1
                  · exact ht0.le
                have h3 : (2*(X+1) : ℝ) ^ t = 2^t * (X+1 : ℝ) ^ t := by
                  rw [mul_comm (2:ℝ) (X+1)]
                  rw [Real.mul_rpow (by norm_cast; omega : 0 ≤ (X+1 : ℝ)) (by norm_num : 0 ≤ (2:ℝ))]
                  ring
                have h4 : (2 : ℝ)^t ≤ 2 := by
                  have hbase : 1 ≤ (2 : ℝ) := by norm_num
                  have hexp : t ≤ 1 := by linarith
                  have : (2:ℝ)^t ≤ (2:ℝ)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
                  simpa using this
                have h5 : (X+1 : ℝ) ^ t ≤ (X+1) := by
                  have hbase : 1 ≤ (X+1 : ℝ) := by norm_cast; omega
                  have hexp : t ≤ 1 := by linarith
                  have : (X+1 : ℝ) ^ t ≤ (X+1 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hbase hexp
                  simpa using this
                calc (2*X+1 : ℝ) ^ t
                    ≤ (2*(X+1) : ℝ) ^ t := h2
                  _ = 2^t * (X+1 : ℝ) ^ t := h3
                  _ ≤ 2 * (X+1 : ℝ) ^ t := by apply mul_le_mul_of_nonneg_right h4 (by positivity)
                  _ ≤ 2 * (X+1) := by apply mul_le_mul_of_nonneg_left h5 (by norm_num)

              calc ((p : ℝ) ^ t - 1) * sum2
                  ≤ ((p : ℝ) ^ t - 1) * Finset.sum (Finset.Icc 1 (min (X+1) K))
                      (fun k => (p : ℝ) ^ (t * ((k : ℝ) - 1))) := by
                    apply mul_le_mul_of_nonneg_left h_sum2_le_minK
                    linarith [Real.one_le_rpow (by norm_cast; omega : (1:ℝ) ≤ (p:ℝ)) ht0.le]
                _ = ((p : ℝ) ^ t) ^ (min (X+1) K) - 1 := h_geom_prod
                _ ≤ ((p : ℝ) ^ t) ^ K - 1 := by linarith [h_le_pK]
                _ ≤ (2*X+1 : ℝ) ^ t - 1 := by linarith [h_le_2X1t]
                _ ≤ (2*X+1 : ℝ) ^ t := by linarith
                _ ≤ 2 * (X + 1) := h_2X1_bound

            -- [LEVEL 3] Combine: (X+1) + (p^t-1)*sum1 + (p^t-1)*sum2 ≤ (1+4p)*(X+1)
            have hp_t_ge_one : (1 : ℝ) ≤ (p : ℝ) ^ t := by
              apply Real.one_le_rpow (by norm_cast; omega : (1:ℝ) ≤ (p:ℝ)) ht0.le
            have hp_t_minus_one_nonneg : 0 ≤ (p : ℝ) ^ t - 1 := by linarith

            calc (X + 1 : ℝ) + ((p : ℝ) ^ t - 1) * (sum1 + sum2)
                = (X + 1) + ((p : ℝ) ^ t - 1) * sum1 + ((p : ℝ) ^ t - 1) * sum2 := by ring
              _ ≤ (X + 1) + ((p : ℝ) ^ t - 1) * ((X + 1) * 2) + 2 * (X + 1) := by
                  apply _root_.add_le_add
                  · apply add_le_add_right
                    exact mul_le_mul_of_nonneg_left sum1_bound hp_t_minus_one_nonneg
                  · exact sum2_prod_bound
              _ = (X + 1) + ((p : ℝ) ^ t - 1) * (2 * (X + 1)) + 2 * (X + 1) := by ring
              _ = (X + 1) + 2 * ((p : ℝ) ^ t - 1) * (X + 1) + 2 * (X + 1) := by ring
              _ = (X + 1) * (1 + 2 * ((p : ℝ) ^ t - 1) + 2) := by ring
              _ = (X + 1) * (1 + 2 * (p : ℝ) ^ t - 2 + 2) := by ring
              _ = (X + 1) * (1 + 2 * (p : ℝ) ^ t) := by ring
              _ ≤ (X + 1) * (1 + 2 * (p : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_cast; omega)
                  have hpow : (p : ℝ) ^ t ≤ (p : ℝ) := by
                    have : (p : ℝ) ^ t ≤ (p : ℝ) ^ (1:ℝ) := by
                      apply Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega : (1:ℝ) ≤ (p:ℝ))
                      linarith
                    simpa using this
                  linarith
              _ ≤ (X + 1) * (1 + 4 * (p : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left _ (by norm_cast; omega)
                  have : 3 ≤ p := by omega
                  have : (2:ℝ) * (p:ℝ) ≤ (4:ℝ) * (p:ℝ) := by linarith
                  linarith
              _ = (1 + 4 * (p : ℝ)) * (X + 1) := by ring

          exact h_goal_expand

      -- [END calc chain for h_sum_bound]

  -- [END LEVEL 2] Prove h_sum_bound: sum ≤ (1 + 4p)(X+1)
  -- ⊢ (∑ n ∈ Finset.Icc 0 X, ↑p ^ (t * (↑↑(padicValNat p (2 * n + 1)) - 2))) / (↑X + 1) ≤ C






  -- この部分は次のことを行い、最終的に定数 `C` との不等式を得ることを示します。

  -- - `padicValNat p (2*n+1) : ℤ` と定義上等しい `V n : ℕ` （および実数へのキャスト）を用いて和の表現を整理します。
  -- - 指数の項に対して `Real.rpow_add` を使い、各項から共通因子 `(p : ℝ) ^ (-2 * t)` をくくり出します（`Finset.mul_sum` と `ring` を利用）。
  --   この際に `hp.pos` によって `p > 0` が保証され、実数の冪の加法性が適用可能になります。
  -- - 既に得ている仮定 `h_sum_bound` を用いて和の平均
  --   (すなわち `(Finset.sum ...)/(X+1)`) が `1 + 4 * (p : ℝ)` を上回らないことを確認し（`ABC.div_le_iff` と `norm_cast; omega` により分母が正であることを扱う）、
  --   それを共通因子 `(p : ℝ) ^ (-2 * t)` と掛け合わせることで全体の上界を得ます（`mul_le_mul_of_nonneg_left` を使用し、左側の因子が非負であることを `Real.rpow_nonneg` で示す）。
  -- - 最後に代数的な計算で順序を入れ替え、定義された定数 `C` と一致させて終了します。

  -- 要点としては、整数・自然数・実数間のキャスト、冪の性質、有限和に対する因数分解、分母が正であることの確認を組み合わせることで
  -- 「(p^{-2t}) × 平均和 ≤ (1 + 4 p) × p^{-2t} = C」を形式的に導出している点です。

  -- Convert from V n : ℕ to padicValNat (equality by definition)
  /-
  有限和の項が定義上一致することによる自明な等式。

  ここでは V n を (padicValNat p (2*n+1) : ℤ) を実数に写したものとして扱っているため、
  各 n に対する被積分関数
    (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))
  は項ごとに
    (p : ℝ) ^ (t * (V n : ℝ))
  と一致する。したがって Finset.Icc 0 X 上の和も定義により一致し、この等式は rfl によって示される。
  -/
  have h_sum_with_int : Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ)))
      = Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * (V n : ℝ))) := by
    rfl

  /-
  与式の各項から共通因子 p^{-2*t} をくくり出す変形の説明。

  指数の線形性 t * (padicValNat p (2*n+1) - 2) = -2*t + t * padicValNat p (2*n+1)
  により各項は p^{-2*t} * p^{t * padicValNat p (2*n+1)} と表せる。したがって
  有限和に対して Finset.mul_sum で定数因子 p^{-2*t} を和の外に出し、ext と ring により
  各項の指数を変形する。実数べき乗の和の法則 Real.rpow_add を適用する際には底 p が正であること
  (hp.pos) を用いており、padicValNat の値は整数であるため適切にキャストして扱っている。
  -/
  have h_factor : (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * ((padicValNat p (2*n+1) : ℤ) - 2)))
      = (p : ℝ) ^ (-2 * t) * (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) := by
    rw [Finset.mul_sum]
    congr 1
    ext n
    have : t * ((padicValNat p (2*n+1) : ℤ) - 2)
         = -2 * t + t * (padicValNat p (2*n+1) : ℤ) := by ring
    rw [this, Real.rpow_add (by norm_cast; exact hp.pos)]

  rw [h_factor, mul_div_assoc]

  /-
  h_ineq の証明についての説明:

  - まず `h_sum_with_int` によって和の表現を適切な形に書き換え，分子が既に得ている上界 `h_sum_bound` と対応するようにする。
  - 次に `ABC.div_le_iff` を用いて不等式
    A / (X + 1) ≤ B
    を分母を払って
    A ≤ B * (X + 1)
    と同値に変換する（この変換には分母が正であることが必要）。
  - 分母 `(X + 1 : ℝ) > 0` の確認は `norm_cast; omega` により，整数から実数へのキャストと簡単な代数的不等式処理で解決する。
  - 最後に，既に得られている `h_sum_bound` を適用することで所望の不等式を導く。

  補足: `padicValNat` の整数から実数へのキャストや累乗に関する整理は `h_sum_with_int` 側で行われているため，この箇所では主に分母の正性の確認と `h_sum_bound` の適用が鍵となる。
  -/
  have h_ineq : (Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) / (X + 1) ≤ (1 + 4 * (p : ℝ)) := by
    rw [h_sum_with_int]
    rw [ABC.div_le_iff]
    · exact h_sum_bound
    · norm_cast; omega

  /-
  この計算は、有限和の平均に対して次の上界を与えることを示す:

    (p : ℝ) ^ (-2 * t) * (Finset.sum (Finset.Icc 0 X) fun n =>
      (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) / (X + 1)
    ≤ (p : ℝ) ^ (-2 * t) * (1 + 4 * (p : ℝ)).

  主な論旨と手順:
  - まず mul_le_mul_of_nonneg_left を適用して、左から乗じる (p : ℝ) ^ (-2 * t) が非負であることにより不等式の向きを保つ。
    この非負性は Real.rpow_nonneg によって示し、型変換や符号関係の処理は norm_cast; omega により正当化する。
  - 次に ring を用いて乗法の順序を整理し、表現を (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t) の形に書き換える。
  - 最後に rfl によりこれを定数 C と同一視する。

  ここで用いている仮定 h_ineq は
    (Finset.sum ...)/(X + 1) ≤ 1 + 4 * (p : ℝ)
  のような和の上界を与えるものであり、上の補題適用により安全に計算を進められる。
  -/
  calc (p : ℝ) ^ (-2 * t) * ((Finset.sum (Finset.Icc 0 X) fun n => (p : ℝ) ^ (t * (padicValNat p (2*n+1) : ℤ))) / (X + 1))

      -- Apply the inequality h_ineq with the nonnegative factor (p : ℝ) ^ (-2 * t)
      ≤ (p : ℝ) ^ (-2 * t) * (1 + 4 * (p : ℝ)) := by
        apply mul_le_mul_of_nonneg_left h_ineq
        apply Real.rpow_nonneg
        norm_cast; omega

    -- Rearrange to match C
    _ = (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t) := by ring

    -- Finish by showing equality to C (QED)
    _ = C := by rfl

/-
      ここで、上記の計算チェーンの各ステップを詳しく説明します。

      - `h_sum_with_int` は、和の各項において `padicValNat p (2*n+1) : ℤ` と定義上等しい `V n : ℕ` を用いて和の表現を整理しています。
        これは定義に基づく単純な書き換えであり、`rfl` によって証明されます。

      - `h_factor` は、指数の項に対して `Real.rpow_add` を使い、各項から共通因子 `(p : ℝ) ^ (-2 * t)` をくくり出しています。
        ここでは `Finset.mul_sum` を利用して和の外に因子を出し、`ring` を使って指数の加法性を示しています。
        この際に `hp.pos` によって `p > 0` が保証され、実数の冪の加法性が適用可能になります。

      - `h_ineq` は、既に得ている仮定 `h_sum_bound` を用いて和の平均
        (すなわち `(Finset.sum ...)/(X+1)`) が `1 + 4 * (p : ℝ)` を上回らないことを確認しています。
        ここでは `ABC.div_le_iff` と `norm_cast; omega` により分母が正であることを扱い、その結果として不等式を導出しています。

      - 最後に、計算チェーン全体で共通因子 `(p : ℝ) ^ (-2 * t)` と掛け合わせることで全体の上界を得ています。
        ここでは `mul_le_mul_of_nonneg_left` を使用し、左側の因子が非負であることを `Real.rpow_nonneg` で示しています。

    最終的な定数 `C` との不等式を得る

      展開された定数 `C` の定義に従って順序を入れ替え
      C = (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t)
      ⊢ (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t) = C
      定義により等しいことを示す
      C の定義: C := (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t)
      したがって、上記の式と一致する
      両辺を展開して確認する
      左辺: (1 + 4 * (p : ℝ)) * (p : ℝ) ^ (-2 * t)
      右辺: C
      両辺は同じ式であるため、等しい
      よって、等式が成り立つことが確認できる
      最終的に、等式を証明するために `rfl` を使用する
-/

end ABC
