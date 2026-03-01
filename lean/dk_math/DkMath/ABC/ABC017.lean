/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC016

#print "file: DkMath.ABC.ABC017"

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

/-- 可算和収束 ⇒ limsup が測度 0（Borel–Cantelli #1 の素朴版）
    標準手順：
    1) `μ (⋃ n≥N, E n) ≤ ∑ n≥N μ(E n)` を使う（measure_iUnion_le）
    2) N→∞ で右辺の尾和→0（summable の定義）
    3) `limsup = ⋂ N ⋃ n≥N E n` なので、連続性＋単調性から 0 -/
theorem borel_cantelli_one
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (E : ℕ → Set Ω) (hmeas : ∀ n, MeasurableSet (E n))
  (hSumm : Summable (fun n => μ.real (E n))) :
  μ.real (limsup E atTop) = 0 := by
  classical
  -- limsup E atTop = ⋂ N, ⋃ n≥N, E n
  have hlim : limsup E atTop = ⋂ N, ⋃ n ∈ {m | N ≤ m}, E n := by
    -- limsup の定義から：⨅ を ⋂ に、⨆ を ⋃ に変換
    simp only [limsup_eq_iInf_iSup_of_nat, Set.iInf_eq_iInter, Set.iSup_eq_iUnion]
    -- ⋃ i, ⋃ (_ : i ≥ N), E i を ⋃ n ∈ {m | N ≤ m}, E n に書き換える
    ext N
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq, ge_iff_le]


  -- 尾和が 0 に収束
  have htail : Tendsto (fun N => ∑' n, μ.real (E (N + n))) atTop (nhds 0) := by
    -- ∑' n, f(N+n) = (∑' n, f n) - (∑ i<N, f i) → 0 as N → ∞
    have h_shift : ∀ N, ∑' n, μ.real (E (N + n)) = ∑' n, μ.real (E n) - ∑ i ∈ Finset.range N, μ.real (E i) := by
      intro N
      rw [← hSumm.sum_add_tsum_nat_add N]
      ring_nf
    simp_rw [h_shift]
    have : Tendsto (fun N => ∑ i ∈ Finset.range N, μ.real (E i)) atTop (nhds (∑' n, μ.real (E n))) := by
      exact hSumm.hasSum.tendsto_sum_nat
    have h_sub : ∑' (n : ℕ), μ.real (E n) - ∑' (n : ℕ), μ.real (E n) = 0 := by ring
    convert Tendsto.sub tendsto_const_nhds this using 1
    rw [h_sub]

  -- 各 N で μ(⋃ n≥N E n) ≤ ∑ μ(E(N+n))
  have hUnion_le : ∀ N : ℕ, μ.real (⋃ n ∈ {m | N ≤ m}, E n) ≤ ∑' n, μ.real (E (N + n)) := by
    intro N
    -- 可算劣加法を使う
    have h_Union : (⋃ n ∈ {m | N ≤ m}, E n) = ⋃ k, E (N + k) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n - N
        convert hx
        omega
      · intro ⟨k, hx⟩
        exact ⟨N + k, by omega, hx⟩
    rw [h_Union]
    -- μ.real = ENNReal.toReal ∘ μ
    unfold Measure.real
    -- 測度の可算劣加法性 + toReal の単調性
    trans (∑' k, μ (E (N + k))).toReal
    · -- μ(⋃ k, E(N+k)) ≤ ∑' k, μ(E(N+k)) を toReal で写す
      apply ENNReal.toReal_mono
      · -- ∑' k, μ(E(N+k)) ≠ ⊤ を示す
        -- 確率測度なので各項 μ(E(N+k)) ≠ ⊤
        -- ENNReal.tsum_eq_top_of_eq_top の対偶：∀ k, f k ≠ ⊤ → ∑' f ≠ ⊤
        -- しかしこの補題は逆方向なので、背理法で示す
        intro h_eq_top
        -- ∑' = ⊤ なら、ある k で μ(E(N+k)) = ⊤ のはず
        have h_exists_top : ∃ k, μ (E (N + k)) = ⊤ := by
          -- ENNReal.tsum_eq_top_of_eq_top: (∃ a, f a = ∞) → ∑' f = ∞
          -- の逆を使いたいが、これは直接使えない
          -- 代わりに、全ての項が < ⊤ なら tsum < ⊤ を示す
          by_contra h_all_ne_top
          push_neg at h_all_ne_top
          -- 各項 ≠ ⊤ なので、tsum_toReal_eq が使える
          have h_eq : (∑' k, μ (E (N + k))).toReal = ∑' k, (μ (E (N + k))).toReal := by
            exact ENNReal.tsum_toReal_eq h_all_ne_top
          -- 左辺は toReal(⊤) = 0
          rw [h_eq_top] at h_eq
          simp only [ENNReal.toReal_top] at h_eq
          -- h_eq : 0 = ∑' k, toReal(...)
          -- これは ∑' toReal = 0 を意味する
          -- ENNReal の世界で考え直す：
          -- もし ∃ k, μ(E(N+k)) > 0 なら、toReal(μ(...)) > 0 となる（≠ ⊤ だから）
          -- すると ∑' toReal > 0 となり h_eq に矛盾
          have h_each_zero : ∀ k, (μ (E (N + k))).toReal = 0 := by
            intro k
            by_contra h_ne_zero
            -- (μ (E (N + k))).toReal ≠ 0
            -- toReal ≠ 0 かつ ≠ ⊤ → 元の値 > 0
            have h_pos : 0 < (μ (E (N + k))).toReal := by
              have : 0 ≤ (μ (E (N + k))).toReal := ENNReal.toReal_nonneg
              obtain hlt | heq := this.lt_or_eq
              · exact hlt
              · exfalso; exact h_ne_zero heq.symm
            -- すると ∑' toReal ≥ toReal(μ(E(N+k))) > 0
            have h_tsum_pos : 0 < ∑' k, (μ (E (N + k))).toReal := by
              -- hSumm : Summable (fun n => μ.real (E n)) から
              -- Summable (fun k => (μ (E (N + k))).toReal) を導出
              have hsum : Summable (fun k => (μ (E (N + k))).toReal) := by
                have : Summable (fun i => μ.real (E (i + N))) :=
                  hSumm.comp_injective (add_left_injective N)
                convert this using 2
                simp only [Measure.real, add_comm]
              calc 0
                  < (μ (E (N + k))).toReal := h_pos
                _ ≤ ∑' j, (μ (E (N + j))).toReal := by
                    apply hsum.le_tsum k
                    intro b hb
                    exact ENNReal.toReal_nonneg
            -- しかし h_eq : 0 = ∑' より矛盾
            linarith [h_eq]
          -- よって ∀ k, μ(E(N+k)) = 0
          have : ∀ k, μ (E (N + k)) = 0 := by
            intro k
            -- toReal = 0 かつ ≠ ⊤ → 元 = 0
            have h_toReal_zero := h_each_zero k
            have h_ne_top := h_all_ne_top k
            rw [ENNReal.toReal_eq_zero_iff] at h_toReal_zero
            exact h_toReal_zero.resolve_right h_ne_top
          -- よって ∑' = 0 であるべきだが、h_eq_top で ⊤ と仮定
          have : ∑' k, μ (E (N + k)) = 0 := by
            rw [ENNReal.tsum_eq_zero]
            exact this
          exact absurd this (ne_of_eq_of_ne h_eq_top (by simp))
        obtain ⟨k, hk⟩ := h_exists_top
        -- しかし確率測度なので measure_ne_top μ _ より矛盾
        exact measure_ne_top μ _ hk

      · exact measure_iUnion_le _
    · -- ENNReal.tsum_toReal_eq を使う
      rw [ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ _)]

  -- 交わりの測度 ≤ inf_N μ(⋃_{n≥N} E n) ≤ inf_N 尾和 → 0
  have hconv : Tendsto (fun N => μ.real (⋃ n ∈ {m | N ≤ m}, E n)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    · exact tendsto_const_nhds
    · exact htail
    · intro N
      exact measureReal_nonneg
    · exact hUnion_le

  -- 交わり = limsup の測度は上の極限 0
  rw [hlim]
  -- 測度の連続性を使う：単調減少列の交わり
  have h_anti : ∀ N M, N ≤ M → (⋃ n ∈ {m | M ≤ m}, E n) ⊆ (⋃ n ∈ {m | N ≤ m}, E n) := by
    intro N M hNM x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    intro ⟨n, hn, hx⟩
    exact ⟨n, le_trans hNM hn, hx⟩

  -- μ.real (⋂ N, ...) = (μ (⋂ N, ...)).toReal
  unfold Measure.real
  -- hconv より μ(⋃_{n≥N} E_n) → 0
  -- tendsto_measure_iInter_atTop を使う
  have h_tend_measure : Tendsto (fun N => μ (⋃ n ∈ {m | N ≤ m}, E n)) atTop (nhds (μ (⋂ N, ⋃ n ∈ {m | N ≤ m}, E n))) := by
    apply tendsto_measure_iInter_atTop
    · intro N
      -- 可測性: ⋃ n ∈ {m | N ≤ m}, E n が可測
      -- これは ⋃ k, E (N + k) と同じ（h_Union で証明済み）
      have h_Union : (⋃ n ∈ {m | N ≤ m}, E n) = ⋃ k, E (N + k) := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        constructor
        · intro ⟨n, hn, hx⟩
          use n - N
          convert hx
          omega
        · intro ⟨k, hx⟩
          exact ⟨N + k, by omega, hx⟩
      rw [h_Union]
      -- MeasurableSet → NullMeasurableSet
      apply NullMeasurableSet.iUnion
      intro k
      exact (hmeas (N + k)).nullMeasurableSet
    · -- 単調減少
      exact fun N M hNM => h_anti N M hNM
    · -- 有限測度
      use 0
      exact measure_ne_top μ _  -- toReal の連続性と組み合わせる
  have : (μ (⋂ N, ⋃ n ∈ {m | N ≤ m}, E n)).toReal = 0 := by
    -- hconv : Tendsto (fun N => μ.real (⋃ n ∈ {m | N ≤ m}, E n)) atTop (nhds 0)
    -- unfold した形では Tendsto (fun N => (μ (⋃ ...)).toReal) atTop (nhds 0)
    -- h_tend_measure : Tendsto (fun N => μ (⋃ ...)) atTop (nhds (μ (⋂ ...)))
    -- toReal は連続なので、0 = lim toReal(μ(⋃)) = toReal(lim μ(⋃)) = toReal(μ(⋂))

    -- hconv を unfold した形に変換
    have hconv' : Tendsto (fun N => (μ (⋃ n ∈ {m | N ≤ m}, E n)).toReal) atTop (nhds 0) := by
      convert hconv using 2

    -- ENNReal.toReal は連続（≠ ⊤ のとき）
    have h_ne_top : μ (⋂ N, ⋃ n ∈ {m | N ≤ m}, E n) ≠ ⊤ := measure_ne_top μ _

    -- toReal の連続性から h_tend_measure を toReal で写す
    have h_toReal_tend : Tendsto (fun N => (μ (⋃ n ∈ {m | N ≤ m}, E n)).toReal) atTop
              (nhds ((μ (⋂ N, ⋃ n ∈ {m | N ≤ m}, E n)).toReal)) :=
      (ENNReal.tendsto_toReal h_ne_top).comp h_tend_measure

    -- 極限の一意性から 0 = (μ(⋂...)).toReal
    exact tendsto_nhds_unique h_toReal_tend hconv'
  exact this


/-- 尾確率の可算和収束から、deterministic に eventually `¬is_bad_a` が成り立つ。

    実装戦略：
    A) Summable ⇒ tendsto 0 ⇒ eventually C * exp(...) < 1
    B) eventually n ≥ n0 と合流させて分岐を消す
    C) Deterministic 性を使って矛盾法で ¬is_bad_a を導く

    注：確率空間 Ω は任意に取れるので、結論は確率空間によらない。
-/
theorem eventually_not_is_bad_adjacent (δ : ℝ) (hδ : 0 < δ) :
  ∀ᶠ n in atTop, ¬is_bad_a δ (2*n+1) (n+1) n := by
  classical
  -- 任意確率空間で良いが、ここでは Unit 空間に固定
  let Ω := Unit
  let μ : Measure Ω := Measure.dirac ()
  haveI : IsProbabilityMeasure μ := by infer_instance

  -- 尾確率の上界（既存 API を利用）
  obtain ⟨C, c, β, n0, hC_pos, hc_pos, hβ_gt, hBound⟩ :=
    tail_prob_is_bad_adjacent μ δ hδ
  -- hBound : ∀ n ≥ n0, μ.real (BadAdj δ n Ω) ≤ C * Real.exp (- c * (Real.log n) ^ β)

  --------------------------------------------------------------------------------
  -- Step A: exp(-c (log n)^β) → 0 なので C倍しても 0 に収束。
  -- Summable ⇒ tendsto 0 を使って "やがて < 1" を取る。
  --------------------------------------------------------------------------------
  have hsum : Summable (fun n : ℕ => if n = 0 then 0 else Real.exp (-(c * (Real.log n) ^ β))) :=
    summable_exp_neg_log_pow c β hc_pos hβ_gt

  -- Summable → 0 へ収束
  have htend0 : Tendsto (fun n : ℕ => if n = 0 then (0:ℝ) else Real.exp (-(c * (Real.log n) ^ β))) atTop (nhds 0) := by
    exact hsum.tendsto_atTop_zero

  -- C を掛けても 0 へ収束
  have htend0_scaled : Tendsto (fun n : ℕ => C * (if n = 0 then (0:ℝ) else Real.exp (-(c * (Real.log n) ^ β)))) atTop (nhds 0) := by
    have : (0:ℝ) = C * 0 := by ring
    rw [this]
    refine Filter.Tendsto.congr ?_ (Tendsto.const_mul C htend0)
    intro n
    cases n <;> ring_nf

  -- よって、十分大きい n で `C * exp(...) < 1` が成り立つ
  have h_bound_small : ∀ᶠ n : ℕ in atTop,
      C * Real.exp (- c * (Real.log n) ^ β) < 1 := by
    -- 0 に収束する関数は任意の正の ε（ここでは 1）より小さくなる
    rw [Metric.tendsto_atTop] at htend0_scaled
    have h1 : 0 < (1 : ℝ) := by norm_num
    obtain ⟨N, hN⟩ := htend0_scaled 1 h1
    -- N と n0 の両方より大きい値から開始すれば n=0 は起こらない
    refine Filter.eventually_atTop.2 ⟨max N (n0 + 1), fun n hn => ?_⟩
    have hn_ge_N : n ≥ N := le_of_max_le_left hn
    have hn_ge_1 : n ≥ 1 := by
      have : n ≥ n0 + 1 := le_of_max_le_right hn
      omega
    have := hN n hn_ge_N
    -- dist x 0 = |x| for real numbers
    rw [Real.dist_eq] at this
    simp only [sub_zero] at this
    -- n ≥ 1 なので if は else になる
    have hn_ne_zero : n ≠ 0 := by omega
    have hpos : 0 ≤ C * Real.exp (- c * (Real.log n) ^ β) := by
      apply mul_nonneg (le_of_lt hC_pos)
      exact Real.exp_nonneg _
    -- this : |C * (if n=0 then 0 else exp(...))| < 1
    -- n ≠ 0 より if は else
    simp only [hn_ne_zero, ↓reduceIte, abs_mul, abs_exp] at this
    -- this : |C| * exp(-(c*...)) < 1
    -- C > 0 より |C| = C
    rw [abs_of_pos hC_pos] at this
    -- -(c*x) = -c*x は自明
    convert this using 2
    ring_nf

  --------------------------------------------------------------------------------
  -- Step B: "やがて n ≥ n0" も同時に確保しておく（分岐を消す）
  --------------------------------------------------------------------------------
  have h_ge_n0 : ∀ᶠ n : ℕ in atTop, n ≥ n0 :=
    Filter.eventually_atTop.2 ⟨n0, by intro n hn; exact hn⟩

  -- 2つの eventually を束ねる
  have h_small_and_ge : ∀ᶠ n : ℕ in atTop,
      C * Real.exp (- c * (Real.log n) ^ β) < 1 ∧ n ≥ n0 :=
    h_bound_small.and h_ge_n0

  --------------------------------------------------------------------------------
  -- Step C: 各 n について、deterministic な矛盾法で `¬ is_bad_a ...` を導く
  --------------------------------------------------------------------------------
  refine h_small_and_ge.mono ?_
  intro n hpair
  obtain ⟨h_small, hn⟩ := hpair

  -- もし bad なら、BadAdj δ n Ω = univ で測度が 1 になる
  by_contra h_bad

  have h_univ : BadAdj δ n Ω = Set.univ := by
    ext ω; simp [BadAdj, h_bad]

  have h_meas_one : μ.real (BadAdj δ n Ω) = 1 := by
    rw [h_univ]
    rw [prob_real_univ μ]

  -- 一方、尾確率上界より μ(BadAdj) ≤ C * exp(...)
  -- hBound が直接 log n で与えられているので、そのまま使う
  have h_upper : μ.real (BadAdj δ n Ω) ≤ C * Real.exp (- c * (Real.log n) ^ β) := by
    exact hBound n hn

  have : μ.real (BadAdj δ n Ω) < 1 :=
    lt_of_le_of_lt h_upper h_small

  -- 1 = μ(BadAdj) < 1 の矛盾
  rw [h_meas_one] at this
  exact this.false

end ABC
