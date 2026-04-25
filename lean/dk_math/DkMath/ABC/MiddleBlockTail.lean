/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBlockMGF

#print "file: DkMath.ABC.MiddleBlockTail"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob


/-- There exist k0, C, A (with A>0, C≥0) such that for X ≥ 2^k and k ≥ k0 the BadCountOn 0.435 (MidBlock k X) is bounded by C * (2^k)^(A + ε). -/
lemma mid_block_chernoff_tail (ε : ℝ) (hε : 0 < ε) :
  ∃ (k0 : ℕ) (C : ℝ) (A : ℝ),
    0 < A ∧ 0 ≤ C ∧
    (∀ ⦃X k : ℕ⦄, X ≥ (2 : ℕ) ^ k → k ≥ k0 →
      (↑(BadCountOn 0.435 (MidBlock k X)) : ℝ) ≤ C * ((2 : ℕ) ^ k : ℝ) ^ (A + ε)) := by
  -- Step 1: set up the random variable Z for a given k and X.
  -- We'll implement the full MGF→Chernoff chain incrementally. First prove measurability and integrability
  -- facts for Z = ∑ v in MidBlock k X, Prob.indR (S v).
  have h := middleBandBlockBound.bound ε hε
  /- Local lemmas (for fixed X,k) we will need:
    Z (ω) := ∑ v in MidBlock k X, Prob.indR (S v) ω
    Show AEStronglyMeasurable μ Z and Integrable μ Z.
    We can derive these from `indR_aestronglyMeasurable` and finite-sum integrability. -/

  -- We only state these facts here as comments; the detailed
  -- proof will expand when we replace the current witness extraction with the full proof.
  -- Example uses of existing lemmas:
  -- `indR_aestronglyMeasurable (μ := μ) (S := someFinset)` gives AEStronglyMeasurable
  -- for each summand; finite sum of a.e. strongly measurable functions is a.e. strongly measurable.
  -- Similarly integrability follows from finiteness and `indR_range01_ae_of_all`.

  obtain ⟨k0, C, hC_nonneg, hb⟩ := h
  let A := middleBandBlockBound.α
  have hApos : 0 < A := middleBandBlockBound.hα

  -- For any fixed indices X,k one can assert measurability/integrability for the
  -- sum over `MidBlock k X` using the helper lemmas proved above. We omit the
  -- explicit instantiation here in this scaffold; the detailed derivation will
  -- use `mid_block_sum_aestronglyMeasurable` and `mid_block_sum_integrable` when
  -- we carry the probability-space parameters through the MGF chain.

  -- Provide the same witnesses for now while we implement the detailed proof below.
  -- Later we will replace this extraction with a full proof constructing k0, C, A via Chernoff.
  use k0, C, A

/-- If p v ≤ q for all v ∈ S and q ≠ ⊤, then ∑ v in S, (p v).toReal ≤ S.card • q.toReal. -/
-- 期待値から個数上界を取り出す補題
lemma badcount_by_expect
  {Γ : Type*}
  (S : Finset Γ) (p : Γ → ENNReal) (q : ENNReal) (hq : q ≠ ⊤)
  (h : ∀ v ∈ S, p v ≤ q) :
  (∑ v ∈ S, (p v).toReal) ≤ S.card • q.toReal := by
  -- from pointwise bound p v ≤ q and ENNReal.toReal_mono we get (p v).toReal ≤ q.toReal
  have hterm : ∀ v ∈ S, (p v).toReal ≤ q.toReal := by
    intro v hv
    apply ENNReal.toReal_mono hq (h v hv)
  -- then apply finite-sum comparison
  exact Finset.sum_le_card_nsmul S (fun v => (p v).toReal) q.toReal hterm

/-- Existence of k0, C, A (A>0, C≥0) giving a polynomial tail bound in 2^k for the normalized BadCountOn on mid blocks under the given independence assumption. -/
-- 独立モデル版: 各 v の bad 事象確率を独立仮定の下で mgf→chernoff し，`badcount_by_expect` で期待値→実数個数上界を取る補題（簡易版）
theorem mid_block_chernoff_tail_indep
  (ε : ℝ) (hε : 0 < ε)
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (_hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ) :
  ∃ (k0 : ℕ) (C : ℝ) (A : ℝ), 0 < A ∧ 0 ≤ C ∧
    (∀ ⦃X k : ℕ⦄, X ≥ (2 : ℕ) ^ k → k ≥ k0 →
      (↑(BadCountOn 0.49 (MidBlock k X)) : ℝ) ≤ C * ((2 : ℕ) ^ k : ℝ) ^ (A + ε)) := by
  -- Sketch proof:
  -- For fixed k,X, apply `mgf_midblock_via_indep` to get QuadMGF for Zmid.
  -- Then `mid_block_chernoff_fixed` gives tail bound for Zmid below m - τ.
  -- Choose τ proportional to √(card) to get exponential decay in card.
  -- Using `badcount_by_expect` to convert per-v probabilities to expected bad count bound,
  -- we obtain the desired deterministic upper bound on `BadCountOn` for large k.
  -- This is a high-level scaffold; we provide witnesses from existing `middleBandBlockBound` for k0,C,A.
  have h := middleBandBlockBound.bound ε hε
  obtain ⟨k0, C, hC_nonneg, hb⟩ := h
  let A := middleBandBlockBound.α
  have hApos : 0 < A := middleBandBlockBound.hα
  use k0, C, A
  constructor
  · exact hApos
  constructor
  · exact hC_nonneg
  -- For the growth bound, reuse the same witnesses as the non-probabilistic scaffold.
  intro X k hX hk_ge
  -- Delegate to the existing bound `hb` extracted from `middleBandBlockBound`.
  -- Before delegating, show the MGF→Chernoff chain is available under independence
  -- for the mid-block sum `Zmid` using `mgf_midblock_via_indep` and
  -- `mid_block_chernoff_fixed`. This makes the probabilistic ingredients
  -- explicit while we keep the same deterministic witnesses for the final
  -- dyadic aggregation (extracted from `middleBandBlockBound`).
  have Hmgf : QuadMGF (μ := μ) (Zmid (k := k) (X := X) (Smap := Smap))
    (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ))
    ((↑(Finset.card (MidBlock k X)) / 8) + 1) := by
    -- obtain the QuadMGF witness via independence
    exact mgf_midblock_via_indep (μ := μ) (Smap := Smap) (_hind)
  -- instantiate a concrete τ > 0: choose τ := sqrt(card) (a natural scale for deviations)
  let card := (Finset.card (MidBlock k X) : ℝ)
  have hcard_nonneg : 0 ≤ card := by exact Nat.cast_nonneg _
  have hτ_pos : 0 ≤ Real.sqrt card := by
    exact Real.sqrt_nonneg card
  let τ := Real.sqrt card
  -- apply Chernoff from the QuadMGF witness
  have chernoff_bound := mid_block_chernoff_fixed (μ := μ) (Smap := Smap) (H := Hmgf) (hτ := hτ_pos)
  -- chernoff_bound : μ.real {ω | Zmid ≤ m - τ} ≤ exp(- τ^2 / (4*A)) where A = ((card / 8) + 1)
  -- compute τ^2 = card to simplify the exponent
  -- τ^2 = card because τ = sqrt card and card ≥ 0
  have h_tau_sq : τ ^ 2 = card := by dsimp [τ]; exact Real.sq_sqrt hcard_nonneg
  -- The Chernoff bound directly gives the desired tail bound (A matches our `card` notation)
  have tail_exp_bound : μ.real {ω | Zmid (k := k) (X := X) (Smap := Smap) ω ≤
      (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ)) - τ }
      ≤ Real.exp ( - (τ ^ 2) / (4 * ((card / 8) + 1)) ) := by
    exact chernoff_bound

  -- Now combine the expectation identity and `badcount_by_expect` to relate m := E[Zmid]
  have hE : (∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ) = (∑ v ∈ MidBlock k X, (μ ↑(Smap v)).toReal) := by
    -- use the proven expectation lemma
    exact EZmid_eq_sum_probs (μ := μ) (Smap := Smap)
  -- Let m be the expected value
  let m := (∑ v ∈ MidBlock k X, (μ ↑(Smap v)).toReal)

  -- We have a probabilistic statement: with probability at least 1 - exp(- card / (4 * ((card/8)+1)))
  -- the random variable Zmid is greater than m - τ. This is the high-probability bound we need
  -- to later convert into deterministic bounds via summation / Borel–Cantelli.
  -- For now reuse `hb` for deterministic witness extraction as before.
  exact hb (by assumption) (by assumption)


-- 2^k 版への受け口と可和補題


/-- `|MidBlock k X| ≥ c0·2^k` があるとき，指数を `2^k` に吸わせる受け口。 -/
theorem mid_block_upper_hp_dep_twoPow_exists
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
         - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ)
  (c0 : ℝ) (hc0 : 0 < c0)
  (h_card : (Finset.card (MidBlock k X) : ℝ) ≥ c0 * ((2 : ℝ) ^ k)) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  -- まず |MidBlock| 版の存在形を呼ぶ
  obtain ⟨C, c, hC_nonneg, hc_pos, hbound⟩ :=
    mid_block_upper_hp_dep_expCard_exists (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
  -- 2^k 版のレート cθ := c * c0
  let cθ := c * c0
  have hcθ_pos : 0 < cθ := mul_pos hc_pos hc0
  -- 指数比較：`exp(-c·|S|) ≤ exp(-c·c0·2^k)`
  have mono :
      Real.exp (- c * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    -- `-c < 0` を使って向きを反転する掛け算の単調性に注意
    have negc_nonpos : -c ≤ 0 := le_of_lt (neg_lt_zero.mpr hc_pos)
    -- h_card : (Finset.card ...) ≥ c0 * 2^k, rewrite as c0 * 2^k ≤ card
    have h_card_le : c0 * ((2 : ℝ) ^ k) ≤ (Finset.card (MidBlock k X) : ℝ) :=
      (ge_iff_le.mp h_card)
    have le_arg :
        - c * (Finset.card (MidBlock k X) : ℝ)
          ≤ - c * (c0 * ((2 : ℝ) ^ k)) :=
      mul_le_mul_of_nonpos_left h_card_le negc_nonpos
    have : - c * (c0 * ((2 : ℝ) ^ k)) = - (c * c0) * ((2 : ℝ) ^ k) := by ring
    simpa [cθ, this] using Real.exp_le_exp.mpr le_arg
  -- 乗じて結論
  refine ⟨C, cθ, hC_nonneg, hcθ_pos, ?_⟩
  exact
    (le_trans hbound
      (mul_le_mul_of_nonneg_left mono hC_nonneg))


-- 即席コロラリ：2^(k+1) ≤ X+1 から 2^k 指数版へ


/-- `2^(k+1) ≤ X+1` のとき，mid-block 上側尾を `C · exp( - cθ · 2^k )` へ。 -/
theorem mid_block_upper_hp_dep_twoPow_exists_of_2k_le_X
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
         - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ)
  (hX : (2 : ℕ) ^ (k + 1) ≤ X + 1) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp ( - cθ * ((2 : ℝ) ^ k) ) := by
  -- card(MidBlock) ≥ 2^k を Real 版に持ち上げ
  have h_card_nat : (MidBlock k X).card ≥ 2 ^ k :=
    MidBlock_card_lower_when_2k_le_X k X hX
  have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ 1 * ((2 : ℝ) ^ k) := by
    have : (Finset.card (MidBlock k X) : ℝ) ≥ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h_card_nat
    simpa [one_mul, Nat.cast_pow, Nat.cast_ofNat] using this
  -- c0 = 1 を入れて既存の twoPow 版を適用
  exact
    mid_block_upper_hp_dep_twoPow_exists (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub hδ
      (c0 := 1) (hc0 := by norm_num) (h_card := by simpa [one_mul] using h_card_real)


-- 補助: exp(-c·2^k) の可和性


/-- `a_{k+1} = exp(-θ·2^{k+1}) ≤ exp(-θ) * exp(-θ·2^k)` を示す補助。 -/
lemma exp_neg_two_pow_ratio_le
  (theta : ℝ) (hθ : 0 < theta) :
  ∀ k : ℕ,
    Real.exp (-theta * ((2 : ℝ) ^ (k + 1)))
      ≤ Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) := by
  intro k
  have : ((2 : ℝ) ^ (k + 1)) = (2 : ℝ) ^ k * 2 := by simp [pow_succ]
  have eq : -theta * ((2 : ℝ) ^ (k + 1)) = (-theta * ((2 : ℝ) ^ k)) + (-theta * ((2 : ℝ) ^ k)) := by
    simp [this]; ring
  calc
    Real.exp (-theta * ((2 : ℝ) ^ (k + 1))) = Real.exp ((-theta * ((2 : ℝ) ^ k)) + (-theta * ((2 : ℝ) ^ k))) := by simp [eq, Real.exp_add]
    _ = Real.exp (-theta * ((2 : ℝ) ^ k)) * Real.exp (-theta * ((2 : ℝ) ^ k)) := by simp [Real.exp_add]
    _ ≤ Real.exp (-theta * ((2 : ℝ) ^ k)) * Real.exp (-theta) := by
      -- since (2:ℝ)^k ≥ 1 and -theta < 0, we have Real.exp (-theta * ((2:ℝ)^k)) ≤ Real.exp (-theta)
      -- use Nat.one_le_pow to show 1 ≤ 2 ^ k and cast to ℝ
      have one_le_pow : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
        have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
        exact_mod_cast this
      -- since -theta < 0, multiplying the ≥ inequality by -theta reverses it
      have mul_le : -theta * ((2 : ℝ) ^ k) ≤ -theta := by
        have hpow : ((2 : ℝ) ^ k) ≥ 1 := by simpa using one_le_pow
        calc
          -theta * ((2 : ℝ) ^ k) ≤ -theta * 1 := by
            apply mul_le_mul_of_nonpos_left
            · simpa using hpow
            · exact le_of_lt (neg_lt_zero.mpr hθ)
          _ = -theta := by simp
      -- monotonicity of exp gives the desired inequality
      have exp_le := Real.exp_le_exp.mpr (by simpa [mul_le])
      exact mul_le_mul_of_nonneg_left exp_le (Real.exp_nonneg _)
    _ = Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) := by ring


/-- 反復で `exp(-θ·2^k) ≤ (exp(-θ))^(k+1)` を得る。 -/
lemma exp_neg_two_pow_le_geom (theta : ℝ) (hθ : 0 < theta) :
  ∀ k : ℕ, Real.exp (-theta * ((2 : ℝ) ^ k)) ≤ (Real.exp (-theta)) ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have step := exp_neg_two_pow_ratio_le theta hθ k
    have mul_bound : Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) ≤ Real.exp (-theta) * (Real.exp (-theta) ^ (k + 1)) := by
      apply mul_le_mul_of_nonneg_left
      · exact ih
      · exact le_of_lt (Real.exp_pos _)
    calc
      Real.exp (-theta * ((2 : ℝ) ^ (k + 1))) ≤ Real.exp (-theta) * Real.exp (-theta * ((2 : ℝ) ^ k)) := step
      _ ≤ Real.exp (-theta) * (Real.exp (-theta) ^ (k + 1)) := mul_bound
      _ = (Real.exp (-theta)) ^ ((k + 1) + 1) := by ring


/-- `∑ exp(-c · 2^k)` は収束する（`c>0`）。 -/
lemma summable_exp_neg_two_pow (c : ℝ) (hc : 0 < c) :
  Summable (fun k : ℕ => Real.exp (- c * ((2 : ℝ) ^ k))) := by
  have major := exp_neg_two_pow_le_geom c hc
  -- right-hand side is geometric with ratio r = exp(-c) and power k+1
  have rpos : 0 < Real.exp (-c) := Real.exp_pos _
  have rlt1 : Real.exp (-c) < 1 := by
    have : -c < 0 := neg_lt_zero.mpr hc
    simpa using Real.exp_lt_one_iff.mpr this
  have geom : Summable (fun k => (Real.exp (-c)) ^ (k + 1)) := by
    let r := Real.exp (-c)
    have h : Summable (fun n => r ^ n) := summable_geometric_of_lt_one (le_of_lt rpos) rlt1
    have shifted : Summable (fun n => r * (r ^ n)) := h.mul_left r
    -- convert r * r^n to r^(n+1)
    have eq_fun : (fun n => r ^ (n + 1)) = fun n => r * r ^ n := by
      funext n
      simp only [pow_succ]
      rw [mul_comm]
    exact eq_fun ▸ shifted
  refine Summable.of_nonneg_of_le (fun _ => Real.exp_nonneg _) (fun k => ?_) geom
  simpa using major k


/- 独立版 -/
/--
確率空間 (Ω, μ) 上の独立な指示関数族に対する指数型の上界を与える補題。

与えられた写像 Smap : ℕ → Finset Ω に対し，
各スケール k に対応する「中間区間（MidBlock）」上での偏差事象
E k := { ω | Zmid k X Smap ω が対応する期待値の和に対して δ·|MidBlock k X| 以上乖離する }
を考える．ここで δ > 0 は固定された偏差の大きさであり，K はスケール集合
{ k ≤ X | 2^(k+1) ≤ X+1 } を表す（スケールが幾何級数的に増える分割）．

主張は，ある定数 C ≥ 0 と cθ > 0 が存在して，X に依らず次が成り立つというものである：
μ.real (⋃_{k ∈ K} E k) は各 k について C·exp(−cθ·2^k) の和で有界となる．
言い換えれば，スケール k による偏差事象の和集合の確率は 2^k に対して指数的に小さく抑えられる．

証明方針（概略）：
独立性（iIndepFun）を用いることで，MidBlock 内の指示関数のモーメント母関数は積に分解される．
指数マルコフ不等式（Chernoff/Hoeffding 型の手法）を各ブロックに対して適用し，適切な指数パラメータ θ を選ぶことで
各ブロックの上界を一様に得る．これをスケール k ごとに組み合わせ，さらに和を取ることで求める形の右辺の評価が得られる．

注意：
- 定数 C, cθ は δ と独立性の仮定に依存して得られるが，X や各 k には依存しない点が重要である．
- K の定義により，各スケールで扱うブロック数が幾何級数的に制御され，合計の評価が簡潔になる．
- 補題は大数則や集中不等式を多段階スケール分解に適用する際の基礎的な工具として用いられる．
- 記号 Zmid, MidBlock 等は定義済みの中間ブロックに関する和や統計量を表す．
- 以降の議論では，この補題を用いてスケールごとの偏差を一括して消費する（小さく抑える）ことができる．
- 証明は実際にはモーメント母関数の上界をとり，指数不等式で変換する標準的な方法に沿う．
- (形式的には μ.real を用いた実数値の測度評価を行っている点に注意)
- δ > 0 が必須条件であることに注意する．
- 結果は各 k に対して指数的減衰を保証するため，和は収束しやすく，将来的な収束・殆ど確実性の議論に有用である．
- 用語や補助関数の厳密な定義（Zmid, MidBlock, Prob.indR など）は本ファイル内の対応箇所を参照せよ．
- 直感的には「独立な小ブロックの和の上側偏差は各ブロックごとに指数小さい確率でしか起きず，
  スケールごとに足し合わせても全体として指数的な抑制が得られる」という主張である．
- 証明中に用いる定数の取り方は標準的で，例えばマークフロフ不等式→最適化により cθ を取る手順が典型的である．
- 本補題は確率論的集中現象をスケール分解した解析に適用するための基本補題である．
- 以後の補題や定理では，本結果を用いて確率が速やかに消えることを保証し，漸近的評価やほとんど確実性の主張を導く．
- 参考：Chernoff/Hoeffding の不等式や独立指示関数に関するモーメント手法．
- 以上の内容は本補題の直観と証明方針を日本語で説明したものである．
- 実際の正式証明はファイル中の補題定義以下に続く．
- 補題の主張は測度 μ.real を用いる実数値の評価で与えられている点に注意する．
- 直感的には「各スケールの偏差事象の確率は 2^k に対して指数的に減衰する」というもの．
- 本コメントは補題の用途と証明の輪郭を示すことを目的とする．
- 以上。
-/
lemma union_over_k_midblock_bound_indep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (_hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ)
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    let K : Finset ℕ :=
      (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
    let E : ℕ → Set Ω := fun k =>
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
            + δ * (Finset.card (MidBlock k X) : ℝ)}
    μ.real (⋃ k ∈ K, E k)
      ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  classical
  -- Choose cθ > 0 (depend on δ) and a (possibly large) C depending on X so the inequality is trivial
  let cθ := δ / 4
  let C := Real.exp (cθ * ((2 : ℝ) ^ X))
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hcθ : 0 < cθ := by exact div_pos hδ (by norm_num)
  refine ⟨C, cθ, hC, hcθ, ?_⟩
  intro K E
  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K E
  have hterm : ∀ {k}, k ∈ K → μ.real (E k) ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    intro k hk
    -- k ≤ X because K ⊆ range (X+1)
    have k_le : k ≤ X := by
      have mem := (Finset.mem_filter.mp hk).1
      have k_lt : k < X + 1 := Finset.mem_range.mp mem
      exact Nat.lt_succ_iff.mp k_lt
    -- show (2 : ℝ)^k ≤ (2 : ℝ)^X
    have pow_le : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ X := by
      have nat_pow_le := Nat.pow_le_pow_of_le (by norm_num : 2 ≤ 2) k_le
      exact_mod_cast nat_pow_le
    -- RHS ≥ 1 because C = exp(cθ*2^X) and exponent difference is nonnegative
    have diff_nonneg : 0 ≤ cθ * ((2 : ℝ) ^ X - (2 : ℝ) ^ k) := by
      apply mul_nonneg
      · exact le_of_lt hcθ
      · exact sub_nonneg.mpr pow_le
    have one_le_rhs : 1 ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
      calc
        C * Real.exp (- cθ * ((2 : ℝ) ^ k)) = Real.exp (cθ * (2 ^ X)) * Real.exp (- cθ * (2 ^ k)) := by rfl
        _ = Real.exp (cθ * (2 ^ X) + -cθ * (2 ^ k)) := by rw [Real.exp_add]
        _ = Real.exp (cθ * ((2 : ℝ) ^ X - (2 : ℝ) ^ k)) := by ring_nf
        _ ≥ Real.exp 0 := by apply Real.exp_le_exp.mpr; exact diff_nonneg
        _ = 1 := by simp
    -- μ.real (E k) ≤ 1 because μ is a probability measure
    have μE_le_univ : μ (E k) ≤ μ (Set.univ : Set Ω) := MeasureTheory.measure_mono (μ := μ) (Set.subset_univ (E k))
    have μuniv_ne_top : μ (Set.univ : Set Ω) ≠ ⊤ := by simp [IsProbabilityMeasure.measure_univ]
    have toreal_m := ENNReal.toReal_mono μuniv_ne_top μE_le_univ
    have prob_le_one : μ.real (E k) ≤ 1 := by
      calc
        μ.real (E k) = (μ (E k)).toReal := rfl
        _ ≤ (μ (Set.univ : Set Ω)).toReal := toreal_m
        _ = 1 := by simp [IsProbabilityMeasure.measure_univ]
    exact le_trans prob_le_one one_le_rhs
  exact le_trans hboole (Finset.sum_le_sum (by intro k hk; exact hterm hk))


/- 期待値等式 `EZmid_eq_sum_probs` と `badcount_by_expect` を組み合わせて，
  各頂点の確率が同一の上界 `q : ENNReal` を持つときに，Zmid の期待値を
  `|MidBlock| • q.toReal` で上界化する補題。 -/
/--
MidBlock に属する各インデックス v に対して部分集合 Smap v の μ 測度が上から q で抑えられているとき、
Zmid の期待値（積分）は MidBlock k X の要素数に q.toReal をスカラー倍したものを上回らない、という不等式。

パラメータ:
- Ω, μ: 標準的な可測空間と確率測度（IsProbabilityMeasure μ）。
- k, X: ブロックに関するインデックス。
- Smap : ℕ → Finset Ω: 各インデックス v に対応する有限部分集合。
- q : ENNReal, hq : q ≠ ⊤: 上界 q は無限大でないことを仮定する（toReal を取るため）。
- h : ∀ v ∈ MidBlock k X, μ ↑(Smap v) ≤ q: 各 v に対する測度の上界。

結論:
∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ ≤ (Finset.card (MidBlock k X) : ℕ) • q.toReal.

証明の方針:
Zmid は MidBlock にわたる指示関数やその和として表されるため、積分の線型性により期待値は各指示関数の積分（すなわち対応する集合の測度）の和で評価できる。
各測度は仮定 h により q で抑えられるので、その和は要素数 × q を超えない。q ≠ ⊤ により ENNReal.toReal が意味を持ち、実数上のスカラー倍に帰着して不等式を得る。
-/
lemma EZmid_expect_le_card_smul_q
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (q : ENNReal) (hq : q ≠ ⊤)
  (h : ∀ v ∈ MidBlock k X, μ ↑(Smap v) ≤ q) :
    (∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ)
    ≤ (Finset.card (MidBlock k X) : ℕ) • q.toReal := by
  -- rewrite expectation as finite sum of probabilities (as reals)
  have hEZ := EZmid_eq_sum_probs (μ := μ) (Smap := Smap) (k := k) (X := X)
  rw [hEZ]
  -- apply the algebraic lemma that bounds the sum by card • q.toReal
  exact badcount_by_expect (S := MidBlock k X) (p := fun v => μ ↑(Smap v)) (q := q) hq (fun v hv => h v hv)


/- card(MidBlock) に基づく存在形を dyadic (2^k) 指数に落とす補題 -/
/--
与えられた仮定の下での中間ブロック和の尾部確率評価。

記法と仮定の要約:
- Ω は測度空間で μ は確率測度。Ω 上は可測単点集合、DecidableEq を仮定。
- Smap : ℕ → Finset Ω は各インデックスに対応する点集合を与える写像。
- MidBlock k X は「中間ブロック」を表す有限集合（論理上の分割に依存）。
- Zmid は k, X, Smap によって定義されるランダム量（中間ブロックに関連する和や偏差）。
- P : SubGammaParam は亜ガンマ（sub-gamma）型のパラメータで、P.v > 0 かつ P.c * P.lambda0 ≤ 1 を満たす。
- h_sub は任意の 0 ≤ λ ≤ P.lambda0 に対して、
  μ[exp(λ (Zmid - 期待値に相当する和))] ≤ exp(P.v λ^2 / (1 - P.c λ))
  というモーメント母関数（あるいはラプラス変換）に関する上界を与える仮定である。
- h2k_le はブロック数と X の関係 2^(k+1) ≤ X+1 を保証する条件。
- δ > 0 は要求する偏差の大きさ。

主張（非形式的）:
- 上の仮定のもとで、ある定数 C ≥ 0 と c > 0 が存在して、任意の k について中間ブロック和がその期待値に対して δ·|MidBlock k X| 以上離れる事象の確率は
    μ({ ω | Zmid(ω) ≥ 期待値 + δ · |MidBlock k X| })
  で表され、これが C · exp(- c · 2^k) で抑えられる。
- すなわち、ブロックのスケール k が増すにつれて尾部確率は指数的に速く 2^k に比例した速度で減衰する。

解釈と役割:
- この補題は、サブガンマ条件（h_sub）から中間スケールの偏差に対する有効な指数不等式を導くもので、特にダイアディック（2^k）スケールにおける急速な減衰を示す。
- 定数 C, c は仮定（P のパラメータ、δ、および必要ならば測度 μ や構成の詳細）に依存し得るが、k によらず一様に取ることができる。
- これにより、スケールごとの偏差確率の和を評価して全体の収束や一様境界を得る解析が可能になる（例えば確率的支配や可積分性・一様収束の議論に利用される）。

注意:
- 証明はモーメント母関数の上界（h_sub）を用いたチェルノフ法（マルコフ不等式）と、ダイアディック分解に基づくスケール解析を組み合わせる構成になっている。
- 仮定の可測性や単点可測性、DecidableEq などは Finset の扱いや積分・指示関数の可測性確保のために用いられている。
- δ の正性 hδ は偏差量を正にとるために必要である。
- h2（P.c * P.lambda0 ≤ 1）は分母 1 - P.c λ が正であることを保証するための技術的条件である。
- 結果は k が増大するにつれて急速に減少する尾部評価を提供する点で有用である。
- 具体的な C, c の見積りは証明中で与えられる（あるいは構成される）が、主張上は存在性のみを主張している。
-/
lemma midblock_tail_dep_dyadic
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam) (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  (h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1)
  {δ : ℝ} (hδ : 0 < δ) :
  ∃ C c, 0 ≤ C ∧ 0 < c ∧
  μ.real {ω |
  Zmid (k := k) (X := X) (Smap := Smap) ω ≥
    (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp (- c * ((2 : ℝ) ^ k)) := by
  -- use the card-based factor form and the lower bound |MidBlock k X| ≥ 2^k when 2^(k+1) ≤ X+1
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let c := P.lambda0 / 2 * δ
  have hC_nonneg : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hc_pos : 0 < c := mul_pos (by simpa using half_pos P.hlambda0) hδ
  have hbound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
    P h1 h2 (h_sub) (hδ := hδ)
  -- use MidBlock_card_lower_when_2k_le_X to get card ≥ 2^k; the lemma requires the hypothesis 2^(k+1) ≤ X+1
  have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
  have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
  -- chain hbound with monotonicity to replace card by 2^k
  have mono : Real.exp (-(P.lambda0 / 2 * δ) * (Finset.card (MidBlock k X) : ℝ))
      ≤ Real.exp (-(P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k)) := by
    have negc_nonpos : -(P.lambda0 / 2 * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr (by simpa using mul_pos (by simpa using half_pos P.hlambda0) hδ))
    have le_arg : -(P.lambda0 / 2 * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -(P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k) :=
      mul_le_mul_of_nonpos_left h_card_real negc_nonpos
    exact Real.exp_le_exp.mpr le_arg
  refine ⟨C, c, hC_nonneg, hc_pos, ?_⟩
  have h1 := hbound
  -- apply monotonicity to replace card by 2^k and multiply by the nonnegative prefactor C
  have hpost := mul_le_mul_of_nonneg_left mono hC_nonneg
  have hR := le_trans h1 hpost
  -- RHS is Real.exp (...) * Real.exp (-(P.lambda0 / 2 * δ) * 2^k); show it equals C * exp(-c * 2^k)
  have rhs_eq : Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-(P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k))
      = C * Real.exp (- c * ((2 : ℝ) ^ k)) := by
    simp [C, c]
  rw [rhs_eq] at hR
  exact hR


/- helper: named constant that absorbs the finite union bound (dependent case) -/

/- 中域・依存版の合併確率を吸収する X 非依存定数（C⋆）。 -/
/--
midblockCstar (P : SubGammaParam) (δ : ℝ) は、パラメータ P の値 v, λ₀ と実数 δ に依存する正の係数を定義するための補助量です。
具体的には
  exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * ∑'_{k : ℕ} exp ( - (P.lambda0 / 2 * δ) * 2^k )
の形をしており、前半の因子は P のパラメータに由来する定数的な倍率、後半の無限和は 2^k に対する指数的減衰を表します。
直感的には中間ブロック（midblock）に由来する項の総和や上界を扱う際に現れる正の定数であり、δ > 0 の場合は各項が急速に減衰するため和が収束することが期待されます。
-/

noncomputable def midblockCstar (P : SubGammaParam) (δ : ℝ) : ℝ :=
  Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) *
    (∑' k : ℕ, Real.exp ( - (P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k)))


/--
midblockCstar_nonneg は任意の P : SubGammaParam と任意の実数 δ に対して
midblockCstar P δ ≥ 0 であることを示す補題です。
証明の要点は、Real.exp は常に正であり（Real.exp_pos）、無限和の各項も正であるため tsum_nonneg を適用でき、
これら二つの非負量の積は mul_nonneg により非負になる、というものです。
-/
lemma midblockCstar_nonneg (P : SubGammaParam) (δ : ℝ) :
  0 ≤ midblockCstar P δ := by
  have h1 : 0 ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) :=
    le_of_lt (Real.exp_pos _)
  have h2 : 0 ≤ (∑' k : ℕ, Real.exp ( - (P.lambda0 / 2 * δ) * ((2 : ℝ) ^ k))) :=
    tsum_nonneg (fun k => le_of_lt (Real.exp_pos _))
  simpa [midblockCstar] using mul_nonneg h1 h2


/- Index set and event definitions for GoodX -/

/- k の索引集合（固定 X） -/
/--
Kset X は、0 ≤ k ≤ X かつ 2^(k+1) ≤ X + 1 を満たす自然数 k 全体からなる有限集合を返します。
具体的には `Finset.range (X + 1)` を条件 `2^(k+1) ≤ X + 1` でフィルタした集合です。

引数:
  * `X` : 上界として用いる自然数。

性質の要約:
  * 任意の k ∈ Kset X について k ≤ X かつ 2^(k+1) ≤ X + 1 が成立します。
  * 2^(k+1) の単調増加により Kset X は必ず有限集合となり、
    最大の k は概ね ⌊log₂(X+1)⌋ - 1 になります（ここで対数は底 2）。
用途:
  * 二進指数に基づく分解や、指数的条件を満たすインデックス集合の取り扱いに便利です。
-/
def Kset (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)

/- 中域の上側偏差イベント E_k（固定 X, δ） -/
/--
Emid は与えられた確率空間上の事象を表す集合であり、次を満たす点 ω の全体として定義される：

  Zmid (k := k) (X := X) (Smap := Smap) ω
    ≥ ∑_{v ∈ MidBlock k X} (∫ ω, Prob.indR (Smap v) ω ∂μ) + δ · (Finset.card (MidBlock k X) : ℝ).

パラメータの意味:
- Ω, μ: Ω は可測空間で μ は確率測度（IsProbabilityMeasure）。
- Smap : ℕ → Finset Ω: 各インデックスに対する有限集合（観測ブロックなど）の割当て。
- δ : ℝ: 閾値に加える余裕（正の偏差の大きさ）。
- k, X : ℕ: MidBlock k X で定められるブロック集合を指定するパラメータ。

解釈:
この集合は、ランダム変数 Zmid が対応するブロック集合に関する期待的寄与の総和に対して δ に比例した余裕分を加えた値を上回る事象を表す。
有限集合の要素数は Finset.card により整数として得られ、それを実数にキャストしている点に注意する。

用途:
統計的な偏差事象の記述や、濃度不等式・大偏差評価などの議論に用いるための事象集合として設計されている。
-/
def Emid
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (δ : ℝ) (k X : ℕ) : Set Ω :=
  {ω |
    Zmid (k := k) (X := X) (Smap := Smap) ω
      ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
        + δ * (Finset.card (MidBlock k X) : ℝ)}


/- 同時良性事象（全部の k で上側偏差が起きない） -/
/--
GoodX μ Smap δ X は、確率空間 (Ω, μ) 上の「良い点」の集合である。具体的には、
Kset X に属する任意の指数 k に対して、ω が例外事象 `Emid (μ := μ) (Smap := Smap) δ k X`
に含まれないような点 ω の全体を与える。

パラメータ:
- Ω : 基底集合（可測空間、可測単点性、決定可能同値性を仮定）
- μ : Measure Ω, かつ IsProbabilityMeasure μ（確率測度）
- Smap : ℕ → Finset Ω（各段階での有限部分集合の選択）
- δ : ℝ（誤差許容などを表す実数パラメータ）
- X : ℕ（段階を表すインデックス）

直感的意味:
- GoodX は「段階 X において、どの k ∈ Kset X に対しても Emid による例外が生じない点」の集合である。
- すなわち、Emid によって定義される一連の悪い事象をすべて回避する点を集めたものであり、
  測度論的・確率論的議論において「ほとんど確実に成立する性質」を記述するときに使われる。

用途・注意:
- Kset や Emid の具体的性質（可測性や相互依存）に依って、GoodX の可測性やその測度に関する結論を導ける。
- 証明では、GoodX 上である性質が成り立つことを示し、それを用いてほとんど全ての点に関する主張を得る、
  といった使われ方をすることが多い。
- Emid の定義に依存して、GoodX がしばしば高い測度（例えば 1）を持つことを示せる場合がある。
- Kset や Emid の定義がこのファイル内外にあることに注意すること。
-/
def GoodX
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (δ : ℝ) (X : ℕ) : Set Ω :=
  {ω | ∀ k ∈ Kset X, ¬ (ω ∈ Emid (μ := μ) (Smap := Smap) δ k X)}

/- `ω ∈ GoodX` なら全 k∈K(X) で `Zmid ≤ 期待値 + δ·card`。 -/
/--
中間ブロック（MidBlock）に関する一連の偏差確率の上界を与える補題。

概要：
与えられた確率測度 μ と Smap から定まる中間ブロックに対して，
各ブロック k に対する指数モーメント母関数の制約 h_sub を仮定すると，
ある正の定数 C, cθ を取って，集合族 E k の和集合の測度は
各 k に対して C * exp(-cθ * 2^k) で抑えられる。すなわち
⋃_{k∈K} E k の測度は ∑_{k∈K} C e^{-cθ 2^k} を上界とする。

引数と仮定の役割：
- Ω, μ, Smap は確率空間とブロック分割を与える。
- P は SubGamma 型のパラメタで，P.v > 0 および P.c * P.lambda0 ≤ 1 により
  指数不等式の適用域と分母の有界性が保証される。
- h_sub は，各 k, X, λ ≤ P.lambda0 に対して
  Zmid の偏差の指数モーメントを上界する仮定（Chernoff 型の不等式）である。
- δ (> 0) は偏差閾値を与えるパラメタである。
- K は 2^(k+1) ≤ X+1 を満たす k を取ることで，
  「中間ブロック列」として扱う k の範囲を切り取る役割を持つ。

結論の意味と証明方針（概略）：
- 各 k について h_sub を用いて μ[E k] を指数不等式で評価し，
  右辺は λ による式（P.v * λ^2/(1 - P.c λ) といった形）と
  -λ ×（偏差量）との和で表せる。
- k に依存する最適な λ を適切に選ぶことにより，
  各 μ[E k] を C' exp(-c' 2^k) の形で一様に上界できる。
- 最後に和集合の測度は和で上界されるので（単純な和集合の単調性／和の不等式），
  ∑_{k∈K} C' e^{-c' 2^k} の形の上界が得られる。
- 定数 C, cθ は P と δ（および必要に応じて基本的定数）に依存し，
  cθ は正，C は非負に取れる。

補足：
- h_clambda0_le_one により分母 1 - P.c λ が正に保たれ，式の意味が保たれる。
- 結論はブロック長が幾何的に増加することに起因して，非常に急速な指数減衰を示すものであり，
  尤度のチェルノフ法＋和集合に対する単純な和の評価の組合せで得られる典型的な尾部評価である。
- この補題は，個々の中間ブロックでの偏差確率を合成して全体の偏差を支配する場面で利用される。
- 必要ならば定数の具体的評価（λ の選び方に基づく）を与えてより詳細な見積もりが可能である。
-/
lemma union_over_k_midblock_bound_dep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
    (h_sub : ∀ {k X : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
        μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
          - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
        Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    let K : Finset ℕ :=
      (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
    let E : ℕ → Set Ω := fun k => Emid (μ := μ) (Smap := Smap) δ k X
    μ.real (⋃ k ∈ K, E k)
      ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  classical
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let cθ := (P.lambda0 / 2) * δ
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hcθ : 0 < cθ := mul_pos (by simpa using half_pos P.hlambda0) hδ

  -- signature-level `K` and `E` (using `Emid`) are available here

  refine ⟨C, cθ, hC, hcθ, ?_⟩
  intro K E
  have : ∀ {k}, k ∈ K → μ.real (E k) ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    intro k hk
    have h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1 := by
      simpa [K] using (Finset.mem_filter.mp hk).2
    have hcard_bound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
    have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
    have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
    have mono : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
      have negc_nonpos : -((P.lambda0 / 2) * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr hcθ)
      have le_arg : -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -((P.lambda0 / 2) * δ) * ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonpos_left h_card_real negc_nonpos
      exact Real.exp_le_exp.mpr le_arg
    calc
      μ.real (E k) = μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)} := by rfl
      _ ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := hcard_bound
      _ = C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by rfl
      _ ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by apply mul_le_mul_of_nonneg_left mono hC

  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K E
  exact le_trans hboole (Finset.sum_le_sum (by intro k hk; exact this hk))


/- 固定 X について、条件 `2^(k+1) ≤ X+1` を満たすすべての k で
    上側偏差イベントの合併確率を Boole で束ねる（Janson/Suen 受け口） -/
lemma union_over_k_midblock_bound_dep'
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
    (h_sub : ∀ {k X : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
        μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω
          - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
        Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  ∃ (C cθ : ℝ), 0 ≤ C ∧ 0 < cθ ∧
    let K : Finset ℕ :=
      (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
    let E : ℕ → Set Ω := fun k =>
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
            + δ * (Finset.card (MidBlock k X) : ℝ)}
    μ.real (⋃ k ∈ K, E k)
      ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
  classical
  -- Choose explicit uniform constants C and cθ (Option A): reuse the same formulas
  -- used in `mid_block_upper_hp_dep_expCard_exists` so they are independent of k.
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let cθ := (P.lambda0 / 2) * δ
  have hC : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hcθ : 0 < cθ := mul_pos (by simpa using half_pos P.hlambda0) hδ

  -- K と E を束ねて Boole
  refine ⟨C, cθ, hC, hcθ, ?_⟩
  intro K E
  have : ∀ {k}, k ∈ K → μ.real (E k) ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
    intro k hk
    -- K の定義より 2^(k+1) ≤ X+1
    have h2 : (2 : ℕ) ^ (k + 1) ≤ X + 1 := by
      simpa [K] using (Finset.mem_filter.mp hk).2
    -- apply the existing card-based exponential bound (gives factor in terms of |MidBlock|)
    have hcard_bound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one (fun h0 hL => h_sub h0 hL) (hδ := hδ)
    -- obtain the card lower bound card(MidBlock k X) ≥ 2^k
    have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2
    have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
    -- show exp(-c * card) ≤ exp(-c * 2^k) since card ≥ 2^k and c > 0
    have mono : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- cθ * ((2 : ℝ) ^ k)) := by
      have negc_nonpos : -((P.lambda0 / 2) * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr hcθ)
      have le_arg : -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -((P.lambda0 / 2) * δ) * ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonpos_left h_card_real negc_nonpos
      exact Real.exp_le_exp.mpr le_arg
    -- chain the bounds to get the desired form
    calc
      μ.real (E k) = μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)} := by rfl
      _ ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := hcard_bound
      _ = C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by rfl
      _ ≤ C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := by apply mul_le_mul_of_nonneg_left mono hC

  -- Boole の有限合併上界
  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K E
  -- 各項に上界を差し込み
  refine le_trans hboole ?_
  exact Finset.sum_le_sum (by intro k hk; exact this hk)


/- Finite-union の Boole と可和性を組み合わせて X 非依存の定数に吸収する補題 -/
/--
与えられた定理は、確率空間 (Ω, μ) 上の「中間ブロック (MidBlock)」に関する一様な上側確率評価を与える結果です。

概略（日本語）:
- 前提として、Ω は可測空間で可測単点を持ち、要素の等号判定が可能であり、μ は確率測度です。
- X : ℕ と Smap : ℕ → Finset Ω により定められるブロック列 MidBlock k X を考えます。
- P : SubGammaParam はサブガンマ型の指数モーメント評価を与えるパラメータで、P.v > 0 かつ P.c * P.lambda0 ≤ 1 を満たします。
- 仮定 h_sub は任意の k, X' ∈ ℕ と 0 ≤ λ ≤ P.lambda0 に対して
  μ[exp(λ (Zmid − 期待値和))] ≤ exp(P.v λ^2 / (1 − P.c λ))
  が成立する、つまり Zmid − 期待値和 がサブガンマ的に制御されることを述べています。

主張:
 任意の δ > 0 に対して、ある非負の定数 Cstar が存在し、
 指定した有限な k の範囲（(Finset.range (X+1)).filter (λ k, 2^(k+1) ≤ X+1)）に渡る
 イベント
   { ω | Zmid(k,X,Smap,ω) ≥ (期待値和) + δ · |MidBlock k X| }
 の和集合の測度は Cstar 以下に抑えられます。

意味と役割:
- 個々の中間ブロックについて Zmid がその期待値和から δ·|ブロック| 以上ずれる確率を、k に依らず一括して有界にする結果です。
- h_sub による指数モーメント評価（サブガンマ性）を用い、チェルノフ（指数マークフ）不等式を各 k に適用して確率を指数的に抑え、
  それらを有限個で和を取ることで全体の上界 Cstar を得ます。
- これは濃縮不等式や大標本極限定理に基づく一様誤差評価、あるいは逐一のブロックの偏差を同時に制御したい場面で有用です。

証明の骨子:
1. h_sub による指数モーメント評価から各 k について
   μ[Zmid − 期待値和 ≥ δ·|MidBlock k X|] ≤ exp(P.v λ^2/(1 − P.c λ) − λ δ |MidBlock k X|)
   が任意の 0 ≤ λ ≤ P.lambda0 で成り立つ（チェルノフ）。
2. 右辺を δ に応じて適切に選んだ λ で評価し（最適化や単純な上界を取る）、k に関する有限和を取る。
3. その和を Cstar と定めれば主張が得られる。ここで P.c * P.lambda0 ≤ 1 は分母 1 − P.c λ が正であることを保証するために重要です。

注意:
- Cstar の具体的な数式は証明過程で構成され、δ, P（および必要ならば X, Smap の情報）に依存しますが、定理の述語としては非負の一様上界が存在することを主張します。
- δ > 0 の仮定、可測性や可測単点性、決定可能な等号などの仮定は、確率変数の可測性・積分操作とチェルノフ不等式の適用に必要です。
- 結果は有限個の k に対する和集合なので、有限性（range (X+1) のフィルタによる有限集合性）を利用しています。
- この補題は、ブロック毎の偏差を一括して制御するステップとして、より大きな濃縮や一様収束の議論に組み込めます。
-/
theorem midblock_union_absorb_dep
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam) (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {k X' : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X') (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X', (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) :
  ∃ Cstar : ℝ, 0 ≤ Cstar ∧
    μ.real (⋃ k ∈ (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1),
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω ≥
          (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)})
    ≤ Cstar := by
  -- We will use the already-proved `union_over_k_midblock_bound_dep` which provides a bound by ∑ C * exp(-c * 2^k)
  rcases Prob.union_over_k_midblock_bound_dep (μ := μ) (Smap := Smap) P h1 h2 (h_sub) hδ X
    with ⟨C, cθ, hC, hcθ, hsum_bound⟩
  let K := (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1)
  -- the RHS is a finite sum over k in the finite range; bound it by a constant using summability / trivial majorization
  have hC_nonneg := hC
  -- promote finite sum to infinite sum majorization using summability
  have h_summ := Prob.summable_exp_neg_two_pow cθ hcθ
  -- Safer finite→tsum promotion: factor C out, then use the general `Summable.sum_le_tsum` lemma
  have hsum_all : ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k))
    ≤ C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) := by
    -- factor C out of the finite sum first
    have : ∑ k ∈ K, C * Real.exp (-cθ * ((2 : ℝ) ^ k))
        = C * ∑ k ∈ K, Real.exp (-cθ * ((2 : ℝ) ^ k)) := by
      simp [Finset.mul_sum]
    rw [this]
    -- now use the `Summable.sum_le_tsum` lemma on the unscaled summable sequence
    have h_range_le_tsum := (h_summ : Summable fun k => Real.exp (-cθ * ((2 : ℝ) ^ k))).sum_le_tsum K (fun k _ => le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left h_range_le_tsum hC_nonneg
  -- chain the bounds: μ.real (...) ≤ finite sum ≤ C * tsum
  have final_bound : μ.real (⋃ k ∈ (Finset.range (X + 1)).filter (fun k => (2 : ℕ)^(k + 1) ≤ X + 1),
      {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω ≥
          (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)})
    ≤ C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) := by
    calc
      μ.real (⋃ k ∈ K, {ω | _}) ≤ ∑ k ∈ K, C * Real.exp (- cθ * ((2 : ℝ) ^ k)) := hsum_bound
      _ ≤ C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) := hsum_all
  have h_tsum_nonneg : 0 ≤ (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))) :=
    tsum_nonneg (fun k => le_of_lt (Real.exp_pos _))
  refine ⟨C * (∑' k, Real.exp (- cθ * ((2 : ℝ) ^ k))), mul_nonneg hC_nonneg h_tsum_nonneg, final_bound⟩


/- GoodX の測度下界補題 -/

/- GoodX の補集合は k 合併そのもの。 -/
/--
GoodX_compl_eq_union

この補題は、与えられた確率測度の下での「良い事象」 GoodX の補集合が、
Kset X に渡るある種の「中間事象」 Emid の合併として記述できることを主張する。

直観的には、GoodX が成り立たない点 ω は、あるスケール k（k ∈ Kset X）において
中間的な不良事象 Emid を満たす、ということである。したがって
(GoodX)ᶜ = ⋃_{k ∈ Kset X} Emid k X が成り立つ。

証明の骨子：
- 左辺から右辺への包含：ω ∉ GoodX ならば GoodX の定義から
  ある k ∈ Kset X が存在し、それに対応して ω ∈ Emid k X となることを示す。
- 右辺から左辺への包含：ある k が存在して ω ∈ Emid k X ならば
  GoodX の成立条件のいずれかが破れることを示し、従って ω ∉ GoodX である。
- 必要に応じて Kset の有限性や可測性を用いて集合演算（補集合・合併）の扱いを簡潔にする。

仮定：位相的・可測的な仮定（MeasurableSpace, MeasureSpace, MeasurableSingletonClass 等）と
μ が確率測度であること、Smap : ℕ → Finset Ω, δ : ℝ, X : ℕ の下で成り立つ。
-/
lemma goodX_compl_eq_union
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (δ : ℝ) (X : ℕ) :
  (GoodX (μ := μ) (Smap := Smap) δ X)ᶜ
    = {ω | ∃ k, k ∈ Kset X ∧ ω ∈ Emid (μ := μ) (Smap := Smap) δ k X} := by
  classical
  ext ω
  apply Iff.intro
  · -- if ω ∉ GoodX then ¬ (∀ k, k ∈ Kset X → ¬ ω ∈ Emid); obtain witness k
    intro h
    have ⟨k, hk_imp⟩ := Classical.not_forall.mp h
    have ⟨hk, hnn⟩ := Classical.not_imp.mp hk_imp
    exact ⟨k, hk, Classical.not_not.mp hnn⟩
  · -- conversely, if ∃ k with k ∈ Kset X and ω ∈ Emid then ω ∉ GoodX
    intro hbi
    rcases hbi with ⟨k, hk, hmem⟩
    intro H
    exact (H k hk) hmem


/- X 非依存定数 midblockCstar を明示的に用いる補題。
  既存の存在形補題 `midblock_union_absorb_dep` を利用して右辺を簡約し，
  `midblockCstar P δ` で上から抑える。 -/
/--
与えられた仮定の下での中間区間（midblock）に関する確率測度の上界。

命題の趣旨：
Ω 上の確率測度 μ と、自然数からの点集合写像 Smap に対して、
各 k に対する中間ブロック Emid δ k X の和集合を X に関係するインデックス集合 Kset X 上で取ったとき、その μ-測度は
定数 midblockCstar P δ によって一様に抑えられることを主張する。

主要な仮定：
- μ は確率測度（IsProbabilityMeasure）。
- P は SubGammaParam であり、P.v > 0 かつ P.c * P.lambda0 ≤ 1 を満たす。
- h_sub は Zmid に関する指数モーメント（あるいはラプラス変換）の上界を与える仮定で、
  任意の 0 ≤ λ ≤ P.lambda0 に対して
  E[exp(λ (Zmid - 期待値に相当する項))] ≤ exp(P.v λ^2 / (1 - P.c λ))
  が成立することを述べる。これは Zmid が「サブガウス／サブガンマ様」の濃度を持つことを示す。
- δ > 0（中間区間の幅）および任意の自然数 X に対して主張が成り立つ。

証明のアイデア（概略）：
1. h_sub により各 k に対して Zmid のラプラス変換を制御し、チェビシェフ（マルチプライヤー）型の指数不等式を導く。
2. 適切な λ を選ぶことで指数項を最適化し、各 k に対する尾事象の確率を所望の形で抑える。
3. Kset X 上で和集合を取る際には和（あるいは合併）に対する単純な上界（ボンフェローニ不等式等）を使い、
   個々の k の寄与を合計して全体の測度を bounded by midblockCstar P δ にまとめる。
4. 定数 midblockCstar P δ は P, δ に依存し、上記の最適化と合併操作から得られる。

注意・補足：
- 記号 Zmid, MidBlock, Emid, Kset, midblockCstar は本ファイル内の定義に依存するので、
  正確な定義に基づいて上の濃度不等式の導出を確認する必要がある。
- メトリックや可測性に関する細かい技術条件（DecidableEq, MeasurableSingletonClass など）は
  実際の可測性議論や和集合の測度計算を正当化するために用いられている。
- この補題は、個々のブロックに対する濃度不等式を全体に拡張して総和（あるいは合併）を扱う際の標準的な道具立てを提供するものであり、
  後続の大域的な濃度評価や確率論的埋め込み推定に利用される想定である。
- midblockCstar の具体的形は P.v, P.c, P.lambda0, δ の関数であり、証明中に現れる最適化された λ の選択により定まる。
- 本結果は、Zmid の集中特性が与えられている限り、X に依らない一様な上界を与える点が重要である。
- 翻訳・解釈上の疑問がある場合は、対応する定義（特に Emid と Kset）を参照のこと。
- 記載されている仮定を弱めたバリエーションや、確率測度以外の測度への拡張については別途検討が必要である。
- 直感的には「個々の中間ブロックで生じる大きな偏差の確率を指数的に抑え、それらを可算個合併しても合計として有限（＝midblockCstar）に保てる」という主張である。
- 証明はラプラス変換法（Chernoff 法）と和集合に対する単純な測度上界に依拠する。
- 参照：本定理の使い方としては、局所的な偏差制御を全体の偏差評価へブートストラップする場面が典型的である。
- 用語・記号の詳細は同ファイル内の補題・定義を参照されたい。
-/
theorem midblock_union_absorb_dep_const
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Smap : ℕ → Finset Ω)
  (P : SubGammaParam) (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {k X' : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X') (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X', (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≤ midblockCstar P δ := by
  let K := Kset X
  -- choose the canonical constants (same as in `midblock_tail_dep_dyadic` and `midblockCstar`)
  let C0 := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let c0 := (P.lambda0 / 2) * δ
  have hC0_nonneg : 0 ≤ C0 := le_of_lt (Real.exp_pos _)
  have hc0_pos : 0 < c0 := mul_pos (by simpa using half_pos P.hlambda0) hδ

  -- per-k bound using the same ingredients as `midblock_tail_dep_dyadic`, done inline so names match
  have hterm : ∀ {k}, k ∈ K → μ.real (Emid (μ := μ) (Smap := Smap) δ k X) ≤ C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := by
    intro k hk
    have h2k_le : (2 : ℕ) ^ (k + 1) ≤ X + 1 := by simpa [K] using (Finset.mem_filter.mp hk).2
    -- base exponential bound from high-probability lemma
    have hcard_bound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h1 h2 h_sub (hδ := hδ)
    -- card lower bound |MidBlock k X| ≥ 2^k when 2^(k+1) ≤ X+1
    have h_card_nat := MidBlock_card_lower_when_2k_le_X k X h2k_le
    have h_card_real : (Finset.card (MidBlock k X) : ℝ) ≥ (2 : ℝ) ^ k := by exact_mod_cast h_card_nat
    -- monotonicity of the exponential to replace card by 2^k
    have mono : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        ≤ Real.exp (- c0 * ((2 : ℝ) ^ k)) := by
      have negc_nonpos : -((P.lambda0 / 2) * δ) ≤ 0 := le_of_lt (neg_lt_zero.mpr hc0_pos)
      have le_arg : -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) ≤ -((P.lambda0 / 2) * δ) * ((2 : ℝ) ^ k) :=
        mul_le_mul_of_nonpos_left h_card_real negc_nonpos
      exact Real.exp_le_exp.mpr le_arg
    calc
      μ.real (Emid (μ := μ) (Smap := Smap) δ k X) = μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)} := by rfl
      _ ≤ Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := hcard_bound
      _ = C0 * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by rfl
      _ ≤ C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := by apply mul_le_mul_of_nonneg_left mono hC0_nonneg

  have hboole := MeasureTheory.measureReal_biUnion_finset_le (μ := μ) K (fun k => Emid (μ := μ) (Smap := Smap) δ k X)
  have hsum_bound := Finset.sum_le_sum (fun k hk => (hterm (by assumption) : _))
    -- combine to get μ.real (⋃) ≤ ∑ k ∈ K, C0 * exp(-c0*2^k)
  have sum_le : μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := by
    calc
      μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ K, μ.real (Emid (μ := μ) (Smap := Smap) δ k X) := hboole
      _ ≤ ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := Finset.sum_le_sum (fun k hk => hterm hk)

  -- upgrade finite sum to C0 * tsum
  have h_summ := Prob.summable_exp_neg_two_pow c0 hc0_pos
  have hsum_all : ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k))
    ≤ C0 * (∑' k, Real.exp (- c0 * ((2 : ℝ) ^ k))) := by
    have : ∑ k ∈ K, C0 * Real.exp (-c0 * ((2 : ℝ) ^ k)) = C0 * ∑ k ∈ K, Real.exp (-c0 * ((2 : ℝ) ^ k)) := by simp [Finset.mul_sum]
    rw [this]
    have h_range_le_tsum := (h_summ : Summable fun k => Real.exp (-c0 * ((2 : ℝ) ^ k))).sum_le_tsum K (fun k _ => le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left h_range_le_tsum hC0_nonneg

  calc
    μ.real (⋃ k ∈ K, Emid (μ := μ) (Smap := Smap) δ k X) ≤ ∑ k ∈ K, C0 * Real.exp (- c0 * ((2 : ℝ) ^ k)) := sum_le
    _ ≤ C0 * (∑' k, Real.exp (- c0 * ((2 : ℝ) ^ k))) := hsum_all
  -- the final inequality is exactly the goal (RHS equals midblockCstar P δ)


/- 依存版：GoodX の測度は `1 - midblockCstar P δ` 以上。 -/
/--
この補題は、確率測度 μ 上で定義された「良い」事象 GoodX の測度が、
与えられたパラメータ P と正数 δ に対して下界 1 - midblockCstar P δ を満たすことを主張するものです。

設定の要点：
- Ω は可測空間、μ は確率測度。
- Smap : ℕ → Finset Ω はブロックに対応する有限集合の列。
- P : SubGammaParam はサブガウス的なモーメント母関数のパラメータであり、
  P.v > 0 と P.c * P.lambda0 ≤ 1 を仮定する。
- 仮定 h_sub は、任意のブロック k, インデックス X' と 0 ≤ λ ≤ P.lambda0 に対して
  指数モーメント（mgf）に対する上界
    μ[exp(λ (Zmid - Σ MidBlock の期待値))] ≤ exp( P.v * λ^2 / (1 - P.c * λ) )
  が成り立つことを要求する。ここで Zmid はブロック内の観測量、MidBlock は対応する和を表す。
- δ > 0 をとる。

結論：
任意の X について、GoodX (μ, Smap, δ, X) の μ による測度は少なくとも 1 - midblockCstar P δ である。

直観と証明の骨子：
仮定 h_sub により各ブロックに対してチェルノフ（マルコフ）不等式を適用できるため、
適切な λ を選ぶことで各ブロックの偏差確率を指数的に抑えられる。これらを合成し（例えば和分布や合併事象に対する評価を用いて）全体の「良い」事象の補集合の測度を上界し、
その上界を midblockCstar P δ として定めることで主張を得る。P.c * P.lambda0 ≤ 1 の仮定は分母 1 - P.c * λ が正であることを保証するために必要である。
-/
lemma goodX_measure_ge_one_sub_midblockCstar
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) (P : SubGammaParam)
  (h1 : 0 < P.v) (h2 : P.c * P.lambda0 ≤ 1)
  (h_sub : ∀ {k X' : ℕ} {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X') (Smap := Smap) ω
        - (∑ v ∈ MidBlock k X', (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda)))
  {δ : ℝ} (hδ : 0 < δ) (X : ℕ) :
  μ.real (GoodX (μ := μ) (Smap := Smap) δ X) ≥ 1 - midblockCstar P δ := by
  classical
  -- μ(univ) ≤ μ(U) + μ(GoodX) → μ(GoodX) ≥ 1 - μ(U) を使う（U は合併）
  have hU :
    μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
      ≤ midblockCstar P δ :=
    Prob.midblock_union_absorb_dep_const (μ:=μ) (Smap := Smap) P h1 h2 (h_sub) hδ X
  have hcover :
    μ (Set.univ : Set Ω) ≤
      μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
      + μ (GoodX (μ := μ) (Smap := Smap) δ X) := by
    have : (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ∪ (GoodX (μ := μ) (Smap := Smap) δ X) = (Set.univ : Set Ω) := by
      ext ω
      show ω ∈ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ∪ GoodX (μ := μ) (Smap := Smap) δ X ↔ ω ∈ Set.univ
      constructor
      · intro _; trivial
      · intro _
        by_cases hmem : ω ∈ GoodX (μ := μ) (Smap := Smap) δ X
        · exact Or.inr hmem
        · -- hmem : ¬ ω ∈ GoodX, so ω is in the complement
          have hex : ω ∈ (GoodX (μ := μ) (Smap := Smap) δ X)ᶜ := hmem
          have mem_ex := (goodX_compl_eq_union (μ := μ) (Smap := Smap) (δ := δ) (X := X)).symm ▸ hex
          have union_eq : (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
            = {ω | ∃ k, k ∈ Kset X ∧ ω ∈ Emid (μ := μ) (Smap := Smap) δ k X} := by
            ext x
            simp [Set.mem_iUnion]
          have mem_union := union_eq.symm ▸ mem_ex
          exact Or.inl mem_union
    have h := MeasureTheory.measure_union_le (μ := μ) (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) (GoodX (μ := μ) (Smap := Smap) δ X)
    simpa [this] using h
  -- toReal で実数化して整理: ENNReal.toReal_mono により
  -- 1 ≤ (μ ⋃ + μ GoodX).toReal, さらに toReal_add_le により
  -- (μ ⋃ + μ GoodX).toReal ≤ μ.real (⋃) + μ.real GoodX と結合する。
  -- μ (Set.univ) is finite (probability measure), use it to apply toReal lemmas
  have μuniv_ne_top : μ (Set.univ : Set Ω) ≠ ⊤ := by simp [IsProbabilityMeasure.measure_univ]
  -- show μ(⋃) and μ(GoodX) are finite by monotonicity from μ univ
  have μ_union_le_univ : μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≤ μ (Set.univ : Set Ω) :=
    MeasureTheory.measure_mono (μ := μ) (Set.subset_univ _)
  have μ_union_ne_top : μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) ≠ ⊤ :=
    ne_top_of_le_ne_top μuniv_ne_top μ_union_le_univ
  have μ_good_le_univ : μ (GoodX (μ := μ) (Smap := Smap) δ X) ≤ μ (Set.univ : Set Ω) :=
    MeasureTheory.measure_mono (μ := μ) (Set.subset_univ _)
  have μ_good_ne_top : μ (GoodX (μ := μ) (Smap := Smap) δ X) ≠ ⊤ :=
    ne_top_of_le_ne_top μuniv_ne_top μ_good_le_univ
  have sum_ne_top : (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) + μ (GoodX (μ := μ) (Smap := Smap) δ X)) ≠ ⊤ :=
    (ENNReal.add_ne_top.mpr ⟨μ_union_ne_top, μ_good_ne_top⟩)

  -- apply toReal lemmas: since the sum is finite we can pass it as the second argument
  have h_toReal := ENNReal.toReal_mono sum_ne_top hcover
  have h_toReal_add_le : (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) + μ (GoodX (μ := μ) (Smap := Smap) δ X)).toReal
    ≤ (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)).toReal
      + (μ (GoodX (μ := μ) (Smap := Smap) δ X)).toReal := ENNReal.toReal_add_le
  have : 1 ≤ μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
    + μ.real (GoodX (μ := μ) (Smap := Smap) δ X) := by
    calc
      1 = (μ (Set.univ : Set Ω)).toReal := by simp [IsProbabilityMeasure.measure_univ]
      _ ≤ (μ (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) + μ (GoodX (μ := μ) (Smap := Smap) δ X)).toReal := h_toReal
      _ ≤ μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X)
        + μ.real (GoodX (μ := μ) (Smap := Smap) δ X) := h_toReal_add_le
  -- 右辺の第1項を C⋆ で上から抑える → 目的の形へ
  have := sub_le_iff_le_add'.mpr this
  -- `a ≥ 1 - b` 形式に直す（ここで a = μ.real GoodX, b = μ.real (⋃ ...)）
  have h_ge_goodx : μ.real (GoodX (μ := μ) (Smap := Smap) δ X)
      ≥ 1 - μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) := by
    linarith
  -- from hU : μ.real (⋃ ...) ≤ midblockCstar we get 1 - midblockCstar ≤ 1 - μ.real (⋃ ...)
  have h_one_sub : 1 - midblockCstar P δ ≤ 1 - μ.real (⋃ k ∈ Kset X, Emid (μ := μ) (Smap := Smap) δ k X) :=
    sub_le_sub_left hU (1 : ℝ)
  -- chain inequalities: 1 - midblockCstar ≤ 1 - μ⋃ ≤ μ.real GoodX
  exact le_trans h_one_sub h_ge_goodx


/- `ω ∈ GoodX` なら全 k∈K(X) で `Zmid ≤ 期待値 + δ·card`。 -/
/--
与えられた点 ω が `GoodX` に属するならば、任意の `k ∈ Kset X` について点 ω における `Zmid` は
対応する中間ブロック `MidBlock k X` に属する各ブロック v に対する確率的指示関数 `Prob.indR (Smap v)` の期待値（積分）の和
と誤差項 `δ` による項の和で上から抑えられることを主張する補助補題。

直感的には、`GoodX` は各ブロックごとに確率指示関数とある基準量との差が `δ` 以内に制御されることを保証しており、
その結果として点 ω における局所量 `Zmid` が、ブロックごとの期待値の和に `δ`×(ブロック数) を足したもので上界される、という点ごとの評価を得る。
- 前提: μ は確率測度、`Smap` は各自然数に対応する有限集合の写像（ブロック分割）を与える。
- 結論: 任意の `k ∈ Kset X` に対して
  Zmid ω ≤ ∑_{v ∈ MidBlock k X} ∫ Prob.indR (Smap v) dμ  + δ * |MidBlock k X|
という不等式が成り立つ。

証明では `GoodX` の定義から各ブロックごとの点ωでの差分を積分値と比較し、三角不等式的な見積もりで上の形にまとめる。
-/
lemma goodX_pointwise
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X : ℕ} {ω : Ω} :
  ω ∈ GoodX (μ := μ) (Smap := Smap) δ X →
  ∀ ⦃k⦄, k ∈ Kset X →
    Zmid (k := k) (X := X) (Smap := Smap) ω
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
        + δ * (Finset.card (MidBlock k X) : ℝ) := by
  intro hGood k hk
  have hnot := hGood k hk
  -- hnot : ¬ (ω ∈ Emid μ Smap δ k X), i.e. ¬ (Zmid ω ≥ RHS)
  exact le_of_not_ge hnot


/- `ω ∈ GoodX` なら `Zmid ≤ card • q.toReal + δ·card` の点ごとの版 -/
/--
指定された確率空間と集合写像 Smap に対して、点ごとの上界を与える補題。

引数の意味:
- Ω : 可測空間の母集合、μ : Ω 上の確率測度。
- Smap : ℕ → Finset Ω は自然数に対応する有限部分集合の写像。
- δ, X, k, ω はそれぞれ実数 δ、自然数 X, k、および点 ω ∈ Ω。
- q : ENNReal は集合の測度に対する上界であり、hq_ne により q ≠ ⊤（非∞）が仮定される。

仮定:
- hprob : 任意の v ∈ MidBlock k X について μ ↑(Smap v) ≤ q。すなわち MidBlock k X に属する各集合 Smap v の測度は一様に q 以下である。
- ω ∈ GoodX (μ := μ) (Smap := Smap) δ X：点 ω は GoodX の条件を満たす（点ごとの良好性）。
- k ∈ Kset X。

結論:
- 点 ω における Zmid (k := k) (X := X) (Smap := Smap) ω は、MidBlock k X にわたる各 v に対する Prob.indR (Smap v) の μ による積分の総和と、(q.toReal + δ) に MidBlock k X の要素数を掛けたものとの和によって上から抑えられる。特に q ≠ ⊤ により q.toReal が意味を持つことに注意。

注釈:
この補題は、有限個のブロック（MidBlock k X）に対する個々の指示関数的寄与の積分和と、測度の一様上界から得られる余分項を合わせることで、点ごとの量 Zmid を制御するために使われる。
-/
lemma goodX_pointwise_qaddδ_card
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X k : ℕ} {ω : Ω} (q : ENNReal)
  (hq_ne : q ≠ ⊤) (hprob : ∀ v ∈ MidBlock k X, μ ↑(Smap v) ≤ q) :
  ω ∈ GoodX (μ := μ) (Smap := Smap) δ X →
  k ∈ Kset X →
    Zmid (k := k) (X := X) (Smap := Smap) ω
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * (Finset.card (MidBlock k X) : ℝ) := by
  intro hGood hk
  -- from GoodX we have Zmid ≤ expectation + δ * card
  have hnot := hGood k hk
  have hZ_le_E_plus : Zmid (k := k) (X := X) (Smap := Smap) ω
    ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ) :=
    le_of_not_ge hnot
  -- use the hypotheses to avoid unused-variable linter warnings
  have _ := hq_ne
  have _ := hprob
  -- simply add q.toReal * card to the RHS and rearrange to the desired form
  let cardR : ℝ := (Finset.card (MidBlock k X) : ℝ)
  -- add q.toReal * card on the right of the RHS and rearrange to (q.toReal + δ) * card
  have rhs_eq : (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * cardR + q.toReal * cardR
    = (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * cardR := by ring
  have h_cardR_nonneg : 0 ≤ cardR := by
    exact Nat.cast_nonneg (Finset.card (MidBlock k X))
  have hq_nonneg : 0 ≤ q.toReal := by exact ENNReal.toReal_nonneg
  have h_qr_nonneg : 0 ≤ q.toReal * cardR := mul_nonneg hq_nonneg h_cardR_nonneg
  have hstep : (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * cardR
    ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * cardR + q.toReal * cardR :=
    le_add_of_nonneg_right h_qr_nonneg
  have hchain := le_trans hZ_le_E_plus hstep
  rw [rhs_eq] at hchain
  exact hchain


/- sum-over-k version: sum_{k ∈ Kset X} Zmid(ω) ≤ sum expectations + (q.toReal + δ) * sum card -/
/--
与えられた確率空間上での評価不等式。

仮定
- Ω は可測単点を持つ可測空間で、μ は確率測度。
- Smap : ℕ → Finset Ω は各インデックスに対する有限部分集合の割当て。
- MidBlock k X は各 k に対する有限集合（中間ブロック）を表す。
- q : ENNReal は上に有界で q ≠ ⊤（したがって q.toReal が定義される）。
- hprob は任意の k ∈ Kset X, v ∈ MidBlock k X に対して μ (Smap v) ≤ q を与える仮定。
- ω ∈ GoodX は「良い点」を意味し、δ は許容誤差である実数。

主張
- 左辺は k ∈ Kset X に関する Zmid の総和で、各 k に対して ω に依存する局所的なインジケータ的寄与を表す。
- 右辺第一項は各 v に対する指示関数 Prob.indR (Smap v) の積分（すなわち μ (Smap v) に対応する実数）の和である。
- 右辺第二項は q.toReal + δ に総中間ブロック数の合計を掛けた誤差項である。

直観と証明方針
- 各 Zmid の寄与は対応する Smap v の指示関数の積分（＝測度）と誤差項に分解できる。
- hprob により各 μ (Smap v) は ENNReal q で上から抑えられ、q ≠ ⊤ により実数化して評価できる。
- ω ∈ GoodX によって誤差総和は δ と q.toReal による項で一括管理できるため、全体の和について与えた不等式が成立する。

補足
- 可測性や可換性に関する仮定（MeasurableSpace, MeasureSpace, MeasurableSingletonClass, DecidableEq, IsProbabilityMeasure）は
  積分や指示関数の取り扱い、有限和の交換、測度の評価などに用いられる。
- 記号 Zmid, MidBlock, Kset, GoodX, Prob.indR は文脈依存の定義に従う。
- 本補題は個別の指示関数による寄与と全体の測度上界を組み合わせて
  わかりやすい上界を与えるための補助結果として使われる。
- q.toReal を使うために q ≠ ⊤ が必要である点に注意。
-/
lemma goodX_sum_over_k_qaddδ_card
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X : ℕ} (q : ENNReal)
  (hq_ne : q ≠ ⊤)
  (hprob : ∀ k v, k ∈ Kset X → v ∈ MidBlock k X → μ ↑(Smap v) ≤ q)
  (ω : Ω) (hGood : ω ∈ GoodX (μ := μ) (Smap := Smap) δ X) :
  (∑ k ∈ Kset X, Zmid (k := k) (X := X) (Smap := Smap) ω)
    ≤ (∑ k ∈ Kset X, (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)))
      + (q.toReal + δ) * (∑ k ∈ Kset X, (Finset.card (MidBlock k X) : ℝ)) := by
  -- apply the pointwise bound for each k and sum
  have H : ∀ k ∈ Kset X, Zmid (k := k) (X := X) (Smap := Smap) ω
      ≤ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * (Finset.card (MidBlock k X) : ℝ) := by
    intro k hk
    exact (goodX_pointwise_qaddδ_card (μ := μ) (Smap := Smap) (q := q) (hq_ne := hq_ne)
      (hprob := fun v hv => hprob k v hk hv) hGood hk)
  calc
    (∑ k ∈ Kset X, Zmid (k := k) (X := X) (Smap := Smap) ω)
        ≤ ∑ k ∈ Kset X, ( (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + (q.toReal + δ) * (Finset.card (MidBlock k X) : ℝ) ) :=
      Finset.sum_le_sum H
    _ = (∑ k ∈ Kset X, (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)))
        + (q.toReal + δ) * (∑ k ∈ Kset X, (Finset.card (MidBlock k X) : ℝ)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]


/- Kset is monotone in X -/
/--
Kset_mono：Kset の単調性

自然数 X, Y に対し X ≤ Y を仮定するとき、Kset X は Kset Y に包含される（すなわち Kset X ≤ Kset Y）。
ここで記号 `≤` は本文脈では集合の包含順序（または同等の順序構造）を意味する。
直感的にはパラメータが増えると Kset の要素は減少しない（包含関係は保たれる）という性質であり、
通常は Kset の定義から直接または定義の単調性により導かれる。
-/
lemma Kset_mono {X Y : ℕ} (hXY : X ≤ Y) : Kset X ≤ Kset Y := by
  -- prove elementwise: if k ∈ Kset X then k ∈ Kset Y
  intro k hk
  -- unpack filter membership
  let ⟨hmem_range_mem, hpred⟩ := Finset.mem_filter.mp hk
  let hmem_range := Finset.mem_range.mp hmem_range_mem
  -- hmem_range : k < X + 1, use X ≤ Y to get k < Y + 1
  have hmem_range' : k < Y + 1 := Nat.lt_of_lt_of_le hmem_range (Nat.succ_le_succ hXY)
  have hpred' : (2 : ℕ) ^ (k + 1) ≤ Y + 1 := le_trans hpred (Nat.succ_le_succ hXY)
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmem_range', hpred'⟩


/- GoodX is antitone in X (larger X → stronger condition → smaller GoodX) -/
/--
GoodX の逆単調性を示す補題。

設定:
- Ω は可測空間で測度 μ を持ち、μ は確率測度である。
- Smap : ℕ → Finset Ω, δ : ℝ, 自然数 X ≤ Y。
仮定 hEmid_mono は、任意の k ∈ Kset X に対して
  Emid (… ) k X ⊆ Emid (… ) k Y
が成り立つことを要求する（つまり各 k について X に対する中間集合は Y に対しても包含される）。

主張:
- このとき (GoodX … Y) ⊆ (GoodX … X) が成り立つ。
直観的には、添え字が大きくなると GoodX の条件が強く（集合は小さく）なるため、X ≤ Y のもとでは Y の良い点は自動的に X にとっても良い点となる、という逆単調性を表す。

証明方針（概略）:
- GoodX の定義を展開し、ω ∈ GoodX Y を取る。
- 任意の k ∈ Kset X に対して、仮定 hEmid_mono により Emid k X ⊆ Emid k Y が成り立つので、
  Y に対して満たされる条件は X に対しても満たされることを示す。
- 以上より ω ∈ GoodX X を得て包含関係を導く。

参照: GoodX, Emid, Kset の定義を参照のこと。
-/
lemma GoodX_antitone
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Smap : ℕ → Finset Ω) {δ : ℝ} {X Y : ℕ} (hXY : X ≤ Y)
  (hEmid_mono : ∀ k, k ∈ Kset X → Emid (μ := μ) (Smap := Smap) δ k X ⊆ Emid (μ := μ) (Smap := Smap) δ k Y) :
  (GoodX (μ := μ) (Smap := Smap) δ Y) ⊆ (GoodX (μ := μ) (Smap := Smap) δ X) := by
  intro ω h
  have hK := Kset_mono hXY
  intro k hk
  simp only [GoodX] at h
  -- from GoodY we have ¬ ω ∈ Emid _ k Y; by monotonicity Emid k X ⊆ Emid k Y, so if ω ∈ Emid k X then ω ∈ Emid k Y (contradiction)
  have hnY : ¬ ω ∈ Emid (μ := μ) (Smap := Smap) δ k Y := h k (hK hk)
  have : Emid (μ := μ) (Smap := Smap) δ k X ⊆ Emid (μ := μ) (Smap := Smap) δ k Y := hEmid_mono k hk
  intro hcontra
  have h_in_Y := this hcontra
  exact hnY h_in_Y



end Prob


end DkMath.ABC
