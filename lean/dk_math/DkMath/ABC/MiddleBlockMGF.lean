/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleZmidBasic

#print "file: DkMath.ABC.MiddleBlockMGF"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `MiddleBlockTail.lean` から切り出した MGF / Chernoff owner。
  `QuadMGF` / `SubGammaParam` / `Zmid` MGF wrappers と、
  fixed-block Chernoff 受け口を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

namespace Prob


/-- 抽象 MGF インターフェイス：`Z` の中心化 MGF が `exp(A lambda ^ 2)` で抑えられる。 -/
structure QuadMGF
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A : ℝ) : Prop where
(intg : ∀ lambda ≥ 0, Integrable (fun ω => Real.exp (-lambda * (Z ω - m))) μ)
(bnd : ∀ lambda ≥ 0, μ[fun ω => Real.exp (-lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2))
(Apos : 0 < A)


/-- `exp(lambda (Z-m))` 側の二次 MGF 上界（正号版） -/
structure QuadMGFPos
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A : ℝ) : Prop where
  (intg : ∀ lambda ≥ 0, Integrable (fun ω => Real.exp (lambda * (Z ω - m))) μ)
  (bnd : ∀ lambda ≥ 0, μ[fun ω => Real.exp (lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2))
  (Apos : 0 < A)


/- Janson/Suen style "sub-gamma" parameterization for log-MGF upper bounds.
   This is a small POD record capturing the usual shape
   log E exp(lambda (Z-m)) ≤ v lambda ^ 2 / (1 - c lambda) for 0 ≤ lambda ≤ lambda0.
-/
structure SubGammaParam where
  v : ℝ
  c : ℝ
  lambda0 : ℝ
  hv  : 0 ≤ v
  hc  : 0 ≤ c
  hlambda0 : 0 < lambda0


/- From a sub-gamma bound (valid up to lambda0) we can cut lambda small (≤ lambda0/2)
   and obtain a pure quadratic upper bound A lambda ^ 2 with A = 2 v.
   The lemma below is a receive-port: it expects a pointwise log-MGF bound `h_sub`.
   Some project-specific numeric relations (e.g. P.c * P.lambda0 ≤ 1) are passed as
   extra hypotheses so the lemma remains generic but usable.
-/
/-- Local "up-to" quadratic MGF witness.
  This records integrability and quadratic MGF bounds only for 0 ≤ lambda ≤ L.
  It is intentionally local so callers need only provide integrability on the small lambda-range. -/
structure QuadMGFPosUpTo {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℝ) (m A L : ℝ) : Prop where
  intg : ∀ (lambda : ℝ) (_ : 0 ≤ lambda) (_ : lambda ≤ L), Integrable (fun ω => Real.exp (lambda * (Z ω - m))) μ
  bnd  : ∀ (lambda : ℝ) (_ : 0 ≤ lambda) (_ : lambda ≤ L), μ[fun ω => Real.exp (lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2)
  Apos : 0 < A


/-- From a sub-gamma bound (valid up to P.lambda0) we can cut lambda small (≤ P.lambda0/2)
   and obtain a pure quadratic upper bound A * lambda ^ 2 with A = 2 * P.v.
   This receive-port expects the caller to provide integrability on the interval [0, P.lambda0/2]
   (h_intg). In return it provides a QuadMGFPosUpTo witness valid up to L = P.lambda0/2. -/
lemma quad_from_subgamma_upto
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m : ℝ)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
  -- integrability hypothesis only on the small lambda-range [0, P.lambda0/2]
  (h_intg : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 / 2 → Integrable (fun ω => Real.exp (lambda * (Z ω - m))) μ)
  -- sub-gamma hypothesis: valid for 0 ≤ lambda ≤ P.lambda0
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Z ω - m))] ≤ Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda))) :
  QuadMGFPosUpTo (μ := μ) Z m (2 * P.v) (P.lambda0 / 2) := by
  let A := 2 * P.v
  have Apos : 0 < A := by
    exact mul_pos (by norm_num) h_vpos
  refine QuadMGFPosUpTo.mk (fun lambda h0 hL => ?intg) (fun lambda h0 hL => ?bnd) Apos
  · -- integrability on the small range is given by h_intg
    exact h_intg (by exact h0) (by exact hL)
  · -- bound on the small range: use the sub-gamma bound and the denominator lower bound 1 - c * lambda ≥ 1/2
    have hden_ge : 1 - P.c * lambda ≥ (1 : ℝ) / 2 := by
      have h1 : P.c * lambda ≤ P.c * (P.lambda0 / 2) := mul_le_mul_of_nonneg_left hL P.hc
      have h2 : P.c * (P.lambda0 / 2) = (P.c * P.lambda0) / 2 := by ring
      have h3 : (P.c * P.lambda0) / 2 ≤ 1 / 2 := by
        have two_pos : 0 < (2 : ℝ) := by norm_num
        have inv_nonneg : 0 ≤ (2 : ℝ)⁻¹ := le_of_lt (inv_pos.mpr two_pos)
        exact mul_le_mul_of_nonneg_right h_clambda0_le_one inv_nonneg
      linarith
    have hsub := h_sub (by exact h0) (by linarith [hL, P.hlambda0])
    have : μ[fun ω => Real.exp (lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2) := by
      refine le_trans hsub ?_
      -- show P.v * lambda ^ 2 / (1 - P.c * lambda) ≤ A * lambda ^ 2
      have a_le_b : (1 : ℝ) / 2 ≤ 1 - P.c * lambda := by linarith [hden_ge]
      have recip_le := one_div_le_one_div_of_le (by norm_num : 0 < (1 : ℝ) / 2) a_le_b
      have mul_nonneg' : 0 ≤ P.v * lambda ^ 2 := mul_nonneg P.hv (pow_two_nonneg lambda)
      have pow_le : P.v * lambda ^ 2 / (1 - P.c * lambda) ≤ A * lambda ^ 2 := by
        have mul_le := mul_le_mul_of_nonneg_left recip_le mul_nonneg'
        have h2 : P.v * lambda ^ 2 / (1 - P.c * lambda) ≤ P.v * lambda ^ 2 * (1 / (1 / 2)) := by
          simpa [div_eq_mul_inv, one_div] using mul_le
        have h3 : P.v * lambda ^ 2 * (1 / (1 / 2)) = A * lambda ^ 2 := by ring
        exact le_trans h2 (le_of_eq h3)
      exact (Real.exp_le_exp.mpr pow_le)
    exact this



/-- Specialize the sub-gamma → quad lemma to the mid-block random variable Zmid.
   This is the Janson/Suen receive-port: callers supply a log-MGF bound `h_sub` for Zmid
   (e.g. proven by counting overlaps / covariance control), and we return a `QuadMGFPos`.
-/
theorem mgf_midblock_via_janson_pos {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (P : SubGammaParam)
  (h_vpos : 0 < P.v)
  (h_clambda0_le_one : P.c * P.lambda0 ≤ 1)
  -- integrability on the small lambda range [0, P.lambda0/2]
  (h_intg : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 / 2 →
      Integrable (fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))) μ)
  (h_sub : ∀ {lambda : ℝ}, 0 ≤ lambda → lambda ≤ P.lambda0 →
      μ[fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))))] ≤
      Real.exp (P.v * lambda ^ 2 / (1 - P.c * lambda))) :
  QuadMGFPosUpTo (μ := μ)
    (Zmid (k := k) (X := X) (Smap := Smap))
    (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
    (2 * P.v) (P.lambda0 / 2) :=
  quad_from_subgamma_upto (μ := μ) (Z := Zmid (k := k) (X := X) (Smap := Smap)) (m := ∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) P h_vpos h_clambda0_le_one (fun h0 hL => h_intg (by exact h0) (by exact hL)) (fun h0 hL => h_sub (by exact h0) (by linarith [hL, P.hlambda0]))



/-- 正号版 MGF から上側 Chernoff：`P(Z ≥ m+τ) ≤ exp(-τ²/(4A))` -/
lemma chernoff_upper_from_quad_mgf_pos
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A τ : ℝ)
  (H : QuadMGFPos (μ := μ) Z m A) (hτ : 0 ≤ τ) :
  μ.real {ω | Z ω ≥ m + τ} ≤ Real.exp (- τ^2 / (4*A)) := by
  -- `H`（正号版 MGF）から `-Z, -m` に対する QuadMGF を構成し、それで下側 Chernoff を得る。
  have Hneg : QuadMGF (μ := μ) (fun ω => -Z ω) (-m) A :=
    QuadMGF.mk
      (fun lambda hl => by
        -- relate the integrand to H.intg via a.e. equality and use integrable_congr
        have ae_eq : (fun ω => Real.exp (-lambda * ((-Z ω) - (-m)))) =ᵐ[μ] fun ω => Real.exp (lambda * (Z ω - m)) :=
          MeasureTheory.ae_of_all μ fun ω => by
            have h : -lambda * ((-Z ω) - (-m)) = lambda * (Z ω - m) := by ring
            exact congrArg Real.exp h
        have hraw := H.intg lambda hl
        -- transfer integrability from RHS to LHS using the ae equality
        exact (integrable_congr ae_eq).mpr hraw)
      (fun lambda hl => by
        -- transfer the integral bound using integral_congr_ae since the functions are a.e. equal
        have ae_eq : (fun ω => Real.exp (-lambda * ((-Z ω) - (-m)))) =ᵐ[μ] fun ω => Real.exp (lambda * (Z ω - m)) :=
          MeasureTheory.ae_of_all μ fun ω => by
            have h : -lambda * ((-Z ω) - (-m)) = lambda * (Z ω - m) := by ring
            exact congrArg Real.exp h
        have hraw := H.bnd lambda hl
        -- rewrite the integral of the RHS to the integral of the LHS using the ae equality
        rw [← integral_congr_ae ae_eq] at hraw
        exact hraw)
      H.Apos
  have hmgf : ∀ lambda ≥ 0,
      Integrable (fun ω => Real.exp (-lambda * ((fun ω => -Z ω) ω - -m))) μ ∧
      μ[fun ω => Real.exp (-lambda * ((fun ω => -Z ω) ω - -m))] ≤ Real.exp (A * lambda ^ 2) :=
    fun lambda hl => ⟨Hneg.intg lambda hl, Hneg.bnd lambda hl⟩
  have hres := chernoff_lower_tail (μ := μ) (Z := fun ω => -Z ω) (m := -m) (A := A) (tau := τ) hmgf Hneg.Apos hτ
  -- 事象の対応：{-Z ≤ -m - τ} = {Z ≥ m + τ}
  have : {ω | -Z ω ≤ -m - τ} = {ω | Z ω ≥ m + τ} := by
    ext ω; simp [le_sub_iff_add_le, add_comm]
  simpa [this] using hres



/-- 抽象 MGF から Chernoff（下側尾）を即時に得る小橋渡し。 -/
lemma chernoff_from_quad_mgf
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A τ : ℝ)
  (H : QuadMGF (μ := μ) Z m A) (hτ : 0 ≤ τ) :
  μ.real {ω | Z ω ≤ m - τ} ≤ Real.exp (- τ^2 / (4*A)) := by
  -- 既存の `chernoff_lower_tail` をフォワードするだけ
  have hmgf : ∀ lambda ≥ 0,
      Integrable (fun ω => Real.exp (-lambda * (Z ω - m))) μ ∧
      μ[fun ω => Real.exp (-lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2) :=
    fun lambda hlambda => ⟨H.intg lambda hlambda, H.bnd lambda hlambda⟩
  exact chernoff_lower_tail (μ := μ) (Z := Z) (m := m) (A := A) (tau := τ) hmgf H.Apos hτ


-- ### Local Chernoff: 1本の `lambda` から上側尾を出す

/- Markov の一発芸：
    `0 ≤ lambda` かつ `E[exp(lambda (Z-m))] ≤ exp(A lambda ^ 2)` なら
    `P(Z ≥ m + τ) ≤ exp(-lambda τ) * exp(A lambda ^ 2)`. -/
lemma chernoff_upper_from_local_mgf_pos
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m : ℝ)
  {lambda A tau : ℝ}
  (hlambda : 0 ≤ lambda)
  (hintg : Integrable (fun ω => Real.exp (lambda * (Z ω - m))) μ)
  (hbnd : μ[fun ω => Real.exp (lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2)) :
  μ.real {ω | Z ω ≥ m + tau} ≤ Real.exp (-lambda * tau) * Real.exp (A * lambda ^ 2) := by
  -- 1_{Z ≥ m+tau} ≤ exp(-λ tau) · exp(λ(Z-m)) を点wiseに示す
  have hpt :
      (fun ω => (Set.indicator {ω | Z ω ≥ m + tau} (fun _ => (1 : ℝ)) ω))
        ≤ fun ω => Real.exp (-lambda * tau) * Real.exp (lambda * (Z ω - m)) := by
    intro ω
    by_cases hz : Z ω ≥ m + tau
    · -- 事象内: RHS = exp(-λtau)·exp(λ(Z-m)) ≥ exp(-λtau)·exp(λtau) = 1
      have : Real.exp (-lambda * tau) * Real.exp (lambda * (Z ω - m))
           = Real.exp ((-lambda * tau) + (lambda * (Z ω - m))) := by
        simp [Real.exp_add]
      have hineq : -lambda * tau + lambda * (Z ω - m) ≥ 0 := by
        have hZ : Z ω - m ≥ tau := by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
        nlinarith [hlambda, hZ]
      have h1_le : (1 : ℝ) ≤ Real.exp (-lambda * tau + lambda * (Z ω - m)) := by
        simpa using Real.one_le_exp_iff.mpr hineq
      simpa [Real.exp_add, mul_comm, mul_left_comm, mul_assoc, Set.indicator, hz] using h1_le
    · -- 事象外: 0 ≤ RHS（指数関数は非負）
      have : 0 ≤ Real.exp (-lambda * tau) * Real.exp (lambda * (Z ω - m)) := by
        exact mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
      simpa [Set.indicator, hz] using this
  -- Use mathlib's Chernoff lemma `measure_ge_le_exp_mul_mgf` on X := Z - m
  -- pass the numeric `lambda` explicitly (the previous code accidentally passed the
  -- proof `hlambda` as the numeric argument which caused elaboration loops).
  have h_ch := ProbabilityTheory.measure_ge_le_exp_mul_mgf tau hlambda hintg
  have mgf_eq : ProbabilityTheory.mgf (fun ω => Z ω - m) μ lambda = μ[fun ω => Real.exp (lambda * (Z ω - m))] := by simp [ProbabilityTheory.mgf]
  have mgf_le : ProbabilityTheory.mgf (fun ω => Z ω - m) μ lambda ≤ Real.exp (A * lambda ^ 2) := by
    simpa [mgf_eq] using hbnd
  have set_eq : {ω | Z ω ≥ m + tau} = {ω | tau ≤ Z ω - m} := by
    ext ω; simp [le_sub_iff_add_le, add_comm]
  calc
    μ.real {ω | Z ω ≥ m + tau} = μ.real ({ω | tau ≤ Z ω - m}) := by rw [set_eq]
    _ ≤ Real.exp (-lambda * tau) * ProbabilityTheory.mgf (fun ω => Z ω - m) μ lambda := by simpa using h_ch
    _ ≤ Real.exp (-lambda * tau) * Real.exp (A * lambda ^ 2) := by exact mul_le_mul_of_nonneg_left mgf_le (by exact Real.exp_nonneg _)


-- ### Up-to MGF witness からの「範囲付き」上側 Chernoff

/- `QuadMGFPosUpTo`（0 ≤ lambda ≤ L で有効）から上側 Chernoff。
    `tau ≤ 2 A L` なら最適 `lambda = tau/(2A)` を使って
    `exp(- tau^2 / (4 A))` 形、さもなくば `lambda = L` で
    `exp(- L tau + A L^2)` 形。 -/
lemma chernoff_upper_from_quad_mgf_upto
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A L : ℝ)
  (H : QuadMGFPosUpTo (μ := μ) Z m A L)
  (hL0 : 0 ≤ L) {tau : ℝ} (htau : 0 ≤ tau) :
  μ.real {ω | Z ω ≥ m + tau}
    ≤ if tau ≤ 2 * A * L
       then Real.exp ( - (tau / (2 * A)) * tau + A * (tau / (2 * A)) ^ 2 )
       else Real.exp ( - L * tau + A * L ^ 2 ) := by
  by_cases hcase : tau ≤ 2 * A * L
  · -- λ* = tau/(2A) がレンジに収まる
    have hApos : 0 < A := H.Apos
    have h_nonneg : 0 ≤ tau / (2 * A) := by
      have pos2A : 0 < 2 * A := mul_pos (by norm_num) hApos
      exact div_nonneg htau (le_of_lt pos2A)
    have h_le_L : tau / (2 * A) ≤ L := by
      have hle : tau ≤ 2 * A * L := hcase
      have pos2A : 0 < 2 * A := mul_pos (by norm_num) hApos
      exact (div_le_iff (by exact pos2A)).mpr (by simpa [mul_comm] using hle)
    have hintg := H.intg (tau / (2 * A)) h_nonneg h_le_L
    have hbnd  := H.bnd  (tau / (2 * A)) h_nonneg h_le_L
    have hres := chernoff_upper_from_local_mgf_pos (μ := μ) (Z := Z) (m := m)
      (lambda := tau / (2 * A)) (A := A) (tau := tau)
      h_nonneg hintg hbnd
    -- use if_pos to reduce the expected if-expression to the then-branch
    rw [if_pos hcase]
    simpa [Real.exp_add, add_comm, add_left_comm, add_assoc, mul_comm] using hres
  · -- レンジ外：lambda は L を使う
    have hL_nonneg : 0 ≤ L := hL0
    have hintg := H.intg L hL_nonneg (le_of_eq rfl)
    have hbnd  := H.bnd  L hL_nonneg (le_of_eq rfl)
    have hresL := chernoff_upper_from_local_mgf_pos (μ := μ) (Z := Z) (m := m)
      (lambda := L) (A := A) (tau := tau)
      hL_nonneg hintg hbnd
    -- use if_neg to reduce the expected if-expression to the else-branch
    simpa [Real.exp_add, add_comm, add_left_comm, add_assoc, if_neg hcase] using hresL


-- ### Zmid 用の短い上側尾（Janson/Suen 版の受け口）

theorem mid_block_upper_hp_dep
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
  {tau : ℝ} (htau : 0 ≤ tau) :
  μ.real {ω | Zmid (k := k) (X := X) (Smap := Smap) ω
              ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) + tau}
    ≤ if tau ≤ 2 * (2 * P.v) * (P.lambda0 / 2)
       then Real.exp ( - (tau / (2 * (2 * P.v))) * tau + (2 * P.v) * (tau / (2 * (2 * P.v))) ^ 2 )
       else Real.exp ( - (P.lambda0 / 2) * tau + (2 * P.v) * (P.lambda0 / 2) ^ 2 ) := by
  -- QuadMGFPosUpTo witness for Zmid（Janson受け口）
  have H :=
    mgf_midblock_via_janson_pos (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one
      (by
        intro lambda h0 hL
        -- integrable_exp_of_mid_block gives integrability of exp(lambda * ∑ indR),
        -- so for the centered version exp(lambda * (Z - m)) we factor out the constant exp(-lambda * m)
        have hraw := integrable_exp_of_mid_block (μ := μ) (k := k) (X := X) (Smap := Smap) (lambda := lambda)
        let m := ∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)
        have : (fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
          = fun ω => Real.exp (-lambda * m) * Real.exp (lambda * (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω)) := by
          funext ω
          dsimp [Zmid]
          have : lambda * ((Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω) - m) = -lambda * m + lambda * Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω := by
            ring_nf
          rw [this, Real.exp_add]
        have hmul := Integrable.const_mul hraw (Real.exp (-lambda * m))
        convert hmul using 1
      )
      (by intro lambda h0 hL; simpa using h_sub h0 (by linarith [hL, P.hlambda0]))
  -- L = P.lambda0/2 は非負
  have hL0 : 0 ≤ P.lambda0 / 2 := le_of_lt (by simpa using half_pos P.hlambda0)
  -- Chernoff（up-to 版）を適用
  simpa using
    chernoff_upper_from_quad_mgf_upto (μ := μ)
      (Z := Zmid (k := k) (X := X) (Smap := Smap))
      (m := ∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
      (A := (2 * P.v)) (L := P.lambda0 / 2) H hL0 htau

-- up-to 版 Chernoff を単純な `exp(AL^2) * exp(-L * tau)` に畳む安全版
lemma chernoff_upper_from_quad_mgf_upto_linear
  {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A L : ℝ)
  (H : QuadMGFPosUpTo (μ := μ) Z m A L)
  (hL0 : 0 ≤ L) {tau : ℝ} (htau : 0 ≤ tau) :
  μ.real {ω | Z ω ≥ m + tau} ≤ Real.exp (A * L ^ 2) * Real.exp (- L * tau) := by
  have h := chernoff_upper_from_quad_mgf_upto (μ := μ) (Z := Z) (m := m) (A := A) (L := L) H hL0 htau
  by_cases hcase : tau ≤ 2 * A * L
  · -- then-branch（最適 λ）: use the tau/(2A) branch of `h` and compare exponents
    have hApos : 0 < A := H.Apos
    -- reduce `h` to the then-branch form (no `simpa` to avoid fragile simp failures)
    have h_then := h; rw [if_pos hcase] at h_then
    -- h_then : μ.real {..} ≤ Real.exp (-(tau/(2*A)) * tau + A * (tau/(2*A))^2)
    -- derive that the then-branch exponent is ≤ (-L * tau + A * L ^ 2)
    -- Consider the difference RHS - LHS and show it equals a nonnegative quantity.
    have hsq : 0 ≤ (tau - 2 * A * L) ^ 2 := sq_nonneg (tau - 2 * A * L)
    have eqsq : (tau - 2 * A * L) ^ 2 = tau ^ 2 - 4 * A * L * tau + 4 * A ^ 2 * L ^ 2 := by ring_nf
    have diff_def : (-L * tau + A * L ^ 2) - (-(tau / (2 * A)) * tau + A * (tau / (2 * A)) ^ 2) = (tau - 2 * A * L) ^ 2 / (4 * A) := by
      -- algebraic normalization; field_simp will clear denominators using A>0, then ring_nf finishes
      field_simp [ne_of_gt hApos]
      ring_nf
    -- RHS - LHS is nonnegative since numerator is a square and denominator 4*A > 0
    have pos4A : 0 < 4 * A := by nlinarith [hApos]
    have diff_nonneg : 0 ≤ (tau - 2 * A * L) ^ 2 / (4 * A) := div_nonneg (sq_nonneg (tau - 2 * A * L)) (le_of_lt pos4A)
    -- rewrite the nonnegativity of the RHS into the difference form and conclude the inequality
    rw [← diff_def] at diff_nonneg
    have leq : (-(tau / (2 * A)) * tau + A * (tau / (2 * A)) ^ 2) ≤ - L * tau + A * L ^ 2 := by linarith
    -- apply monotonicity of exp to lift to exponentials and chain with the bound from `h_then`
    have exp_le := Real.exp_le_exp.mpr leq
    have bound := le_trans h_then exp_le
    -- rewrite target exponential to product form exactly in the desired order
    have rhs_eq : Real.exp (-L * tau + A * L ^ 2) = Real.exp (A * L ^ 2) * Real.exp (-L * tau) := by
      rw [add_comm, Real.exp_add]
    rw [rhs_eq] at bound
    exact bound
  · -- else-branch（λ = L）: directly rewrite the exponent into product form and finish
    have h_else := h
    rw [if_neg hcase] at h_else
    -- rewrite the single-exponent `Real.exp (-L * tau + A * L ^ 2)` into the product
    -- `Real.exp (A * L ^ 2) * Real.exp (-L * tau)` so the order matches the goal.
    have rhs_eq : Real.exp (-L * tau + A * L ^ 2) = Real.exp (A * L ^ 2) * Real.exp (-L * tau) := by
      rw [add_comm, Real.exp_add]
    rw [rhs_eq] at h_else
    exact h_else

-- mid-block 上側尾を A := 2*P.v, L := P.lambda0/2 に特化し、C * exp(-c * |MidBlock|) 形にする
theorem mid_block_upper_hp_dep_expCard
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
  {δ : ℝ} (hδ : 0 < δ) :
  μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤
  Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2) * Real.exp (-(P.lambda0 / 2) * (δ * (Finset.card (MidBlock k X) : ℝ))) := by
  let m := ∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)
  have htau : 0 ≤ δ * (Finset.card (MidBlock k X) : ℝ) := by exact mul_nonneg (le_of_lt hδ) (by exact Nat.cast_nonneg _)
  -- build QuadMGFPosUpTo witness via the Janson receive-port
  let H := mgf_midblock_via_janson_pos (μ := μ) (k := k) (X := X) (Smap := Smap)
    P h_vpos h_clambda0_le_one
    (by
      intro lambda h0 hL
      have hraw := integrable_exp_of_mid_block (μ := μ) (k := k) (X := X) (Smap := Smap) (lambda := lambda)
      have : (fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
        = fun ω => Real.exp (-lambda * m) * Real.exp (lambda * (Finset.sum (MidBlock k X) fun v => Prob.indR (Smap v) ω)) := by
        funext ω; dsimp [Zmid]; ring_nf; rw [sub_eq_add_neg, Real.exp_add]; rw [mul_comm]
      have hmul := Integrable.const_mul hraw (Real.exp (-lambda * m))
      convert hmul using 1)
    (by intro lambda h0 hL; simpa using h_sub (by exact h0) (by linarith [hL, P.hlambda0]))
  have hL0 : 0 ≤ P.lambda0 / 2 := le_of_lt (by simpa using half_pos P.hlambda0)
  have bound := chernoff_upper_from_quad_mgf_upto_linear (μ := μ)
    (Z := Zmid (k := k) (X := X) (Smap := Smap)) (m := m) (A := 2 * P.v) (L := P.lambda0 / 2) H hL0 (tau := δ * (Finset.card (MidBlock k X) : ℝ)) htau
  -- `m` was defined as the sum of integrals above; keep it as-is and return the bound
  exact bound

/- Fold the explicit bound into a cleaner C * exp(-c * |MidBlock|) form -/
theorem mid_block_upper_hp_dep_expCard_factor
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
  {δ : ℝ} (hδ : 0 < δ) :
  μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤
  (Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by
  have h := mid_block_upper_hp_dep_expCard (μ := μ) (k := k) (X := X) (Smap := Smap)
    P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
  -- rewrite the exponent `-(P.lambda0/2) * (δ * card)` into the form `-((P.lambda0/2) * δ) * card`
  have card_cast : (Finset.card (MidBlock k X) : ℝ) = (Finset.card (MidBlock k X) : ℝ) := rfl
  have exp_rewrite : Real.exp (-(P.lambda0 / 2) * (δ * (Finset.card (MidBlock k X) : ℝ)))
      = Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by
    -- arithmetic normalization by `ring` and lift via `Real.exp`
    have : (-(P.lambda0 / 2) * (δ * (Finset.card (MidBlock k X) : ℝ)))
      = -((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ) := by ring
    exact congrArg Real.exp this
  -- apply the rewrite on the RHS of the bound `h` and finish
  have rhs_eq : (Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)) * Real.exp (-(P.lambda0 / 2) * (δ * (Finset.card (MidBlock k X) : ℝ)))
      = (Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)) * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by
    rw [exp_rewrite]
  rw [rhs_eq] at h
  exact h

-- ---------------------------------------------------------------------------
/- Provide an existence form: there exist C ≥ 0 and c > 0 such that the bound holds -/
theorem mid_block_upper_hp_dep_expCard_exists
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
  {δ : ℝ} (hδ : 0 < δ) :
  ∃ (C c : ℝ), 0 ≤ C ∧ 0 < c ∧
    μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by
  -- choose explicit constants C and c
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let c := (P.lambda0 / 2) * δ
  have hC_nonneg : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hc_pos : 0 < c := mul_pos (by simpa using half_pos P.hlambda0) hδ
  have hbound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
    P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
  -- rewrite the RHS of hbound to use c
  have exp_rewrite2 : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
      = Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by simp [c]
  have rhs_eq2 : C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) = C * Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by rw [exp_rewrite2]
  -- 以下は use C, c 内部挙動を明示的に示す形で存在を与える
  exact ⟨C, c, hC_nonneg, hc_pos, by
    -- 目標の確率上界は `factor` 版からの書換えで得る
    have : μ.real {ω |
        Zmid (k := k) (X := X) (Smap := Smap) ω
          ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
            + δ * (Finset.card (MidBlock k X) : ℝ)}
        ≤ C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) := by
      simpa [C] using hbound
    -- `c := (P.lambda0/2)*δ` で書き換える
    have exp_rewrite2 : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
        = Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by simp [c]
    have rhs_eq2 : C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) = C * Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by rw [exp_rewrite2]
    simpa [rhs_eq2] using this⟩


/- Provide an existence form: there exist C ≥ 0 and c > 0 such that the bound holds -/
theorem mid_block_upper_hp_dep_expCard_exists'
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
  {δ : ℝ} (hδ : 0 < δ) :
  ∃ (C c : ℝ), 0 ≤ C ∧ 0 < c ∧
    μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ C * Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by
  -- choose explicit constants C and c
  let C := Real.exp ((2 * P.v) * (P.lambda0 / 2) ^ 2)
  let c := (P.lambda0 / 2) * δ
  have hC_nonneg : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hc_pos : 0 < c := mul_pos (by simpa using half_pos P.hlambda0) hδ
  have hbound := mid_block_upper_hp_dep_expCard_factor (μ := μ) (k := k) (X := X) (Smap := Smap)
    P h_vpos h_clambda0_le_one h_sub (hδ := hδ)
  -- rewrite the RHS of hbound to use c
  have exp_rewrite2 : Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ))
      = Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by simp [c]
  have rhs_eq2 : C * Real.exp (-((P.lambda0 / 2) * δ) * (Finset.card (MidBlock k X) : ℝ)) = C * Real.exp (- c * (Finset.card (MidBlock k X) : ℝ)) := by rw [exp_rewrite2]
  use C, c


-- Zmid の上側尾を τ = δ * card に特化した形（Janson/Suen 受け口版）
theorem mid_block_upper_hp_dep_card
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
  {δ : ℝ} (hδ : 0 < δ) :
  μ.real {ω |
      Zmid (k := k) (X := X) (Smap := Smap) ω
        ≥ (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ))
          + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤
  if δ * (Finset.card (MidBlock k X) : ℝ) ≤ 2 * (2 * P.v) * (P.lambda0 / 2)
  then
    Real.exp
      ( - ( (δ * (Finset.card (MidBlock k X) : ℝ)) / (2 * (2 * P.v)) )
        * (δ * (Finset.card (MidBlock k X) : ℝ))
        + (2 * P.v) * ( (δ * (Finset.card (MidBlock k X) : ℝ)) / (2 * (2 * P.v)) ) ^ 2 )
  else
    Real.exp
      ( - (P.lambda0 / 2) * (δ * (Finset.card (MidBlock k X) : ℝ))
        + (2 * P.v) * (P.lambda0 / 2) ^ 2 ) := by
  have htau : 0 ≤ δ * (Finset.card (MidBlock k X) : ℝ) := by
    exact mul_nonneg (le_of_lt hδ) (by exact Nat.cast_nonneg _)
  simpa using
    mid_block_upper_hp_dep (μ := μ) (k := k) (X := X) (Smap := Smap)
      P h_vpos h_clambda0_le_one h_sub (tau := δ * (Finset.card (MidBlock k X) : ℝ)) htau

  -- (block removed: duplicate bound and m_eq)



-----------------------------------------------------------------------------------------------------------------------
-- === mgf_midblock_via_indep の let bnd 分割用 private lemma スケルトン ===

/-- Proves measurability of the indicator function for a given finite set at index `v`. -/
private lemma indR_measurable_each
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (Smap : ℕ → Finset Ω) (v : ℕ) :
  Measurable (fun ω => Prob.indR (Smap v) ω) :=
  -- delegate to the already-proved lemma `indR_measurable` in `ABC.lean`
  by
    exact Prob.indR_measurable (S := Smap v)


/-- Proves that the indicator function `Prob.indR (Smap v)` is integrable with respect to a probability measure. -/
private lemma indR_integrable_each
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Smap : ℕ → Finset Ω) (v : ℕ) :
  Integrable (fun ω => Prob.indR (Smap v) ω) μ :=
  by
    -- Use that indR takes values in [0,1] a.e. and is a.e. strongly measurable, hence integrable on a probability space
    have hbound : ∀ᵐ ω ∂μ, 0 ≤ Prob.indR (Smap v) ω ∧ Prob.indR (Smap v) ω ≤ 1 :=
      Prob.indR_range01_ae_of_all (μ := μ) (S := Smap v)
    have hmeas := (Prob.indR_aestronglyMeasurable (μ := μ) (S := Smap v)).aemeasurable
    exact Integrable.of_mem_Icc 0 1 hmeas hbound


/-- Expectation identity: E[Zmid] = ∑ μ(Smap v) (as real) -/
lemma EZmid_eq_sum_probs {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] {k X : ℕ} (Smap : ℕ → Finset Ω) :
  (∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ) = (∑ v ∈ MidBlock k X, (μ ↑(Smap v)).toReal) := by
  -- rewrite integral of finite sum as finite sum of integrals, using integrability of each summand
  dsimp [Zmid]
  have fint : (∫ ω, (∑ v ∈ MidBlock k X, Prob.indR (Smap v) ω) ∂μ) = (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) := by
    apply integral_finset_sum
    intro v hv
    exact indR_integrable_each (μ := μ) (Smap := Smap) (v := v)
  have hsum : (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) = (∑ v ∈ MidBlock k X, (μ ↑(Smap v)).toReal) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact (integral_indR_eq_measure (μ := μ) (S := Smap v))
  calc
    (∫ ω, Zmid (k := k) (X := X) (Smap := Smap) ω ∂μ) = (∫ ω, (∑ v ∈ MidBlock k X, Prob.indR (Smap v) ω) ∂μ) := by rfl
    _ = (∑ v ∈ MidBlock k X, (∫ ω, Prob.indR (Smap v) ω ∂μ)) := by exact fint
    _ = (∑ v ∈ MidBlock k X, (μ ↑(Smap v)).toReal) := by exact hsum


/-- Bounds the moment generating function of a centered indicator random variable by `exp(l^2 / 8)`. -/
private lemma mgf_bound_centered_each
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Smap : ℕ → Finset Ω) (v : ℕ) (l : ℝ) :
  ProbabilityTheory.mgf (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l
    ≤ Real.exp (l ^ 2 / 8) :=
  by
    -- Apply the Hoeffding-style mgf bound `mgf_bound_unit01` from `ABC.lean`.
    have hmeas : Measurable (fun ω => Prob.indR (Smap v) ω) := Prob.indR_measurable (S := Smap v)
    have hint : Integrable (fun ω => Prob.indR (Smap v) ω) μ := indR_integrable_each (μ := μ) (Smap := Smap) (v := v)
    have h01 : ∀ᵐ ω ∂μ, 0 ≤ Prob.indR (Smap v) ω ∧ Prob.indR (Smap v) ω ≤ 1 :=
      Prob.indR_range01_ae_of_all (μ := μ) (S := Smap v)
    exact mgf_bound_unit01 hmeas hint h01 l


/--
Smap で与えられる集合の指示関数を平均で中心化した確率変数のモーメント母関数（mgf）の積に対する上界。

内容の要点：
- Ω は可測空間、μ は確率測度である。
- 各 v について X_v := Prob.indR (Smap v) - ∫ ω, Prob.indR (Smap v) ω ∂μ と置くと，
  X_v はほとんど確実に値域が [-1, 1] に入る有界平均ゼロ確率変数である。
- 有界平均ゼロ変数に対する Hoeffding の補題（または同等の mgf の評価）より，
  E[exp(l * X_v)] ≤ exp(l^2 / 8) が各 v に対して成り立つ。
- よって s にわたる各因子の積は上の評価を掛け合わせることで，
  ∏_{v∈s} ProbabilityTheory.mgf (X_v) μ l ≤ (exp(l^2 / 8)) ^ (|s|) が従う。

備考：
- l は任意の実数、s は Finset ℕ。
- 証明は各因子に対する Hoeffding 型の不等式適用と積の性質から直ちに得られる。
- 必要に応じて「指示関数 - その期待値」に対する有界性の確認を行うこと。
-/
-- Bounds the product of mgfs of centered indicators by an exponential function of the set size.
private lemma prod_mgf_bound_by_exp_card
  {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (Smap : ℕ → Finset Ω) (l : ℝ) (s : Finset ℕ) :
  (Finset.prod s fun v => ProbabilityTheory.mgf (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l)
    ≤ (Real.exp (l ^ 2 / 8)) ^ (Finset.card s) :=
  by
    -- prove by induction on `s`
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      let f := fun v => ProbabilityTheory.mgf (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l
      let r := Real.exp (l ^ 2 / 8)
      have hprod : Finset.prod (insert a s) f = f a * Finset.prod s f := by rw [Finset.prod_insert ha]
      have hfa : f a ≤ r := mgf_bound_centered_each (μ := μ) (Smap := Smap) (v := a) (l := l)
      have prod_nonneg : 0 ≤ Finset.prod s f := Finset.prod_nonneg fun v hv => ProbabilityTheory.mgf_nonneg
      have step1 := mul_le_mul_of_nonneg_right hfa prod_nonneg
      have exp_nonneg : 0 ≤ r := le_of_lt (Real.exp_pos (l ^ 2 / 8))
      have step2 := mul_le_mul_of_nonneg_left ih exp_nonneg
      have tmp : f a * Finset.prod s f ≤ r * r ^ (Finset.card s) := le_trans step1 step2
      -- assemble the final inequality by a short calc chain to avoid heavy rewriting
      have final_ine : (insert a s).prod f ≤ r ^ (Finset.card (insert a s)) := by
        calc
          (insert a s).prod f = f a * Finset.prod s f := by rw [Finset.prod_insert ha]
          _ ≤ r * r ^ (Finset.card s) := tmp
          _ = r ^ (Finset.card (insert a s)) := by
            rw [Finset.card_insert_of_notMem ha, pow_succ, mul_comm]
      exact final_ine


-----------------------------------------------------------------------------------------------------------------------

/--
与えられた確率空間 (Ω, μ) と、各インデックス v に対して部分集合 Smap v を対応させる写像 Smap に対する補助定理。

仮定:
- Ω は可測空間であり、要素の比較に対して DecidableEq を備え、単点が可測である（MeasurableSingletonClass）。
- μ は確率測度（IsProbabilityMeasure）。
- 各 v に対する確率変数 Prob.indR (Smap v)（Smap v の指示関数）は、hind によって独立族であると仮定する（ProbabilityTheory.iIndepFun）。
- k, X は自然数、MidBlock k X は定義された有限集合（Finset）である。

主張:
- 中心化されたランダム変数 Zmid（引数に k, X, Smap を持つ）は、与えられた中心化定数
  m := Finset.sum (MidBlock k X) fun v => ∫ ω, Prob.indR (Smap v) ω ∂μ
  に対して二次モーメント母関数（Quadratic MGF）の評価 QuadMGF を満たす。
- 具体的には、QuadMGF (μ := μ) (Zmid ...) m (((↑(Finset.card (MidBlock k X)) / 8) + 1)) が成立する。
  ここで右辺のパラメータは MidBlock の要素数に依存する上界を与えるものであり、
  指示関数族の独立性を用いてこの二次型の MGFs の制御が可能になる。

要するに、独立な指示関数から構成される中間ブロック Zmid は、
その期待値で中心化すると、要素数に基づいた明示的な二次的 MGF の上界を満たす、という主張である。
-/
-- Proves a quadratic MGF bound for the mid-block sum Zmid using the independence of the indicator functions.
theorem mgf_midblock_via_indep {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ) :
  QuadMGF (μ := μ)
    (Zmid (k := k) (X := X) (Smap := Smap))
    (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ))
  ((↑(Finset.card (MidBlock k X)) / 8) + 1) := by
  let A := (↑(Finset.card (MidBlock k X)) / 8 : ℝ) + 1
  have hApos : 0 < A := by
    have hnum_nonneg : 0 ≤ (↑(Finset.card (MidBlock k X)) : ℝ) := by exact Nat.cast_nonneg _
    have hden_pos : 0 < (8 : ℝ) := by norm_num
    have hdiv_nonneg : 0 ≤ (↑(Finset.card (MidBlock k X)) / 8 : ℝ) := by
      apply div_nonneg
      · exact hnum_nonneg
      · exact le_of_lt hden_pos
    have : 0 < (1 : ℝ) := by norm_num
    exact add_pos_of_nonneg_of_pos hdiv_nonneg this

  let m := Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ)

  let intg : ∀ (lambda : ℝ) (h : lambda ≥ 0), Integrable (fun ω => Real.exp (-lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))) μ := by
    intro lambda hlambda
    have hraw := integrable_exp_of_mid_block (μ := μ) (k := k) (X := X) (Smap := Smap) (lambda := -lambda)
    -- rexp (-lambda*(Z - m)) = rexp (lambda*m) * rexp (-lambda*Z), so convert Integrable.const_mul accordingly
    have : (fun ω => Real.exp (-lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
      = fun ω => Real.exp (lambda * m) * Real.exp (-lambda * Zmid (k := k) (X := X) (Smap := Smap) ω) :=
      by
        funext ω
        have : -lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m) = (lambda * m) + -lambda * Zmid (k := k) (X := X) (Smap := Smap) ω := by
          ring
        rw [this]
        rw [Real.exp_add]
    have hmul := Integrable.const_mul hraw (Real.exp (lambda * m))
    convert hmul using 1

  let bnd : ∀ (l : ℝ) (h : l ≥ 0), μ[fun ω => Real.exp (-l * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))] ≤ Real.exp (A * l ^ 2) :=
    fun l hl => by
      let s := MidBlock k X
      -- express Z - m as the finite sum of centered summands (small step to avoid heavy whnf)
      -- express Z - m pointwise as the finite sum of centered summands (small step to avoid heavy whnf)
      have h_centered_def : (fun ω => Zmid (k := k) (X := X) (Smap := Smap) ω - m)
        = fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) := by
        ext ω
        dsimp [Zmid, m]
        rw [Finset.sum_sub_distrib]
      -- rewrite the integrand using the above pointwise equality
      have h_integrand_eq : (fun ω => Real.exp (-l * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
        = fun ω => Real.exp (-l * (Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)))) := by
        ext ω
        dsimp
        -- apply the pointwise equality obtained from `h_centered_def`
        have h_point := congrFun h_centered_def ω
        rw [h_point]
      rw [h_integrand_eq]
      -- now the LHS is exactly the mgf of the finite sum of centered summands at parameter -l
      have h_mgf_def :
        μ[fun ω => Real.exp (-l * (Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))))] =
          ProbabilityTheory.mgf (fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))) μ (-l) := rfl
      rw [h_mgf_def]
      have h_sum_as_fun :
        (fun ω =>
            Finset.sum s fun v =>
              (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))) =
          (∑ v ∈ s, fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) := by
        ext ω
        simp
      have h_sum_rewrite :
        ProbabilityTheory.mgf (fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))) μ (-l) =
          ProbabilityTheory.mgf (∑ v ∈ s, fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ (-l) := by
        apply congrArg (fun g => ProbabilityTheory.mgf g μ (-l))
        exact h_sum_as_fun
      rw [h_sum_rewrite]
      -- obtain independence for the centered family by composing the original independent family with x ↦ x - const
      have h_meas_g : ∀ i, Measurable (fun x => x - (∫ ω, Prob.indR (Smap i) ω ∂μ)) := by
        intro i; exact Measurable.sub measurable_id (measurable_const (a := (∫ ω, Prob.indR (Smap i) ω ∂μ)))
      let hind_centered := hind.comp (fun i => fun x => x - (∫ ω, Prob.indR (Smap i) ω ∂μ)) h_meas_g
      -- measurability of each centered summand (needed by mgf_sum)
      have h_meas_centered : ∀ i, Measurable (fun ω => Prob.indR (Smap i) ω - (∫ ω, Prob.indR (Smap i) ω ∂μ)) := by
        intro i; exact Measurable.sub (indR_measurable_each (Smap := Smap) (v := i)) (measurable_const (a := (∫ ω, Prob.indR (Smap i) ω ∂μ)))
      -- apply mgf_sum to the centered independent family to factor into product of mgfs
      have h_prod_fun :
        ProbabilityTheory.mgf
            (∑ v ∈ s, fun ω =>
              Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ
          =
        fun l =>
          Finset.prod s fun v =>
            ProbabilityTheory.mgf
              (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l := by
        funext l
        exact
          ProbabilityTheory.iIndepFun.mgf_sum hind_centered h_meas_centered s
      have h_prod :
        ProbabilityTheory.mgf
            (∑ v ∈ s, fun ω =>
              Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ (-l)
          =
        Finset.prod s fun v =>
          ProbabilityTheory.mgf
            (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ (-l) := by
        have := congrArg (fun f => f (-l)) h_prod_fun
        simpa using this
      rw [h_prod]
      -- bound each factor and assemble via the product lemma
      -- bound product of mgfs at parameter -l by using the lemma with parameter (-l)
      have h_prod_le := prod_mgf_bound_by_exp_card (μ := μ) (Smap := Smap) (l := -l) (s := s)
      -- rewrite the target upper bound using (-l)^2 = l^2 and express the power as a single exponential
      have h_step :
        (Real.exp ((-l) ^ 2 / 8)) ^ (Finset.card s) ≤ Real.exp (A * l ^ 2) := by
        -- (-l)^2 = l^2
        have h_rewrite : (Real.exp ((-l) ^ 2 / 8)) ^ (Finset.card s) = (Real.exp (l ^ 2 / 8)) ^ (Finset.card s) := by
          simp [pow_two]
        -- (exp a)^n = exp (n * a)
        have h_pow :
          (Real.exp (l ^ 2 / 8)) ^ (Finset.card s)
              = Real.exp ((Finset.card s : ℝ) * (l ^ 2 / 8)) := by
          -- use (exp a)^n = exp (n * a)
          simpa [mul_comm] using (Real.exp_nat_mul (l ^ 2 / 8) (Finset.card s)).symm
        -- reshape (card * (l^2 / 8)) = (card/8) * l^2 (solve by ring to avoid fragile simp/linarith goals)
        have h_mul : (Finset.card s : ℝ) * (l ^ 2 / 8) = ((Finset.card s : ℝ) / 8) * l ^ 2 := by ring
        -- final comparison of exponents
        have h_exp_le :
          Real.exp (((Finset.card s : ℝ) / 8) * l ^ 2)
            ≤ Real.exp (((Finset.card s : ℝ) / 8 + 1) * l ^ 2) := by
          apply Real.exp_le_exp.mpr
          simp only [add_comm]
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact pow_two_nonneg l
        -- assemble
        calc
          (Real.exp ((-l) ^ 2 / 8)) ^ (Finset.card s)
              = (Real.exp (l ^ 2 / 8)) ^ (Finset.card s) := h_rewrite
          _ = Real.exp ((Finset.card s : ℝ) * (l ^ 2 / 8)) := h_pow
          _ = Real.exp (((Finset.card s : ℝ)/8) * l ^ 2) := by simp [h_mul]
          _ ≤ Real.exp (((Finset.card s : ℝ)/8 + 1) * l ^ 2) := h_exp_le
          _ = Real.exp (A * l ^ 2) := by
            -- A = (card s)/8 + 1
            have hs : (Finset.card s : ℝ) = (Finset.card (MidBlock k X) : ℝ) := rfl
            simp [A, hs, add_comm, mul_comm]
      -- combine the product bound with the exponential growth bound
      exact le_trans h_prod_le h_step

  exact QuadMGF.mk intg bnd hApos


/-- Positive-side mirror: prove QuadMGFPos for Zmid using independence. -/
theorem mgf_midblock_via_indep_pos {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ) :
  QuadMGFPos (μ := μ)
    (Zmid (k := k) (X := X) (Smap := Smap))
    (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ))
  ((↑(Finset.card (MidBlock k X)) / 8) + 1) := by
  let A := (↑(Finset.card (MidBlock k X)) / 8 : ℝ) + 1
  have hApos : 0 < A := by
    have hnum_nonneg : 0 ≤ (↑(Finset.card (MidBlock k X)) : ℝ) := by exact Nat.cast_nonneg _
    have hden_pos : 0 < (8 : ℝ) := by norm_num
    have hdiv_nonneg : 0 ≤ (↑(Finset.card (MidBlock k X)) / 8 : ℝ) := by
      apply div_nonneg
      · exact hnum_nonneg
      · exact le_of_lt hden_pos
    have : 0 < (1 : ℝ) := by norm_num
    exact add_pos_of_nonneg_of_pos hdiv_nonneg this

  let m := Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ)

  let intg : ∀ (lambda : ℝ) (h : lambda ≥ 0), Integrable (fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))) μ := by
    intro lambda hlambda
    have hraw := integrable_exp_of_mid_block (μ := μ) (k := k) (X := X) (Smap := Smap) (lambda := lambda)
    -- exp(lambda*(Z - m)) = exp(-lambda * m) * exp(lambda * Z)
    have : (fun ω => Real.exp (lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
      = fun ω => Real.exp (-lambda * m) * Real.exp (lambda * Zmid (k := k) (X := X) (Smap := Smap) ω) := by
      funext ω
      have : lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m) = -lambda * m + lambda * Zmid (k := k) (X := X) (Smap := Smap) ω := by ring
      rw [this]; rw [Real.exp_add]
    have hmul := Integrable.const_mul hraw (Real.exp (-lambda * m))
    convert hmul using 1

  let bnd : ∀ (l : ℝ) (h : l ≥ 0), μ[fun ω => Real.exp (l * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))] ≤ Real.exp (A * l ^ 2) :=
    fun l hl => by
      let s := MidBlock k X
      have h_centered_def : (fun ω => Zmid (k := k) (X := X) (Smap := Smap) ω - m)
        = fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) := by
        ext ω; dsimp [Zmid, m]; rw [Finset.sum_sub_distrib]
      have h_integrand_eq : (fun ω => Real.exp (l * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
        = fun ω => Real.exp (l * (Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)))) := by
        ext ω; dsimp; have h_point := congrFun h_centered_def ω; rw [h_point]
      rw [h_integrand_eq]
      have h_mgf_def :
        μ[fun ω => Real.exp (l * (Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))))] =
          ProbabilityTheory.mgf (fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))) μ l := rfl
      rw [h_mgf_def]
      have h_sum_as_fun :
        (fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))) =
          (∑ v ∈ s, fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) := by ext ω; simp
      have h_sum_rewrite :
        ProbabilityTheory.mgf (fun ω => Finset.sum s fun v => (Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ))) μ l =
          ProbabilityTheory.mgf (∑ v ∈ s, fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l := by
        apply congrArg (fun g => ProbabilityTheory.mgf g μ l); exact h_sum_as_fun
      rw [h_sum_rewrite]
      have h_meas_g : ∀ i, Measurable (fun x => x - (∫ ω, Prob.indR (Smap i) ω ∂μ)) := by intro i; exact Measurable.sub measurable_id (measurable_const (a := (∫ ω, Prob.indR (Smap i) ω ∂μ)))
      let hind_centered := hind.comp (fun i => fun x => x - (∫ ω, Prob.indR (Smap i) ω ∂μ)) h_meas_g
      have h_meas_centered : ∀ i, Measurable (fun ω => Prob.indR (Smap i) ω - (∫ ω, Prob.indR (Smap i) ω ∂μ)) := by intro i; exact Measurable.sub (indR_measurable_each (Smap := Smap) (v := i)) (measurable_const (a := (∫ ω, Prob.indR (Smap i) ω ∂μ)))
      have h_prod_fun :
        ProbabilityTheory.mgf (∑ v ∈ s, fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ =
          fun l => Finset.prod s fun v => ProbabilityTheory.mgf (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l := by
        funext l; exact ProbabilityTheory.iIndepFun.mgf_sum hind_centered h_meas_centered s
      have h_prod :
        ProbabilityTheory.mgf (∑ v ∈ s, fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l =
          Finset.prod s fun v => ProbabilityTheory.mgf (fun ω => Prob.indR (Smap v) ω - (∫ ω, Prob.indR (Smap v) ω ∂μ)) μ l := by
        have := congrArg (fun f => f l) h_prod_fun; simpa using this
      rw [h_prod]
      have h_prod_le := prod_mgf_bound_by_exp_card (μ := μ) (Smap := Smap) (l := l) (s := s)
      have h_step : (Real.exp (l ^ 2 / 8)) ^ (Finset.card s) ≤ Real.exp (A * l ^ 2) := by
        -- rewrite (exp (l^2/8))^card as exp (card * (l^2/8))
        have h_pow := (Real.exp_nat_mul (l ^ 2 / 8) (Finset.card s)).symm
        -- reshape card * (l^2/8) = (card/8) * l^2
        have h_mul : (Finset.card s : ℝ) * (l ^ 2 / 8) = ((Finset.card s : ℝ) / 8) * l ^ 2 := by ring
        -- compare exponents via monotonicity of exp
        have h_exp_le :
          Real.exp (((Finset.card s : ℝ) / 8) * l ^ 2)
            ≤ Real.exp (((Finset.card s : ℝ) / 8 + 1) * l ^ 2) := by
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_right
          · linarith
          · exact pow_two_nonneg l
        calc
          (Real.exp (l ^ 2 / 8)) ^ (Finset.card s) = Real.exp ((Finset.card s : ℝ) * (l ^ 2 / 8)) := by simpa using h_pow
          _ = Real.exp (((Finset.card s : ℝ)/8) * l ^ 2) := by simp [h_mul]
          _ ≤ Real.exp (((Finset.card s : ℝ)/8 + 1) * l ^ 2) := h_exp_le
          _ = Real.exp (A * l ^ 2) := by
            have hs : (Finset.card s : ℝ) = (Finset.card (MidBlock k X) : ℝ) := rfl
            simp [A, hs, add_comm, mul_comm]
      exact le_trans h_prod_le h_step

  exact QuadMGFPos.mk intg bnd hApos


/-- Use the positive-side Chernoff to get an exponential upper-tail bound for Zmid under independence. -/
theorem mid_block_upper_hp_indep {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun v => Prob.indR (Smap v)) μ)
  (δ : ℝ) (hδ : 0 < δ) :
  μ.real {ω | Zmid (k := k) (X := X) (Smap := Smap) ω ≥ (Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ)) + δ * (Finset.card (MidBlock k X) : ℝ)}
    ≤ Real.exp (- (δ * (Finset.card (MidBlock k X) : ℝ)) ^ 2 / (4 * ((↑(Finset.card (MidBlock k X)) / 8 : ℝ) + 1))) := by
  let A := (↑(Finset.card (MidBlock k X)) / 8 : ℝ) + 1
  let Hmgf := mgf_midblock_via_indep_pos (μ := μ) (k := k) (X := X) (Smap := Smap) hind
  -- apply positive Chernoff with m = expectation and τ = δ * card
  have hτ : 0 ≤ δ * (Finset.card (MidBlock k X) : ℝ) := by
    apply mul_nonneg
    · exact le_of_lt hδ
    · exact Nat.cast_nonneg _
  exact chernoff_upper_from_quad_mgf_pos (μ := μ) (Z := Zmid (k := k) (X := X) (Smap := Smap))
      (m := Finset.sum (MidBlock k X) fun v => (∫ ω, Prob.indR (Smap v) ω ∂μ)) (A := A) (τ := δ * (Finset.card (MidBlock k X) : ℝ)) Hmgf hτ


/--
A Janson-style interface: if one can bound the log-MGF of the (centered) mid-block
by a quadratic A * lambda ^ 2, then we can assemble a `QuadMGF` for `Zmid` using the
already-proved integrability lemma. This lemma is useful when dependence among
indicators is controlled via Janson/Suen style variance/covariance bounds.
-/
theorem mgf_midblock_via_janson {Ω : Type*} [MeasurableSpace Ω] [DecidableEq Ω]
  [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  (m A : ℝ)
  (hApos : 0 < A)
  (h_logmgf : ∀ lambda ≥ 0, μ[fun ω => Real.exp (-lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))] ≤ Real.exp (A * lambda ^ 2)) :
  QuadMGF (μ := μ) (Zmid (k := k) (X := X) (Smap := Smap)) m A := by
  -- integrability follows from the dominating bound we already proved
  have intg : ∀ (lambda : ℝ) (h : lambda ≥ 0), Integrable (fun ω => Real.exp (-lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))) μ :=
    by
      intro lambda hlambda
      have hraw := integrable_exp_of_mid_block (μ := μ) (k := k) (X := X) (Smap := Smap) (-lambda)
      -- rexp (-lambda*(Z - m)) = rexp (lambda*m) * rexp (-lambda*Z), so convert Integrable.const_mul accordingly
      have : (fun ω => Real.exp (-lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m)))
        = fun ω => Real.exp (lambda * m) * Real.exp (-lambda * Zmid (k := k) (X := X) (Smap := Smap) ω) :=
        by
          funext ω
          -- show equality of the exponents first
          have : -lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m) = (lambda * m) + -lambda * Zmid (k := k) (X := X) (Smap := Smap) ω := by
            ring
          rw [this]
          rw [Real.exp_add]
      have hmul := Integrable.const_mul hraw (Real.exp (lambda * m))
      convert hmul using 1
  have bnd : ∀ (lambda : ℝ) (h : lambda ≥ 0), μ[fun ω => Real.exp (-lambda * (Zmid (k := k) (X := X) (Smap := Smap) ω - m))] ≤ Real.exp (A * lambda ^ 2) :=
    fun lambda hlambda => h_logmgf lambda hlambda
  exact QuadMGF.mk intg bnd hApos


/--
Given a QuadMGF witness for the mid-block sum, derive a Chernoff lower-tail
bound via `chernoff_from_quad_mgf`. This packages the final step of the MGF→Chernoff
chain for reuse.
-/
theorem mid_block_chernoff_fixed {Ω : Type*} [MeasurableSpace Ω] [MeasureSpace Ω] [DecidableEq Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  {k X : ℕ} (Smap : ℕ → Finset Ω)
  {m A : ℝ} (H : QuadMGF (μ := μ) (Zmid (k := k) (X := X) (Smap := Smap)) m A)
  {τ : ℝ} (hτ : 0 ≤ τ) :
  μ.real {ω | (Zmid (k := k) (X := X) (Smap := Smap) ω) ≤ m - τ} ≤ Real.exp (- τ ^ 2 / (4 * A)) := by
  exact chernoff_from_quad_mgf (μ := μ) (Z := Zmid (k := k) (X := X) (Smap := Smap)) (m := m) (A := A) (τ := τ) H hτ




end Prob

end DkMath.ABC
