/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.MiddleBandJansonSkeleton
import DkMath.ABC.AdjKBadDensity

#print "file: DkMath.ABC.JansonFiniteUniform"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※ `JansonBasic.lean` から切り出した finite-uniform block wrapper owner。
  `MiddleBandJansonSkeleton` の `S_of` / `Prob.indR` API を使う
  Hoeffding/Janson 型の有限一様補題と adjacent density placeholders を置く。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/- Finite-uniform corollary specialized to indicator families (skeleton). -/
/--
有限標本空間上の指示関数の下側偏差不等式（Hoeffding 型）。

設定：
  - Ω, I は有限集合、μ は Ω 上の一様確率測度（ProbabilityTheory.uniformOn を仮定）、
  - A : I → Finset Ω に対し、各 i に対応する集合 A i の指示関数 Prob.indR (A i) が
    独立である（ProbabilityTheory.iIndepFun）とする、
  - t ≥ 0。

ここで S_of A ω は点 ω における包含数（すなわち S_of A ω = ∑ i 1_{A i}(ω) を意味する）、
期待値は ∑ i ∫ ω, Prob.indR (A i) ω ∂μ = ∑ i μ(A i) に等しい。

命題の内容：
  標本点 ω に対して S_of A ω が期待値から t だけ下回る割合（つまり
  { ω ∈ Ω | S_of A ω ≤ E[S_of A] - t } の元の割合）は
  exp(-2 t^2 / |I|) 以下に抑えられる。
  これは独立な 0-1 変数の和に対する標準的な下側大偏差不等式（Hoeffding の不等式）の有限標本空間における表現である。

補足：
  - 一様測度と指示関数の独立性の仮定により、典型的な確率的不等式がそのまま「割合」表示に書き換えられる点に注意。
  - 不等式は非漸近的で、任意の有限 I, t に対して有効である。
-/
theorem Block_Janson_downward_skeleton_indep
  {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [Fintype I] [DecidableEq I]
  (A : I → Finset Ω)
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (hμ : μ = ProbabilityTheory.uniformOn (Set.univ : Set Ω))
  (hind : ProbabilityTheory.iIndepFun (fun i => Prob.indR (A i)) μ)
  (t : ℝ) (ht : 0 ≤ t) :
  ((Finset.univ.filter fun ω => (S_of A ω : ℝ)
      ≤ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ)) - t).card : ℝ)
    / (Fintype.card Ω : ℝ)
  ≤ Real.exp (- 2 * t^2 / (Fintype.card I : ℝ)) := by
  -- Apply the proved Hoeffding bound for indicator families to the probability measure μ.
  -- Define Sfin using the integer-valued S_of coerced to ℝ; this matches the theorem statement.
  let Sfin : Finset Ω := (Finset.univ : Finset Ω).filter (fun ω => (S_of A ω : ℝ)
    ≤ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ)) - t)
  have h_bound := Prob.hoeffding_downward_indep01_indicator (μ := μ) (S := A) hind t ht

  -- E is the coercion of the Finset to a Set; it's finite
  have hfin : (Sfin : Set Ω).Finite := Finset.finite_toSet Sfin
  -- count measure of Sfin equals the ENNReal nat-cast of Sfin.card
  have hcount_fin : Measure.count (Sfin : Set Ω) = (Sfin.card : ENNReal) := Measure.count_apply_finset Sfin

  -- evaluate μ.real on the coerced finset under the uniform measure assumption
  have hmu_val : μ.real (Sfin : Set Ω) = (Sfin.card : ℝ) / (Fintype.card Ω : ℝ) := by
    calc
      μ.real (Sfin : Set Ω) = (μ (Sfin : Set Ω)).toReal := by simp [Measure.real_def]
      _ = (ProbabilityTheory.uniformOn Set.univ (Sfin : Set Ω)).toReal := by rw [←hμ]
      _ = (Measure.count (Sfin : Set Ω) / Fintype.card Ω).toReal := by rw [ProbabilityTheory.uniformOn_univ]
      _ = ((Sfin.card : ENNReal) / Fintype.card Ω).toReal := by rw [hcount_fin]
      _ = (ENNReal.toReal (Sfin.card : ENNReal)) / (ENNReal.toReal (Fintype.card Ω : ENNReal)) := by rw [ENNReal.toReal_div]
      _ = (Sfin.card : ℝ) / (Fintype.card Ω : ℝ) := by
        rw [ENNReal.toReal_natCast, ENNReal.toReal_natCast]

  -- rewrite the Hoeffding bound (about μ.real of the event) into the desired inequality
  have h_bound' : ((Finset.univ.filter fun ω => (S_of A ω : ℝ)
      ≤ (∑ i, (∫ ω', (Prob.indR (A i)) ω' ∂μ)) - t).card : ℝ) / (Fintype.card Ω : ℝ)
    ≤ Real.exp (- 2 * t^2 / (Fintype.card I : ℝ)) := by
    -- show the coerced Finset `Sfin : Set Ω` equals the indicator-event set by an explicit extensionality proof
    have hset : (Sfin : Set Ω) = {ω | (S_of A ω : ℝ) ≤ (∑ i, (∫ ω', (Prob.indR (A i)) ω' ∂μ)) - t} := by
      ext ω
      -- use Finset.mem_filter to relate membership in the filtered finset to the predicate
      constructor
      · intro h; exact (Finset.mem_filter.1 h).2
      · intro h; exact (Finset.mem_filter.2 ⟨Finset.mem_univ ω, h⟩)
    -- apply hoeffding bound to the set; first show the predicate using `S_of` is equal to the sum-of-indicators predicate
    have hsum_eq : {ω | (∑ i, Prob.indR (A i) ω) ≤ (∑ i, (∫ ω', (Prob.indR (A i)) ω' ∂μ)) - t}
      = {ω | (S_of A ω : ℝ) ≤ (∑ i, (∫ ω', (Prob.indR (A i)) ω' ∂μ)) - t} := by
      ext ω
      dsimp [S_of]
      -- show pointwise equality of the sums using Finset.sum_congr
      have : (Finset.univ : Finset I).sum (fun i => Prob.indR (A i) ω)
        = (Finset.univ : Finset I).sum (fun i => (indicator (A i) ω : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [Prob.indR, indicator]
        by_cases hmem : (ω ∈ (A i) : Prop)
        · simp [hmem]
        · simp [hmem]
      simp [this]
    have hbound_sets : μ.real (Sfin : Set Ω) ≤ Real.exp (- 2 * t^2 / (Fintype.card I : ℝ)) := by
      -- rewrite the Hoeffding bound's set to the S_of form, then replace with Sfin
      rw [hsum_eq] at h_bound
      rwa [←hset] at h_bound
    -- replace μ.real (Sfin : Set Ω) with the computed numeric value and finish
    rwa [hmu_val] at hbound_sets

  exact h_bound'

/- Project-scoped density-one fact for AdjK-quality (placeholder). -/
axiom adjK_quality_density_one :
  ∀ (k : Nat) (ε : ℝ), 0 < ε →
    Tendsto (fun X => ((Finset.Icc 1 (X - k)).filter (fun n => ∀ h : Nat.Coprime n (n + k), quality (AdjK k n h) ≤ 1 + ε)).card / (X : ℝ))
    atTop (nhds 1)

/-- grid (a,b) 全体の bad count と密度 0 の主張 -/
/- Project-scoped density-zero fact for the whole grid (placeholder). -/
axiom tendsto_grid_bad_fraction_zero :
  Tendsto (fun X => (gridBadCount (0.435 : ℝ) X : ℝ) / (X * X : ℝ)) atTop (nhds 0)

end DkMath.ABC
