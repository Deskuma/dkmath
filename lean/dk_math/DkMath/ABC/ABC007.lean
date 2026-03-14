/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC006

#print "file: DkMath.ABC.ABC007"

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

-- -------------------------------------------------------

/- ABCSkeletons.lean
  Skeletons for the ABC framework

  so#rry / axioms serving as placeholders for key lemmas and theorems in the ABC project.
  TODO: replace with actual proofs
-/

-- Replace the previous axiom: callers should supply a coprimality witness.
-- axiom adjK_coprime_axiom (k n : ℕ) : Nat.Coprime n (n + k)

/- Helper lemmas to improve readability and reuse -/

/- Placeholder: previously we ad#mitted a global coprimality axiom and an equality
   between a finset-card expression and `adjKBadCount`.  Instead of ad#mitting
   these, provide a small constructive unfolding lemma for `adjKBadCount` so
   downstream code can work with the concrete `Finset.filter` form (the
   exact predicate used by `adjKBadCount` is the `BadPair` predicate over
  `(n, n+k)` and the range `Icc 1 ((X - k)/2)`).
--/

/- Unfold `adjKBadCount` to the explicit filter.card representation when X > k. -/
theorem adjKBadCount_unfold {δ : ℝ} {k X : ℕ} (h : ¬ X ≤ k) :
  adjKBadCount δ k X = (@Finset.filter ℕ (fun n => BadPair δ X (n, n + k))
    (fun n => Classical.propDecidable (BadPair δ X (n, n + k))) (Finset.Icc 1 ((X - k) / 2))).card := by
  simp [adjKBadCount, if_neg h]


/-- k-diagonal triple: (n, n+k, 2n+k)
  AdjK ad#mit の証明スケルトン
  AdjK を実際に証明し定義する場所
  証明が完了したらこれを AdjK に置換する
-/
def AdjK_proof (k n : Nat) (hcop : Nat.Coprime n (n + k)) : Triple :=
  -- Construct using the canonical helper from `ABC.lean`.
  ABC.AdjK_of_coprime k n hcop
  -- coprimality は呼び出し側で供給すること。

-- -------------------------------------------------------

-- Example: register the exponent α = 1.75 for θ = 0.435 (placeholder).
axiom middleBandBlockBound : BlockBound 0.435

-- Now `MiddleBand_exception_bound'` becomes a one-liner up to minor set-theoretic glue.
axiom MiddleBand_exception_bound'_via_dyadic
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, X ≥ X0 →
      BadCountOn 0.435 (MidIdx X) ≤ ⌈C * (X : ℝ) ^ (1.75 + ε)⌉₊

/- 中帯の外部結果（強化版）：
    例外 ≤ X^(1.75 + ε + o(1)) の形式（十分大きい X で成立）。 -/

/- Existence of a polynomial upper bound for the number of middle-band exceptions.

For every fixed ε > 0 there are constants `X0 : ℕ` and `C : ℝ` with `0 ≤ C` such that
for all `X ≥ X0` the counting function `BadCount (0.435) X` is bounded by
`⌈C * (X : ℝ) ^ (1.75 + ε)⌉₊`.  In other words, the number of "bad" indices in the
middle band grows at most on the order of `X^(1.75+ε)` (up to the integer ceiling),
for any arbitrarily small positive ε.

Proof sketch:
Choose auxiliary parameters depending on `ε` and use a dyadic decomposition of the
middle band together with the previously established estimates on each dyadic block.
Summing these contributions and absorbing lower-order error terms into the constant
`C` yields the claimed global bound for sufficiently large `X`.-/

axiom MiddleBand_exception_bound'
  (ε : ℝ) (hε : 0 < ε) :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, X ≥ X0 →
      BadCount (0.435) X ≤ ⌈C * (X : ℝ) ^ (1.75 + ε)⌉₊

/- Simple, project-scoped variants of Janson / Suen style large-deviation bounds.

These statements are intentionally written as lightweight skeletons tuned to the needs of the
`BadCount` / middle-band analysis in this repository. They are *not* full, general-purpose
implementations of the classical Janson or Suen inequalities; rather they capture the shape of the
results we need here so the rest of the formal development can be written against stable names.

The intended workflow is:
1. Use these lemma names and the documented API in the downstream proofs (for example the
   middle-band dyadic-sum -> global bound argument).
2. Iteratively refine the statements (add precise measure-theoretic hypotheses) and replace
   `so#rry` by complete proofs — either by reusing Mathlib building blocks (MGF / Chernoff /
   Hoeffding / Azuma) or by formalizing a small, project-specific Janson/Suen argument.

Notes on notation used below (informal):
  squarefactor pattern in a particular (a,b)-cell; `S = ∑_{i ∈ I} 1_{A_i}` is the count of
  contributing small-prime-square events in a dyadic block.
  (a sum of pairwise joint probabilities / covariances measuring the amount of dependence).

We provide two canonical skeletons: a downward (Janson-style) tail and an upward (Suen-style)
tail adapted to the combinatorial counting needs of `BadCount`.-/

/- Informal Janson downward tail (skeleton).

Intended statement (informal):
For a finite family of indicator events on a finite probability space with sum `S`, expectation `μ`,
and dependency parameter `Δ`, for any `t ≥ 0` one has

  P(S ≤ μ - t) ≤ exp(- t^2 / (2μ)).

This is the basic Janson inequality in a form sufficient to prove that, with exponentially high
probability, the count in a dyadic block does not fall far below its expectation.  The formal
statement below is a placeholder: refine the quantifiers and probabilistic objects when proving it.-/

/- The following are lightweight axiomatic skeletons for the Janson/Suen style bounds that the
project documentation refers to.  They serve as named placeholders so downstream proofs can be
written and later refined into full formal proofs (either by reusing Mathlib's MGF/Chernoff
machinery or by formalizing a small, targeted Janson/Suen argument).-/

axiom Janson_downward_tail_skeleton : Prop

/- Informal Suen (upper-tail for dependent indicators) simplified skeleton.

Intended statement (informal):
With the same notation as above, for `t ≥ 0` one has an upper-tail bound of the form

  P(S ≥ μ + t) ≤ exp(- c * t^2 / (μ + Δ) )

for an absolute constant `c > 0` (in the literature one can take `c = 1/8` or similar depending on
the exact formulation).  This is a Suen-style bound (a refinement of Janson allowing nontrivial
upper-tail control for dependent indicator families).  The declaration below is a project-scoped
placeholder; it will be made precise during formalization.-/

/- Project-scoped placeholder: simplified Suen upper-tail inequality (axiom form).

This is intentionally an abstract placeholder. The concrete formulation should quantify over a
finite probability space, an indexed family of indicator events, and the usual Janson-style
parameters `μ` (expectation) and `Δ` (dependency sum). The final formal proof may be implemented
by MGF / Chernoff techniques plus bookkeeping of dependencies, or by a direct formalization of
the classical Suen argument.-/

axiom Suen_upper_tail_skeleton : Prop

/- Dyadic block level skeletons -/

-- move: Block_Janson_downward_skeleton to after from Suen Block
-- move: Block_Suen_upper_skeleton to after Janson


/- Concrete finite-uniform probability helpers for blocks -/

/-- Indicator function for membership in a Finset (returns 1 or 0). -/
def indicator {Ω : Type _} [DecidableEq Ω] (A : Finset Ω) (ω : Ω) : ℕ :=
  if ω ∈ A then 1 else 0

/-- Pointwise block-count S built from a family of local Finsets `A : I → Finset Ω`. -/
def S_of {Ω : Type _} [DecidableEq Ω] {I : Type _} [Fintype I] [DecidableEq I]
  (A : I → Finset Ω) (ω : Ω) : ℕ :=
  ∑ i : I, indicator (A i) ω

/-- Expectation of S over the finite uniform sample space Ω. -/
noncomputable def mu_of {Ω : Type _} [Fintype Ω] (S : Ω → ℕ) : ℝ :=
  (∑ ω, (S ω : ℝ)) / (Fintype.card Ω : ℝ)

/-- Probability of a Finset event A under uniform measure on Ω. -/
noncomputable def prob_of {Ω : Type _} [Fintype Ω] (A : Finset Ω) : ℝ :=
  (A.card : ℝ) / (Fintype.card Ω : ℝ)

/-- Dependency parameter delta (informal project definition): sum of pairwise joint probs.
    This is left as a placeholder definition to be specialized later. -/
def delta_of {Ω : Type _} [Fintype Ω] {I : Type _} (_A : I → Finset Ω) : ℝ :=
  0


/- Helper lemmas and a general Hoeffding skeleton -/

example : ‖(1 : ℝ) - (0 : ℝ)‖₊ = (1 : NNReal) := by norm_num

/-- MGF bound for a single [0,1]-valued random variable.
This follows the standard Hoeffding mgf bound: if Y is a.e. in [0,1], then
E[exp(λ (Y - E Y))] ≤ exp(λ^2 / 8).
We place this lemma here so downstream proofs can use it; the proof uses standard
convexity/Jensen arguments available in Mathlib.
-/
theorem mgf_bound_unit01 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
  (hY_meas : Measurable Y) (_ : Integrable Y μ) (hY_range : ∀ᵐ ω ∂μ, 0 ≤ Y ω ∧ Y ω ≤ 1) (r : ℝ) :  -- _ := hY_int
  (∫ ω, Real.exp (r * (Y ω - ∫ ω, Y ω ∂μ)) ∂μ) ≤ Real.exp (r ^ 2 / 8) := by
  -- Use Hoeffding's lemma from Mathlib: a bounded variable in [0,1] yields a centered
  -- variable with sub-Gaussian MGF parameter (1/4), hence mgf ≤ exp(r^2 / 8).
  -- Convert measurability to a.e. measurability required by the lemma.
  have h_ae_meas : AEMeasurable Y μ := hY_meas.aemeasurable
  -- Apply the corollary `hasSubgaussianMGF_of_mem_Icc` which returns a
  -- `HasSubgaussianMGF (fun ω => Y ω - μ[Y]) ((‖b-a‖₊ / 2)^2)` with a = 0, b = 1.
  let hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (hm := h_ae_meas) (hb := hY_range)
  -- `hsub.mgf_le r` gives the desired bound: mgf (Y - μ[Y]) r ≤ exp (((‖1-0‖₊/2)^2) * r^2 / 2).
  have bound := ProbabilityTheory.HasSubgaussianMGF.mgf_le hsub r
  -- simplify the numeric constant: ‖1 - 0‖₊ = 1, hence the cgf bound equals r^2 / 8
  set norm_one := (‖(1 : ℝ) - (0 : ℝ)‖₊) with hnr1
  set r_pow_28 := ((↑norm_one / 2 : ℝ) ^ 2) * r ^ 2 / 2 with hrpow28
  -- compute the numeric norm ‖1 - 0‖₊ = 1
  have norm1 : (norm_one : ℝ) = 1 := by
    simp only [hnr1, sub_zero, nnnorm_one, NNReal.coe_one]
  -- compute the numeric exponent equality on the coerced NNReal expression
  have rhs_eq : r_pow_28 = r ^ 2 / 8 := by
    -- replace ↑norm_one by 1 and finish by ring
    rw [hrpow28, norm1]
    ring

  have rhs_exp_eq : Real.exp (r_pow_28) = Real.exp (r ^ 2 / 8) :=
    congrArg Real.exp rhs_eq

  -- Use bound : ProbabilityTheory.mgf (...) ≤ Real.exp (((↑norm_one / 2 : ℝ) ^ 2) * r ^ 2 / 2)
  -- rewrite that RHS using rhs_exp_eq to obtain the desired Real.exp (r^2 / 8)
  have bound' : (ProbabilityTheory.mgf (fun ω => Y ω - ∫ ω, Y ω ∂μ) μ r) ≤ Real.exp (r ^ 2 / 8) := by
    -- rewrite the RHS of the existing `bound` using `rhs_exp_eq` and conclude
    convert bound using 1
    symm
    exact congrArg Real.exp rhs_eq
  -- `bound'` is the desired inequality about the mgf
  exact bound'



-- ===========================================================================
-- Measure theory / measurable functions for finite sets
-- ===========================================================================



namespace Prob


/- ℝ 値指示子（簡潔）-/
/--
S : Finset Ω に対して定める指示関数（特徴関数）。

具体的には、`indR S` は型 `Ω → ℝ` の関数で、任意の `x : Ω` について
- `x ∈ S` のとき `indR S x = 1`、
- `x ∉ S` のとき `indR S x = 0`。

実装上は `Finset` を `Set` に変換して `Set.indicator` を用いている。
`DecidableEq Ω` の仮定が必要であり、値は実数 `ℝ` に取られる。
非計算的定義（`noncomputable`）である点に注意。
-/
noncomputable def indR {Ω} [DecidableEq Ω] (S : Finset Ω) : Ω → ℝ :=
  Set.indicator (S : Set Ω) (fun _ => (1 : ℝ))


/- 有限集合を可測集合として扱う補助。 -/
/--
`S : Finset Ω` を集合に強制したものは可測であることを示す補題。

前提:
- `Ω` は `MeasurableSpace` を持つ。
- `MeasurableSingletonClass Ω` により任意の点 `x : Ω` の単点 `{x}` は可測である。

主張:
- `S : Finset Ω` を集合に強制した `(S : Set Ω)` は可測集合 `MeasurableSet (S : Set Ω)` である。

証明の概略:
- 有限集合は各要素の単点の有限合併として表せるので，
  `(S : Set Ω) = ⋃ x ∈ S, ({x} : Set Ω)`。
- 単点は可測であり，可測集合は有限合併に対して閉じているため結論が従う。

備考:
- 本補題は有限個の点からなる集合が可測であることを使う場面で頻繁に用いられる。
-/
lemma measurableSet_finset'
  {Ω} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (S : Finset Ω) : MeasurableSet (S : Set Ω) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s _ hs =>
    have : (↑(insert a s) : Set Ω) = {a} ∪ (↑s : Set Ω) := by simp [Finset.coe_insert]
    rw [this]
    have ha : MeasurableSet ({a} : Set Ω) := measurableSet_singleton a
    exact ha.union hs

-- これだけで有限集合の可測性が出ます（mathlib 既存）
lemma measurableSet_finset
  {Ω} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (S : Finset Ω) : MeasurableSet (S : Set Ω) := by
  classical
  simpa using (S.finite_toSet.measurableSet)


/--
Ω を MeasurableSpace とし、DecidableEq と MeasurableSingletonClass を仮定する。
有限集合 S : Finset Ω に対して、indR S は可測関数である。

説明: indR S は S 上で 1、それ以外で 0 をとる実数値指示関数である。MeasurableSingletonClass により各単点 {ω} が可測であり、有限和や補集合に関する可測性保存により S とその補集合の逆像が可測であることから、indR S の各値の逆像が可測集合となり、したがって indR S は可測である。
-/
theorem indR_measurable
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (S : Finset Ω) : Measurable (indR S) := by
  -- indicator on a finite set is measurable
  have hS : MeasurableSet (S : Set Ω) := measurableSet_finset (S := S)
  exact Measurable.indicator (measurable_const : Measurable fun (_ : Ω) => (1 : ℝ)) hS


/--
S : Finset Ω に対する指示関数 indR の値域が [0, 1] に含まれることを示す補題。

内容：
- 前提として Ω は可測空間 (MeasurableSpace)、元の判定可能性 (DecidableEq)、および単点集合が可測であること (MeasurableSingletonClass) を仮定する。
- 任意の ω に対して 0 ≤ indR S ω ∧ indR S ω ≤ 1 が成り立つ。
  直感的には indR は S の指示関数であり、各点で 0 か 1 の値をとるため、区間 [0,1] に収まる。

証明の方針：
- ω ∈ S の場合は indR S ω = 1、ω ∉ S の場合は indR S ω = 0 であることを示し、両者ともに [0,1] に含まれることを確認する。
- Finset を仮定しているため集合の扱いが有限であり、DecidableEq により所属判定が可能である点に注意する。
- MeasurableSingletonClass の仮定は可測性に関する補助的な仮定である。
-/
theorem indR_range01
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (S : Finset Ω) : ∀ ω, 0 ≤ indR S ω ∧ indR S ω ≤ 1 := by
  -- indicator takes only values 0 or 1, so it is pointwise in [0,1]
  classical
  intro ω; dsimp [indR]; by_cases h : ω ∈ (S : Set Ω) <;> simp [h]

theorem indR_range01'
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (S : Finset Ω) : ∀ ω, 0 ≤ indR S ω ∧ indR S ω ≤ 1 := by
  intro ω; dsimp [indR]; by_cases h : ω ∈ (S : Set Ω) <;> simp [h]


/- `indR S` は任意の確率測度に対して almost-everywhere 強可測である。 -/
/--
有限集合 S の指示関数 `indR S` は測度 `μ` に関して μ-ほとんど至る所強可測であることを述べる定理。

仮定：
- `Ω` は可測空間 `MeasurableSpace Ω` を持つ。
- 点の比較が決定可能な `DecidableEq Ω`。
- 任意の単集合が可測である `MeasurableSingletonClass Ω`。
- `S : Finset Ω` は有限集合。

説明：
単集合が可測であるため、有限個の単集合の和として表される `indR S` は単純関数であり、したがって（ほとんど至る所で）強可測である。
-/
theorem indR_aestronglyMeasurable
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) (S : Finset Ω) : AEStronglyMeasurable (indR S) μ := by
  -- Use the library bridge from Measurable to AEStronglyMeasurable
  exact Measurable.aestronglyMeasurable (indR_measurable (S := S))


/- 指示関数 `indR S` は μ-ほとんど至る所で [0,1] に値を取る。 -/
/--
μ を測度、S を有限集合とすると、indR S は μ-ほとんど至るところで 0 ≤ indR S ω ≤ 1 を満たす。

説明:
indR S は集合 S の実数値指標関数（characteristic / indicator 関数）であり、任意の ω に対して indR S ω は 0 または 1 を取る。
したがって任意の ω について 0 ≤ indR S ω ≤ 1 が成り立つ。ここでは可測空間・可測単点の仮定により
有限和としての S の可測性が保障され、測度 μ に関する「ほとんど至るところ (a.e.)」の表現が適切である。

備考:
実際には点別に成り立つため a.e. はやや弱い主張だが、測度論的文脈での利用を念頭に置いた表現である。
-/
theorem indR_range01_ae_of_all
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) (S : Finset Ω) : ∀ᵐ ω ∂μ, 0 ≤ indR S ω ∧ indR S ω ≤ 1 := by
  -- pointwise lemma を almost-everywhere に昇格させる
  have h : ∀ ω, 0 ≤ indR S ω ∧ indR S ω ≤ 1 := indR_range01 (S := S)
  -- 全ての点で成り立つ命題は当然ほとんど至る所（almost everywhere）でも成り立つ
  exact MeasureTheory.ae_of_all μ h


/- Downward Hoeffding for independent `[0,1]`-valued family on a prob. space (proved). -/
/--
与えられた確率測度 μ 上で、有限個の 0–1 指標関数 indR (S i) が互いに独立であるときの Hoeffding 型下側偏差不等式。

設定：
- (Ω, μ) は確率空間（μ は確率測度）、
- I は有限集合、S : I → Finset Ω は各 i に対応する事象 S i、
- hind は各指標関数 i ↦ indR (S i) の相互独立性を表す仮定、
- t ≥ 0。

主張：
確率 μ による事象「和 ∑ i indR (S i) がその期待値 ∑ i E[indR (S i)] から t 以上下回る」について、
その確率は exp(− 2 t^2 / |I|) 以下に抑えられる：
P(∑ i indR (S i) ≤ ∑ i E[indR (S i)] − t) ≤ exp(− 2 t^2 / |I|)。

解説：
各 indR (S i) は値域が {0,1} に含まれるため取りうる幅が 1 に制限される。したがって Hoeffding の不等式（有界独立変数の和に対する集中不等式）を適用することで上の評価が得られる。なお ∑ i E[indR (S i)] は各事象の確率の和 ∑ i μ (S i) に等しい。
-/
theorem hoeffding_downward_indep01
  {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  [Fintype I]
  (S : I → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun i ω => indR (S i) ω) μ)
  (t : ℝ) (ht : 0 ≤ t) :
  μ.real {ω | (∑ i, indR (S i) ω) ≤ (∑ i, ∫ ω, indR (S i) ω ∂μ) - t}
    ≤ Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
  -- Reduce to Hoeffding's lemma in Mathlib4: each indicator has mean in [0,1]
  have h_meas : ∀ i, AEMeasurable (indR (S i)) μ := fun i => (indR_aestronglyMeasurable (μ := μ) (S := S i)).aemeasurable
  have h01 : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ indR (S i) ω ∧ indR (S i) ω ≤ 1 := fun i => indR_range01_ae_of_all (μ := μ) (S := S i)
  -- Apply Hoeffding: use Hoeffding lemma to get sub-Gaussian mgf for centered indicators,
  -- then apply `measure_sum_ge_le_of_iIndepFun` from Mathlib's SubGaussian API.
  -- Build centered variables Y_i = indR (S i) - μ[indR (S i)] and obtain sub-Gaussianity
  let X := fun i => fun ω => indR (S i) ω - (∫ ω, indR (S i) ω ∂μ)
  -- `indR (S i)` is a.e. measurable and a.e. in `Icc 0 1`.
  have h_meas_ind : ∀ i, AEMeasurable (indR (S i)) μ := h_meas
  have h01' : ∀ i, ∀ᵐ ω ∂μ, indR (S i) ω ∈ Set.Icc (0 : ℝ) 1 := h01
  -- Use the Hoeffding lemma `hasSubgaussianMGF_of_mem_Icc` on the original indicators; it
  -- yields a `HasSubgaussianMGF` for the centered variables `indR - E[indR]` with parameter
  -- `((‖1 - 0‖₊ / 2) ^ 2) = (1/2)^2 = 1/4`.
  have subG : ∀ i, HasSubgaussianMGF (X i) ((‖(1 : ℝ) - (0 : ℝ)‖₊ / 2) ^ 2) μ := by
    intro i
    apply hasSubgaussianMGF_of_mem_Icc
    · exact h_meas_ind i
    · exact h01' i
  -- Apply Hoeffding (measure_sum_ge_le_of_iIndepFun) on the sum
  -- We obtain independence for the centered variables by composing the original independent
  -- family `indR (S i)` with the measurable translations `φ_i (x) = x - E[indR (S i)]`.
  -- Then negate the centered family to apply the right-tail Hoeffding bound.
  let phi := fun i => fun x => (x : ℝ) - (∫ ω, indR (S i) ω ∂μ)
  have phi_meas : ∀ i, Measurable (phi i) := by
    intro i
    let c := (∫ ω, indR (S i) ω ∂μ)
    have hc : Measurable (fun _ : ℝ => c) := measurable_const
    exact measurable_id.sub hc
  -- compose the original independent family with the measurable translations `phi`.
  have h_indep_X : iIndepFun (fun i => phi i ∘ fun ω => indR (S i) ω) μ :=
    hind.comp phi phi_meas
  -- `phi i ∘ indR (S i) = X i`, so `h_indep_X` is independence of the centered family `X`.
  -- Negate the centered family to get independence for `-X` as required by the right-tail bound.
  have h_indep_neg : iIndepFun (fun i => (fun x => -x) ∘ phi i ∘ fun ω => indR (S i) ω) μ :=
    h_indep_X.comp (fun _ => fun x => -x) fun _ => measurable_neg

  -- Relate the event in the statement to the right-tail event for the negated centered sum
  have h_eq : {ω | (∑ i, indR (S i) ω) ≤ (∑ i, ∫ ω, indR (S i) ω ∂μ) - t}
      = {ω | t ≤ ∑ i, - X i ω} := by
    ext ω
    -- show pointwise equivalence of the two inequalities
    calc
      (∑ i, indR (S i) ω) ≤ (∑ i, ∫ ω, indR (S i) ω ∂μ) - t
        ↔ t ≤ (∑ i, ∫ ω, indR (S i) ω ∂μ) - (∑ i, indR (S i) ω) := by
          simp [le_sub_iff_add_le, add_comm]
      _ ↔ t ≤ ∑ i, - X i ω := by
        have : (∑ i, -X i ω) = (∑ i, ∫ ω, indR (S i) ω ∂μ) - (∑ i, indR (S i) ω) := by
          simp [X, Finset.sum_sub_distrib]
        simp [this]
  -- Apply the Hoeffding bound to the composed (negated-centered) family.
  have bound_comp := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h_indep_neg (s := (Finset.univ : Finset I)) (fun i _ => (subG i).neg) ht

  -- Show the event in `bound_comp` equals `{ω | t ≤ ∑ i, - X i ω}` so we can transfer the bound.
  have sums_eq : ∀ ω, (∑ i, ((fun x => -x) ∘ phi i ∘ fun ω' => indR (S i) ω') ω) = ∑ i, - X i ω := by
    intro ω
    simp [phi, X, Finset.sum_sub_distrib]
  have sets_eq : {ω | t ≤ ∑ i, ((fun x => -x) ∘ phi i ∘ fun ω => indR (S i) ω) ω} = {ω | t ≤ ∑ i, - X i ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [sums_eq ω]

  -- Rewrite the RHS exponential first (needs sum_val and c_eq) and then apply the set equality
  have sum_val : (Finset.univ : Finset I).sum (fun _ => ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ)) = (Fintype.card I : ℝ) * ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) := by
    simp [Finset.sum_const, Finset.card_univ]

  -- show the nonnegative norm of 1 equals 1, then reduce the constant to 1/4
  have c_eq : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ) = (1 / 4) := by
    simp; norm_num

  have exp_eq : Real.exp (- t ^ 2 / (2 * ((Finset.univ : Finset I).sum fun _ => ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ))))
      = Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
    rw [sum_val, c_eq]
    field_simp [mul_comm]
    ring_nf

  -- Apply the set equality to the bound, then rewrite the exponential RHS using the
  -- computed `sum_val` and `c_eq` so the expression matches the desired final form.
  have bound'' := by
    rw [sets_eq] at bound_comp
    -- rewrite the RHS exponential `Real.exp (-t^2 / (2 * ↑(∑ ...)))` to the simplified form
    -- `Real.exp (-2 * t^2 / ↑(Fintype.card I))`.
    have rhs_eq : Real.exp (- t ^ 2 / (2 * ↑((Finset.univ : Finset I).sum fun _ => ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ)))) =
                  Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
      rw [sum_val, c_eq]
      field_simp [mul_comm]
      ring_nf
    simpa [rhs_eq] using bound_comp

  -- Rewrite goal's event to match `bound''` and finish.
  -- Convert the negated-sum shape `-∑ i, X i ω` to the sum-of-negatives `∑ i, - X i ω`
  -- so it matches the form produced by `h_eq`.
  have eq_sets_sum_neg : {ω | t ≤ - (∑ i, X i ω)} = {ω | t ≤ ∑ i, - X i ω} := by
    ext ω
    simp [Finset.sum_neg_distrib]
  rw [eq_sets_sum_neg] at bound''
  rw [h_eq]

  -- The exponential on the RHS may be in an algebraically equivalent but syntactically
  -- different form; simplify it to the target `Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ))`.
  have rhs_simp : Real.exp (- t ^ 2 / (2 * (↑(Fintype.card I) * (2 ^ 2)⁻¹))) =
                  Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
    field_simp [mul_comm]
  rw [rhs_simp] at bound''
  exact bound''


/--
Hoeffding の不等式（下側偏差）:
0–1 指示関数の和がその期待値から t 以上下回る確率に対する指数的上界を与える補題。

前提：
- (Ω, ...) は可測空間で μ は確率測度 (IsProbabilityMeasure μ)。
- I は有限集合 (Fintype I)。
- 各 i ∈ I に対して S i : Finset Ω を与え，indR (S i) はその 0–1 指示関数を実数値として扱ったもの。
- hind は ω ↦ indR (S i) ω の族が i 単位で独立であることを表す仮定 (ProbabilityTheory.iIndepFun)。
- t ≥ 0。

主張：
μ.real { ω | ∑_i indR (S i) ω ≤ ∑_i ∫ indR (S i) ω ∂μ − t }
は exp(− 2 t^2 / |I|) 以下である。

注記：
- 各指示関数は値が 0 と 1 に制限されるため，分散に対して簡単な上界が得られる（値域が [0,1] にあることを利用）。
- 証明の骨子はチャーノフ（マルコフ）不等式と独立性を用いた積分の分離，さらに各変数の範囲に基づく二次評価（Hoeffding の標準的な推定）である。
- この補題は和の「下側」偏差に対する評価であり，対称的に上側偏差についても同様の不等式が成り立つ。
- |I| は有限集合 I の元数を表す。
- 応用例：独立なベルヌーイ試行の成功数／失敗数が期待値から大きく外れる確率の評価など。
- 記法：indR は集合の指示関数を実数値として返す関数，μ.real は対応する実数値関数に対する測度の像（push-forward measure）を表す。
-/
lemma hoeffding_downward_indep01_indicator
  {Ω I} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  [Fintype I] (S : I → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun i ω => indR (S i) ω) μ)
  (t : ℝ) (ht : 0 ≤ t) :
  μ.real {ω | (∑ i, indR (S i) ω) ≤ (∑ i, ∫ ω, indR (S i) ω ∂μ) - t}
    ≤ Real.exp (- 2 * t^2 / (Fintype.card I : ℝ)) := by
  -- TODO: mgf-bound → Chernoff → optimize λ
  -- Reduce to the general Hoeffding skeleton by supplying the indicator family
  have hmeas : ∀ i, AEStronglyMeasurable (indR (S i)) μ := fun i =>
    indR_aestronglyMeasurable (μ := μ) (S := S i)
  have h01ae : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ indR (S i) ω ∧ indR (S i) ω ≤ 1 := fun i =>
    indR_range01_ae_of_all (μ := μ) (S := S i)
  exact hoeffding_downward_indep01 (μ := μ) (S := S) hind t ht

-- cid: 68d53354-6900-8333-89c8-62cdc86780af

-- #check indR
-- #check measurableSet_finset
-- #check indR_measurable
-- #check indR_range01
-- #check indR_aestronglyMeasurable
-- #check indR_range01_ae_of_all
-- #check hoeffding_downward_indep01
-- #check hoeffding_downward_indep01_indicator

-- -------------------------------------------------------
open MeasureTheory

/--
有限集合 S に対する指示関数 indR の積分は，S の測度の実数化に等しいことを示す補題。

仮定:
- Ω は測度空間を張る可測空間 (MeasurableSpace Ω),
- 元の等値判定が存在する (DecidableEq Ω),
- 単点集合が可測である (MeasurableSingletonClass Ω),
- μ は Ω 上の測度,
- S は有限集合 (Finset Ω)。

説明:
indR S は S 上で 1，それ以外で 0 を取る実数値の指示関数である．
有限個の互いに素な単点集合の和として indR S の積分を分解し，
それぞれの単点に対する積分が対応する単点の測度に等しいことを用いる．
有限和を取ることで μ (S : Set Ω) の ENNReal から Real への変換 (toReal) が得られる．

証明の方針の概略:
1. indR S は可測であり，各単点に対する指示関数の和に展開できる．
2. 積分の線形性と互いに素な支持により積分を単点ごとの和に分解する．
3. 各単点の積分はその点の測度に等しく，有限和は μ (S : Set Ω) に一致する．
4. 必要に応じて ENNReal → Real の変換を行う．

この補題は簡約化ルール (simp) として使われ，有限集合上の指示関数の積分計算を単純化するために有用である．
-/
@[simp] lemma integral_indR_eq_measure
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) (S : Finset Ω) :
  ∫ ω, indR S ω ∂μ = (μ (S : Set Ω)).toReal := by
  classical
  have hS : MeasurableSet (S : Set Ω) := Prob.measurableSet_finset S
  simpa [Prob.indR, one_mul] using integral_indicator (s:= (S : Set Ω)) (f := fun _ : Ω => (1:ℝ)) hS


/--
有限集合 S に対する実数値指示関数 indR の期待値は，その集合の測度を実数に写したものに等しいことを述べる補題。

より具体的には，(Ω, measurable_space) 上の確率測度 μ と有限集合 S : Finset Ω に対して，
indR S : Ω → ℝ の μ に関する積分は (μ (S : Set Ω)).toReal に等しい。
ここで `DecidableEq Ω` や `MeasurableSingletonClass Ω` の仮定は点の可測性や等号判定を保証するためのものである。

証明は integral_indR_eq_measure から直接従う。
-/
@[simp] lemma expect_indR
  {Ω} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Finset Ω) :
  ∫ ω, indR S ω ∂μ = (μ (S : Set Ω)).toReal := integral_indR_eq_measure μ S


/--
有限集合 S : Finset Ω に対する指示関数 indR の値に関する補題。

具体的には，S を集合として見たときに ω ∈ S であれば indR S ω = 1 となる。
（ここでの indR は Prob.indR の定義に従い，S 上で 1，外では 0 を取る指示関数である。）
DecidableEq Ω は要素の比較を可判定にするための仮定である。
-/
@[simp] lemma indR_mem {Ω} [DecidableEq Ω] (S : Finset Ω) {ω : Ω}
  (h : ω ∈ (S : Set Ω)) : indR S ω = 1 := by
  dsimp [Prob.indR]
  simp [h]


/--
S を有限集合（`Finset Ω`）としたとき、要素 `ω` が集合 `S` の外にあるならば
指示関数 `Prob.indR S` はその点で 0 になることを述べる補題。

ここで `ω ∉ (S : Set Ω)` は `Finset` を `Set` に coerced した表現での非包含を意味し、
`DecidableEq Ω` は要素の包含判定を行うために要求される。
この補題は、指示関数がその支持（ここでは `S`）の外では 0 をとるという直観的性質を形式化したもので、
`@[simp]` 属性により簡約時に自動的に適用される。
-/
@[simp] lemma indR_not_mem {Ω} [DecidableEq Ω] (S : Finset Ω) {ω : Ω}
  (h : ω ∉ (S : Set Ω)) : indR S ω = 0 := by
  dsimp [Prob.indR]
  simp [h]


/--
チェルノフの下方尾確率評価（下方テールバウンド）を示す補題。

確率空間 `(Ω, μ)` 上の実数値関数 `Z` に対し、`Z` のモーメント生成関数（MGF）が
任意の非負の λ について `μ[exp(-λ(Z - m))] ≤ exp(A λ^2)` で抑えられていると仮定する。
このとき、`Z` が平均値 `m` から `tau` だけ下方に逸脱する確率
`μ{ω | Z(ω) ≤ m - tau}` は `exp(-tau^2 / (4A))` で上から抑えられる。

- `Ω`: 標本空間
- `μ`: 確率測度
- `Z`: 実数値確率変数
- `m`: 平均値
- `A`: モーメント生成関数の上界定数（正の実数）
- `tau`: 下方逸脱量（非負実数）
- `hmgf`: モーメント生成関数の評価仮定
- `hApos`: `A > 0` の仮定
- `ht`: `tau ≥ 0` の仮定

この補題は、確率変数の下方大偏差の確率を指数関数的に抑えるチェルノフ型不等式の一例である。
-/
lemma chernoff_lower_tail
  {Ω} [MeasurableSpace Ω] [MeasureSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Z : Ω → ℝ) (m A tau : ℝ)
  (hmgf : ∀ lambda ≥ 0, Integrable (fun ω => Real.exp (-lambda * (Z ω - m))) μ ∧
    μ[fun ω => Real.exp (-lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2))
  (hApos : 0 < A) (ht : 0 ≤ tau) :
  μ.real {ω | Z ω ≤ m - tau} ≤ Real.exp (- tau ^ 2 / (4*A)) := by
  -- Use mathlib's Chernoff/Markov lemma on the lower tail.
  -- We will apply `ProbabilityTheory.measure_le_le_exp_mul_mgf` to the random variable `X := Z - m`.
  have hmgf_int_and_bound : ∀ lambda ≥ 0,
    Integrable (fun ω => Real.exp (-lambda * (Z ω - m))) μ ∧
      μ[fun ω => Real.exp (-lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2) := hmgf
  have est : ∀ (lambda : ℝ) (h_lambda : 0 ≤ lambda), μ.real {ω | Z ω - m ≤ -tau} ≤ Real.exp (A * lambda ^ 2 - lambda * tau) := by
    intro lambda h_lambda
    have hpair := hmgf_int_and_bound lambda h_lambda
    have integrable_exp : Integrable (fun ω => Real.exp (-lambda * (Z ω - m))) μ := hpair.1
    have mgf_bound : μ[fun ω => Real.exp (-lambda * (Z ω - m))] ≤ Real.exp (A * lambda ^ 2) := hpair.2
    -- apply lower-tail Chernoff to X := Z - m with t := -lambda (≤ 0) and ε := -tau
    have h_nonpos : (-lambda) ≤ 0 := by linarith
    have h_ch := ProbabilityTheory.measure_le_le_exp_mul_mgf (-tau) h_nonpos integrable_exp
    have h_ch' : μ.real {ω | Z ω - m ≤ -tau} ≤ Real.exp (-lambda * tau) * ProbabilityTheory.mgf (fun ω => Z ω - m) μ (-lambda) := by simpa using h_ch
    have mgf_eq : ProbabilityTheory.mgf (fun ω => Z ω - m) μ (-lambda) = μ[fun ω => Real.exp (-lambda * (Z ω - m))] := by simp [ProbabilityTheory.mgf]
    have mgf_le : ProbabilityTheory.mgf (fun ω => Z ω - m) μ (-lambda) ≤ Real.exp (A * lambda ^ 2) := by rwa [← mgf_eq] at mgf_bound
    have lhs := le_trans h_ch' (mul_le_mul_of_nonneg_left mgf_le (by exact (Real.exp_pos (-lambda * tau)).le))
    -- combine exponentials
    have : Real.exp (-lambda * tau) * Real.exp (A * lambda ^ 2) = Real.exp (A * lambda ^ 2 - lambda * tau) := by
      rw [← Real.exp_add]
      have : (-lambda * tau) + A * lambda ^ 2 = A * lambda ^ 2 - lambda * tau := by ring
      rw [this]
    exact by rwa [this] at lhs
  -- choose optimal lambda = t / (2A)
  let lambda := tau / (2 * A)
  have lambda_nonneg : 0 ≤ lambda := by
    apply div_nonneg
    · exact ht
    · linarith [hApos]
  have eq_sets : {ω | Z ω ≤ m - tau} = {ω | Z ω - m ≤ -tau} := by
    ext ω
    constructor
    · intro h
      have h1 : Z ω - m ≤ (m - tau) - m := sub_le_sub_right h m
      have h2 : (m - tau) - m = -tau := by ring
      rwa [h2] at h1
    · intro h
      have h1 : (Z ω - m) + m ≤ -tau + m := add_le_add_left h m
      rw [sub_add_cancel] at h1
      have h2 : -tau + m = m - tau := by ring
      rwa [h2] at h1
  calc
    μ.real {ω | Z ω ≤ m - tau} = μ.real {ω | Z ω - m ≤ -tau} := by rw [eq_sets]
    _ ≤ Real.exp (A * lambda ^ 2 - lambda * tau) := est lambda lambda_nonneg
    _ = Real.exp (- tau ^ 2 / (4 * A)) := by
      have hAne : A ≠ 0 := ne_of_gt hApos
      have : A * lambda ^ 2 - lambda * tau = - tau ^ 2 / (4 * A) := by
        dsimp [lambda]
        field_simp [hAne]
        ring
      rw [this]


/--
与えられた測度空間 `Ω`、測度 `μ`、集合 `s`、実数 `r`（`0 ≤ r`）について、
`μ.real s ≤ r` かつ `μ s ≠ ⊤` のとき、`μ s ≤ ENNReal.ofReal r` が成り立つことを示す補題。

この補題は、測度の実数値評価が上から抑えられている場合に、
測度の値自体も対応する拡張実数値で抑えられることを保証します。
-/
lemma measure_le_ofReal_of_real_le
  {Ω} [MeasurableSpace Ω] (μ : Measure Ω) (s : Set Ω) (r : ℝ) (hr : 0 ≤ r)
  (h : μ.real s ≤ r) (hμs_ne_top : μ s ≠ ⊤) :
  μ s ≤ ENNReal.ofReal r := by
  -- μ.real s = (μ s).toReal by definition
  have : μ.real s = (μ s).toReal := (Measure.real_def μ s)
  have h_toReal : (μ s).toReal ≤ r := by simpa [this] using h
  -- use lemma: μ s ≤ ENNReal.ofReal r ↔ (μ s).toReal ≤ r when μ s ≠ ∞ and 0 ≤ r
  rw [ENNReal.le_ofReal_iff_toReal_le (hμs_ne_top) hr]
  exact h_toReal


-- 指示族版の下側 tail を chernoff から即出す薄皮（独立は仮定で注入）
/--
Hoeffding の不等式（下側尾部）：
S : I → Finset Ω に対して，各 i に対する indR (S i) が 0–1 値の指示関数であり，
これらが確率測度 μ の下で相互独立であるとする（`ProbabilityTheory.iIndepFun`）。
任意の t ≥ 0 に対して，和 X := ∑ i, indR (S i) の下側偏差は指数小さい：
μ.real { ω | X ω ≤ E[X] - t } ≤ exp ( - 2 * t^2 / (Fintype.card I : ℝ) ).

概略証明：
チェルノフ法（指数マルコフ不等式）を用いて，
P(X ≤ E[X] - t) = P(e^{-sX} ≥ e^{-s(E[X]-t)}) ≤ e^{ - s t } E[e^{ s (E[X] - X) }].
独立性によりモーメント母関数は因数分解し，各 0–1 変数に対して
Hoeffding の補題（区間幅 1 の一様有界変数に対する mgf の上界）を適用すると，
E[e^{ s (E[X_i] - X_i) }] ≤ e^{ s^2 / 8 } が得られる。
これを合成して全体で e^{ |I| * s^2 / 8 - s t } となり，s を最適化（s = 4 t / |I|）すると右辺は
exp( - 2 * t^2 / |I| ) となる。

注：
- `indR (S i)` は集合 S i の指示関数を実数値化したもので，値域は {0,1}。
- `ProbabilityTheory.iIndepFun` は各 i に対応する事象列（あるいは可測関数列）が独立であることを表す仮定。
- これは各変数が [0,1] に有界である場合の標準的な Hoeffding の不等式の特殊形である。
- 右辺の定数は Hoeffding 補題の定数に由来し，範囲幅 1 に対して 2 が現れる。
- 下側（"downward"）の偏差に対する評価であり，上側偏差（≥ E[X] + t）についても同様に得られる。
- 証明はチェルノフ法と Hoeffding 補題（または同等の mgf の評価）による簡潔な推論である。
- 仮定として Ω の可測性や μ が確率測度であること，I が有限集合であることが必要である。
- 記法：E[X] = ∑ i, ∫ ω, indR (S i) ω ∂μ を表す。
- 参考：チェルノフ不等式（Chernoff bound）・Hoeffding 不等式に対応する標準的な濃度不等式の一例。
-/
theorem hoeffding_downward_indep01_from_chernoff
  {Ω I} [MeasurableSpace Ω] [DecidableEq Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype I]
  (S : I → Finset Ω)
  (hind : ProbabilityTheory.iIndepFun (fun i => indR (S i)) μ)
  (t : ℝ) (ht : 0 ≤ t) :
  μ.real {ω | (∑ i, indR (S i) ω) ≤ (∑ i, ∫ ω, indR (S i) ω ∂μ) - t}
    ≤ Real.exp (- 2 * t^2 / (Fintype.card I : ℝ)) := by
  -- mgf 境界と chernoff_lower_tail を適用して証明する
  let Z := fun ω => ∑ i, indR (S i) ω
  let m := ∑ i, ∫ ω, indR (S i) ω ∂μ
  -- indR (S i) は [0,1] に値を取る（既存の補題を再利用）
  have h01 : ∀ i ω, 0 ≤ indR (S i) ω ∧ indR (S i) ω ≤ 1 := by
    intro i ω
    exact Prob.indR_range01 (S := S i) ω
  -- 既に本ファイル（`ABC.lean` 内の Prob 名前空間）で Hoeffding の不等式を導いてある
  -- それを再利用して薄いコロラリを与える
  exact hoeffding_downward_indep01 (μ := μ) (S := S) hind t ht


-- #check integral_indR_eq_measure
-- #check expect_indR
-- #check indR_mem
-- #check indR_not_mem
-- #check chernoff_lower_tail
-- #check measure_le_ofReal_of_real_le
-- #check hoeffding_downward_indep01_from_chernoff



end Prob

end ABC
