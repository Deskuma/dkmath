/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC007

#print "file: DkMath.ABC.ABC008"

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

-- ===========================================================================
-- Janson's inequality skeletons
-- ===========================================================================



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
      ≤ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ)) - t).card : ℝ) / (Fintype.card Ω : ℝ)
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

-- Final Theorems --

/- Project-scoped density-one fact for AdjK-quality (placeholder). -/
axiom adjK_quality_density_one :
  ∀ (k : Nat) (ε : ℝ), 0 < ε →
    Tendsto (fun X => ((Finset.Icc 1 (X - k)).filter (fun n => ∀ h : Nat.Coprime n (n + k), quality (AdjK k n h) ≤ 1 + ε)).card / (X : ℝ))
    atTop (nhds 1)


/-- grid (a,b) 全体の bad count と密度 0 の主張 -/
/- Project-scoped density-zero fact for the whole grid (placeholder). -/
axiom tendsto_grid_bad_fraction_zero :
  Tendsto (fun X => (gridBadCount (0.435 : ℝ) X : ℝ) / (X * X : ℝ)) atTop (nhds 0)

-- -------------------------------------------------------

-- Use Mathlib's PMF (probability mass function) utilities to construct discrete product measures
-- We'll import the PMF modules needed for Bernoulli distributions and constructions

/- cid: 68cd641a-6bb4-8325-aef6-5889a81bd85b

  MathlibHello/JansonSuen.lean
  ABC: Middle band のための Janson / Suen 雛形（scaffold）

  目的：
    - 記号  λ, Δ, \barΔ の定義枠
    - Finset ベースの族 A（イベント集合）の骨格
    - Janson 型上界（2 版）の定理シグネチャ
    - Suen 型拡張のシグネチャ
  方針：
    - まずは「確率」の詳細を抽象化（構造体で保持）
    - 後で MeasureTheory にブリッジして E[·] を実装
-/

namespace Janson

/-- 有限集合にわたる ENNReal の和が ∞ にならないことを述べる補題。

説明:
α 型の有限集合 s と写像 f : α → ENNReal を考える。各要素 a ∈ s に対して f a ≠ ⊤（無限大でない）ならば、
s の全ての要素にわたる和 s.sum (fun a => f a) も ⊤ ではない（有限値になる）。

補足:
- ENNReal は非負の拡張実数（∞ を含む）であるため、個々の項が ∞ でないことからそれらは有限の実数として扱える。
- s が有限集合であることにより、有限個の有限値の和は再び有限であることを示すことで結論を得る。
- DecidableEq α は Finset の操作のための技術的仮定である。
-/
theorem Finset.sum_ne_top_of_ne_top
  {α : Type*} {s : Finset α} {f : α → ENNReal}
  (h : ∀ a ∈ s, f a ≠ ⊤) : (s.sum fun a => f a) ≠ ⊤ := by
  -- 標準的な Finset に対する帰納法パターンを使う
  classical
  induction s using Finset.induction_on
  case empty =>
    -- ベースケース: 空集合の和は 0 なので ⊤ にはならない
    rw [Finset.sum_empty]
    exact ENNReal.zero_ne_top
  case insert a t ha ih =>
    -- 帰納ステップ: s = insert a t, a ∉ t
    -- a 自身と t の元に対する仮定を h から得る
    have hfa : f a ≠ ⊤ := h a (Finset.mem_insert_self a t)
    have ht : ∀ b ∈ t, f b ≠ ⊤ := fun b hb => h b (Finset.mem_insert_of_mem hb)
    -- 帰納法で t の和が ⊤ でないことを得る
    have h_t_sum_ne : (t.sum fun b => f b) ≠ ⊤ := ih ht
    -- insert の和が ⊤ になると仮定すると矛盾する
    by_contra hsum_top
    -- sum_insert で和を展開し、加算が ⊤ になる等式を得る
    rw [Finset.sum_insert ha] at hsum_top
    -- ENNReal.add_eq_top を適用して場合分け
    rcases ENNReal.add_eq_top.mp hsum_top with h_left | h_right
    · exact hfa h_left  -- f a = ⊤ は hfa に矛盾
    · exact h_t_sum_ne h_right  -- t.sum = ⊤ は帰納仮定に矛盾

/-- 有限な集合 s に対して、ENNReal 値 f の総和 s.sum f が ∞ (⊤) であるならば、
s の中に少なくとも一つの要素 a が存在して f a = ⊤ となる。

直感的には、有限和が無限大になるのは、少なくとも一つの項が無限大である場合に限るということ。
（逆向きの含意は自明で、ある項が ⊤ ならば和も ⊤ になる。）
-/
theorem Finset.sum_eq_top_iff_exists_eq_top
  {α : Type*} {s : Finset α} {f : α → ENNReal} :
  s.sum f = ⊤ → ∃ a ∈ s, f a = ⊤ := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · intro h; simp at h
  · intro a t ha ih hsum
    rw [Finset.sum_insert ha] at hsum
    rcases ENNReal.add_eq_top.mp hsum with hfa | hts
    · exact ⟨a, by simp, hfa⟩
    · rcases ih hts with ⟨b, hb, hbtop⟩
      exact ⟨b, by simp [hb], hbtop⟩


/-- Expectation of a function under a PMF on a finite type: use finite sum over `Finset.univ`.
  This avoids tsum/topology issues when the type is `Fintype`.
  We keep the same name `PMF.expect` but require `[Fintype α]` for this definition.
-/
/- Expectation as an ENNReal sum (useful to do algebra in ENNReal, postpone .toReal)
 -/
noncomputable def PMF.expect_ennreal {α : Type*} [Fintype α] (p : PMF α) (f : α → ENNReal) : ENNReal :=
  (Finset.univ : Finset α).sum fun a => (p a) * f a

/- Expectation of an ENNReal-valued function under a pure PMF collapses to the value at the point. -/
/--
PMF.expect_ennreal_pure は、点質量分布 `PMF.pure x` に対する ENNReal 値の期待値が
その点での関数値と一致することを表します。

具体的には、`PMF.pure x` は要素 `x` に全質量を持つ確率分布（デルタ分布）であり、
したがって任意の `g : β → ENNReal` に対して期待値は単に `g x` になります。

前提:
- `β` は有限集合 (`Fintype`) かつ判定可能な等号 (`DecidableEq`) を持つ。
- `g` は `β` 上の ENNReal 値を与える関数。

証明の要点: `PMF.pure` の定義（全質量が `x` に集中）から自明に導かれます。
-/
lemma PMF.expect_ennreal_pure {β : Type*} [Fintype β] (x : β) (g : β → ENNReal) :
  PMF.expect_ennreal (PMF.pure x) g = g x := by
  dsimp only [PMF.expect_ennreal]
  classical
  rw [Finset.sum_eq_single x]
  · simp only [PMF.pure_apply, ↓reduceIte, one_mul]
  · intros b hb hne
    simp [hne]
  · simp [Finset.mem_univ]

/- Expectation of a real-valued function: compute ENNReal-sum then convert to Real once -/
noncomputable def PMF.expect {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ) : ℝ :=
  (PMF.expect_ennreal p fun a => ENNReal.ofReal (f a)).toReal

/-- Expectation of a nonnegative real-valued function under a PMF is nonnegative. -/
lemma PMF.expect_nonneg {α : Type*} [Fintype α] (p : PMF α) (f : α → ℝ)
  (hf : ∀ a, 0 ≤ f a) : 0 ≤ PMF.expect p f := by
  dsimp [PMF.expect]
  -- work at ENNReal level and show the ENNReal-sum is finite, then toReal is nonnegative
  dsimp [PMF.expect_ennreal]
  have pointwise : ∀ a ∈ (Finset.univ : Finset α), (p a) * ENNReal.ofReal (f a) ≠ ⊤ := by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top p a) ENNReal.ofReal_ne_top
  have hsum_ne : ((Finset.univ : Finset α).sum fun a => (p a) * ENNReal.ofReal (f a)) ≠ ⊤ :=
    Finset.sum_ne_top_of_ne_top pointwise
  -- Mark `hf` as used (it is a genuine hypothesis about the summand nonnegativity)
  have _ := hf
  -- ENNReal.toReal_nonneg gives 0 ≤ a.toReal for any ENNReal `a` provided it's ≠ ⊤.
  apply ENNReal.toReal_nonneg

/-- Expectation under bind -/
noncomputable def PMF.bind_expect {α β : Type*} [Fintype β] (p : PMF α) (f : α → PMF β) (g : β → ℝ) : ℝ :=
  PMF.expect (p.bind f) g

/-- bind_expect equals expect of bind -/
lemma PMF.bind_expect_eq {α β : Type*} [Fintype β] (p : PMF α) (f : α → PMF β) (g : β → ℝ) :
  PMF.bind_expect p f g = PMF.expect (p.bind f) g := rfl

/- Expectation of bind equals iterated expectation: E_{p.bind f}[g] = E_p [ E_{f a}[g] ]. -/
/--
PMF.expect_ennreal の bind に関する恒等式（全期待値の法則）。
有限型の確率質量関数 p : PMF α と、各 a に対する確率分布 f a : PMF β
および ENNReal 値 g : β → ENNReal に対し、結合された分布 p.bind f に対する g の期待値は、
まず各 a について f a に対する g の期待値を取り、それを確率 p によって期待したものに等しい。
すなわち、混合分布の期待値は条件付き期待値の期待値に一致する（反復期待値の性質）。
-/
lemma PMF.expect_ennreal_bind {α β : Type*} [Fintype α] [Fintype β]
  (p : PMF α) (f : α → PMF β) (g : β → ENNReal) :
  PMF.expect_ennreal (p.bind f) g = PMF.expect_ennreal p fun a => PMF.expect_ennreal (f a) g := by
  dsimp [PMF.expect_ennreal]
  -- pointwise expansion of bind as a finite sum
  have h_pointwise : ∀ b, (p.bind f) b = (Finset.univ : Finset α).sum fun a => p a * f a b := by
    intro b
    simp [PMF.bind_apply, tsum_fintype]
  -- 明示的に各変形を分離して書く（型推論が Prop に流れるのを防ぐ）
  have eq1 : (Finset.univ : Finset β).sum (fun b => (p.bind f b) * g b)
    = (Finset.univ : Finset β).sum (fun b => ((Finset.univ : Finset α).sum (fun a => p a * f a b)) * g b) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [h_pointwise b]
  have eq2 : (Finset.univ : Finset β).sum (fun b => ((Finset.univ : Finset α).sum (fun a => p a * f a b)) * g b)
    = (Finset.univ : Finset β).sum (fun b => (Finset.univ : Finset α).sum (fun a => (p a * f a b) * g b)) := by
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.sum_mul]
  have eq3 : (Finset.univ : Finset β).sum (fun b => (Finset.univ : Finset α).sum (fun a => (p a * f a b) * g b))
    = (Finset.univ : Finset α).sum (fun a => (Finset.univ : Finset β).sum (fun b => (p a * f a b) * g b)) := by
    rw [Finset.sum_comm]
  have eq4 : (Finset.univ : Finset α).sum (fun a => (Finset.univ : Finset β).sum (fun b => (p a * f a b) * g b))
    = (Finset.univ : Finset α).sum (fun a => p a * ((Finset.univ : Finset β).sum (fun b => f a b * g b))) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    simp [mul_assoc]
  -- 以上の等式列を順に適用して目的の等号を得る
  calc
    (Finset.univ : Finset β).sum (fun b => (p.bind f) b * g b)
      = (Finset.univ : Finset β).sum (fun b => ((Finset.univ : Finset α).sum (fun a => p a * f a b)) * g b) := eq1
    _ = (Finset.univ : Finset β).sum (fun b => ((Finset.univ : Finset α).sum (fun a => p a * f a b * g b))) := eq2
    _ = (Finset.univ : Finset α).sum (fun a => (Finset.univ : Finset β).sum (fun b => p a * f a b * g b)) := eq3
    _ = (Finset.univ : Finset α).sum (fun a => p a * ((Finset.univ : Finset β).sum (fun b => f a b * g b))) := eq4
    _ = PMF.expect_ennreal p fun a => PMF.expect_ennreal (f a) g := rfl

/- Now lift to the real-valued expectation while keeping .toReal only once -/
/--
PMFについての全望（全期待値）を表す補題。

離散確率分布PMFに対する「結合した分布の期待値は，まず条件付き分布で期待値を取り，
その結果に対して外側の分布で期待値を取ることに等しい」ことを述べる。
すなわち，p : PMF αとaごとの条件付き分布f a : PMF β，および観測関数g : β → ℝに対して，
期待値は次のように入れ替え可能である：
E_{y ∼ p.bind f}[g y] = E_{x ∼ p}[ E_{y ∼ f x}[g y] ].

この補題は有限集合（Fintype）上のPMFに対して成り立ち，有限和の可換性に基づく。
直感的には「全期待値の法則（law of total expectation）」または離散版のFubiniの定理に対応する。
-/
lemma PMF.expect_bind {α β : Type*} [Fintype α] [Fintype β]
  (p : PMF α) (f : α → PMF β) (g : β → ℝ) :
  PMF.expect (p.bind f) g = PMF.expect p fun a => PMF.expect (f a) g := by
  dsimp [PMF.expect]
  -- Work at ENNReal level then apply toReal once at the end
  have h_enn := PMF.expect_ennreal_bind p f fun b => ENNReal.ofReal (g b)
  -- show each inner ENNReal expectation is finite (≠ ⊤) so we can apply ENNReal.ofReal_toReal
  have h_inner_non_top : ∀ a, (Finset.univ : Finset β).sum (fun b => (f a b) * ENNReal.ofReal (g b)) ≠ ⊤ := by
    intro a
    have pointwise : ∀ b ∈ (Finset.univ : Finset β), (f a b) * ENNReal.ofReal (g b) ≠ ⊤ := by
      intro b _
      exact ENNReal.mul_ne_top (PMF.apply_ne_top (f a) b) ENNReal.ofReal_ne_top
    exact Finset.sum_ne_top_of_ne_top pointwise
  -- rewrite RHS of h_enn by replacing each inner PMF.expect_ennreal (f a) (ofReal ∘ g) with ofReal (toReal ...)
  have h_rhs : PMF.expect_ennreal p (fun a => PMF.expect_ennreal (f a) fun b => ENNReal.ofReal (g b))
    = (Finset.univ : Finset α).sum (fun a => p a * ENNReal.ofReal ((PMF.expect_ennreal (f a) fun b => ENNReal.ofReal (g b)).toReal)) := by
    dsimp [PMF.expect_ennreal]
    -- 各 a ごとに PMF.expect_ennreal (f a) ... が ⊤ でないことを h_inner_non_top で保証
    apply Finset.sum_congr rfl
    intro a _
    have hnt := h_inner_non_top a
    rw [ENNReal.ofReal_toReal hnt]
  -- combine and take toReal once
  calc
    PMF.expect (p.bind f) g = (PMF.expect_ennreal (p.bind f) fun b => ENNReal.ofReal (g b)).toReal := rfl
    _ = (PMF.expect_ennreal p fun a => PMF.expect_ennreal (f a) fun b => ENNReal.ofReal (g b)).toReal := by rw [h_enn]
    _ = ((Finset.univ : Finset α).sum fun a => p a * ENNReal.ofReal ((PMF.expect_ennreal (f a) fun b => ENNReal.ofReal (g b)).toReal)).toReal := by rw [h_rhs]
    _ = PMF.expect p fun a => PMF.expect (f a) g := rfl

/--
`JansonSetup`:
  有限集合 Γ 上で、イベント族 `Afamily ⊆ 𝒫(Γ)` を扱う抽象枠。
  本来は確率空間 (Ω, 𝔓) と独立ベルヌーイ族から `I_A` を定義し、
  `μ = E[X]`, `Δ`, `\barΔ` を期待値から作るが、
  ここでは **抽象パラメータ** として先に用意しておく。
-/
structure JansonSetup (Γ : Type*) [Fintype Γ] where
  /-- イベント族（部分集合の有限族）。`Afamily` の各要素は `Finset Γ`。 -/
  Afamily : Finset (Finset Γ)
  /-- 指示変数和 `X = ∑_{A∈Afamily} I_A` の期待値 `μ = E[X]` を抽象的に保持。 -/
  mu        : ℝ
  /-- Janson 記法の `Δ`。半分の重み等、定義は設計指針に合わせ後で具体化。 -/
  Delta     : ℝ
  /-- `\barΔ := μ + 2Δ` を直接持つ（定義と等しいことは lemma で繋ぐ）。 -/
  DeltaBar  : ℝ
  /-- 非負性などの素朴な前提（必要に応じて拡張）。 -/
  mu_nonneg     : 0 ≤ mu
  Delta_nonneg  : 0 ≤ Delta
  DeltaBar_def  : DeltaBar = mu + 2 * Delta

namespace Combinatorics

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- 2つのブロック `A, B` が交差する（Janson の依存グラフの辺に相当）。 -/
def blocksOverlap (A B : Finset Γ) : Prop := (A ∩ B) ≠ (∅ : Finset Γ)

instance decidable_blocksOverlap (A B : Finset Γ) : Decidable (blocksOverlap A B) := by
  dsimp [blocksOverlap]
  have d := inferInstanceAs (Decidable (A ∩ B = (∅ : Finset Γ)))
  cases d
  case isTrue h => exact isFalse (fun H => H h)
  case isFalse h => exact isTrue h

/-- 交差ペアだけを数える（対角は除外するのが普通なので注意）。 -/
def overlapPairs (Afamily : Finset (Finset Γ)) :
    Finset (Finset Γ × Finset Γ) :=
  -- two-stage filter: first remove diagonal (uses decidable equality on Finset Γ),
  -- then filter by overlap (we provide `decidable_blocksOverlap` above).
  let prod := Afamily.product Afamily
  let no_diag := prod.filter fun p => p.1 ≠ p.2
  no_diag.filter fun p => blocksOverlap p.1 p.2
    -- ↑ 述語が decidable であることを Lean に伝える必要あり
    -- ここで Decidable インスタンスを与える
    -- `Finset.filter` の述語には `DecidablePred` が必要
    -- Lean 4 では `Finset.filter` の述語が decidable なら自動で解決されるが、型推論が難しい場合は明示する
    -- 述語 (A, B) ↦ A ≠ B ∧ blocksOverlap A B は decidable
    -- これを補助するため `@[simp]` などは不要
    -- もし型エラーが残る場合は下記のように書き換えるとよい
    -- Afamily.product Afamily |>.filter (λ p => (p.1 ≠ p.2) ∧ blocksOverlap p.1 p.2)

end Combinatorics

/--
`JansonModel`:
  具体的な「ベルヌーイ選択（頂点ごとに確率 p）」を導入したい場合に後付けする層。
  まずは `p : Γ → ℝ`（各点の選択確率）だけ載せておく。
  実際には独立性・期待値の計算などを MeasureTheory で与える。
-/
structure JansonModel (Γ : Type*) [Fintype Γ] where
  -- 各点でのベルヌーイ確率（非負実数型 NNReal を使う）
  p : Γ → NNReal
  -- 依存近傍（Suen 用）をモデルに持たせるとミドル層との整合が簡単になる
  N : Γ → Finset Γ
  -- NNReal は非負性を内包するので 0 ≤ は不要。上限 1 を仮定する。
  hp_in01 : ∀ g, p g ≤ 1

/-- Janson モデル（各点 v の成功確率 p v : NNReal を持つ）と、
List 上の段階的生成 `product_pmf_on` を仮定（あなたの既存定義に合せてください）。
  product_pmf_on M []      : PMF (Γ → Bool)
  product_pmf_on M (v::L)  = (product_pmf_on M L).bind (fun ω =>
                            (bernoulli_pmf (M.p v)).map (fun b => Function.update ω v b))
  product_pmf              = product_pmf_on M (Finset.univ.toList)
-/
-- * not referenced yet *
structure JansonModel' (Γ) where
  (p : Γ → NNReal)


/- 指示変数 `I_A` の期待値 E[I_A] を PMF ベースで定義する雛形。
   実際には確率変数 I_A(ω) = ∏_{v∈A} 1_{X_v(ω)=1} をとり、その期待値を返す。
   ここでは積分を PMF の積により計算することを仮定する。
-/
def indicatorA {Γ : Type*} [Fintype Γ]
    (M : JansonModel Γ) (A : Finset Γ) : ℝ :=
  -- PMF 側は NNReal で扱うので、実数としての期待値は toReal を取る。
  A.prod fun v => (M.p v).toReal

/- Useful concrete mu/dbar for a given model M and event A -/
noncomputable def mu {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (M : JansonModel Γ) (A : Finset Γ) : ℝ :=
  A.sum fun v => (M.p v).toReal

noncomputable def dbar {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (M : JansonModel Γ) (A : Finset Γ) : ℝ :=
  -- sum over v in A of sum over u in A ∩ N(v), u ≠ v, of E[I_u I_v]
  A.sum fun v =>
    let S := A.filter fun u => u ∈ (M.N v) ∧ u ≠ v
    S.sum fun u => (M.p u).toReal * (M.p v).toReal


/- PMF bridge: build per-vertex Bernoulli PMF and product PMF on `Γ → Bool` -/
-- section PMF_Bridge

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

open PMF

/- Monadic product construction: fold over vertices using PMF.bind to build the joint PMF. -/
/- removed: product_pmf_monadic (inlined into product_pmf)-/

/- 今は独立性を仮定して E[I_A] = ∏ p(v) とする。厳密には PMF の積測度を導入して示す必要がある。 -/

/-- `μ = E[ ∑_{A∈Afamily} I_A ]` を計算で作る骨格（今は抽象）。 -/
def computeMu {Γ : Type*} [Fintype Γ]
    (S : JansonSetup Γ) (M : JansonModel Γ) : ℝ :=
  S.Afamily.sum fun A => indicatorA M A
  -- ↑ 雛形：本実装では `∑ E[I_A]` を構成

/-- Δ を「交差ペアの joint 期待値の半分の総和」として具体化する骨格。 -/
noncomputable def computeDelta {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
  (S : JansonSetup Γ) (M : JansonModel Γ) : ℝ :=
  -- (1/2) * ∑_{A≠B, A∩B≠∅} E[I_A · I_B]
  let jointExpectation := fun (A B : Finset Γ) => (A ∪ B).prod fun v => (M.p v).toReal
  (1 / 2 : ℝ) * (Combinatorics.overlapPairs S.Afamily).sum (fun p => jointExpectation p.1 p.2)

/-- \barΔ を `μ + 2Δ` として再構成。 -/
noncomputable def computeDeltaBar {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
  (S : JansonSetup Γ) (M : JansonModel Γ) : ℝ :=
  computeMu S M + 2 * computeDelta S M

/-- `computeDeltaBar` が定義通りであることを将来示す予定の骨格。 -/
lemma computeDeltaBar_spec {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (S : JansonSetup Γ) (M : JansonModel Γ) :
    computeDeltaBar S M = computeMu S M + 2 * computeDelta S M := by
  rfl

theorem indicatorA_eq_pmf_expectation' {Γ : Type*} [Fintype Γ]
    (M : JansonModel Γ) (A : Finset Γ) :
    indicatorA M A = A.prod fun v => (M.p v).toReal := by
  -- Intended proof sketch:
  -- 1. For each v, form `PMF.bernoulli` (as `PMF`) using `M.p v` (coerced to ℝ≥0 or ENNReal as needed).
  -- 2. Form the product PMF on `∀ v, Bool` (sequence/monadic product of PMFs).
  -- 3. The random variable `I_A` is the product of coordinate indicators; its expectation equals the product of probabilities by independence.
  rfl

/- ------------------------------------------------------------------------------------------------ -/
--                                    Janson 型 上界：主定理雛形
/- ------------------------------------------------------------------------------------------------ -/

variable {Γ : Type*} [Fintype Γ]

/--
(Janson その1)
\[
  \mathbb{P}[X=0] \le \exp(-\mu + \Delta).
\]
`μ,Δ` は `JansonSetup` による抽象パラメータ。将来は MeasureTheory から構成。
-/
theorem janson_bound_v1
    (S : JansonSetup Γ) :
    -- 形式的：確率を実数に埋める `Pr[X=0] : ℝ` を抽象的記号として置く
    -- 雛形では左辺を `Pr0` という仮変数で表現しておく
    ∃ (Pr0 : ℝ), 0 ≤ Pr0 ∧ Pr0 ≤ Real.exp ( - S.mu + S.Delta ) := by
  -- 将来：
  --   - 指数の単調性、log の凸性、有限 Jensen 等で積→和→指数の鎖を作る。
  --   - `Pr[X=0]` の導入は MeasureTheory のイベントから。
  refine ⟨0, ?h0, ?h1⟩
  · exact le_of_eq rfl
  · -- 0 ≤ exp(…)
    have : 0 ≤ Real.exp (- S.mu + S.Delta) := by exact Real.exp_pos _ |> le_of_lt
    simpa using this

/--
(Janson その2)
\[
  \mathbb{P}[X=0] \le \exp\!\Big( - \frac{\mu^2}{\bar\Delta} \Big)
\]
ただし \(\bar\Delta = \mu + 2\Delta\)。
-/
theorem janson_bound_v2
    {Γ : Type*} [Fintype Γ]
    (S : JansonSetup Γ) (_ : 0 < S.DeltaBar) :  -- hpos は将来の証明で使う
    ∃ (Pr0 : ℝ), 0 ≤ Pr0 ∧ Pr0 ≤ Real.exp ( - (S.mu ^ 2) / (S.DeltaBar) ) := by
  refine ⟨0, le_of_eq rfl, ?_⟩
  have hx : 0 ≤ Real.exp ( - (S.mu ^ 2) / S.DeltaBar ) :=
    (Real.exp_pos _).le
  simpa using hx
/- Expectation of a real-valued function: compute ENNReal-sum then convert to Real once -/
/- ------------------------------------------------------------------------------------------------ -/
--                                      Suen 拡張：雛形
/- ------------------------------------------------------------------------------------------------ -/

/--
Suen 型：依存度の高い場合の上界（プロトタイプ）。
実用には、依存グラフの最大次数や重み付けをフィールドに追加して強化する。
-/
structure SuenSetup (Γ : Type*) [Fintype Γ] extends JansonSetup Γ where
  -- 依存グラフの次数上界や局所パラメータなど（今はプレースホルダ）
  depDeg : ℕ
  nontriv : depDeg ≥ 0 := by decide

/-- Suen 型上界（型のみ先に用意）。 -/
theorem suen_bound_proto
    {Γ : Type*} [Fintype Γ]
    (S : SuenSetup Γ)
    -- 例：`c1, c2` は Suen 版の補正係数プレースホルダ
    (c1 c2 : ℝ) (_ : 0 < c1) (_ : 0 < c2) :  -- hc1, hc2 は将来の証明で使う
    ∃ (Pr0 : ℝ), 0 ≤ Pr0 ∧ Pr0 ≤ Real.exp ( - c1 * (S.mu ^ 2) / (S.DeltaBar + c2) ) := by
  refine ⟨0, le_of_eq rfl, ?_⟩
  have hx : 0 ≤ Real.exp ( - c1 * (S.mu ^ 2) / (S.DeltaBar + c2) ) :=
    (Real.exp_pos _).le
  simpa using hx






/-
Block-level Janson-style downward tail (project-scoped skeleton).

We model a dyadic block by a finite sample space `Ω` (with `[Fintype Ω]`) and a finite
index set `I` of local indicator events represented as `A : I → Finset Ω` (each `A i` is the
subset of `Ω` where indicator `i` fires).  Let `S : Ω → ℕ` be the pointwise count
`S ω = ∑ i, 1_{A i} (ω)`.  For `μ = E[S]` and a deviation `t ≥ 0` we assert the usual Janson
downward-tail bound in probability form (uniform measure on `Ω`):

  |{ω | S(ω) ≤ μ - t}| / |Ω| ≤ exp(- t^2 / (2μ)).

-/
/--
有限確率空間上の独立な指示関数の和に対する下側偏差評価（Block–Janson 型の下側スケルトン不等式）。

概要：
与えられた有限集合 Ω と有限添字集合 I に対して，各 i ∈ I に対応する部分集合 A i ⊆ Ω を考える。
各 ω ∈ Ω について S_of A ω は ω が属する A i の個数を表す（すなわち指示関数の和）。
μ_meas は Ω 上の一様確率分布（ProbabilityTheory.uniformOn の全体集合上）であり，
(i ↦ Prob.indR (A i)) が μ_meas の下で独立であると仮定する。
実数 t ≥ 0 に対して，「S_of A ω が期待値より t だけ下回る ω の割合」は
exp(-2 t^2 / |I|) 以下であることを結論づける。

仮定の説明：
- Ω, I は有限集合かつ要素比較が決定可能。
- A : I → Finset Ω は各添字に対する部分集合の族。
- 可測構造と単点の可測性を仮定し，μ_meas は確率測度で一様分布であることを指定する。
- hind は添字ごとの指示関数族が独立であることを表す仮定。
- t は非負実数。

結論の解釈：
分母を |Ω| に取ることで，「Ω の要素に対する割合」として評価している。
右辺は Hoeffding 型の指数的減衰を示しており，添字集合 I の大きさに反比例して
偏差確率が急速に小さくなることを保証する。

備考：
- 証明は独立な 0–1 値確率変数に対する標準的な濃縮不等式（Hoeffding の不等式等）に基づく。
- 本定理はより一般的な Block_Janson_downward_skeleton_indep に帰着させている。
- 用語や記法（S_of, Prob.indR, uniformOn）は本ファイル内の定義に依存する。
- t = 0 の場合は自明に左辺が 1 以下となり不等式は成り立つ。
- 英語圏の文献では Janson の不等式や下側偏差に関する項目を参照すると類似結果が見つかる。
- 記述は有限母集団かつ一様分布という離散的設定に特化している。
- 補題や派生命題として，大数の法則的挙動や濃縮による組合せ的推定に応用できる。
- 証明は最終的に Block_Janson_downward_skeleton_indep を呼び出す簡潔なものになっている。
- 用語の整合性のため，ファイル内の関連定義（S_of, Prob.indR 等）を参照のこと。
- 日本語による概説は読みやすさを優先しつつ，数学的厳密性を保つことを意図している。
- 参考：Janson の不等式，Hoeffding の不等式，および確率論における独立 0–1 変数の濃縮不等式。
- 実装メモ：この定理は一様確率測度 μ_meas を仮定しているため，非一様測度へ拡張する際は期待値や正規化係数の取り扱いに注意する。
- 記法上の注意：card を実数にキャストして割合を取っている点が重要である。
-/
theorem Block_Janson_downward_skeleton
  {Ω : Type _} [Fintype Ω] [DecidableEq Ω] {I : Type _} [Fintype I] [DecidableEq I]
  (A : I → Finset Ω)
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ_meas : Measure Ω) [IsProbabilityMeasure μ_meas]
  (hμ : μ_meas = ProbabilityTheory.uniformOn (Set.univ : Set Ω))
  (hind : ProbabilityTheory.iIndepFun (fun i => Prob.indR (A i)) μ_meas)
  (t : ℝ) (ht : 0 ≤ t) :
  ((Finset.univ.filter fun ω => (S_of A ω : ℝ)
      ≤ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) - t).card : ℝ) /
    (Fintype.card Ω : ℝ)
  ≤ Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
  exact Block_Janson_downward_skeleton_indep (A := A) (μ := μ_meas) (hμ := hμ) (hind := hind) t ht


/-
Block-level Suen-style upper tail (project-scoped skeleton).

Same setup as above.  For `t ≥ 0` and a dependency parameter `Δ` we assert a simplified
Suen upper-tail bound of the form

  |{ω | S(ω) ≥ μ + t}| / |Ω| ≤ exp(- c * t^2 / (μ + Δ))

for some absolute constant `c > 0`.  This is provided as an axiom placeholder to be
replaced by a full formal proof later.
-/
/--
A: 各 i ∈ I に対して Ω 上の有限集合 A i を与える。
S_of A ω は点 ω における指示関数 1_{ω ∈ A i} の i に関する和、すなわち
S_of A ω = |{ i ∈ I | ω ∈ A i }| と読む。

仮定:
- Ω と I は有限集合、μ_meas は Ω 上の一様確率測度である（ProbabilityTheory.uniformOn と同値）、
- 各指示関数 Prob.indR (A i) は μ_meas に関して独立である（i に関する独立性）、
- t ≥ 0。

結論:
期待値 E[S_of A] = ∑_i ∫ Prob.indR (A i) dμ_meas に対して、
S_of A がその期待値より t 以上偏る点 ω の割合（|{ω | S_of A ω ≥ E[S_of A] + t}| / |Ω|）
は e^{-2 t^2 / |I|} 以下である。

これは、各指示関数が [0,1] に値を取り独立であるという状況に対する Hoeffding 型の尾不等式に対応する。
-/
theorem Block_Suen_upper_skeleton
  {Ω : Type _} [Fintype Ω] [DecidableEq Ω] {I : Type _} [Fintype I] [DecidableEq I]
  (A : I → Finset Ω)
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ_meas : Measure Ω) [IsProbabilityMeasure μ_meas]
  (hμ : μ_meas = ProbabilityTheory.uniformOn (Set.univ : Set Ω))
  (hind : ProbabilityTheory.iIndepFun (fun i => Prob.indR (A i)) μ_meas)
  (t : ℝ) (ht : 0 ≤ t) :
  ((Finset.univ.filter fun ω => (S_of A ω : ℝ) ≥ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) + t).card : ℝ)
    / (Fintype.card Ω : ℝ)
  ≤ Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
  -- Reduce upper-tail to lower-tail by sign flip: apply the independent Hoeffding upper-tail
  -- bound available as `Prob.hoeffding_downward_indep01` by considering - (S - m).
  -- We reuse the already proved Block_Janson_downward_skeleton_indep applied to the same data
  -- with an appropriate relabeling of t sign. Concretely, the standard Hoeffding constants yield
  -- the exponent -2 * t^2 / |I| for the independent indicator sum.
  -- Delegate to the independent theorem declared earlier.
  have count_eq :
    ((Finset.univ.filter fun ω => (S_of A ω : ℝ) ≥ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) + t).card : ℝ)
      / (Fintype.card Ω : ℝ)
    ≤ Real.exp (- 2 * t ^ 2 / (Fintype.card I : ℝ)) := by
    -- Consider the complements Aᶜ i = univ \ A i. For each i,
    -- indR (Aᶜ i) = 1 - indR (A i). The family of complements is independent
    -- because it is obtained by composing the original independent indicators with
    -- the measurable map x ↦ 1 - x.
    let Acomp : I → Finset Ω := fun i => (Finset.univ : Finset Ω) \ (A i)
    -- The indicator of the complement equals 1 - the indicator of the original set pointwise,
    -- so the family of complements is independent as well. We obtain independence of the
    -- centered/negated indicators by composing with the measurable map x ↦ 1 - x and then
    -- transfer this independence to the actual indicator-of-complement family via a.e. congr.
    have hind_neg : ProbabilityTheory.iIndepFun (fun i => fun ω => (1 : ℝ) - Prob.indR (A i) ω) μ_meas :=
      hind.comp (fun i => fun x => (1 : ℝ) - x) fun _ => measurable_const.sub measurable_id

    -- Pointwise function equality: indR of complement equals 1 - indR of original set for every ω.
    have h_fun_eq : (fun i => Prob.indR (Acomp i)) = fun i => fun ω => (1 : ℝ) - Prob.indR (A i) ω := by
      funext i
      ext ω
      -- expand indicators and perform case analysis using `split_ifs` so goals are purely propositional
      dsimp [Prob.indR]
      by_cases hA : (ω ∈ A i : Prop)
      · -- ω ∈ A i, so ω ∉ Acomp i and indicators evaluate to 1 and 0 respectively
        have hnot : ¬ (ω ∈ Acomp i) := by
          intro h'; have ⟨_, hna⟩ := Finset.mem_sdiff.1 h'; exact hna hA
        simp [hA, hnot]
      · -- ω ∉ A i, so ω ∈ Acomp i (since Acomp i = univ \ A i)
        have hin : ω ∈ Acomp i := Finset.mem_sdiff.2 ⟨Finset.mem_univ ω, hA⟩
        simp [hA, hin]

    -- Use function equality to rewrite the independence statement for the complement family.
    have hind_comp : ProbabilityTheory.iIndepFun (fun i => Prob.indR (Acomp i)) μ_meas :=
      h_fun_eq.symm ▸ hind_neg

    -- Apply the independent downward-tail bound to the complement family.
    have bound_comp :=
      Block_Janson_downward_skeleton_indep (A := Acomp) (μ := μ_meas) (hμ := hμ) (hind := hind_comp) t ht

    -- Relate the two events pointwise: S_of Acomp = |I| - S_of A and the sum of expectations
    -- for Acomp equals |I| - the sum of expectations for A. From these equalities the two
    -- filter sets are equal and hence their counts coincide.
    have hsum_point : ∀ ω, (S_of Acomp ω : ℝ) = (Fintype.card I : ℝ) - (S_of A ω : ℝ) := by
      intro ω
      have : (Finset.univ : Finset I).sum (fun i => (indicator (Acomp i) ω : ℝ))
        = (Finset.univ : Finset I).sum (fun i => (1 : ℝ) - (indicator (A i) ω : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [indicator]
        by_cases hmem : (ω ∈ A i : Prop)
        · -- ω ∈ A i, so ω ∉ Acomp i
          have hnot : ¬ (ω ∈ Acomp i) := by
            intro h'; have ⟨_, hna⟩ := Finset.mem_sdiff.1 h'; exact hna hmem
          simp [hmem, hnot]
        · -- ω ∉ A i, so ω ∈ Acomp i
          have hin : ω ∈ Acomp i := Finset.mem_sdiff.2 ⟨Finset.mem_univ ω, hmem⟩
          simp [hmem, hin]
      simp [S_of, this]

    have hsum_int : (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas))
    = (Fintype.card I : ℝ) - (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) := by
      have hterm : ∀ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas) =
          1 - (∫ ω, (Prob.indR (A i)) ω ∂μ_meas) := by
          intro i
          -- use the pointwise function equality h_fun_eq to rewrite the integrand for this i
          have hpoint := congrArg (fun F => F i) h_fun_eq
          have hpoint_fun : (fun ω => Prob.indR (Acomp i) ω) = fun ω => 1 - Prob.indR (A i) ω := by
            exact hpoint
          -- rewrite the integral using the pointwise equality
          rw [hpoint_fun]
          calc
            (∫ ω, (1 - Prob.indR (A i) ω) ∂μ_meas) = (∫ ω, (1 : ℝ) ∂μ_meas) - (∫ ω, (Prob.indR (A i)) ω ∂μ_meas) := by simp [integral_sub]
            _ = 1 - (∫ ω, (Prob.indR (A i)) ω ∂μ_meas) := by
              have hmu_univ : μ_meas Set.univ = 1 := by simp only [measure_univ]
              rw [integral_const]
              simp only [probReal_univ, smul_eq_mul, mul_one,
                Prob.integral_indR_eq_measure]
      -- 各項の差を直接計算する
      calc
        (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas))
          = ∑ i, (1 - (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hterm i
        _ = (∑ i, 1) - (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) := by
            rw [Finset.sum_sub_distrib]
        _ = (Fintype.card I : ℝ) - (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) := by
          -- Simplify the Finset.sum_const expression by rewriting the card of `Finset.univ`
          -- to `Fintype.card` and then reduce the scalar multiplication.
          rw [Finset.sum_const, Finset.card_univ]
          simp [mul_one]

    -- Now conclude that the two filter sets are equal pointwise and translate the bound.
    have hset_eq : {ω | (S_of A ω : ℝ) ≥ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) + t}
      = {ω | (S_of Acomp ω : ℝ) ≤ (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas)) - t} := by
      ext ω
      dsimp
      have h1 := hsum_point ω
      have h2 := hsum_int
      apply Iff.intro
      -- forward: S ≥ m + t → F - S ≤ F - (m + t) → sum_comp - t
      · intro h
        calc
          (S_of Acomp ω : ℝ) = (Fintype.card I : ℝ) - (S_of A ω : ℝ) := h1
          _ ≤ (Fintype.card I : ℝ) - ((∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) + t) := by linarith
          _ = (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas)) - t := by
            rw [h2]; ring
      -- backward: sum_comp - t ≥ S_of Acomp → (F - S) ≤ F - (m + t) → m + t ≤ S
      · intro h
        -- rewrite the hypothesis using h1 and h2 so it has shape (F - S) ≤ (F - (m + t)),
        -- then let `linarith` finish to obtain m + t ≤ S.
        rw [h1, h2] at h
        linarith

    -- Replace the filtered finset by the complement-family filtered finset and apply the bound.
    have : ((Finset.univ.filter fun ω => (S_of A ω : ℝ) ≥ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) + t).card : ℝ)
      / (Fintype.card Ω : ℝ)
    = ((Finset.univ.filter fun ω => (S_of Acomp ω : ℝ) ≤ (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas)) - t).card : ℝ)
      / (Fintype.card Ω : ℝ) := by
      have hS_set : (Finset.univ.filter fun ω => (S_of A ω : ℝ) ≥ (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) + t)
        = (Finset.univ.filter fun ω => (S_of Acomp ω : ℝ) ≤ (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas)) - t) := by
        apply Finset.filter_congr
        intro ω _
        -- rewrite the integrals as measures (toReal) so the predicates match the simplified goal,
        -- then use the pointwise relation between S_of A and S_of Acomp and conclude by linarith.
        have hsum_meas : (∑ i, (∫ ω, (Prob.indR (A i)) ω ∂μ_meas)) = ∑ i, (μ_meas ↑(A i)).toReal := by
          apply Finset.sum_congr rfl
          intro i _
          exact Prob.integral_indR_eq_measure μ_meas (A i)
        have hsum_meas_comp : (∑ i, (∫ ω, (Prob.indR (Acomp i)) ω ∂μ_meas)) = ∑ i, (μ_meas ↑(Acomp i)).toReal := by
          apply Finset.sum_congr rfl
          intro i _
          exact Prob.integral_indR_eq_measure μ_meas (Acomp i)
        rw [hsum_point ω, hsum_meas, hsum_meas_comp]
        apply Iff.intro
        · intro h
          linarith
        · intro h
          linarith
      rw [hS_set]
    -- apply the independent bound to the complement family
    rw [this.symm] at bound_comp
    exact bound_comp

  exact count_eq



/- ------------------------------------------------------------------------------------------------ -/
--                           Middle band へ接続するための外側 API
/- ------------------------------------------------------------------------------------------------ -/

/--
Head/Middle/Tail のうち Middle 用：`BadCountOn θ (MidBlock k X)` を
Janson/Suen で総和上界する外側 API（プロトタイプ）。
実装では `S : JansonSetup Γ` を `θ, k, X` に応じて構築して適用する。
-/
structure MiddleBandParams where
  θ : ℝ
  k : ℕ
  X : ℕ

/-- middle-band の総和を `C * X^(α+ε)` で抑える雛形（存在定理の“型”）。 -/
theorem middle_band_bound_proto
  (α ε : ℝ) (_ : 0 < α + ε) :  -- hpos は将来の証明で使う
  ∃ (C : ℝ), 0 ≤ C ∧ ∀ (p : MiddleBandParams), (1 : ℕ) ≤ p.X → True := by
      -- 実戦では：`BadCountOn θ (MidBlock k X)` の Finset 和 ≤ C * X^(α+ε)
    refine ⟨1, by norm_num, ?_⟩
    intro p hX
    -- 本体は Janson/Suen を呼び出して和を評価する流れに繋ぐ。
    trivial


-- end PMF_Bridge

open PMF

-- -------------------------------------------------------
-- PMF Bool ⇔ ENNReal in [0,1] の同型を構成する。
-- -------------------------------------------------------

/-- `μ : PMF Bool` のうち `true` の質量（確率） -/
def probTrue (μ : PMF Bool) : ENNReal := μ true

/-- パラメータ p のベルヌーイ PMF（`true` が p、`false` が 1 - p`） -/
noncomputable def pmfOfProb (p : NNReal) (hp : p ≤ 1) : PMF Bool :=
  PMF.bernoulli p hp

/--
PMF Bool と ENNReal の区間 Set.Icc (0 : ENNReal) 1 との同型（equivalence）。

概要：
- toFun は二値確率分布 μ をその true 成分 probTrue μ（型は ENNReal）に写すことで、
  ENNReal 上の閉区間 [0,1] の元を得る。probTrue μ は 0 ≤ μ true ≤ 1 を満たすため
  Set.Icc (0 : ENNReal) 1 の要素となることを示す。
- invFun は区間の点 p を PMF.bernoulli (p.1.toNNReal) ... に送ることで二値の PMF を構成する。
  ここで p.1.toNNReal は p.1 ≤ 1（p の上界条件）に基づき有界な ENNReal を NNReal に落とす操作を用いる。
- left_inv は任意の PMF μ について invFun (toFun μ) = μ を示す。true 成分は ENNReal と NNReal
  間の coercion (ENNReal.coe_toNNReal) によって復元され、false 成分は μ true + μ false = 1 から 1 - μ true として導かれる。
- right_inv は区間の要素 p について toFun (invFun p) = p を示す。ここでは p.1 ≠ ⊤ をまず示し、
  ENNReal.coe_toNNReal を用いて↑(p.1.toNNReal) = p.1 を得て、bernoulli の true 成分が期待通りになることを確かめる。

注意事項：
- 定義は noncomputable であり、ENNReal と NNReal の変換（toNNReal, coe）や PMF.apply_ne_top,
  tsum_fintype, ENNReal.eq_sub_of_add_eq といった補題に依存している。
- 結果として、Bool 型上の確率質量関数全体は ENNReal 上の区間 [0,1] と一対一対応することが得られる。
- ドメイン上の全ての PMF は各点で ⊤ をとらないこと（PMF.apply_ne_top）を利用している。
- invFun では ENNReal.one_ne_top と p.2.right（p ≤ 1）を使って ENNReal → NNReal への単調性を確保している。
- 証明は各成分ごとの等式検証に還元され、bern oulli の具体的な適用則を用いて閉じられる。
- この同型は Bool 上のベルヌーイ分布と実際の確率 p ∈ [0,1] を対応させる標準的な同値である。
- 日本語コメントは定義の意図と主要な技術点を説明することを目的としている。
-/
noncomputable def pmfBoolEquivUnit : PMF Bool ≃ Set.Icc (0:ENNReal) 1 :=
{ toFun := fun μ =>
    ⟨probTrue μ, ⟨zero_le (probTrue μ), by
      -- 0 ≤ μ true ≤ 1 は PMF の和が 1 であることから従う
      have hsum : μ true + μ false = 1 := by
        -- fixed: build ok: Lean 4.24.0-release
        have htsum : tsum (fun b : Bool => μ b) = (Finset.univ : Finset Bool).sum (fun b => μ b) :=
          tsum_fintype (f := fun b : Bool => μ b)
        have hsum_eq : (Finset.univ : Finset Bool).sum (fun b => μ b) = 1 := by
          rw [←htsum]
          exact μ.tsum_coe
        convert hsum_eq using 1
        rw [show (Finset.univ : Finset Bool) = {true, false} by decide]
        simp [Finset.sum_insert, Finset.sum_singleton]
      calc
        μ true ≤ μ true + μ false := by
          apply le_add_of_nonneg_right
          exact zero_le (μ false)
        _ = 1 := by simp [hsum]
    ⟩⟩,
  invFun := fun p => PMF.bernoulli p.1.toNNReal (ENNReal.toNNReal_mono ENNReal.one_ne_top p.2.right),
  left_inv := by
    intro μ
    apply PMF.ext
    intro b
    cases b
    case true =>
      -- true 成分は定義通り
      -- μ true は PMF によって ⊤ にならないので ENNReal の toNNReal と逆変換で元に戻せる
      have : ↑((μ true).toNNReal) = μ true := ENNReal.coe_toNNReal (PMF.apply_ne_top μ true)
      simp [probTrue, this]
    case false =>
      -- false 成分は和が 1 であることから決まる
      have hsum : μ true + μ false = 1 := by
        calc  -- calc version
          μ true + μ false = (Finset.univ : Finset Bool).sum (fun b => μ b) := by simp
          _ = μ.toOuterMeasure (Finset.univ : Finset Bool) := by
            rw [PMF.toOuterMeasure_apply_finset μ (Finset.univ : Finset Bool)]
          _ = ∑' b, (Set.univ : Set Bool).indicator μ b := by
            rw [PMF.toOuterMeasure_apply_finset μ (Finset.univ : Finset Bool)]
            simp only [Set.indicator_univ]
            -- Finset.sum と tsum の一致は tsum_fintype で得られる
            rw [tsum_fintype]
          _ = ∑' b, μ b := by simp
          _ = 1 := μ.tsum_coe
      -- μ true ≠ ⊤ なので μ true = ↑(μ true).toNNReal
      have h_true : μ true = ↑(μ true).toNNReal := Eq.symm (ENNReal.coe_toNNReal (PMF.apply_ne_top μ true))
      -- μ false も ⊤ でない（PMF の性質）
      have h_false : μ false ≠ ⊤ := PMF.apply_ne_top μ false
      -- add の順序を入れ替えてから引き算の等式を得る
      have hsum_comm : μ false + μ true = (1 : ENNReal) := by
        rw [add_comm] at hsum
        exact hsum
      -- use the ENNReal-specific lemma so Lean picks the correct subtraction instance
      have h_false_eq : μ false = (1 : ENNReal) - μ true := ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top μ true) hsum_comm
      have : μ false = (1 : ENNReal) - ↑(μ true).toNNReal := by
        rw [h_true] at h_false_eq
        exact h_false_eq
      simp [probTrue, this]
  right_inv := by
    intro p
    -- p.1 ∈ Set.Icc 0 1 なので p.1 ≠ ⊤
    have h_ne_top : p.1 ≠ ⊤ := by
      intro H
      -- H : p.1 = ⊤ と p.2.right : p.1 ≤ 1 から (⊤ : ENNReal) ≤ 1 を得る
      have hle : (⊤ : ENNReal) ≤ 1 := by
        rw [←H]; exact p.2.right
      -- しかし 1 ≤ ⊤ も成り立つので le_antisymm で ⊤ = 1 となり、1 ≠ ⊤ と矛盾する
      have heq : (⊤ : ENNReal) = 1 := le_antisymm hle (le_top : (1 : ENNReal) ≤ (⊤ : ENNReal))
      have : (1 : ENNReal) = ⊤ := Eq.symm heq
      exact absurd this ENNReal.one_ne_top
    -- ↑(p.1.toNNReal) = p.1
    have h_coe : ↑(p.1.toNNReal) = p.1 := ENNReal.coe_toNNReal h_ne_top
    -- 2つの構造体が等しいことを示す：toFun (invFun p) の true 成分が p.1 になることを示す
    apply Subtype.ext
    -- 定義を展開して true 成分の等式に帰着させる
    dsimp [probTrue]
    -- bernoulli の true 成分は ↑(p.1.toNNReal) に等しいのでそれを示す
    have hb : (PMF.bernoulli (p.1.toNNReal) (ENNReal.toNNReal_mono ENNReal.one_ne_top p.2.right)) true
      = ↑(p.1.toNNReal) := by
      simp [PMF.bernoulli_apply]
    -- 最後に coercion lemma を使って p.1 に戻す
    simp [hb, h_coe]
}

-- #check @tsum_fintype
-- #print tsum_fintype
-- #check @pmfBoolEquivUnit


/- bernoulli_pmf: for each vertex v we produce a PMF on Bool -/
/--
`bernoulli_pmf` は、有限型 `Γ` 上の Janson モデル `M` と要素 `v : Γ` に対して、`v` におけるベルヌーイ分布（成功確率 `M.p v`）を返します。
`PMF.bernoulli` 関数を用いて、`M.p v`（`NNReal` 型）を直接利用し、確率が `[0, 1]` の範囲にあることは `M.hp_in01 v` で保証されます。
-/
def bernoulli_pmf {Γ : Type*} [Fintype Γ] (M : JansonModel Γ) (v : Γ) : PMF Bool :=
  -- `PMF.bernoulli` ∈ mathlib takes a probability ∈ ENNReal or NNReal depending on API;
  -- here we use the NNReal `M.p v` directly where available.
  PMF.bernoulli (M.p v) (M.hp_in01 v)

/- bernoulli_pmf: for each vertex v we produce a PMF on Bool -/
/--
`bernoulli_pmf.toEnnreal` は、有限型 `Γ` 上の Janson モデル `M` と要素 `v : Γ` に対して、
`v` におけるベルヌーイ分布の確率質量関数（PMF）を `ENNReal` 型で返します。
`M.p v` は `v` における成功確率（`NNReal` 型）であり、`M.hp_in01 v` により [0,1] 範囲にあることが保証されています。
この関数は、`PMF.bernoulli` を用いて `v` の確率を計算し、`probTrue` で `ENNReal` 型に変換します。
-/
def bernoulli_pmf.toEnnreal {Γ : Type*} [Fintype Γ] (M : JansonModel Γ) (v : Γ) : ENNReal :=
  probTrue (PMF.bernoulli (M.p v) (M.hp_in01 v))

/- bernoulli_pmf: for each vertex v we produce a PMF on Bool -/
/--
`bernoulli_pmf_nnreal` は、非負実数 `M`（`M ≤ 1` を満たす）を確率として、ベルヌーイ分布の確率質量関数（PMF）を返す関数です。
この関数は、`PMF.bernoulli` を用いて、`M` の値に基づく真偽値の分布を構築します。

引数:
- `M` : ベルヌーイ分布の成功確率（`NNReal` 型、`0 ≤ M ≤ 1`）
- `hM` : `M ≤ 1` を保証する証明

戻り値:
- `PMF Bool` : 真偽値に対するベルヌーイ分布の確率質量関数
-/
def bernoulli_pmf_nnreal (M : NNReal) (hM : M ≤ 1) : PMF Bool :=
  PMF.bernoulli M hM

/--
`bernoulli_pmf_ennreal` は、`ENNReal` 型の確率 `M`（`M.toNNReal ≤ 1` を満たす）から、`Bool` 型のベルヌーイ分布の確率質量関数（PMF）を構築します。

引数:
- `M` : 拡張実数型 (`ENNReal`) の確率値。`M.toNNReal` が 1 以下である必要があります。
- `hM` : `M.toNNReal ≤ 1` を保証する証明。

返り値:
- `PMF Bool` : `Bool` 型（`true` または `false`）のベルヌーイ分布の確率質量関数。
-/
def bernoulli_pmf_ennreal (M : ENNReal) (hM : M.toNNReal ≤ 1) : PMF Bool :=
  PMF.bernoulli M.toNNReal hM

-- #check PMF.bernoulli
-- #check bernoulli_pmf
-- #check bernoulli_pmf.toEnnreal
-- #check bernoulli_pmf_nnreal

/-- product_pmf: monadic product of Bernoulli PMFs over vertices -/
-- product_pmf: construct product PMF on (Γ → Bool) by giving pointwise mass function
--   g(ω) = ∏_{v ∈ Finset.univ} (if ω v then p v else (1 - p v))
-- density-based product helper removed in favor of monadic construction
noncomputable def product_pmf {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (M : JansonModel Γ) : PMF (Γ → Bool) :=
  let vs := (Finset.univ : Finset Γ).toList
  vs.foldr (fun v pmf => pmf.bind fun ω => (bernoulli_pmf M v).map fun b => Function.update ω v b) (PMF.pure fun _ => false)

/- removed: replaced by expect_indicator_prod' proof later -/

/-
Bridge lemma skeleton: express indicatorA as an expectation under the product PMF of independent Bernoulli trials.
We rely on Mathlib's `PMF.bernoulli` and `PMF.ofFinset` to form a joint PMF, then integrate the indicator function.
Proof is left as `so#rry` for now and can be completed once the exact product/sequence API is chosen.
-/
-- removed; reinserted after expect_indicator_prod' to avoid forward reference


/- Small helper: expectation on a pure PMF reduces to the function value -/
/--
`PMF.expect_pure` は、有限型 `β` 上の確率質量関数 `PMF.pure x` に対して、関数 `g : β → ℝ` の期待値を計算します。
この補題は、`PMF.pure x` の期待値が単に `g x` になることを示します。
`g` は全ての値で非負 (`g_nonneg : ∀ y, 0 ≤ g y`) である必要があります。
-/
lemma PMF.expect_pure {β : Type*} [Fintype β]
  (x : β) (g : β → ℝ) (g_nonneg : ∀ y, 0 ≤ g y) :
  PMF.expect (PMF.pure x) g = g x := by
  dsimp [PMF.expect]
  -- use ENNReal-level lemma for pure PMF then convert to Real
  have : (PMF.expect_ennreal (PMF.pure x) fun y => ENNReal.ofReal (g y)) = ENNReal.ofReal (g x) := by
    rw [PMF.expect_ennreal_pure x fun y => ENNReal.ofReal (g y)]
  calc
    PMF.expect (PMF.pure x) g = (PMF.expect_ennreal (PMF.pure x) fun y => ENNReal.ofReal (g y)).toReal := rfl
    _ = (ENNReal.ofReal (g x)).toReal := by rw [this]
    _ = g x := by rw [ENNReal.toReal_ofReal (g_nonneg x)]

/-- Expectation of map: E_{p.map f}[g] = E_p[g ∘ f].
`PMF.expect_map` は、有限型 `α` から有限型 `β` への写像 `f` と、`β` 上の非負関数 `g` に対して、
確率測度 `p` の写像 `f` による像 `p.map f` に関する期待値が、`p` に関する `g ∘ f` の期待値に等しいことを示します。

具体的には、`PMF.expect (p.map f) g = PMF.expect p (g ∘ f)` という等式が成り立ちます。
この補題は、確率測度の写像と期待値の関係を明確にし、期待値の計算を簡略化する際に有用です。

引数:
- `α`, `β`: 有限型（`Fintype`）で、等値性判定可能（`DecidableEq`）な型
- `p`: 型 `α` 上の確率測度
- `f`: `α` から `β` への写像
- `g`: `β` 上の実数値関数
- `g_nonneg`: `g` が非負であることの証明（すべての `b` について `0 ≤ g b`）

戻り値:
- `PMF.expect (p.map f) g = PMF.expect p (g ∘ f)` の等式
-/
lemma PMF.expect_map {α β : Type*} [Fintype α] [Fintype β]
  (p : PMF α) (f : α → β) (g : β → ℝ) (g_nonneg : ∀ b, (0 : ENNReal).toReal ≤ g b) :
  PMF.expect (p.map f) g = PMF.expect p (g ∘ f) := by
  -- Simple term-level proof using bind and pure lemmas (we keep algebra in ENNReal inside PMF.expect_bind)
  have : p.map f = p.bind fun a => PMF.pure (f a) := rfl
  rw [this]
  calc
    PMF.expect (p.map f) g = PMF.expect (p.bind fun a => PMF.pure (f a)) g := rfl
    _ = PMF.expect p fun a => PMF.expect (PMF.pure (f a)) g := by exact PMF.expect_bind p (fun a => PMF.pure (f a)) g
    _ = PMF.expect p fun a => g (f a) := by congr; funext a; exact PMF.expect_pure (f a) g g_nonneg
    _ = PMF.expect p (g ∘ f) := rfl

namespace Combinatorics

variable {Γ : Type*} [DecidableEq Γ]

/--
`mem_overlapPairs` 補題は、`Afamily` という有限集合族に対して、ペア `(A, B)` が `overlapPairs Afamily` に属する条件を示します。
具体的には、`(A, B)` が `overlapPairs Afamily` に含まれることは、次の4つの条件がすべて満たされることと同値です:
- `A` が `Afamily` に含まれる
- `B` が `Afamily` に含まれる
- `A` と `B` が異なる集合である (`A ≠ B`)
- `A` と `B` が重なっている (`blocksOverlap A B`)
この補題は、集合族内の重なり合うペアの特徴付けに役立ちます。
-/
lemma mem_overlapPairs {Afamily : Finset (Finset Γ)} {A B : Finset Γ} :
    (A, B) ∈ overlapPairs Afamily
    ↔ A ∈ Afamily ∧ B ∈ Afamily ∧ A ≠ B ∧ blocksOverlap A B := by
  dsimp [overlapPairs]
  simp [Finset.mem_filter, Finset.mem_product, and_assoc]

end Combinatorics

/- Small helper lemmas about Function.update used in re-indexing sums. -/
/--
`Function.update_same`定理は、関数`f : α → β`に対して、引数`i : α`の値を`b : β`に更新した場合、
その更新した引数`i`に対する値は必ず`b`になることを示します。

すなわち、`Function.update f i b i = b`が成り立ちます。

この定理は、型`α`が可判別（`DecidableEq α`）である場合に成立します。
-/
@[simp]
theorem Function.update_same {α β : Type*} [DecidableEq α] (f : α → β) (i : α) (b : β) :
  Function.update f i b i = b := by
  simp [Function.update]

/--
`Function.update_noteq`は、関数`f : α → β`に対して、`i ≠ j`の場合に`i`の値を`b`に更新しても、`j`での値は変わらず`f j`になることを示す定理です。
- `α`と`β`は型です。
- `DecidableEq α`は`α`上の可判別な等号です。
- `f`は関数です。
- `i, j : α`は引数です。
- `b : β`は更新する値です。
- `h : j ≠ i`は`j`と`i`が異なることの証明です。
この定理は、関数の更新操作が異なる引数には影響しないことを保証します。
-/
@[simp]
theorem Function.update_noteq {α β : Type*} [DecidableEq α] (f : α → β) {i j : α} (b : β) (h : j ≠ i) :
  Function.update f i b j = f j := by
  simp [Function.update, h]


/- PMF bridge: build per-vertex Bernoulli PMF and product PMF on `Γ → Bool` -/
-- section PMF_Bridge
open PMF
/- 非負定数を期待値から外に出す補題: PMF.expect (fun x => c * f x) = c * PMF.expect f  -/
/--
非負実数 c と非負関数 g に対して、PMF の期待値はスカラー倍を外に出せることを示す補題。

仮定:
- α は有限型 (Fintype) であり DecidableEq を持つ。
- p : PMF α は確率質量関数。
- c : ℝ は非負 (hc : 0 ≤ c)。
- g : α → ℝ は全点で非負 (∀ x, 0 ≤ g x)。

結論:
PMF.expect p (fun x => c * g x) = c * PMF.expect p g。

直感的には期待値は線型であり、非負性の仮定によりスカラー c を期待値の外に出せる、という内容である。
-/
lemma PMF.expect_const_mul {α : Type*} [Fintype α]
  (p : PMF α) (c : ℝ) (hc : 0 ≤ c) (g : α → ℝ) (_ : ∀ x, 0 ≤ g x) : -- _ = g_nonneg
  PMF.expect p (fun x => c * g x) = c * PMF.expect p g := by
  -- Expand the definition of PMF.expect
  dsimp [PMF.expect]

  -- For non-negative c and g x, we have ENNReal.ofReal (c * g x) = ENNReal.ofReal c * ENNReal.ofReal (g x)
  have h_mul : ∀ x, ENNReal.ofReal (c * g x) = ENNReal.ofReal c * ENNReal.ofReal (g x) := by
    intro x
    apply ENNReal.ofReal_mul
    exact hc

  -- Rewrite the LHS using the above identity
  have h_congr : PMF.expect_ennreal p (fun x => ENNReal.ofReal (c * g x)) =
                 PMF.expect_ennreal p (fun x => ENNReal.ofReal c * ENNReal.ofReal (g x)) := by
    congr
    funext x
    exact h_mul x
  rw [h_congr]

  -- Expand definition and factor out ENNReal.ofReal c
  dsimp [PMF.expect_ennreal]

  -- Distribute the multiplication inside sum
  have h_dist : (Finset.univ : Finset α).sum (fun x => p x * (ENNReal.ofReal c * ENNReal.ofReal (g x))) =
                (Finset.univ : Finset α).sum (fun x => ENNReal.ofReal c * (p x * ENNReal.ofReal (g x))) := by
    apply Finset.sum_congr rfl
    intro x _
    calc
      p x * (ENNReal.ofReal c * ENNReal.ofReal (g x))
          = (p x * ENNReal.ofReal c) * ENNReal.ofReal (g x) := by rw [mul_assoc]
      _ = ENNReal.ofReal c * (p x * ENNReal.ofReal (g x)) := by
        rw [mul_comm (p x) (ENNReal.ofReal c)]
        rw [←mul_assoc]
  rw [h_dist]

  -- Factor out the constant ENNReal.ofReal c
  have h_factor : (Finset.univ : Finset α).sum (fun x => ENNReal.ofReal c * (p x * ENNReal.ofReal (g x))) =
                 ENNReal.ofReal c * (Finset.univ : Finset α).sum (fun x => p x * ENNReal.ofReal (g x)) := by
    -- rewrite the sum of scaled terms into the scalar times the sum, then finish by reflexivity
    rw [←Finset.mul_sum]
  rw [h_factor]

  -- Convert back to Real
  -- ENNReal.ofReal c is finite because c ≥ 0
  have h_finite : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal hc]

/--
PMF α に対する正規化条件：有限型 α 上の確率質量関数 p は
全ての値の和が 1 になる。

仮定:
- `α` は `Fintype`（有限集合）であるため `Finset.univ` 上で和を取れる。
- `DecidableEq α` は要素の比較に必要。

この補題は、PMF 型が確率分布として正規化されていることを表す基本的な性質を与える。
-/
lemma PMF.sum_eq_one {α : Type*} [Fintype α] (p : PMF α) :
  (Finset.univ : Finset α).sum (fun x => p x) = 1 := by
  -- 有限型 α の全元に対する和は 1 になる
  -- まず tsum と Finset.sum が等価であることを示す
  have h : tsum (fun x => p x) = (Finset.univ : Finset α).sum (fun x => p x) := by
    apply tsum_eq_sum
    intro x hx
    -- x ∉ Finset.univ は矛盾
    exact absurd (Finset.mem_univ x) hx
  -- PMF の tsum は 1
  rw [←h]
  -- PMF の定義より、tsum (λ x, p x) = 1
  exact p.tsum_coe

/- Expectation of the constant function 1 equals 1 -/
/--
PMF.expect に関する補助補題。

任意の有限集合 α 上の確率質量関数 p に対して，定数関数 (fun _ => (1 : ℝ)) の期待値は 1 である。
これは期待値の定義が ∑ a, p a * f a であり，f が恒等的に 1 の場合には各項が p a になり，
確率質量関数 p の総和が 1 であることによる。

引数:
- α : 値の型
- [Fintype α] : α が有限集合であること
- [DecidableEq α] : α 上の等価性が決定可能であること
- p : PMF α

関連項目: PMF における確率の和が 1 であることを表す補題（例えば PMF.sum_values_eq_one など）。
-/
lemma PMF.expect_one {α : Type*} [Fintype α] (p : PMF α) :
  PMF.expect p (fun _ => (1 : ℝ)) = 1 := by
  -- Expand the definitions
  dsimp [PMF.expect, PMF.expect_ennreal]

  -- Factor out ENNReal.ofReal 1 from the sum
  have h_sum : (Finset.univ : Finset α).sum (fun x => p x * ENNReal.ofReal 1)
             = ENNReal.ofReal 1 * (Finset.univ : Finset α).sum (fun x => p x) := by
    rw [Finset.mul_sum]
    simp [mul_comm]
  rw [h_sum]

  -- Simplify ENNReal.ofReal 1 to 1
  rw [ENNReal.ofReal_one]

  -- Use the fact that sum of a PMF is 1
  have h_sum_1 : (Finset.univ : Finset α).sum (fun x => p x) = 1 := PMF.sum_eq_one p
  rw [h_sum_1]

  -- Simplify 1 * 1 to 1 and convert to Real
  rw [one_mul]
  exact ENNReal.toReal_one

/-
ENNReal-level helper: expand the sum over Bool for bernoulli_pmf and show only the true-term contributes
This produces an equality in ENNReal so PMF.expect_ennreal/PMF.expect can use it definitionally before .toReal.
-/

/--
v ∈ A のとき、Bool 全体にわたる和
  ∑_{b : Bool} bernoulli_pmf M v b * ENNReal.ofReal (A.prod (λ v', if Function.update ω v b v' then 1 else 0))
は、b = true の項だけに等しい、という補題。

直感的には、v ∈ A のため b = false のとき積の中に v' = v の項が含まれ、
  Function.update ω v false v = false
となるのでその項は 0 になり、積全体が 0 となる。したがって和は b = true の寄与のみ残る。
証明はその観察を使って b = false の項が消えることを示すだけである。

引数:
- Γ : 基底型、Fintype と DecidableEq を仮定
- M : JansonModel Γ（ベルヌーイ分布の確率質量関数 bernoulli_pmf を用いる）
- A : Finset Γ（v がこの A に含まれることを仮定）
- v : Γ（hmem により v ∈ A）
- ω : Γ → Bool（更新関数の元）

結論:
- 上記の和は b = true の項と等しい（ENNReal の等式として）。
- 補題は、確率質量と指示関数（積）の性質を組み合わせた単純な場合分けに基づく。
-/
private lemma bernoulli_sum_true_only {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (M : JansonModel Γ)
  (A : Finset Γ) {v : Γ} (ω : Γ → Bool) (hmem : v ∈ A) :
  (Finset.univ : Finset Bool).sum (fun b => (bernoulli_pmf M v b) * ENNReal.ofReal (A.prod fun v' => if Function.update ω v b v' then (1 : ℝ) else 0))
  = (bernoulli_pmf M v true) * ENNReal.ofReal (A.prod fun v' => if Function.update ω v true v' then (1 : ℝ) else 0) := by
  -- Finset.univ = {true, false}; expand the sum explicitly and show false-term is zero
  have h_univ : (Finset.univ : Finset Bool) = {true, false} := by simp
  have h_not : true ∉ ({false} : Finset Bool) := by simp
  rw [h_univ]
  rw [Finset.sum_insert h_not, Finset.sum_singleton]
  -- show the false branch ENNReal.ofReal (...) = 0 because the product contains a zero factor
  have prod_false_zero : A.prod (fun v' => if Function.update ω v false v' then (1 : ℝ) else 0) = 0 := by
    have H : A = insert v (A.erase v) := Eq.symm (Finset.insert_erase hmem)
    rw [H]
    have nv : v ∉ A.erase v := Finset.notMem_erase v A
    rw [Finset.prod_insert nv]
    -- the head factor is false at v, so it's 0
    have first_zero : (if Function.update ω v false v then (1 : ℝ) else 0) = 0 := by simp
    simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte, zero_mul]
  -- now substitute to eliminate the false-term
  simp [prod_false_zero, ENNReal.ofReal_zero]

/--
`Function.update` が異なる引数では元の関数値を保持することの小さな wrapper lemma.

`Function.update_ne` は、関数 `f : α → β` に対して、`i : α` の値を `b : β` に更新した新しい関数 `Function.update f i b` を考えます。
この補題は、`j ≠ i` のとき、更新後の関数を `j` で評価しても元の関数 `f` の値と変わらないことを示します。
つまり、`Function.update f i b j = f j` です。
-/
@[simp]
lemma Function.update_ne {α β : Type*} [DecidableEq α] (f : α → β) {i j : α} (b : β) (h : j ≠ i) :
  Function.update f i b j = f j := by
  simp [Function.update, h]

/--
補題: `A.prod (λ v', if Function.update ω v true v' then ...)` を `A.erase v` 上の積に書き換える。
前提: v ∈ A. これにより、cons ケースの積評価を簡潔にできる。

`prod_update_eq_erase_prod` は、有限集合 `A` 上の積に関する補題です。
`ω` を `Γ → Bool` 型の関数、`v ∈ A` を仮定します。
`A` 上で、`ω` の `v` を `true` に更新した関数で積を取ると、
`A` から `v` を除いた集合上で元の `ω` で積を取る場合と等しくなります。

この補題は、関数の一点更新と有限集合上の積の関係を示します。
-/
lemma prod_update_eq_erase_prod {Γ : Type*} [DecidableEq Γ] (A : Finset Γ) {v : Γ} (ω : Γ → Bool)
  (hmem : v ∈ A) :
  A.prod (fun v' => if Function.update ω v true v' then (1 : ℝ) else 0) = (A.erase v).prod fun v' => if ω v' then (1 : ℝ) else 0 := by
  -- Decompose A as insert v (A.erase v)
  have hdecomp : A = insert v (A.erase v) := by
    -- Finset.insert_erase is available given membership: insert v (A.erase v) = A
    exact (Finset.insert_erase hmem).symm
  rw [hdecomp]
  -- split off the v factor using prod_insert (v ∉ A.erase v)
  have nv : v ∉ A.erase v := Finset.notMem_erase v A
  have step : (insert v (A.erase v)).prod (fun v' => if Function.update ω v true v' then (1 : ℝ) else 0)
    = (if Function.update ω v true v then (1 : ℝ) else 0) * (A.erase v).prod fun v' => if Function.update ω v true v' then (1 : ℝ) else 0 := by
    apply Finset.prod_insert nv
  rw [step]
  -- the head factor is 1 by Function.update_same
  simp only [Function.update_self, ↓reduceIte, one_mul, Finset.erase_insert_eq_erase,
    Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
    Finset.erase_eq_of_notMem]
  -- for the remaining product, update does not affect elements of A.erase v
  apply Finset.prod_congr rfl
  intro x hx
  have ⟨x_ne, _⟩ := Finset.mem_erase.mp hx
  have eq_fun : Function.update ω v true x = ω x := Function.update_noteq ω true x_ne
  rw [eq_fun]

/- Helper lemma: expectation over the monadic fold can be computed by induction on the list -/

/- ビット値 -/

/- unify to r_bool_prod: helper nonneg lemma for if-expression -/

/--
Bool の値 b に対して、if b then (1 : ℝ) else 0 が常に非負であることを示す補題。
証明は b の場合分け（true のときは 1 ≥ 0、false のときは 0 ≥ 0）で自明に得られるため、
実数への埋め込みを含む簡単な不等式処理で便利に使える補助結果である。
-/
lemma if_nonneg (b : Bool) : 0 ≤ (if b then (1 : ℝ) else 0) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, le_refl]
  · simp only [↓reduceIte, zero_le_one]

/- 0/1 指示積（if/then/else 版）
A に含まれる各要素 v について `ω v` が `true` なら 1、`false` なら 0 を掛け合わせた実数値を返す関数。

直感的には、A 上で ω が全て真であることを示す指示関数（指標）の積であり、次が成り立つ。
- A の全ての要素で `ω` が `true` のとき値は `1`。
- A に `ω v = false` となる要素が 1 個でもあれば値は `0`。

空集合に対しては空積の規約により `1` を返す。定義では `Finset.prod` を用いているため、`Finset Γ` を扱うための `DecidableEq Γ` が要求される。
名称は 0–1（ブール）値の積を表すことを意図している。
-/

/--
有限集合 A の各元 v に対して述語 ω v が true なら 1、false なら 0 を掛け合わせた実数値を返す関数。

具体的には
  r_bool_prod A ω = ∏ v in A, (if ω v then 1 else 0)
であり、A の中に ω v = false を満たす元が一つでもあれば結果は 0、全て true であれば結果は 1 になる。
Γ には DecidableEq の仮定があることに注意する。主に有限集合上の指示関数の積を表す目的で用いる。
-/
private def r_bool_prod {Γ : Type*} [DecidableEq Γ] (A : Finset Γ) (ω : Γ → Bool) : ℝ :=
  A.prod (fun v => if ω v then (1 : ℝ) else 0)

-- #eval r_bool_prod {1, 2, 3} (fun x => x > 5)  -- expect 0 (because 1,2,3 ≤ 5)
-- #eval r_bool_prod {1, 2, 3} (fun x => x ≤ 3)  -- expect 1 (because 1,2,3 ≤ 3)
-- #eval r_bool_prod {1, 2, 3} (fun x => x ≠ 2)  -- expect 0 (because 2 = 2)
-- #eval r_bool_prod {1, 2, 3} (fun x => x = 2)  -- expect 0 (because 1,3 ≠ 2)
-- #eval r_bool_prod {1, 2, 3} (fun _ => true)  -- expect 1 (because all true)
-- #eval r_bool_prod {1, 2, 3} (fun _ => false)  -- expect 0 (because all false)
-- #eval r_bool_prod (∅ : Finset Nat) (fun (_ : Nat) => false)  -- expect 1 (empty product)

/- 1点更新の因子分解（r_bool_prod 版） -/
lemma prod_update_factor {Γ : Type*} [DecidableEq Γ]
  (A : Finset Γ) (v : Γ) (ω : Γ → Bool) (b : Bool) :
  r_bool_prod A (Function.update ω v b)
  = (if v ∈ A then (if b then (1 : ℝ) else 0) else 1) * r_bool_prod (A.erase v) ω := by
  classical
  by_cases hv : v ∈ A
  · -- case v ∈ A
    have hdecomp : A = insert v (A.erase v) := (Finset.insert_erase hv).symm
    have nv : v ∉ A.erase v := Finset.notMem_erase v A
    dsimp [r_bool_prod]
    rw [hdecomp]
    rw [Finset.prod_insert nv]
    -- case split on b: when b = false head is 0 so whole product is 0; when b = true head is 1
    cases b
    · -- b = false
      simp [Function.update_self, hv]
    · -- b = true
      simp only [Function.update_self, ↓reduceIte, one_mul, Finset.mem_insert, Finset.mem_erase,
        ne_eq, not_true_eq_false, false_and, or_false, Finset.erase_insert_eq_erase,
        not_false_eq_true, Finset.erase_eq_of_notMem]
      -- tail: for x ∈ A.erase v we have Function.update ω v true x = ω x
      apply Finset.prod_congr rfl
      intro x hx
      have x_ne : x ≠ v := Finset.ne_of_mem_erase hx
      simp [Function.update_noteq ω true x_ne]
  · -- case v ∉ A
    dsimp [r_bool_prod]
    -- simplify RHS (the outer if) using hv first
    simp only [hv, ↓reduceIte, not_false_eq_true, Finset.erase_eq_of_notMem, one_mul]
    -- for any x ∈ A, x ≠ v, so Function.update leaves value unchanged
    have tail_eq : ∀ x ∈ A, Function.update ω v b x = ω x := by
      intro x hx
      have x_ne : x ≠ v := by
        intro heq
        have : v ∈ A := heq.symm ▸ hx
        exact absurd this hv
      exact Function.update_noteq ω b x_ne
    apply Finset.prod_congr rfl
    intro x hx
    simp [tail_eq x hx]

/-- Bernoulli の一次期待: E[1_{B=true}] = p
p : NNReal (p ≤ 1) に対するベルヌーイ分布の期待値計算補題。

この補題は、ベルヌーイ PMF `bernoulli_pmf_nnreal p hp` に対して
関数 `b ↦ if b then 1 else 0` の期待値が `p.toReal` に等しいことを主張する。
証明は `PMF.expect` を定義展開して Bool 上の有限和として計算し、
`Finset.univ : Finset Bool = {true, false}` を用いて各項を評価することで行う。
-/
lemma bernoulli_expect_bitVal (p : NNReal) (hp : p ≤ 1) :
  PMF.expect (bernoulli_pmf_nnreal p hp) (fun b => if b then (1 : ℝ) else 0) = p.toReal := by
  classical
  -- PMF.expect を定義展開して Bool 上の有限和として計算する
  dsimp [PMF.expect]
  -- Bool の全体集合を明示化して和を展開
  have h_univ : (Finset.univ : Finset Bool) = {true, false} := by
    apply Finset.ext
    intro b
    simp
  dsimp [PMF.expect_ennreal]
  -- sum の範囲を Finset.univ から {true, false} に置換
  have eq_sum : (Finset.univ : Finset Bool).sum (fun a => (bernoulli_pmf_nnreal p hp) a * ENNReal.ofReal (if a = true then 1 else 0))
    = ({true, false} : Finset Bool).sum (fun a => (bernoulli_pmf_nnreal p hp) a * ENNReal.ofReal (if a = true then 1 else 0)) := by
    rw [h_univ]
  -- false 項は 0 なので残るは true 項のみ
  have : ({true, false} : Finset Bool).sum (fun b => (bernoulli_pmf_nnreal p hp b) * ENNReal.ofReal (if b then (1 : ℝ) else 0))
    = (bernoulli_pmf_nnreal p hp true) * ENNReal.ofReal (if true then (1 : ℝ) else 0) := by
    have not_in : true ∉ ({false} : Finset Bool) := by simp
    rw [Finset.sum_insert not_in, Finset.sum_singleton]
    -- false branch is zero
    have hb : ENNReal.ofReal (if false then (1 : ℝ) else 0) = 0 := by simp
    simp
  -- true branch reduces to 1
  simp
  dsimp [bernoulli_pmf_nnreal]
  simp

/-- 1点ステップの期待の因子化
ある頂点 v に対して Bernoulli 試行で値を生成し元の布尔関数 ω を v の位置で更新した分布に関する期待値の計算補題。

具体的には、pmf.bind を使って ω の v 成分を (bernoulli_pmf M v) による独立な 0/1 試行で更新した分布における
r_bool_prod A の期待値は、もし v ∈ A であれば M.p v の実数値 ((M.p v).toReal) を掛けた
r_bool_prod (A.erase v) の期待値に等しく、v ∉ A であればそのまま r_bool_prod (A.erase v) の期待値に等しい、
という主張です。

直観的には r_bool_prod が A に含まれる各頂点の Bernoulli 成分の積であり、v に対応する因子は独立に 0/1 を取り得るため、
期待値の計算でその因子を外に出して (M.p v).toReal を掛けることができる、ということに基づきます。

パラメータ:
- pmf : PMF (Γ → Bool) -- 元の分布
- v : Γ               -- 更新を行う頂点
- A : Finset Γ        -- 積を取る頂点の集合
- M : JansonModel Γ   -- Bernoulli パラメータを与えるモデル

結果:
- pmf を v で更新した分布に対する r_bool_prod A の期待値は
  (if v ∈ A then (M.p v).toReal else 1) * PMF.expect pmf (r_bool_prod (A.erase v))
  に等しい。

証明方針:
v に対応する 0/1 の寄与を場合分けして期待値の外に出し、残りは元の分布 pmf に対する期待値として扱うことで示される。
-/
lemma expect_step {Γ : Type*} [DecidableEq Γ] [Fintype Γ]
  (pmf : PMF (Γ → Bool)) (v : Γ) (A : Finset Γ) (M : JansonModel Γ) :
  PMF.expect
    (pmf.bind (fun ω => (bernoulli_pmf M v).map (fun b => Function.update ω v b)))
    (r_bool_prod A)
  =
  (if v ∈ A then (M.p v).toReal else 1) *
  PMF.expect pmf (r_bool_prod (A.erase v)) := by
  classical
  -- Apply law of total expectation (bind) to move inner expectation outside
  have h_bind := PMF.expect_bind pmf (fun ω => (bernoulli_pmf M v).map fun b => Function.update ω v b) (r_bool_prod A)
  rw [h_bind]
  -- show for each fixed ω the inner expectation equals (if v ∈ A then (M.p v).toReal else 1) * g (A.erase v) ω
  have inner_eq : ∀ ω, PMF.expect ((bernoulli_pmf M v).map fun b => Function.update ω v b) (r_bool_prod A) =
    (if v ∈ A then (M.p v).toReal else 1) * r_bool_prod (A.erase v) ω := by
    intro ω
    -- move the map inside the expectation
    have g_nonneg_all : ∀ ω', 0 ≤ r_bool_prod A ω' := by intro ω'; apply Finset.prod_nonneg; intro x hx; apply if_nonneg
    have hmap := PMF.expect_map (p := bernoulli_pmf M v) (f := fun b => Function.update ω v b) (g := fun ω' => r_bool_prod A ω') g_nonneg_all
    rw [hmap]
    -- rewrite the composition into a lambda so we can rewrite it pointwise
    have comp_def : ((fun ω' => r_bool_prod A ω') ∘ fun b => Function.update ω v b) = fun b => r_bool_prod A (Function.update ω v b) := rfl
    rw [comp_def]
    -- use prod_update_factor to relate r_bool_prod A (update ω v b) to r_bool_prod (A.erase v) ω
    have pf := prod_update_factor (A := A) (v := v) (ω := ω)
    let c := r_bool_prod (A.erase v) ω
    by_cases hv : v ∈ A
    · -- when v ∈ A, r_bool_prod A (update ω v b) = c * (if b then 1 else 0)
      have fun_eq : (fun b => r_bool_prod A (Function.update ω v b)) = fun b => c * (if b then (1 : ℝ) else 0) := by
        funext b
        rw [pf b]
        dsimp [c]
        cases b
        · simp [hv]
        · simp [hv]
      rw [fun_eq]
      have hc : 0 ≤ c := by apply Finset.prod_nonneg; intro x hx; apply if_nonneg
      have hmul := PMF.expect_const_mul (p := bernoulli_pmf M v) (c := c) (hc) (g := fun b => if b then (1 : ℝ) else 0) (by intro b; apply if_nonneg)
      -- hmul : PMF.expect (bernoulli_pmf M v) (fun b => c * (if b then 1 else 0)) = c * PMF.expect (bernoulli_pmf M v) fun b => (if b then 1 else 0)
      -- use bernoulli_expect_bitVal to rewrite the inner expectation, composing equalities with congrArg/Eq.trans
      have hber := bernoulli_expect_bitVal (M.p v) (M.hp_in01 v)
      have h1 : (PMF.expect (bernoulli_pmf M v) fun b => c * (if b then (1 : ℝ) else 0)) = c * (M.p v).toReal := by
        have h2 := congrArg (fun t => c * t) hber
        exact Eq.trans hmul h2
      have h2 : c * (M.p v).toReal = (M.p v).toReal * c := by rw [mul_comm]
      have h3 : (M.p v).toReal * c = (if v ∈ A then (M.p v).toReal else 1) * c := by simp [hv]
      exact Eq.trans (Eq.trans h1 h2) h3
    · -- when v ∉ A, r_bool_prod A (update ...) = c * 1, so expectation reduces to c
      have fun_eq : (fun b => r_bool_prod A (Function.update ω v b)) = fun _ => c * 1 := by
        funext b
        rw [pf b]
        dsimp [c]
        cases b
        · simp [hv]
        · simp [hv]
      rw [fun_eq]
      have hc : 0 ≤ c := by apply Finset.prod_nonneg; intro x hx; apply if_nonneg
      have hmul := PMF.expect_const_mul (p := bernoulli_pmf M v) (c := c) (hc) (g := fun _ => 1) (by intro _; simp)
      -- hmul : PMF.expect (bernoulli_pmf M v) (fun _ => c * 1) = c * PMF.expect (bernoulli_pmf M v) fun _ => 1
      have hone := PMF.expect_one (p := bernoulli_pmf M v)
      have h1 : (PMF.expect (bernoulli_pmf M v) fun _ => c * 1) = c * 1 := by
        have h2 := congrArg (fun t => c * t) hone
        -- compose the equalities: first apply PMF.expect_const_mul, then replace inner expectation by 1
        exact Eq.trans hmul h2
      have h2 : c * 1 = 1 * c := by rw [mul_comm]
      have h3 : 1 * c = (if v ∈ A then (M.p v).toReal else 1) * c := by simp [hv]
      exact Eq.trans (Eq.trans h1 h2) h3
  -- rewrite the outer expectation using inner_eq and factor the constant out
  have : (fun ω => PMF.expect ((bernoulli_pmf M v).map fun b => Function.update ω v b) (r_bool_prod A)) = fun ω => (if v ∈ A then (M.p v).toReal else 1) * r_bool_prod (A.erase v) ω := by funext ω; exact (inner_eq ω)
  rw [this]
  -- factor the scalar (if v ∈ A then (M.p v).toReal else 1) out of the outer expectation in one step
  let c := (if v ∈ A then (M.p v).toReal else 1)
  have hc : 0 ≤ c := by
    by_cases hmem : v ∈ A
    · -- when v ∈ A, c = (M.p v).toReal which is nonnegative
      dsimp [c]; simp [hmem]
    · -- when v ∉ A, c = 1
      dsimp [c]; simp [hmem]
  have hg_nonneg : ∀ ω, 0 ≤ r_bool_prod (A.erase v) ω := by intro ω; apply Finset.prod_nonneg; intro x hx; apply if_nonneg
  -- the integrand is definitionally `c * g (A.erase v) ω` so we can apply PMF.expect_const_mul directly
  exact PMF.expect_const_mul (p := pmf) c hc (g := fun ω => r_bool_prod (A.erase v) ω) hg_nonneg

/-- 主定理の核：`vs` に沿って畳み込む
与えられたリスト vs に対して、各頂点 v ∈ vs に対して JansonModel M の確率 p v に従う独立な
Bernoulli 試行で割当てを更新して得られる PMF（foldr を用いて構成）上での期待値に関する補題。

内容:
- 初期の割当てはすべて false（PMF.pure (fun _ => false)）であり、vs の各要素 v について
  bernoulli_pmf M v に従って値をサンプルし、Function.update で割当てを更新していく。
- r_bool_prod A は有限集合 A に対応するブール値の積（すべて true なら 1 相当、それ以外は 0）を取る写像であると解釈される。
- 前提として A ⊆ vs.toFinset を要求することで、A に含まれる頂点は foldr によって生成される割当てに現れることが保証される。

主張:
- 上記の PMF に対する r_bool_prod A の期待値は、A にわたる各頂点 v の確率 (M.p v).toReal の積に等しい。

証明方針（概略）:
- vs に関する帰納法を行う。
  - 空リストでは自明。
  - 先頭要素 v を加える場合に v ∈ A か v ∉ A かで場合分けする。
    - v ∉ A のときは期待値に影響しない。
    - v ∈ A のときはその変数が独立に真になる確率 p v を期待値に掛け合わせる。
- PMF の bind/map の性質、期待値の線形性、および Bernoulli 分布の期待値を利用することで上の操作を形式化する。
- A ⊆ vs.toFinset によって、帰納の各ステップで考慮すべき変数が有限かつ既知であることを確保する。
-/
lemma expect_over_list {Γ : Type*} [DecidableEq Γ] [Fintype Γ]
  (M : JansonModel Γ) :
  ∀ (vs : List Γ) (A : Finset Γ),
    A ⊆ vs.toFinset →
    PMF.expect
      (vs.foldr
        (fun v pmf => pmf.bind (fun ω => (bernoulli_pmf M v).map (fun b => Function.update ω v b)))
        (PMF.pure (fun _ => false)))
      (r_bool_prod A)
    =
    A.prod (fun v => (M.p v).toReal) := by
    intro vs A hA
    induction vs generalizing A with
    | nil =>
      classical
      by_cases hA_empty : A = ∅
      · rw [hA_empty]
        apply PMF.expect_pure (fun _ => false) (r_bool_prod (∅ : Finset Γ)) (by intro y; simp [r_bool_prod])
      · have hAeq : A = ∅ := by
          apply Finset.eq_empty_of_forall_notMem
          intro x hx
          have x_in_empty : x ∈ ∅ := hA hx
          exact False.elim (Finset.notMem_empty x x_in_empty)
        contradiction
    | cons v vs' ih =>
      classical
      have h_sub : A.erase v ⊆ vs'.toFinset := by
        intro x hx
        have x_in_A : x ∈ A := Finset.mem_of_mem_erase hx
        have x_in_vs : x ∈ (v :: vs').toFinset := hA x_in_A
        have x_ne_v : x ≠ v := Finset.ne_of_mem_erase hx
        rw [List.toFinset_cons] at x_in_vs
        exact Finset.mem_of_mem_insert_of_ne x_in_vs x_ne_v
      have IH := ih (A.erase v) h_sub
      have step_eq := expect_step (pmf := vs'.foldr (fun v pmf => pmf.bind (fun ω => (bernoulli_pmf M v).map (fun b => Function.update ω v b))) (PMF.pure (fun _ => false))) (v := v) (A := A) (M := M)
      -- unfold the foldr for (v :: vs') so the target matches the pmf.bind shape in `step_eq`
      rw [List.foldr_cons]
      rw [step_eq, IH]
      by_cases hv : v ∈ A
      · -- v ∈ A: write A as insert v (A.erase v)
        have h_ins : A = insert v (A.erase v) := (Finset.insert_erase hv).symm
        rw [h_ins]
        simp [Finset.prod_insert]
      · -- v ∉ A: then A.erase v = A and the product is unchanged
        have : A.erase v = A := Finset.erase_eq_of_notMem hv
        rw [this]
        simp [hv]

-- New definitions and main theorem

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]  -- new

/- lemma g_eq_r_bool_prod
※ g と r_bool_prod の同値性 g(A, ω) 統合廃止に伴い当地証明は不要になる。
lemma g_eq_r_bool_prod (A : Finset Γ) (ω : Γ → Bool) :
  g (A:=A) ω = r_bool_prod A ω := by ...
-/

/-- 部分集合 L 上で独立ベルヌーイを積み重ねた分布 -/
noncomputable def product_pmf_on {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
  (M : JansonModel Γ) : List Γ → PMF (Γ → Bool)
| []      => PMF.pure (fun _ => false)   -- 空の基底状態
| (v::L) => (product_pmf_on M L).bind (fun ω =>
                (bernoulli_pmf M v).map (fun b =>
                  Function.update ω v b))

/-- List 上での一般形：A ⊆ L.toFinset のとき、期待＝確率の積
M : JansonModel Γ に対する補助定理。

L : List Γ と A : Finset Γ に対し、A ⊆ L.toFinset が成り立つとき、
product_pmf_on M L 上の 0/1 変数の積 r_bool_prod A の期待値は
各頂点 v ∈ A の成功確率 (M.p v).toReal の積に等しいことを主張する。

説明:
- product_pmf_on M L は、リスト L に現れる頂点ごとに独立な Bernoulli 分布 (確率 M.p v) を取る積 PMF を与える。
- r_bool_prod A は、A に含まれる頂点に対応する 0/1 変数の積を返す写像である。
- PMF.expect は与えられた PMF に関する期待値を表す。

直感的には、product_pmf_on により各頂点の 0/1 変数は独立であるため、
積の期待値は各変数の期待値（すなわち各頂点の成功確率）の積に分解される。
証明は独立性と期待値の積に関する基本的な性質を用いて行う。
-/
theorem expect_product_pmf_on
  (M : JansonModel Γ) :
  ∀ (L : List Γ) (A : Finset Γ), A ⊆ L.toFinset →
    PMF.expect (product_pmf_on M L) (r_bool_prod A)
      = A.prod (fun v => (M.p v).toReal) := by
  classical
  intro L
  induction L with
  | nil =>
      intro A hA
      -- A ⊆ ∅ → A = ∅。空積は 1、期待の中身も常に 1。
      have : A = (∅ : Finset Γ) := by simpa using Finset.subset_empty.mp hA
      subst this
      -- g ∅ は常に 1、空積は 1（純粋分布の有限和は if-then-else の和になり 1 に簡約）
      classical
      simp only [product_pmf_on]
      -- PMF.pure の期待値計算
      have h_pure : PMF.expect (PMF.pure (fun (_ : Γ) => false)) (r_bool_prod ∅) = 1 := by
        -- PMF.expect の引数順序: 分布, 関数
        -- 期待値計算: 分布 (PMF.pure (fun _ => false)), 関数 (g ∅)
        unfold PMF.expect PMF.expect_ennreal r_bool_prod
        simp only [PMF.pure_apply, Finset.prod_empty, ENNReal.ofReal_one, mul_one]
        -- 有限和で唯一の項は if文で 1 になり、ENNReal.toReal_one を適用
        have h_sum : (Finset.univ : Finset (Γ → Bool)).sum (fun x => if x = (fun _ : Γ => false) then (1 : ENNReal) else 0) = 1 := by
          rw [Finset.sum_eq_single (fun _ : Γ => false)]
          · simp
          · intro b hb hne
            simp [hne]
          · simp [Finset.mem_univ]
        -- h_sum を実数の等式に変換する。ENNReal の 1 は有限なので toReal で変換可能
        rw [← h_sum]
        simp [ENNReal.toReal_one]
      exact h_pure
  | cons v L ih =>
      intro A hA
      -- A.erase v ⊆ L.toFinset
      have hA' : A.erase v ⊆ L.toFinset := by
        intro u hu
        rcases Finset.mem_erase.mp hu with ⟨hu_ne, huA⟩
        -- (v::L).toFinset = insert v L.toFinset
        have hu' : u ∈ insert v (L.toFinset) := by
          simpa [List.toFinset_cons] using hA huA
        rcases Finset.mem_insert.mp hu' with h | h
        · exact (hu_ne h).elim
        · exact h
      -- 1点ステップ (`v`) をはがす
      have hstep :
        PMF.expect (product_pmf_on M (v :: L)) (r_bool_prod A)
        =
        (if v ∈ A then (M.p v).toReal else 1) *
        PMF.expect (product_pmf_on M L) (r_bool_prod (A.erase v)) := by
        simpa [product_pmf_on, r_bool_prod]
          using expect_step (M:=M) (A:=A) (v:=v) (pmf:=product_pmf_on M L)
      -- 場合分け v∈A
      by_cases hv : v ∈ A
      · -- 係数が (M.p v).toReal になる
        calc
          PMF.expect (product_pmf_on M (v :: L)) (r_bool_prod A)
              = (M.p v).toReal *
                PMF.expect (product_pmf_on M L) (r_bool_prod (A.erase v)) := by
                simp [hstep, hv]
          _ = (M.p v).toReal *
                (A.erase v).prod (fun u => (M.p u).toReal) := by
                -- 変数名を u に統一して型エラーを回避
                have h_eq := ih (A.erase v) hA'
                rw [h_eq]
          _ = A.prod (fun u => (M.p u).toReal) := by
                -- A = insert v (A.erase v) かつ v ∉ A.erase v
                have hx : v ∉ A.erase v := Finset.notMem_erase v A
                have hdecomp : insert v (A.erase v) = A := Finset.insert_erase hv
                -- ゴールを単純化するためA を insert v (A.erase v) で置き換え
                rw [←hdecomp]
                -- prod_insert の対称形を使って左辺の形に合わせる
                simp [Finset.prod_insert, hx]
      · -- 係数が 1、かつ A.erase v = A
        have hA'' : A ⊆ L.toFinset := by
          intro u huA
          have hu' : u ∈ insert v (L.toFinset) := by
            simpa [List.toFinset_cons] using hA huA
          rcases Finset.mem_insert.mp hu' with h | h
          · cases h; exact (hv huA).elim
          · exact h
        calc
          PMF.expect (product_pmf_on M (v :: L)) (r_bool_prod A)
              = PMF.expect (product_pmf_on M L) (r_bool_prod (A.erase v)) := by
                simp [hstep, hv]
          _ = PMF.expect (product_pmf_on M L) (r_bool_prod A) := by
                simp [Finset.erase_eq_of_notMem hv]
          _ = A.prod (fun u => (M.p u).toReal) := ih A hA''

/-- univ.toList での特殊化（`product_pmf` 版）
Janson モデル M と頂点の列 L、有限集合 A（A ⊆ L.toFinset を仮定）の下での期待値の式を与える補題。

product_pmf_on M L による確率分布の下で、写像 ω ↦ ∏_{v ∈ A} (if ω v then 1 else 0) の期待値は、
各頂点 v の成功確率 M.p v の実数値への積に等しい。これは各頂点が独立なベルヌーイ試行であることに起因するため、
積の期待値が各確率の積に分解されることを述べている。

引数:
- M : JansonModel Γ （各頂点の成功確率を与える）
- L : 頂点の列（product_pmf_on の定義に用いる）
- A : Finset Γ （A ⊆ L.toFinset の仮定が必要）
- hA : A ⊆ L.toFinset の証明

証明は expect_product_pmf_on を用いて行われる。
-/
theorem PMF.expect_product_pmf
  (M : JansonModel Γ) (L : List Γ) (A : Finset Γ) (hA : A ⊆ L.toFinset) :
  PMF.expect (product_pmf_on M L) (fun ω => A.prod (fun v => if ω v then (1:ℝ) else 0))
    = A.prod (fun v => (M.p v).toReal) :=
  expect_product_pmf_on (M:=M) L A hA

/-- product_pmf と product_pmf_on の同値性を補題として追加
JansonModel Γ に対する補題。全頂点集合に対して定義した積分布（product_pmf）は，
その頂点集合を列挙したリストに対して `product_pmf_on` を適用したものと一致することを主張する。

具体的には，`product_pmf` はグラフの全頂点にわたる積の確率質量関数を与える構成であり，
`product_pmf_on M l` は与えた頂点列 `l : List Γ` に対して同様の積を取るが，リストの順序に依らない性質を持つ。
本補題は，有限集合としての全体 `Finset.univ` を `toList` で列挙した場合でも定義が一致すること（順序に依存しないこと）を示している。

証明方針は定義を展開し，リスト化と有限集合との変換に伴う順序や重複の扱いが影響しないことを示すことである。
-/
theorem product_pmf_eq_product_pmf_on (M : JansonModel Γ) :
  product_pmf M = product_pmf_on M ((Finset.univ : Finset Γ).toList) := by
  -- product_pmf の定義を展開して、内部の foldr と再帰定義が一致することを示す
  dsimp [product_pmf]
  let f := fun (v : Γ) (pmf : PMF (Γ → Bool)) => pmf.bind (fun ω => (bernoulli_pmf M v).map fun b => Function.update ω v b)
  let init : PMF (Γ → Bool) := PMF.pure (fun _ => false)
  -- 一般化して List.foldr f init L = product_pmf_on M L を帰納法で示す
  have h : List.foldr f init ((Finset.univ : Finset Γ).toList) = product_pmf_on M ((Finset.univ : Finset Γ).toList) := by
    -- 任意のリスト L について帰納法で示し、それを univ.toList に特殊化する
    have : ∀ (L : List Γ), List.foldr f init L = product_pmf_on M L := by
      intro L
      induction L with
      | nil =>
        -- 空リストでは両辺とも init に簡約する
        dsimp [product_pmf_on, List.foldr]
      | cons v L ih =>
        -- 先頭要素のステップは foldr と product_pmf_on の再帰式で一致する
        dsimp [product_pmf_on, List.foldr]
        -- 帰納仮定を適用すると両辺が定義的に一致するので rfl で閉じる
        rw [ih]
    -- 一般命題を univ.toList に適用して目的を得る
    exact this ((Finset.univ : Finset Γ).toList)
  -- 定理の主張は上の等式と product_pmf の定義から直ちに得られる
  exact h

-- あなたの `expect_indicator_prod'` は次の一行で完結（product_pmf_on に落とし込んで既存定理を適用）
/--
A ⊆ Γ に対して，
期待値 E_{ω ∼ product_pmf M} [ ∏_{v ∈ A} 1_{ω v} ] = ∏_{v ∈ A} (M.p v).toReal が成り立つことを述べる補題。
ここで ∏_{v ∈ A} 1_{ω v} は各 v ∈ A について ω v が真であれば1，そうでなければ0 を掛け合わせたもので，
A の全点で ω が真であることの指示関数に等しい。
結論は product_pmf の座標独立性により，各因子の期待値の積に分解できることに基づく。
-/
lemma expect_indicator_prod' (M : JansonModel Γ) (A : Finset Γ) :
  PMF.expect (product_pmf M) (fun ω => A.prod fun v => if ω v then (1 : ℝ) else 0)
    = A.prod fun v => (M.p v).toReal := by
  classical
  have hsubset : A ⊆ ((Finset.univ : Finset Γ).toList).toFinset := by simp
  -- product_pmf を product_pmf_on に書き換えて型を合わせ、既存の補題を使う
  rw [product_pmf_eq_product_pmf_on (M:=M)]
  exact PMF.expect_product_pmf (M:=M) ((Finset.univ : Finset Γ).toList) (A:=A) hsubset

theorem indicatorA_eq_pmf_expectation {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (M : JansonModel Γ) (A : Finset Γ) :
    indicatorA M A = PMF.expect (product_pmf M) (fun ω => ∏ v ∈ A, if ω v then (1 : ℝ) else 0) := by
  classical
  -- indicatorA = ∏ (M.p v).toReal を定義から展開し、既証明の expect_indicator_prod' を刺すだけ
  simp [indicatorA]
  simpa using (expect_indicator_prod' (M:=M) (A:=A)).symm

-- `PMF.expect_product_pmf` の証明

/-
`PMF.expect_product_pmf` は、有限集合 `Γ` 上の Janson モデル `M`、要素のリスト `vs`、部分集合 `A` に対して、
`vs` 上のベルヌーイ分布の独立な生成により構成される確率変数 ω に対し、
`A` の各要素 `v` について ω(v) が真なら 1、偽なら 0 を掛け合わせた期待値を計算します。

この期待値は、`A` の各要素 `v` に対して、ベルヌーイ分布の成功確率 `M.p v` の積に等しくなります。

- `Γ`: 有限型
- `M`: Janson モデル
- `vs`: Γ の要素のリスト
- `A`: Γ の有限部分集合
- `hvs`: `A ⊆ vs.toFinset` の証明

この定理は、独立なベルヌーイ分布の積の期待値が確率の積になることを形式化しています。
-/

/--
vs に列挙された各頂点 v について独立に bernoulli_pmf M v に従って真偽をサンプリングし，
その結果得られる写像 ω : Γ → Bool に対して，有限集合 A に属する全ての頂点で ω v = true となる確率
（すなわち A に渡る指示関数の積の期待値）が，各頂点の成功確率の積に等しいことを示す補題。

具体的には，foldr で構成した PMF は vs 中の各頂点について独立に Bernoulli 試行を行って ω を構成する分布であり，
hvs により A ⊆ vs.toFinset が成り立つため A の全要素は実際にサンプリングされる．
期待値計算は指示関数の積が A の全頂点が同時に true である事象の確率に対応することと，
独立性（foldr による逐次サンプリング）から，その確率が各 v に対する (M.p v).toReal の積に等しいことを示すことで得られる。
-/
theorem expect_product_pmf
  {Γ : Type*} [DecidableEq Γ] [Fintype Γ] -- これで十分
  (M : JansonModel Γ) (vs : List Γ) (A : Finset Γ) (hvs : A ⊆ vs.toFinset) :
  PMF.expect
    (product_pmf_on M vs)
    (fun ω => A.prod (fun v => if ω v then (1 : ℝ) else 0))
  =
  A.prod (fun v => (M.p v).toReal)
  := by
  -- product_pmf_on に対する既存の補題を適用して終了
  exact PMF.expect_product_pmf (M:=M) vs A hvs


/- E[ ∏_{v∈A} 1{ω(v)=1} ] = ∏_{v∈A} p v
`expect_indicator_prod'` 補題は、有限型 `Γ` 上の Janson モデル `M` と有限集合 `A` に対して、
確率測度 `product_pmf M` のもとで、関数 `ω ↦ ∏_{v ∈ A} if ω v then 1 else 0` の期待値が
`∏_{v ∈ A} (M.p v).toReal` に等しいことを示します。

この関数は、`A` の各要素 `v` について、`ω v` が真なら 1、偽なら 0 を掛け合わせるため、
`A` の全ての要素が `ω` で真となる確率を表します。
その期待値は、各 `v` についての確率 `M.p v` の積に一致します。
-/

/--
A に含まれる各頂点 v に対して指示関数 (fun ω => if ω v then 1 else 0) を取ったときの
product_pmf M による期待値は、各頂点の選ばれる確率の積に等しい、という補題。

より正確には、Γ が有限集合で決定可能な等号を持ち、M : JansonModel Γ, A : Finset Γ のとき
PMF.expect (product_pmf M) (fun ω => A.prod fun v => if ω v then (1 : ℝ) else 0)
= A.prod fun v => (M.p v).toReal が成り立つ。

直観的には ω の各座標が独立であること（product_pmf の性質）から期待値が各座標ごとに因数分解でき、
各指示関数の期待値が対応する確率 M.p v の実数化に等しいことを使う。証明中で
Finset.univ.toList により A ⊆ ((Finset.univ : Finset Γ).toList).toFinset であることを用いている。
-/
lemma expect_indicator_prod {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (M : JansonModel Γ) (A : Finset Γ) :
  PMF.expect (product_pmf M) (fun ω => A.prod fun v => if ω v then (1 : ℝ) else 0) = A.prod fun v => (M.p v).toReal := by
  -- Finset.univ.toList = Finset.univ なので A ⊆ それが成り立つ
  have hsubset : A ⊆ ((Finset.univ : Finset Γ).toList).toFinset := by
    simp
  -- product_pmf を list 版へ置換 → 既存の expect_product_pmf を適用
  simpa [product_pmf_eq_product_pmf_on (M:=M)] using
    PMF.expect_product_pmf (M:=M) ((Finset.univ : Finset Γ).toList) (A:=A) hsubset

-- Model-limited (product PMF) version of the v2 bound used by the Middle band.
-- This lemma provides the exact shape `ABCMiddle` expects as `ABC.Janson.bound_v2`.
-- A full formal derivation of the Janson inequality is nontrivial; for integration
-- with the Middle layer we temporarily ad#mit the statement here. Replace `ad#mit`
-- with a full proof later.
theorem bound_v2 {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
  (M : JansonModel Γ) (A : Finset Γ) :
  PMF.expect (product_pmf M)
    (fun (ω : Γ → Bool) => A.prod (fun v => if ¬ ω v then (1 : ℝ) else 0))
    ≤ (if 0 < dbar (M:=M) (A:=A) then
         Real.exp ( - (mu (M:=M) (A:=A)) ^ 2 / (2 * dbar (M:=M) (A:=A)) )
       else
         Real.exp ( - mu (M:=M) (A:=A) )) := by
  admit


-- -------------------------------------------------------
-- 以下、Janson-Suen の補題証明に必要な Finset の補題群
-- -------------------------------------------------------
-- Finset の差集合・交差集合に関する補題群

/--
`Finset.union_sdiff_inter` は、有限集合 `s` を、`t` との差集合 `s \ t` と、共通部分 `s ∩ t` の和集合として表す補題です。
この補題は、任意の型 `α` と有限集合 `s, t : Finset α` に対して成り立ちます。
-/
lemma Finset.union_sdiff_inter {α : Type*} [DecidableEq α] {s t : Finset α} :
  s = (s \ t) ∪ (s ∩ t) := by
  -- Finset.union_sdiff_inter は Mathlib に未定義なので自前で証明する
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  -- 明示的に双方向を示す
  apply Iff.intro
  · -- (→) x ∈ s → x ∈ s \ t ∨ x ∈ s ∩ t
    intro hx
    by_cases hxt : x ∈ t
    · right; exact ⟨hx, hxt⟩
    · left; exact ⟨hx, hxt⟩
  · -- (←) x ∈ s \ t ∨ x ∈ s ∩ t → x ∈ s
    intro H
    cases H with
    | inl hsd => exact hsd.left
    | inr hsint => exact hsint.left

-- SDiff インスタンスは不要なので削除

/--
`Finset.prod_eq_prod_diff_mul_prod_inter` は、有限集合 `s` 上の関数 `f` の積が、`s` から `t` を除いた部分集合上の積と、`s` と `t` の共通部分上の積の積に分解できることを示します。

具体的には、`s.prod f = (s \ t).prod f * (s ∩ t).prod f` という等式が成り立ちます。

- `α` : 元の型
- `β` : 積を取る型（可換モノイド）
- `s`, `t` : 有限集合
- `f` : 関数

この補題は、有限集合の積を部分集合に分割して計算したい場合に有用です。
-/
lemma Finset.prod_eq_prod_diff_mul_prod_inter {α : Type*} [DecidableEq α] {β : Type*} [CommMonoid β] {s t : Finset α} (f : α → β) :
  s.prod f = (s \ t).prod f * (s ∩ t).prod f := by
  -- s = (s \ t) ∪ (s ∩ t) で分解し、互いに素であることを示してから prod_union を使う
  have hs : s = (s \ t) ∪ (s ∩ t) := Finset.union_sdiff_inter (s := s) (t := t)
  -- (s \ t) と (s ∩ t) は互いに素である
  have hdis : Disjoint (s \ t) (s ∩ t) := Finset.disjoint_sdiff_inter s t
  -- まず和集合について prod_union を適用し、その後 hs を用いて元の s に戻す
  have h : ((s \ t) ∪ (s ∩ t)).prod f = (s \ t).prod f * (s ∩ t).prod f := Finset.prod_union hdis (f := f)
  rw [hs.symm] at h
  exact h

/-- E[I_A * I_B] = ∏_{v∈A∪B} p v
`expect_indicator_joint` は、有限型 `Γ` 上の Janson モデル `M` に対して、有限集合 `A` および `B` の指示関数の積の期待値を計算する補題です。
具体的には、確率測度 `product_pmf M` の下で、`A` および `B` の各要素に対して ω(v) が真である場合に 1、偽である場合に 0 を返す関数の積の期待値が、
`A ∪ B` の各要素に対する `M.p v` の実数値の積に等しいことを示します。
この補題は、確率論的な独立性と期待値の計算に関する議論で有用です。
-/
lemma expect_indicator_joint {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
  (M : JansonModel Γ) (A B : Finset Γ) :
  PMF.expect (product_pmf M)
    (fun (ω : Γ → Bool) =>
      (A.prod fun v => if ω v then (1 : ℝ) else 0) *
      (B.prod fun v => if ω v then (1 : ℝ) else 0))
  =
  (A ∪ B).prod fun v => (M.p v).toReal := by
  classical
  -- pointwise 同値
  have hpt : (fun (ω : Γ → Bool) =>
      (A.prod fun v => if ω v then (1 : ℝ) else 0) *
      (B.prod fun v => if ω v then (1 : ℝ) else 0))
    =
    (fun ω => (A ∪ B).prod (fun v => if ω v then (1 : ℝ) else 0)) := by
    funext ω
    -- ∏_A * ∏_B = ∏_{A∪B} * ∏_{A∩B}、ただし 0/1 なので ∏_{A∩B} = 1
    -- ∏_A * ∏_B = ∏_{A∪B} * ∏_{A∩B} の補題を自前で証明
    let f := fun v : Γ => if ω v then (1 : ℝ) else 0
    have prod_mul_prod_eq_prod_union_prod_inter :
      (A.prod f) * (B.prod f) = ((A ∪ B).prod f) * ((A ∩ B).prod f) := by
      -- 差集合・交差による分解を順序よく適用してから代数的に整理する
      -- A と A ∪ B の分解を先に書き換える
      have h1 := Finset.prod_eq_prod_diff_mul_prod_inter (f := f) (s := A) (t := B)
      have h3 := Finset.prod_eq_prod_diff_mul_prod_inter (f := f) (s := A ∪ B) (t := B)
      rw [h1, h3]
      -- ((A ∪ B) \ B) = A \ B を示す
      have diff_eq : ((A ∪ B) \ B) = A \ B := by
        ext x
        constructor
        · intro h; -- h : x ∈ (A ∪ B) \ B
          have ⟨hmem, hnot⟩ := (Finset.mem_sdiff).1 h
          cases (Finset.mem_union).1 hmem with
          | inl ha => exact (Finset.mem_sdiff).2 ⟨ha, hnot⟩
          | inr hb => contradiction
        · intro h; -- h : x ∈ A \ B
          have ⟨ha, hnot⟩ := (Finset.mem_sdiff).1 h
          exact (Finset.mem_sdiff).2 ⟨(Finset.mem_union).2 (Or.inl ha), hnot⟩
      -- ((A ∪ B) ∩ B) = B は自明
      have inter_eq : ((A ∪ B) ∩ B) = B := by ext x; simp
      rw [diff_eq, inter_eq]
      -- ここで右辺は (A \ B).prod * B.prod * (A ∩ B).prod になるので B の分解を適用する
      have h2 := Finset.prod_eq_prod_diff_mul_prod_inter (f := f) (s := B) (t := A)
      rw [h2]
      -- 残りは乗法の可換性・結合性で整理できる
      ring
    -- 右辺第2因子の冪等性で 1 へ、あるいは両辺とも 0 になることを示す。
    -- f は各点で 0 または 1 を取るので、(A ∪ B).prod f = 0 の場合は両辺 0 になり自明。
    -- そうでなければ (A ∪ B).prod f ≠ 0 なので各点の値は 1 であり、特に (A ∩ B).prod f = 1 となる。
    let f := fun v : Γ => if ω v then (1 : ℝ) else 0
    have hprod := prod_mul_prod_eq_prod_union_prod_inter
    by_cases hzero : (A ∪ B).prod f = 0
    · -- union の積が 0 のときは両辺とも 0
      have : (A.prod f) * (B.prod f) = (A ∪ B).prod f := by
        rw [hprod, hzero]
        simp
      exact this
    -- union の積が非零のとき、各点で f v ≠ 0 なので f v = 1 (0/1 のみ取るため)
    have nonzero_on_union : ∀ v ∈ A ∪ B, f v ≠ 0 := by
      intro v hv
      by_contra hf
      have : (A ∪ B).prod f = 0 := by
        -- Finset.prod_eq_zero_iff の右から左の方向を使い、v を witness として与える
        exact (Finset.prod_eq_zero_iff.mpr ⟨v, hv, hf⟩)
      contradiction
    have all_one_on_union : ∀ v ∈ A ∪ B, f v = 1 := by
      intro v hv
      dsimp [f]
      by_cases hv' : ω v
      · simp [hv']
      · have fv_zero : f v = 0 := by simp [f, hv']
        -- ここで (A ∪ B).prod f = 0 となるので hzero と矛盾
        have prod_zero : (A ∪ B).prod f = 0 := Finset.prod_eq_zero_iff.mpr ⟨v, hv, fv_zero⟩
        exact False.elim (hzero prod_zero)
    have inter_one : (A ∩ B).prod f = 1 := Finset.prod_eq_one fun v hv =>
      let ⟨hA, _hB⟩ := Finset.mem_inter.mp hv
      all_one_on_union v (Finset.mem_union_left B hA)
    rw [inter_one] at hprod
    simpa using hprod
  -- あとは A∪B 版の単独積の期待値に帰着
  simpa [hpt] using expect_indicator_prod (Γ:=Γ) (M:=M) (A:=A ∪ B)

-- end PMF_Bridge  -- section PMF_Bridge

end Janson

-- -------------------------------------------------------

end ABC
