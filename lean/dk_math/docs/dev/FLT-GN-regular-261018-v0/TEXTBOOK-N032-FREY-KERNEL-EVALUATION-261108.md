# NOTE-032 教科書 — 固定差分・核の鋭い濃度上界・実際の慣性評価

日付: 2026-11-08。レビューの追加提案である核の指数上界 n+2 を証明し、
同じ係数核の実際の評価写像と、その像・核の三つの指数の収支まで5ステップ実装した。
後半の5つの Lean ブロックは対応する production ソースの全文。
各 import 群直後の正確な `#print "file: モジュール名"` を省略しない。
既存 DkMath の Lake 環境で各ブロックを別ファイルへコピペして検査できる。

## 使う群・係数・同じ元

同じ Frey 曲線、同じ巡回段 T、同じ上位有限捩れ商 Q=E[p^(n+2)]/T を保持する。
慣性群 I と固定部分群 F=Q^I、実際の通常の群コホモロジーの係数核

    K = ker(H¹(I,F) → H¹(I,Q))

を使う。前回の局所幾何による Q/F≃ₗ[ℤ]K はそのまま使う。
Q の濃度は p^(n+3)。p≥5、素数 q≠p、悪い住所とその上の付値環という
元の局所条件を維持する。障害証明書 h は元の n,T,q,A,τ,y と p•y∈T、
慣性差分の非吸収などを保持する。新しい fixedness・濃度・評価の provider は要求しない。

同じ y の剰余類から構成した核元を k、同じ慣性元 τ での固定差分を d と書く。
以前の構成により k.val は同じ α_I である。

## 1. 固定部分群 F にも厳密位数 p の元がある

元の指標の値を F に制限したまま

    d = c_y(τ) ∈ F,    addOrderOf d = p

と証明する。p 倍零性には同じ前像条件 p•y∈T を使い、非零性には同じ非吸収条件を使う。
従って同じ d が生成する部分群の濃度は p、Lagrange により p は |F| を割る。
F 全体が位数 p、または巡回であるという結論ではない。

## 2. 二つの正の指数と上界 n+2

前回の濃度積 |K|·|F|=p^(n+3) と、今回の F の素数因子から

    |F|=p^r,  |K|=p^s,  r≥1, s≥1, r+s=n+3

を得る。s≥1 は以前の同じ非零核元 k による。
p の冪の単射性によって指数の等式を証明するので、

    1≤r≤n+2,  1≤s≤n+2

となる。レビューの n+3 から n+2 への改善を、新しい算術仮定を加えず形式化した。

## 3. 核の元の実際の慣性評価

F の作用は自明なので、Mathlib の標準同型

    H¹(I,F) ≃ Hom(Additive I,F)

が使える。その同型と実際の核への包含から、各 σ∈I について

    ev_σ : K →ₗ[ℤ] F

を構成する。元の同じ核元については全ての σ に対し

    ev_σ(k) = c_y(σ)

を証明する。特に ev_τ(k)=d。別の cocycle の選択ではなく、
自明係数の標準 H¹ 同型が元の同じ値を回収する。
全ての σ での評価が一致すれば K の元は一致することも証明した。
一つの σ での評価の単射性とは区別する。
この評価写像の定義・分離性は局所幾何や hclass を必要としない。

## 4. 実際の評価像の非自明性と濃度積

元の同じ τ での評価 ev=ev_τ に対し、実際の整数部分加群

    B = range ev,    U = ker ev

を使う。第一同型定理と部分加群の濃度公式により

    |B|·|U|=|K|

を証明する。同じ k の像を B の元 b として保持し、b.val=d と
addOrderOf b=p を証明する。従って p は |B| を割る。
像全体が位数 p、または評価核 U が零だとは結論しない。

## 5. 三つの指数と評価核の上界 n+1

同じ濃度積と p 冪の約数の特徴付けから

    |F|=p^r,  |B|=p^t,  |U|=p^u,
    |K|=p^(t+u),
    r≥1, t≥1, u≥0, r+t+u=n+3

を導く。従って

    r≤n+2,  t≤n+2,  u≤n+1

である。核全体 K と評価核 U は異なる対象。
最終存在定理 `residual_exists_evaluated_coefficient_kernel` は元の hclass と Cofixed から
同じ n,T,q,A,τ,y,h を取り、同じ k,d,b の厳密位数と値の一致、これら三つの指数を返す。
元の算術証明書を強い新仮定へ置き換えていない。

## 模範解答との照合と残る境界

ローカル模範解答の `deltaCochain₀` の coboundary と不変持ち上げの同値、
短完全列の連結写像の自然性の解答を読み、同じ連結像を保持する経路を確認した。
参照 HEAD は 115356cbc627159d0d16add0da6e9a2bb3655ed8。
今回は Mathlib の `H1IsoOfIsTrivial` と同じ代表の値回収、第一同型定理を使う。
模範解答の独自 provider や P2M/P2MW は import しない。
参照ファイルと Mathlib ソースの SHA-256 は evidence の参照監査に保存する。

この5段階は全て通常の群コホモロジーの構造定理である。
連続 H¹ との比較、大域類群への同定、共鳴障害の算術的排除、hclass の供給は未完成。
非零の K・評価像 B はこれらの構造と整合し、それだけでは矛盾しない。
**無条件の一般 hno は引き続き未完成である。**

回帰検査は ZMod5 の座標評価を使う。一つの非零評価が非単射である例、
全座標での分離性、r=t=u=1（n=0）で改善上界が達成される濃度計算を検査する。
18宣言の再帰依存監査と18件の公開入力監査、全宣言の公理出力を通常テストへ接続する。
検証結果は `evidence/validation-note032-frey-kernel-evaluation.txt` に保存する。

## コピペ用 Lean 全文

### 1. DkMath.FLT.FreyFixedDifferencePrimeOrder

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelCertificate

#print "file: DkMath.FLT.FreyFixedDifferencePrimeOrder"

/-!
# 同じ固定差分の厳密位数と固定部分群の素数因子

元の障害点 y と慣性元 τ を保持する。核の非零性とは別に、固定係数 F 自体にも
位数 p の元がある。F 全体が巡回であるとは主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ慣性元で評価した、F に属する同じ差分。 -/
def NarrowAbsorptionObstruction.fixedDifference
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    T.inertiaFixedUpperQuotient A :=
  Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩)

/-- 値域制限後も、同じ固定差分の厳密位数は p。 -/
theorem NarrowAbsorptionObstruction.fixedDifference_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    addOrderOf (h.fixedDifference hp5) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · exact h.fixed_character_values_killed hp5 ⟨τ, h.inertia⟩
  · intro hz
    have he := congrArg (fun v : T.inertiaFixedUpperQuotient A => Multiplicative.ofAdd v.val) hz
    exact (h.inertia_character_nontrivial hp5).1 he

/-- F の中の同じ差分が生成する巡回部分群は濃度 p。 -/
theorem NarrowAbsorptionObstruction.fixedDifference_cyclic_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    Nat.card (AddSubgroup.zmultiples (h.fixedDifference hp5)) = p :=
  (Nat.card_zmultiples _).trans (h.fixedDifference_order_eq_prime hp5)

/-- Lagrange により、固定部分群 F 全体の濃度は p で割れる。 -/
theorem NarrowAbsorptionObstruction.prime_dvd_fixed_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    p ∣ Nat.card (T.inertiaFixedUpperQuotient A) := by
  have hd := (AddSubgroup.zmultiples (h.fixedDifference hp5)).card_addSubgroup_dvd_card
  exact dvd_trans ((h.fixedDifference_cyclic_card hp5).symm ▸ dvd_refl p) hd

end
end DkMath.FLT.Frey.Source
```

### 2. DkMath.FLT.FreyConnectingKernelSharpProfile

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedDifferencePrimeOrder

#print "file: DkMath.FLT.FreyConnectingKernelSharpProfile"

/-!
# 固定部分群と係数核の指数収支、改善された上界 n+2

F の同じ非零差分と K の同じ非零類を別々に使う。両方の指数が正なので、
濃度積の指数 n+3 は r+s に正確に分かれる。新しい算術仮定を加えない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ固定部分群 F の濃度は、正の指数の p 冪。 -/
theorem NarrowAbsorptionObstruction.fixed_positive_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r, 1 ≤ r ∧ r ≤ n + 3 ∧ Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r := by
  have hd : Nat.card (T.inertiaFixedUpperQuotient A) ∣ p ^ (n + 3) := by
    refine ⟨Nat.card (T.fixedH1CoefficientKernel A), ?_⟩
    rw [mul_comm]
    exact (T.fixedKernel_card_mul_fixed A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over).symm
  obtain ⟨r, hr, hc⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hr0 : r ≠ 0 := by
    intro hz
    have hd1 := h.prime_dvd_fixed_card hp5
    rw [hc, hz, pow_zero, Nat.dvd_one] at hd1
    exact (Fact.out : p.Prime).ne_one hd1
  exact ⟨r, by omega, hr, hc⟩

/-- 元の同じ F と K の濃度指数は正で、和は正確に n+3。 -/
theorem NarrowAbsorptionObstruction.fixed_kernel_balanced_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r s, 1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨r, hr, _, hF⟩ := h.fixed_positive_profile hp5
  obtain ⟨s, hs, _, hK⟩ := h.fixedKernel_positive_profile hp5
  have he := T.fixedKernel_card_mul_fixed A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over
  rw [hF, hK, ← pow_add] at he
  have hsum : s + r = n + 3 := Nat.pow_right_injective (Fact.out : p.Prime).two_le he
  exact ⟨r, s, hr, hs, by omega, hF, hK⟩

/-- レビュー提案の改善：両方の正の濃度指数は n+2 以下。 -/
theorem NarrowAbsorptionObstruction.fixed_kernel_sharp_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r s, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ s ∧ s ≤ n + 2 ∧ r + s = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨r, s, hr, hs, hsum, hF, hK⟩ := h.fixed_kernel_balanced_profile hp5
  exact ⟨r, s, hr, by omega, hs, by omega, hsum, hF, hK⟩

end
end DkMath.FLT.Frey.Source
```

### 3. DkMath.FLT.FreyConnectingKernelEvaluation

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelSharpProfile

#print "file: DkMath.FLT.FreyConnectingKernelEvaluation"

/-!
# 実際の係数核を慣性元で評価する

F の作用は自明なので、Mathlib の通常の H¹ 同型が各類の一意な準同型を回収する。
その評価を実際の核 K に制限する。代表の追加選択や連続 H¹ への移行は行わない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の実際の係数核の元を、指定した慣性元で評価する整数線形写像。 -/
def ResidualCyclicStage.fixedKernelEvaluation (σ : inertiaSubgroupIn A ℚ) :
    T.fixedH1CoefficientKernel A →ₗ[ℤ] T.inertiaFixedUpperQuotient A where
  toFun k := (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom
      k.val (Additive.ofMul σ)
  map_add' x y := congrArg
    (fun f : Additive (inertiaSubgroupIn A ℚ) →+ T.inertiaFixedUpperQuotient A => f (Additive.ofMul σ))
    ((groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom.hom.map_add x.val y.val)
  map_smul' m x := congrArg
    (fun f : Additive (inertiaSubgroupIn A ℚ) →+ T.inertiaFixedUpperQuotient A => f (Additive.ofMul σ))
    ((groupCohomology.H1IsoOfIsTrivial
      (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom.hom.map_smul m x.val)

/-- 全慣性元での評価が一致すれば、同じ核の元そのものが一致する。 -/
theorem ResidualCyclicStage.fixedKernelEvaluation_separates
    (x y : T.fixedH1CoefficientKernel A)
    (he : ∀ σ, T.fixedKernelEvaluation A σ x = T.fixedKernelEvaluation A σ y) : x = y := by
  apply Subtype.ext
  apply (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A)))).injective
  apply AddMonoidHom.ext
  intro σ
  exact he σ.toMul

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 以前の同じ核元の評価は、元の同じ固定差分指標の値である。 -/
theorem ResidualCyclicStage.fixedKernelEvaluation_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    T.fixedKernelEvaluation A σ (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
      Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ) := by
  change (groupCohomology.H1IsoOfIsTrivial _).hom
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x).val (Additive.ofMul σ) = _
  rw [T.fixedCosetKernelElement_val hp5 hq hqp haddr A hA x]
  exact TrivialCharacterH1.class_evaluate _ σ

end
end DkMath.FLT.Frey.Source
```

### 4. DkMath.FLT.FreyKernelEvaluationImage

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingKernelEvaluation

#print "file: DkMath.FLT.FreyKernelEvaluationImage"

/-!
# 同じ慣性評価の像にある位数 p の元

評価写像の像・核は実際の整数部分加群を使う。元の障害元の評価は零でなく、
像の中でも厳密位数 p を保つ。ただし一つの評価が K 全体で単射とは主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 第一同型定理による、同じ評価写像の実際の像と核の濃度積。 -/
theorem ResidualCyclicStage.fixedKernelEvaluation_card (σ : inertiaSubgroupIn A ℚ) :
    Nat.card (LinearMap.range (T.fixedKernelEvaluation A σ)) *
      Nat.card (LinearMap.ker (T.fixedKernelEvaluation A σ)) = Nat.card (T.fixedH1CoefficientKernel A) := by
  have hc := (LinearMap.ker (T.fixedKernelEvaluation A σ)).card_eq_card_quotient_mul_card
  have he := Nat.card_congr (T.fixedKernelEvaluation A σ).quotKerEquivRange.toEquiv
  rw [he] at hc
  exact (mul_comm _ _).trans hc.symm

variable {T A} {q : ℕ} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害の核元を元の τ で評価すると、元の固定差分 d そのものになる。 -/
theorem NarrowAbsorptionObstruction.fixedKernelEvaluation_obstruction
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
      h.fixedDifference hp5 :=
  T.fixedKernelEvaluation_coset A hp5 h.prime h.ne_torsion_prime (Or.inr h.support)
    h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩

/-- 同じ核元を評価した、実際の像部分加群の元。 -/
def NarrowAbsorptionObstruction.fixedEvaluationImageElement
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    LinearMap.range (T.fixedKernelEvaluation A ⟨τ, h.inertia⟩) :=
  ⟨_, T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩, rfl⟩

/-- 実際の像で保持した元の値も、同じ固定差分 d。 -/
theorem NarrowAbsorptionObstruction.fixedEvaluationImageElement_val
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    (h.fixedEvaluationImageElement hp5).val = h.fixedDifference hp5 :=
  h.fixedKernelEvaluation_obstruction hp5

/-- 同じ評価像の元は、像部分加群の中でも厳密位数 p。 -/
theorem NarrowAbsorptionObstruction.fixedEvaluationImage_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    addOrderOf (h.fixedEvaluationImageElement hp5) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  have hd := addOrderOf_eq_prime_iff.mp (h.fixedDifference_order_eq_prime hp5)
  constructor
  · apply Subtype.ext
    change p • (h.fixedEvaluationImageElement hp5).val = 0
    rw [h.fixedEvaluationImageElement_val hp5]
    exact hd.1
  · intro hz
    apply hd.2
    exact (h.fixedEvaluationImageElement_val hp5).symm.trans (congrArg Subtype.val hz)

/-- 同じ評価の像全体の濃度は p で割れる。像全体の濃度が p とは限らない。 -/
theorem NarrowAbsorptionObstruction.prime_dvd_evaluation_image_card
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    p ∣ Nat.card (LinearMap.range (T.fixedKernelEvaluation A ⟨τ, h.inertia⟩)) := by
  have hd := addOrderOf_dvd_natCard (h.fixedEvaluationImageElement hp5)
  exact dvd_trans ((h.fixedEvaluationImage_order_eq_prime hp5).symm ▸ dvd_refl p) hd

end
end DkMath.FLT.Frey.Source
```

### 5. DkMath.FLT.FreyKernelEvaluationCertificate

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationImage

#print "file: DkMath.FLT.FreyKernelEvaluationCertificate"

/-!
# 固定係数・慣性評価像・評価核の三つの指数と元の算術証明書

F と評価像にはそれぞれ同じ位数 p の元がある。従って評価核の濃度指数は n+1 以下。
この指数収支は局所障害の存在と整合する構造定理であり、算術的矛盾ではない。
最後の存在定理には元の hclass と Cofixed が明示的に残る。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ F・評価像・評価核の指数収支。評価核の指数上界は n+1。 -/
theorem NarrowAbsorptionObstruction.fixed_evaluation_balanced_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
    ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ n + 2 ∧ u ≤ n + 1 ∧
      r + t + u = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
  obtain ⟨r, s, hr, hrb, hs, _, hrs, hF, hK⟩ := h.fixed_kernel_sharp_profile hp5
  have hc : Nat.card (LinearMap.range ev) * Nat.card (LinearMap.ker ev) =
      Nat.card (T.fixedH1CoefficientKernel A) := T.fixedKernelEvaluation_card A ⟨τ, h.inertia⟩
  have hdR : Nat.card (LinearMap.range ev) ∣ p ^ s :=
    ⟨Nat.card (LinearMap.ker ev), hK.symm.trans hc.symm⟩
  have hdU : Nat.card (LinearMap.ker ev) ∣ p ^ s :=
    ⟨Nat.card (LinearMap.range ev), hK.symm.trans (hc.symm.trans (mul_comm _ _))⟩
  obtain ⟨t, _, hR⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdR
  obtain ⟨u, _, hU⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdU
  have ht0 : t ≠ 0 := by
    intro hz
    have hd := h.prime_dvd_evaluation_image_card hp5
    change p ∣ Nat.card (LinearMap.range ev) at hd
    rw [hR, hz, pow_zero, Nat.dvd_one] at hd
    exact (Fact.out : p.Prime).ne_one hd
  have htu : t + u = s := by
    rw [hR, hU, hK, ← pow_add] at hc
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hc
  exact ⟨r, t, u, hr, hrb, by omega, by omega, by omega, by omega,
    hF, hR, hU, by rw [htu]; exact hK⟩

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 元の同じ算術障害を保持した、厳密位数・実際の評価・三つの濃度指数の証明書。 -/
theorem residual_exists_evaluated_coefficient_kernel
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
      addOrderOf k = p ∧ ev k = h.fixedDifference hp5 ∧
      addOrderOf (h.fixedDifference hp5) = p ∧ addOrderOf (h.fixedEvaluationImageElement hp5) = p ∧
      ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ n + 2 ∧ u ≤ n + 1 ∧
        r + t + u = n + 3 ∧
        Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
        Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
        Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.fixedKernel_order_eq_prime hp5,
    h.fixedKernelEvaluation_obstruction hp5, h.fixedDifference_order_eq_prime hp5,
    h.fixedEvaluationImage_order_eq_prime hp5, h.fixed_evaluation_balanced_profile hp5⟩

end
end DkMath.FLT.Frey.Source
```

