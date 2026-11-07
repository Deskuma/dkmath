# NOTE-032 教科書 — 固定係数の通常の H¹ と元の商加群への係数写像

日付: 2026-11-08。最新レビューの「係数を区別したコホモロジー」という提案を参考に、4ステップを実装した。
4つの Lean ブロックは、対応する4 production ファイルの全文である。
import 群直後の正確な `#print "file: モジュール名"` を保持する。
既存 DkMath の Lake 環境で各ブロックを別ファイルへコピペして検査できる。

## 今回形式化した三つの係数付きの対象

同じ Frey 曲線 E、同じ巡回段 T と上位捩れ商 Q=E[p^(n+2)]/T、
同じ付値環 A と慣性群 I、同じ野生合同部分群 W と馴分岐商 J=I/W を保つ。
F=Q^I は前回までに構成した **元の Q の実際の慣性固定部分群** である。

元の同じ点 x を基点とする差分は

    c_x(σ) = σ[x] − [x] ∈ Q

であり、局所積零性により全ての値は F に入る。
元の Q の作用を F へ制限すると自明作用になるため、今回 F を係数とする表現には
その同じ固定性に対応する自明な整数線形表現を使用する。
F→Q の包含が実際の表現の射であることも、F の元の固定性から証明した。

野生部分群 W は有限捩れ群全体に自明に作用するので、F 値の指標も W を核に含む。
従って同じ代表から次の三つを作れる。

| 群と係数 | 今回証明した通常の H¹ の性質 |
| --- | --- |
| J、係数 F、自明作用 | 同じ非自明な値を持つ指標の類は非零 |
| I、係数 F、自明作用 | 同じ非自明な値を持つ指標の類は非零 |
| I、係数 Q、元の実際の作用 | 同じ点 [x] の作用差の類は零 |

I の固定係数 cocycle と J の固定係数 cocycle は、元を商へ写したとき値が一致する。
今回は代表のこの引き戻し等式を証明した。両者の間の H¹ inflation 写像の比較定理は追加していない。

## 通常の H¹ と連続性を区別する

この実装で使うのは Mathlib の `groupCohomology.H1`、すなわち **通常の群コホモロジー** である。
Mathlib の `H1IsoOfIsTrivial` により、自明作用では H¹ と加法的群準同型が同型になる。
この同型を通じて実際の同じ値を回収し、非自明な値があれば類は非零と証明する。
一般補題は `TrivialCharacterH1` に分離した。

一方、F 値の元の慣性指標と、同じ J へ降ろした指標の **連続性** も別の定理として証明した。
元の Krull 部分群位相、標準商位相、元の離散 Q の固定部分群位相を使用する。
J 全体へ離散位相を設定したり、正規性・連続性を新しい算術 provider にしたりしない。

したがって今回は「連続な代表を持つ非零の通常の H¹ 類」を実装した。
Mathlib の `continuousCohomology 1` における非零性や、通常の H¹ との比較同型は証明していない。
レビューの連続 H¹ に関する提案全体を完成したと主張しない。

## 係数包含の H¹ 写像で同じ非零類が零へ移る

F から元の Q へ戻す包含 ι は、同じ群 I の表現の射である。
Mathlib の実際の `groupCohomology.map` を使い、

    H¹(I,F) → H¹(I,Q)

を扱う。元の同じ固定係数 cocycle の像は、値ごとに

    ι(c_F(σ)) = σ[x] − [x] = d₀₁([x])(σ)

と一致する。この d₀₁([x]) は実際の coboundary である。
`H1π_eq_zero_iff` の像による特徴付けと、`H1π_comp_map_apply` の自然性を使って、

    [c_F] ≠ 0 in H¹(I,F)
    ι_*([c_F]) = 0 in H¹(I,Q)

を証明した。単に異なる二つの cochain を比較したのではなく、
**実際の係数写像に誘導される H¹ 写像** による零性まで閉じた。

これは矛盾ではない。包含 F→Q が単射でも、その H¹ 写像が単射とは限らない。
以前の「Q 係数では coboundary」という説明と、今回の「F 係数では非零」は両立する。
F と Q の係数、および Q の実際の作用を同一視しないことがこの実装の要点である。

## 同じ算術証明書との接続と hno の境界

最終定理 `residual_exists_fixed_coefficient_H1` は、従来の正確な
rootField ζ の ClassModP の ω² 固有空間消滅 `hclass` と同じ Cofixed 候補から、
元の n,T,q,A,τ,y と同じ障害証明書 h を取得する。
同じ x=⟨y,h.killed⟩、同じ値 c(τ)≠0 を用いて、
F 値馴分岐指標の連続性、二つの固定係数の通常の H¹ 類の非零性、
実際の係数写像の像の零性、元の Q 係数の coboundary 類の零性を一緒に出力する。

新たな H¹ 非零性・係数写像・coboundary・連続性を provider として要求しない。
局所の係数写像・元の Q の coboundary 零性は hclass/Cofixed から独立している。
非零性の証明は同じ障害証明書の非自明な値を使用し、算術的な存在定理だけが従来の入力を保持する。

今回の H¹ 類を、大域の円分類群の ω² 固有空間と同一視したわけではない。
局所の通常の H¹ とその係数写像は、今後の算術的な比較のための正確な対象である。
両共鳴分岐の Frey 固有の算術的排除、hclass の供給、連続 H¹ との比較は残る。
**無条件の一般 hno は引き続き未完成。**

## 模範解答・Mathlib との照合

ローカル模範解答の `S_groupCohomology_exists_submodule_mem_iff_conjInvariant.lean` を読み、
通常の H¹ の代表と coboundary 補正で共役条件を扱うことを照合した。
`S_groupCohomology_H2res_comp_H2inf_eq_zero.lean` の解答では、次数2で
`H2π_comp_map_apply` と coboundary の像条件を使っていた。
今回はその次数2の主張を移植せず、Mathlib の次数1の自然性 API を使う。
外部の theorem/provider や P2M/P2MW は import しない。

Mathlib の通常の `GroupCohomology.LowDegree` と `Functoriality`、
連続版 `ContCohomology.LowDegree` の範囲も確認した。
連続版の低次数ファイルが現在扱うのは主に次数0なので、今回の通常の H¹ と混同しない。
参照 HEAD と SHA-256 は `evidence/note032-frey-fixed-h1-reference-audit.json` に保存した。

## 1. 自明作用への準同型と通常の H¹

Mathlib の低次数の同型を使い、同じ代表の値の回収と、その実際の非自明な値による類の非零性を証明する。

ソース: `DkMath/Lib/RepresentationTheory/TrivialCharacterH1.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Group.TypeTags.Hom

#print "file: DkMath.Lib.RepresentationTheory.TrivialCharacterH1"

/-!
# 自明作用の係数への準同型が与える通常の H¹

Mathlib の通常の群コホモロジーを使う。位相や連続 H¹ の比較は主張しない。
-/
namespace DkMath.Lib.RepresentationTheory.TrivialCharacterH1
noncomputable section
variable {Γ V : Type} [Group Γ] [AddCommGroup V] (f : Γ →* Multiplicative V)

/-- 元の同じ加法群を係数とする、自明な整数線形表現。 -/
abbrev coefficient (Γ V : Type) [Group Γ] [AddCommGroup V] : Rep ℤ Γ := Rep.trivial ℤ Γ V

/-- 通常の乗法記法の準同型を、同じ値の加法的準同型へ翻訳する。 -/
def additive : Additive Γ →+ V where
  toFun g := Multiplicative.toAdd (f g.toMul)
  map_zero' := congrArg Multiplicative.toAdd f.map_one
  map_add' g h := congrArg Multiplicative.toAdd (f.map_mul g.toMul h.toMul)

/-- 同じ準同型の通常の 1-cocycle。 -/
def cocycle : groupCohomology.cocycles₁ (coefficient Γ V) :=
  (groupCohomology.cocycles₁IsoOfIsTrivial (coefficient Γ V)).inv (additive f)

/-- 代表 cocycle の値は、元の準同型の同じ値。 -/
theorem cocycle_apply (g : Γ) : cocycle f g = Multiplicative.toAdd (f g) := rfl

/-- 同じ代表から構成した Mathlib の通常の H¹ 類。 -/
def cohomologyClass : groupCohomology.H1 (coefficient Γ V) :=
  groupCohomology.H1π (coefficient Γ V) (cocycle f)

/-- 自明作用の H¹ と準同型の同型を通じて、同じ値を回収できる。 -/
theorem class_evaluate (g : Γ) :
    (groupCohomology.H1IsoOfIsTrivial (coefficient Γ V)).hom (cohomologyClass f)
      (Additive.ofMul g) = Multiplicative.toAdd (f g) :=
  groupCohomology.H1IsoOfIsTrivial_H1π_apply_apply (cocycle f) (Additive.ofMul g)

/-- 実際の非自明な値があれば、自明作用を係数とする通常の H¹ 類は非零。 -/
theorem class_ne_zero (hf : ∃ g, f g ≠ 1) : cohomologyClass f ≠ 0 := by
  intro hc
  obtain ⟨g, hg⟩ := hf
  have he := class_evaluate f g
  rw [hc, map_zero] at he
  exact hg (congrArg Multiplicative.ofAdd he.symm)

end
end DkMath.Lib.RepresentationTheory.TrivialCharacterH1
```

## 2. 同じ固定部分群への連続な馴分岐指標

F=Q^I への値域制限、同じ野生核、同じ J への降下、元の値の保持と連続性を証明する。

ソース: `DkMath/FLT/FreyFixedTameCharacter.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTameResonance

#print "file: DkMath.FLT.FreyFixedTameCharacter"

/-!
# 同じ慣性固定係数への連続な馴分岐差分指標

元の Q の実際の固定部分群 F=Q^I に値を制限し、同じ野生部分群で割る。
係数 F と Q の違いを消さず、同じ値と証人を保持する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ固定部分群値の慣性指標は、元の部分群位相で連続。 -/
theorem ResidualCyclicStage.inertiaFixedDifferenceCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  apply continuous_ofAdd.comp
  apply Continuous.subtype_mk
  exact continuous_toAdd.comp (T.inertiaQuotientDifferenceCharacter_continuous hp5 hq hqp haddr A hA x)

/-- 同じ野生部分群は、値域を実際の固定部分群へ制限しても核に入る。 -/
theorem ResidualCyclicStage.wildInertia_le_fixed_character_kernel
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    wildInertiaSubgroup A ≤ (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x).ker := by
  intro σ hσ
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd
    (T.wildInertia_le_character_kernel hp5 hq hqp haddr A hA x hσ)

/-- 同じ F=Q^I を値域とし、同じ実際の馴分岐商へ降ろした指標。 -/
def ResidualCyclicStage.fixedTameCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    tameInertiaQuotient A →* Multiplicative (T.inertiaFixedUpperQuotient A) :=
  QuotientGroup.lift (wildInertiaSubgroup A)
    (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)
    (T.wildInertia_le_fixed_character_kernel hp5 hq hqp haddr A hA x)

/-- 降下後も、同じ慣性元での同じ固定部分群値を保つ。 -/
theorem ResidualCyclicStage.fixedTameCharacter_mk
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    T.fixedTameCharacter hp5 hq hqp haddr A hA x (QuotientGroup.mk σ) =
      T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ := rfl

/-- 元の F→Q の包含で戻すと、以前と同じ馴分岐指標。 -/
theorem ResidualCyclicStage.fixedTameCharacter_value
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (t : tameInertiaQuotient A) :
    (Multiplicative.toAdd (T.fixedTameCharacter hp5 hq hqp haddr A hA x t)).val =
      Multiplicative.toAdd (T.tameDifferenceCharacter hp5 hq hqp haddr A hA x t) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective t
  rfl

/-- 同じ標準商位相から、同じ離散固定部分群への連続性。 -/
theorem ResidualCyclicStage.fixedTameCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.fixedTameCharacter hp5 hq hqp haddr A hA x) := by
  apply continuous_quot_lift
  exact T.inertiaFixedDifferenceCharacter_continuous hp5 hq hqp haddr A hA x

end
end DkMath.FLT.Frey.Source
```

## 3. 同じ固定係数の通常の H¹ 類の非零性

同じ証人の値から I と J の固定係数の類の非零性を得る。代表の引き戻し値も一致する。

ソース: `DkMath/FLT/FreyFixedInertiaH1.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedTameCharacter
import DkMath.Lib.RepresentationTheory.TrivialCharacterH1

#print "file: DkMath.FLT.FreyFixedInertiaH1"

/-!
# 同じ慣性固定係数の通常の H¹ と非零性

F=Q^I には自明作用を入れる。通常の H¹ と、代表指標の連続性を別々に証明する。
Mathlib の連続群コホモロジーへの比較・同一視は行わない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ固定部分群 F を自明作用の係数とする、馴分岐商の通常の H¹ 類。 -/
def ResidualCyclicStage.fixedTameH1Class
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1 (TrivialCharacterH1.coefficient (tameInertiaQuotient A) (T.inertiaFixedUpperQuotient A)) :=
  TrivialCharacterH1.cohomologyClass (T.fixedTameCharacter hp5 hq hqp haddr A hA x)

/-- 同じ固定部分群値の慣性指標が与える、慣性群の通常の H¹ 類。 -/
def ResidualCyclicStage.fixedInertiaH1Class
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1 (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A)) :=
  TrivialCharacterH1.cohomologyClass (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)

/-- 同じ代表 cocycle は、元の慣性群から馴分岐商へ写した同じ元で一致する。 -/
theorem ResidualCyclicStage.fixedCocycle_inflation_value
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) σ =
      TrivialCharacterH1.cocycle (T.fixedTameCharacter hp5 hq hqp haddr A hA x) (QuotientGroup.mk σ) := rfl

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害値は、固定部分群へ制限しても非自明。 -/
theorem NarrowAbsorptionObstruction.fixed_character_nontrivial
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      ⟨τ, h.inertia⟩ ≠ 1 := by
  dsimp only
  intro he
  have h' := congrArg (fun z : Multiplicative (T.inertiaFixedUpperQuotient A) =>
    Multiplicative.ofAdd (Multiplicative.toAdd z).val) he
  exact (h.inertia_character_nontrivial hp5).1 h'

/-- 同じ証人で、自明作用の固定係数における二つの通常の H¹ 類は非零。 -/
theorem NarrowAbsorptionObstruction.fixed_H1_nonzero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 ∧
      T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 := by
  constructor
  · apply TrivialCharacterH1.class_ne_zero
    exact ⟨QuotientGroup.mk ⟨τ, h.inertia⟩, h.fixed_character_nontrivial hp5⟩
  · apply TrivialCharacterH1.class_ne_zero
    exact ⟨⟨τ, h.inertia⟩, h.fixed_character_nontrivial hp5⟩

end
end DkMath.FLT.Frey.Source
```

## 4. 元の実際の Q への係数写像と零性

元の Q の実際の作用を整数線形表現にし、包含を表現の射として構成する。同じ類の H¹ 写像での零性と、元の同じ算術証明書を接続する。

ソース: `DkMath/FLT/FreyInertiaH1CoefficientBoundary.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedInertiaH1
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

#print "file: DkMath.FLT.FreyInertiaH1CoefficientBoundary"

/-!
# 固定係数での非零性と元の実際の商加群での零性

F=Q^I の自明作用と、元の Q の実際の慣性作用を区別する。
同じ代表の F→Q による像は、同じ商元 [x] の作用差という coboundary になる。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の同じ商 Q の実際の慣性作用を、整数線形表現として読む。 -/
def ResidualCyclicStage.fullInertiaCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep ℤ (inertiaSubgroupIn A ℚ) := Rep.of
  { toFun := fun σ => (T.upperQuotientAction σ.val).toIntLinearMap
    map_one' := by
      apply LinearMap.ext
      intro z
      change T.upperQuotientAction 1 z = z
      rw [map_one]
      rfl
    map_mul' := by
      intro σ τ
      apply LinearMap.ext
      intro z
      exact congrArg (fun f : AddMonoid.End T.upperQuotient => f z)
        (T.upperQuotientAction.map_mul (σ.val : Field.absoluteGaloisGroup ℚ) τ.val) }

/-- 同じ商元 [x] の実際の作用差を代表とする通常の cocycle。 -/
def ResidualCyclicStage.fullInertiaCocycle (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.cocycles₁ (T.fullInertiaCoefficient A) :=
  ⟨groupCohomology.d₀₁ (T.fullInertiaCoefficient A) ((QuotientAddGroup.mk' T.upperStage) x),
    groupCohomology.d₀₁_apply_mem_cocycles₁ _⟩

/-- 元の実際の Q 係数では、この同じ差分の通常の H¹ 類は零。 -/
theorem ResidualCyclicStage.fullInertiaClass_zero (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π (T.fullInertiaCoefficient A) (T.fullInertiaCocycle A x) = 0 := by
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  exact ⟨(QuotientAddGroup.mk' T.upperStage) x, rfl⟩

/-- 自明作用の実際の固定係数 F から、元の実際の Q への表現の射。 -/
def ResidualCyclicStage.fixedCoefficientInclusion (A : ValuationSubring (AlgebraicClosure ℚ)) :
    TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A) ⟶
      T.fullInertiaCoefficient A :=
  Rep.ofHom
    { toLinearMap := (T.inertiaFixedUpperQuotient A).subtype.toIntLinearMap
      isIntertwining' := by
        intro σ
        apply LinearMap.ext
        intro z
        change z.val = T.upperQuotientAction σ.val z.val
        exact (z.property σ.val σ.property).symm }

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 固定係数 cocycle の同じ値を F→Q で写すと、同じ実際の coboundary。 -/
theorem ResidualCyclicStage.fixedCocycle_include_value
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    (TrivialCharacterH1.cocycle
      (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) σ).val =
      T.fullInertiaCocycle A x σ := by
  change Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) =
    T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x
  exact T.inertiaQuotientDifferenceCharacter_coboundary hp5 hq hqp haddr A hA x σ

/-- 係数包含が通常の H¹ に誘導する実際の写像は、同じ固定係数類を零へ送る。 -/
theorem ResidualCyclicStage.fixedInertiaClass_map_zero
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
      (T.fixedInertiaH1Class hp5 hq hqp haddr A hA x) = 0 := by
  rw [fixedInertiaH1Class, TrivialCharacterH1.cohomologyClass,
    groupCohomology.H1π_comp_map_apply]
  have he : groupCohomology.mapCocycles₁ (MonoidHom.id (inertiaSubgroupIn A ℚ))
      (T.fixedCoefficientInclusion A)
      (TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)) =
      T.fullInertiaCocycle A x := by
    apply groupCohomology.cocycles₁_ext
    intro σ
    change (TrivialCharacterH1.cocycle
      (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) σ).val = _
    exact T.fixedCocycle_include_value hp5 hq hqp haddr A hA x σ
  rw [he]
  exact T.fullInertiaClass_zero A x

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
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
/-- 同じ hclass と Cofixed 候補から、固定係数の非零 H¹ 類と元の係数への写像での零性を得る。 -/
theorem residual_exists_fixed_coefficient_H1
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      Continuous (T.fixedTameCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) ∧
      T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 ∧
      T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ≠ 0 ∧
      groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
        (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = 0 ∧
      groupCohomology.H1π (T.fullInertiaCoefficient A) (T.fullInertiaCocycle A x) = 0 := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h,
    T.fixedTameCharacter_continuous hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    (h.fixed_H1_nonzero hp5).1, (h.fixed_H1_nonzero hp5).2,
    T.fixedInertiaClass_map_zero hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    T.fullInertiaClass_zero A ⟨y, h.killed⟩⟩

end
end DkMath.FLT.Frey.Source
```

## 検証

新規25宣言の checked type・constructor・opaque proof value を再帰走査する依存監査と、
16件の公開入力監査を通常テスト入口へ追加した。
ZMod5 の同じ恒等指標で通常の H¹ の非零性・同じ値の回収を検査し、自明指標の類は零と確認する。
同じ剪断表現の実際の作用差は値(t,0)であり、元の二次元係数では coboundary として類が零になる例も検査する。
結果は `evidence/validation-note032-frey-fixed-h1.txt` を参照。
