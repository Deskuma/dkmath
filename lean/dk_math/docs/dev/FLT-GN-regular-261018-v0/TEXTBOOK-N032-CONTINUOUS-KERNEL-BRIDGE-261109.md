# NOTE-032 教科書 — ω² 類群対象・連続係数核比較・鋭い障害指数

日付: 2026-11-09。最新レビューと模範解答を照合し、7モジュールを実装した。
今回は、実際の K の指標を連続準同型として保持し、同じ cocycle の通常 H¹ 類、連結像、inflation を回収する。
また、完成した同じ生成元の単一評価を使い、狭い障害の指数に半分の上界と低段の分類を加えた。
**hclass の算術的消滅・一般 hno の無条件閉鎖は未完成。**

全7 Lean ブロックは対応する production ソースの全文と一致する。
各 import 群直後の必須 `#print "file: 正確なモジュール名"` を保持する。
DkMath の Lake 環境で、各ブロックを別ファイルにコピーして検査できる。
最初の2モジュールは FLT 非依存の Lib、残り5つは同じ実際の Frey Source を扱う FLT 層である。

## 1. hclass の正確な対象と Bernoulli 数の確認

`weightTwoComponent` は、現在の実際の `ClassModP (rootField ζ) p` の中で

    ∀γ, classModPAction p γ a = (baseCharacter hζ γ)^2 • a

を満たす元の整数線形部分加群である。
元の類群作用を使い、別の抽象模型や類群全体の正則性に置き換えていない。
`weightTwo_eq_bot_iff` によって、この部分加群=0 が現在の hclass と同じ条件であることを証明した。
**この同値条件は、部分加群が実際に零であるという証明ではない。**

さらに Mathlib の B₂=1/6 を使用し、実際の有理数の分子 `(bernoulli 2).num=1` と
p≥5 のときその分子を p が割らないことを証明した。
Bernoulli の数値計算から類群消滅への輸送はまだ実装していない。

文献では Sharifi の [Modular curves and cyclotomic fields, §2.2](https://www.math.ucla.edu/~sharifi/aws-iwasawa.pdf)
が、偶数 k に対する反射不等式と Herbrand–Ribet の消滅条件を記述している。
k=2 は今回の対象の候補となる。必要な算術定理と、文献の p-primary 類群成分から
現在の ClassModP・作用への同定は別途形式化する必要がある。
調査した現行の CyclotomicClassVanishing は、この消滅を明示入力として保持している。
Herbrand/Leopoldt の結論を新しい axiom、provider、既知 FLT の別名として追加していない。

## 2. 自明係数の連続指標から同じ通常 H¹ へ

`ContinuousTrivialCharacterH1` は Γ→Multiplicative V の連続準同型 f を扱う。
通常 H¹ で既に使用している `TrivialCharacterH1.cocycle f` と同じ cocycle を選び、
その値が f の値の加法記法であることから連続性を証明する。
`forgetClass` はその同じ cocycle を Mathlib の通常 H¹ へ写す。
自明作用の H¹ 同型で値を回収できるので、この忘却は連続指標の集合上で単射。
非自明な指標値があれば通常 H¹ 像は非零になる。

これは、一般の連続群コホモロジー全体を構成したという主張ではない。
今回必要な「連続な自明係数指標と、その同じ通常 H¹ 代表」の比較に限定する。

## 3. 実際の全係数核 K を連続指標に埋め込む

K の各元の指標が連続であることは既存の `fixedKernelCharacter_continuous` が証明済み。
これを追加仮定にせず、`ContinuousMonoidHom I (Multiplicative F)` の元として保持する。
値は元の ev_σ(k) と同じであり、前回完成した同じ具体的 γ の単一評価により、

    K → continuous characters(I,F)

が単射になる。
自明作用の通常 H¹ 同型を使い、この連続指標を忘却すると元の同じ k.val になることも証明した。
連続性のある別の類の存在ではなく、**同じ元の同じ通常 H¹ 類**を回収する。

## 4. 同じ有限捩れ点の連結 cocycle と δ₀

元の有限捩れ点 x に対応する `fixedCosetKernelElement x` の連続指標を取る。
得られる cocycle は、既存の `inertiaFixedDifferenceCharacter x` の cocycle と等しい。
したがって、その通常 H¹ 像は以前から使用している同じ短完全列の連結像 δ₀ と一致する。
代表の連続性、cocycle 自体の等式、類と連結像の等式をそれぞれ独立した定理として保持した。
新しい連続 H¹ 比較同型を仮定していない。

## 5. 同じ tame 商の連続指標と inflation

既存の `fixedKernelTameCharacter_continuous` から、元の商位相の I/W 上の連続指標を構成する。
商への元 σ の像での値は、I 上の連続指標の値と同じである。
その等式を cocycle の値でも保持し、連続代表を通常 H¹ に忘却してから
既存の実際の inflation を適用すると、元の同じ k.val を回収する。
K から連続 tame 指標への写像も単射である。

ここでは W と標準的な野生慣性との追加同定や、大域の非分岐条件への輸送は結論していない。

## 6. 障害の指数を半分まで制限する

同じ狭い障害 h があると、既存の証明により |F|=p^r、|K|=p^s、r,s≥1、r+s=n+3。
完成した同じ具体的生成元の評価の単射性から |K|∣|F| が得られるので、

    s≤r, 2s≤n+3, s≤(n+3)/2, n+3≤2r

を新しい hcyclic/hgen なしに導く。
n=0 なら r=2,s=1 に一意に決まり、|F|=p²、|K|=p。
n=1 なら (r,s) は (3,1) または (2,2) のどちらかとなる。
これらの数値条件自体は整合的であり、障害の非存在や hno の矛盾にはしていない。

## 7. 同じ非零障害核元の連続検出証明書

元の障害の有限捩れ点から作る同じ k を取り、その通常 H¹ 類の非零性から k≠0 を得る。
同じ具体的 γ の評価が単射なので、この連続指標は γ で非自明な値を持つ。
同じ k について、連続代表の忘却が k.val であり、連続 tame 代表の通常 inflation も k.val となる。
さらに、同じ連続指標の通常 H¹ 像が非零であることを結論する。

`continuous_kernel_detected` は、新しい hclass/hcofixed/hgen/hcyclic/hcontinuous を要求しない。
実際の元の障害証人と p≥5 は保持する。この局所指標の非零性を大域矛盾と混同しない。

## 模範解答との照合と残る工程

模範の `groupCohomology_nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom` を読み、
自明作用では同じ cocycle の H¹ 像が代表を決める部分と、別途の大域・レベル条件を切り分けた。
今回の実装は、既存 DkMath の通常 H¹ と実際の連続指標だけを接続する狭い経路である。
模範の continuousH1Sr、レベル条件、大域非分岐性や Selmer 比較を移植したとは主張しない。
参照コミット・ソース・レビュー SHA-256 と文献 URL は reference audit に記録する。

完了: ω² の正確な対象と B₂ の分子計算、実際の K の連続指標埋め込み、同じ cocycle の連結像・inflation 比較、
同じ γ での連続障害検出、指数の半分上界と n=0/1 分類。
未完了: Herbrand・反射定理と実際の ClassModP への算術的輸送、hclass の供給、
大域 Selmer/非分岐条件、共鳴障害排除、大域矛盾、一般 hno の無条件閉鎖。

28新規宣言の再帰依存・標準公理監査と、実際の Frey 公開入口18件の入力監査を追加した。
有限整合模型の加法性・単射性は、指数制約だけを矛盾と扱わないための境界検査である。
検証: `evidence/validation-note032-continuous-kernel-bridge.txt`。

## 教科書 Lean コード全文

### 1. DkMath.Lib.NumberTheory.CyclotomicWeightTwoTarget

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicClassVanishing
import Mathlib.NumberTheory.Bernoulli

#print "file: DkMath.Lib.NumberTheory.CyclotomicWeightTwoTarget"

/-! # 実際の ω² 類群成分と B₂ の算術的準備
Herbrand・反射定理や類群消滅を仮定も結論もしない。現在の hclass の正確な対象を固定する。 -/
namespace DkMath.Lib.NumberTheory.CyclotomicClassVanishing
open CyclotomicRootModule CyclotomicKernelField CyclotomicKummerWeight
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 元の ClassModP と元の classModPAction を使う整数線形 ω² 固有部分空間。 -/
def weightTwoComponent : Submodule ℤ (ClassModP (rootField ζ) p) where
  carrier := {a | ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
    classModPAction p γ a = (baseCharacter hζ γ : ZMod p) ^ 2 • a}
  zero_mem' := by intro γ; simp
  add_mem' := by intro a b ha hb γ; rw [map_add, ha γ, hb γ, smul_add]
  smul_mem' := by intro n a ha γ; rw [map_smul, ha γ, smul_comm]

/-- 現行 hclass は、同じ固有部分空間が零であることそのもの。消滅の証明ではない。 -/
theorem weightTwo_eq_bot_iff : weightTwoComponent hζ = ⊥ ↔
    ∀ a : ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        classModPAction p γ a = (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0 := by
  constructor
  · intro he a ha
    have hm : a ∈ weightTwoComponent hζ := ha
    rw [he, Submodule.mem_bot] at hm
    exact hm
  · intro hv
    apply le_antisymm _ bot_le
    intro a ha
    exact hv a ha

/-- Herbrand の k=2 に現れる実際の Bernoulli 数。 -/
theorem bernoulli_two_numerator : (bernoulli 2).num = 1 := by
  rw [bernoulli_two]
  norm_num

omit [Fact p.Prime] in
/-- p≥5 なら B₂ の分子を p は割らない。類群への輸送は別途必要。 -/
theorem prime_not_dvd_bernoulli_two_numerator (hp5 : 5 ≤ p) : ¬ (p : ℤ) ∣ (bernoulli 2).num := by
  rw [bernoulli_two_numerator]
  intro hd
  have habs : (p : ℕ) ∣ 1 := by exact_mod_cast hd
  have := Nat.le_of_dvd (by decide : 0 < 1) habs
  omega
end
end DkMath.Lib.NumberTheory.CyclotomicClassVanishing

```

### 2. DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.TrivialCharacterH1
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions

#print "file: DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1"

/-! # 自明係数の連続指標と同じ通常 H¹ 類
連続指標を保持し、通常 H¹ への忘却が同じ cocycle と値を保つことを証明する。
一般の連続群コホモロジー全体や大域 Selmer 比較を定義したとは主張しない。 -/
namespace DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1
noncomputable section
variable {Γ V : Type} [Group Γ] [AddCommGroup V] [TopologicalSpace Γ] [TopologicalSpace V]

/-- 通常 H¹ に使う cocycle と同じ代表。連続性を別の定理で保持する。 -/
def cocycle (f : ContinuousMonoidHom Γ (Multiplicative V)) :=
  TrivialCharacterH1.cocycle f.toMonoidHom

/-- 同じ cocycle は元の位相に関して連続。 -/
theorem cocycle_continuous (f : ContinuousMonoidHom Γ (Multiplicative V)) :
    Continuous (fun g : Γ => cocycle f g) :=
  continuous_toAdd.comp f.continuous

/-- 連続指標の同じ代表を通常 H¹ へ忘却する。 -/
def forgetClass (f : ContinuousMonoidHom Γ (Multiplicative V)) :=
  TrivialCharacterH1.cohomologyClass f.toMonoidHom

/-- 忘却後も元の指標と同じ値を回収する。 -/
theorem forgetClass_evaluate (f : ContinuousMonoidHom Γ (Multiplicative V)) (g : Γ) :
    (groupCohomology.H1IsoOfIsTrivial (TrivialCharacterH1.coefficient Γ V)).hom (forgetClass f)
      (Additive.ofMul g) = Multiplicative.toAdd (f g) :=
  TrivialCharacterH1.class_evaluate f.toMonoidHom g

/-- 自明作用では、連続指標から通常 H¹ への忘却は単射。 -/
theorem forgetClass_injective : Function.Injective (forgetClass (Γ := Γ) (V := V)) := by
  intro f g he
  apply ContinuousMonoidHom.ext
  intro σ
  apply Multiplicative.toAdd.injective
  rw [← forgetClass_evaluate f σ, ← forgetClass_evaluate g σ, he]

/-- 連続性を保持したまま、非自明な値が通常 H¹ の非零性を検出する。 -/
theorem forgetClass_ne_zero (f : ContinuousMonoidHom Γ (Multiplicative V))
    (hf : ∃ g, f g ≠ 1) : forgetClass f ≠ 0 :=
  TrivialCharacterH1.class_ne_zero f.toMonoidHom hf
end
end DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1

```

### 3. DkMath.FLT.FreyContinuousKernelCharacters

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameCyclicClosure
import DkMath.Lib.RepresentationTheory.ContinuousTrivialCharacterH1

#print "file: DkMath.FLT.FreyContinuousKernelCharacters"

/-! # 実際の全係数核を連続指標へ埋め込む
既存の連続性と同じ具体的な γ の単一評価を使用する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の k の指標を、元の位相で連続な準同型として保持する。 -/
def ResidualCyclicStage.continuousKernelCharacter (k : T.fixedH1CoefficientKernel A) :
    ContinuousMonoidHom (inertiaSubgroupIn A ℚ) (Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  { T.fixedKernelCharacter A k with
    continuous_toFun := T.fixedKernelCharacter_continuous A hp5 hq hqp haddr hA k }

/-- 同じ連続指標の値は、元の評価値そのもの。 -/
theorem ResidualCyclicStage.continuousKernelCharacter_apply (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.continuousKernelCharacter A hp5 hq hqp haddr hA k σ) =
      T.fixedKernelEvaluation A σ k := rfl

/-- 同じ γ の評価で連続指標の埋め込みの単射性を得る。 -/
theorem ResidualCyclicStage.continuousKernelCharacter_injective :
    Function.Injective (T.continuousKernelCharacter A hp5 hq hqp haddr hA) := by
  intro x y he
  apply T.generator_evaluation_injective A hp5 hq hqp haddr hA
  exact congrArg (fun f => Multiplicative.toAdd (f
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA))) he

/-- 同じ連続指標を通常 H¹ に忘却すると、元の核元の類を厳密に回収する。 -/
theorem ResidualCyclicStage.continuousKernelCharacter_forget (k : T.fixedH1CoefficientKernel A) :
    ContinuousTrivialCharacterH1.forgetClass
      (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) = k.val := by
  apply (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A)))).injective
  apply AddMonoidHom.ext
  intro σ
  exact ContinuousTrivialCharacterH1.forgetClass_evaluate
    (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) σ.toMul
end
end DkMath.FLT.Frey.Source

```

### 4. DkMath.FLT.FreyContinuousConnectingComparison

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousKernelCharacters

#print "file: DkMath.FLT.FreyContinuousConnectingComparison"

/-! # 同じ有限捩れ連結 cocycle の連続性と通常 H¹ の比較
新しい H¹ 理論への同型を仮定せず、実際に使う cocycle と連結像を同定する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の有限捩れ点から作る、同じ連続な連結 cocycle。 -/
def ResidualCyclicStage.continuousConnectingCocycle
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  ContinuousTrivialCharacterH1.cocycle (T.continuousKernelCharacter A hp5 hq hqp haddr hA
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x))

/-- 実際の連結 cocycle の連続性を内部供給する。 -/
theorem ResidualCyclicStage.continuousConnectingCocycle_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (fun σ : inertiaSubgroupIn A ℚ =>
      T.continuousConnectingCocycle A hp5 hq hqp haddr hA x σ) :=
  ContinuousTrivialCharacterH1.cocycle_continuous _

/-- 連続代表は、通常 H¹ で以前から使用している差分 cocycle と一致する。 -/
theorem ResidualCyclicStage.continuousConnectingCocycle_eq
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.continuousConnectingCocycle A hp5 hq hqp haddr hA x =
      TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  change TrivialCharacterH1.cocycle (T.fixedKernelCharacter A
    (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x)) = _
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]

/-- 同じ連続 cocycle の通常 H¹ 像は、同じ短完全列の連結像 δ₀ と一致する。 -/
theorem ResidualCyclicStage.continuousConnectingClass_eq_delta
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x) =
      T.fixedConnecting A (T.fixedCosetH0 hp5 hq hqp haddr A hA x) := by
  rw [T.continuousConnectingCocycle_eq A hp5 hq hqp haddr hA x]
  exact (T.fixedCoset_connecting hp5 hq hqp haddr A hA x).symm
end
end DkMath.FLT.Frey.Source

```

### 5. DkMath.FLT.FreyContinuousTameInflation

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousConnectingComparison

#print "file: DkMath.FLT.FreyContinuousTameInflation"

/-! # 元の連続 tame 指標と同じ通常 H¹ inflation
K の全ての元について連続代表を保持し、元の同じ I→I/W に沿う値と類を回収する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ商位相を持つ tame 指標を連続準同型として保持する。 -/
def ResidualCyclicStage.continuousKernelTameCharacter (k : T.fixedH1CoefficientKernel A) :
    ContinuousMonoidHom (tameInertiaQuotient A) (Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  { T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k with
    continuous_toFun := T.fixedKernelTameCharacter_continuous A hp5 hq hqp haddr hA k }

/-- 同じ I→I/W に沿う連続代表の値の一致。 -/
theorem ResidualCyclicStage.continuousKernelTameCharacter_mk (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    T.continuousKernelTameCharacter A hp5 hq hqp haddr hA k (QuotientGroup.mk σ) =
      T.continuousKernelCharacter A hp5 hq hqp haddr hA k σ := rfl

/-- 連続 cocycle 自体の inflation における値も一致する。 -/
theorem ResidualCyclicStage.continuousKernelTameCocycle_mk (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    ContinuousTrivialCharacterH1.cocycle (T.continuousKernelTameCharacter A hp5 hq hqp haddr hA k)
      (QuotientGroup.mk σ) =
    ContinuousTrivialCharacterH1.cocycle (T.continuousKernelCharacter A hp5 hq hqp haddr hA k) σ := rfl

/-- 連続代表を忘却してから、同じ通常 H¹ inflation を取ると元の k を回収する。 -/
theorem ResidualCyclicStage.continuousKernelTameClass_inflation (k : T.fixedH1CoefficientKernel A) :
    T.fixedH1Inflation A (ContinuousTrivialCharacterH1.forgetClass
      (T.continuousKernelTameCharacter A hp5 hq hqp haddr hA k)) = k.val :=
  T.fixedKernelTameClass_inflation A hp5 hq hqp haddr hA k

/-- 連続 tame 指標への写像も同じ係数核全体で単射。 -/
theorem ResidualCyclicStage.continuousKernelTameCharacter_injective :
    Function.Injective (T.continuousKernelTameCharacter A hp5 hq hqp haddr hA) := by
  intro x y he
  apply T.continuousKernelCharacter_injective A hp5 hq hqp haddr hA
  apply ContinuousMonoidHom.ext
  intro σ
  exact congrArg (fun f => f (QuotientGroup.mk σ)) he
end
end DkMath.FLT.Frey.Source

```

### 6. DkMath.FLT.FreyCyclicKernelBalancedProfile

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameCyclicClosure

#print "file: DkMath.FLT.FreyCyclicKernelBalancedProfile"

/-! # 実装済み単一評価による障害の指数制約
巡回性を追加仮定とせず、同じ元の F と K の指数を制限する。矛盾は結論しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ具体的な生成元の単一評価から s≤r と半分の上界を内部供給する。 -/
theorem NarrowAbsorptionObstruction.cyclic_balanced_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r s, 1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧ s ≤ r ∧
      2 * s ≤ n + 3 ∧ s ≤ (n + 3) / 2 ∧ n + 3 ≤ 2 * r ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨r, s, hr, hs, hsum, hF, hK⟩ := h.fixed_kernel_balanced_profile hp5
  have hd := T.kernel_card_dvd_fixed_of_radical_generator A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over
  rw [hF, hK] at hd
  have hsr := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨r, s, hr, hs, hsum, hsr, by omega, by omega, by omega, hF, hK⟩

/-- n=0 段の実際の障害なら、同じ F と K の濃度は一意に決まる。 -/
theorem NarrowAbsorptionObstruction.stage_zero_card_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hn : n = 0) :
    Nat.card (T.inertiaFixedUpperQuotient A) = p ^ 2 ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p := by
  obtain ⟨r, s, hr, hs, hsum, hsr, _, _, _, hF, hK⟩ := h.cyclic_balanced_profile hp5
  have hr2 : r = 2 := by omega
  have hs1 : s = 1 := by omega
  simpa only [hr2, hs1, pow_one] using And.intro hF hK

/-- n=1 段では指数対が (3,1) または (2,2) に限定される。 -/
theorem NarrowAbsorptionObstruction.stage_one_card_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hn : n = 1) :
    (Nat.card (T.inertiaFixedUpperQuotient A) = p ^ 3 ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p) ∨
    (Nat.card (T.inertiaFixedUpperQuotient A) = p ^ 2 ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ 2) := by
  obtain ⟨r, s, hr, hs, hsum, hsr, _, _, _, hF, hK⟩ := h.cyclic_balanced_profile hp5
  have hc : (r = 3 ∧ s = 1) ∨ (r = 2 ∧ s = 2) := by omega
  rcases hc with ⟨hr3, hs1⟩ | ⟨hr2, hs2⟩
  · exact Or.inl (by simpa only [hr3, hs1, pow_one] using And.intro hF hK)
  · exact Or.inr (by simpa only [hr2, hs2] using And.intro hF hK)
end
end DkMath.FLT.Frey.Source

```

### 7. DkMath.FLT.FreyContinuousObstructionCertificate

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousTameInflation
import DkMath.FLT.FreyCyclicKernelBalancedProfile

#print "file: DkMath.FLT.FreyContinuousObstructionCertificate"

/-! # 同じ障害核元の連続代表・非零単一評価・通常 H¹ 比較の証明書
連続 H¹ 全体や大域 Selmer 条件を追加の provider として導入しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ非零係数核元を、連続指標と具体的 γ で検出する。 -/
theorem NarrowAbsorptionObstruction.continuous_kernel_detected
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ k : T.fixedH1CoefficientKernel A, k ≠ 0 ∧
      T.continuousKernelCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k
        (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) ≠ 1 ∧
      ContinuousTrivialCharacterH1.forgetClass
        (T.continuousKernelCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k) = k.val ∧
      T.fixedH1Inflation A (ContinuousTrivialCharacterH1.forgetClass
        (T.continuousKernelTameCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k)) = k.val := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
  have hk : k ≠ 0 := by
    intro hz
    have hv := congrArg Subtype.val hz
    have hc := (h.fixed_H1_nonzero hp5).2
    apply hc
    exact (T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).symm.trans hv
  refine ⟨k, hk, ?_, T.continuousKernelCharacter_forget A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over k, T.continuousKernelTameClass_inflation A hp5 h.prime
    h.ne_torsion_prime (Or.inr h.support) h.lies_over k⟩
  intro he
  have hv := congrArg Multiplicative.toAdd he
  change T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k = 0 at hv
  apply hk
  apply T.generator_evaluation_injective A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
  simpa only [map_zero] using hv

/-- 同じ連続障害の通常 H¹ 像も非零で、同じ γ の値で検出される。 -/
theorem NarrowAbsorptionObstruction.continuous_class_nonzero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ k : T.fixedH1CoefficientKernel A,
      ContinuousTrivialCharacterH1.forgetClass
        (T.continuousKernelCharacter A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k) ≠ 0 := by
  obtain ⟨k, _, hdet, _, _⟩ := h.continuous_kernel_detected hp5
  exact ⟨k, ContinuousTrivialCharacterH1.forgetClass_ne_zero _ ⟨_, hdet⟩⟩
end
end DkMath.FLT.Frey.Source

```

