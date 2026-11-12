# NOTE-032 教科書 — 同じ大域 Q coboundary の制限と局所 F 障害の係数境界

日付: 2026-11-09。最新レビューを読み、模範の局所制限における代表回収を照合して7モジュールを実装した。
今回は「局所障害の大域起源」のうち、実際に証明できる係数付きの図式を形式化した。

    同じ局所 F cocycle ──F→Q──> 慣性 Q cocycle
                                      ↑ 大域からの制限
                                同じ大域 Q coboundary

右上への二経路が同じ cocycle・同じ通常 H¹ 類になることを証明する。
**F 値の大域 Selmer 類は構成していない。hclass と無条件一般 hno は未完成。**

以下の7 Lean ブロックは production の全文と一致する。
全ての import 群直後に、必須 `#print "file: 正確なモジュール名"` を保持する。
既存 DkMath の Lake 環境で、各ブロックを別ファイルにコピーして検査できる。
第1段階は FLT 非依存の Lib、残り6段階は元の同じ Frey Source・段・商・点を保持する FLT 層。

## 記号と今回の算術的境界

G=Gal(ℚ̄/ℚ)、A は元の付値環、D はその実際の分解群、I は同じ実際の慣性群。
T は元の G 安定な巡回段で、Q は一段上の元の有限捩れ群を T で割った商。
F=Q^I は元の慣性固定係数群である。

Q は全 G の表現である。一方、F はまず I 固定部分群であり、全 G の安定性は供給されていない。
今回、I が D 内で正規であることから F の **D 安定性** を内部証明する。
F を全 G の係数へ黙って置き換えない。この違いが大域類への輸送に残る数学的条件である。

## 1. 実際の分解群による慣性の正規化

慣性を分解群の剰余作用の核として定義した既存の対象を使う。
その核の正規性を、分解群包含で全自己同型群へ写した実際の慣性群へ輸送し、

    σ∈D, τ∈I ⇒ στσ⁻¹∈I, σ⁻¹τσ∈I

を証明した。I の元が D に属することも公開する。
全 G 内の正規性は仮定も結論もしない。

## 2. 同じ有限商 Q の大域表現と連続 coboundary

既存の `upperQuotientAction` は、同じ T の安定性から得られた全 G の実際の作用。
これを `Rep ℤ G` として読み、同じ Q の商位相をその台集合に保持した。
元の有限捩れ点 x の商類 z=[x] に対し

    b_x(g)=g·z-z

を同じ通常の cocycle として構成する。
既存の元の商作用の連続性から b_x の連続性を内部証明した。
この Q 係数での大域類は coboundary なので零である。
これは、局所 F 係数での類の零性ではない。

## 3. 同じ大域 Q 表現から元の慣性 Q 表現への制限

群包含 I→G と、制限表現から元の `fullInertiaCoefficient A` への恒等係数射を明示した。
これらによる通常 H¹ 制限写像を構成し、同じ大域代表が以前の同じ `fullInertiaCocycle` に写ることを証明する。
通常 H¹ の自然性によって、類の制限も同じ代表の類を回収する。

既存の連続 F 値 cocycle c_x を F→Q で含めた値は、同じ大域 b_x の慣性制限と一致する。
位相を変えたり、別の類の存在だけに置き換えたりしていない。

## 4. 元の F の分解群安定性と実際の D 表現

z∈F、σ∈D、τ∈I とする。σ⁻¹τσ∈I なので

    τ·(σ·z)=σ·((σ⁻¹τσ)·z)=σ·z

となり、σ·z∈F が従う。
この内部証明によって元の F 上の実際の分解群作用を構成し、整数線形表現として読む。
逆元の作用と合成すれば恒等作用になるため、各 σ の F 上の作用は単射である。
新しい F 安定性 provider は要求しない。

## 5. 点の輸送と共役に関する cocycle の共変性

σ による同じ有限捩れ点の像を σx とすると、元の商類は σ·[x]。
同じ大域作用差について

    b_(σx)(τ)=σ·b_x(σ⁻¹τσ)

を証明した。
σ∈D、τ∈I へ限定すれば、右側の入力は元の I に属し、作用先も元の F に残る。
第3・第4段階を使って同じ連続 F cocycle に輸送すると

    c_(σx)(τ)=σ_F·c_x(σ⁻¹τσ)

となる。F への係数包含の単射性によって、値そのものの等式まで証明している。

## 6. 同じ cocycle・同じ通常 H¹ 類による制限図式

`continuousCocycle_global_origin` は、群と係数の両方を明示した等式

    mapCocycles(F→Q)(c_x)=res_I(b_x)

を与える。さらに H¹ の自然性で

    map_H1(F→Q)([c_x])=res_H1([b_x])

を証明した。
これは「同じ局所障害が、係数を含めると同じ大域 Q coboundary の制限になる」という限定された大域起源である。
F 値の大域類や、その Selmer・非分岐条件の証明ではない。

## 7. 局所 F 非零・大域 Q 零の境界と分解群輸送

元の狭い障害証人 h の同じ点 x について、

    [c_x]≠0 in H¹(I,F),   [b_x]=0 in H¹(G,Q)

を同時に証明する。
さらに任意の σ∈D に対し η=στσ⁻¹∈I を取り、共変性と σ_F の単射性を使うと、
元の τ での非零値が輸送後の η でも非零に残る。
従って σx についても局所 F 類は非零、大域 Q 類は零である。
輸送後の点が新たな NarrowAbsorptionObstruction の全ての算術条件を満たすとは主張しない。
今回輸送したのは同じ係数を持つ連続 cocycle の非零性である。

この二つの零性は矛盾しない。異なる係数での類だからである。
F→Q の局所 H¹ 写像の単射性も仮定していない。
次に必要なのは、F 値の大域的な係数・類・局所制限と算術的条件を独立に供給することである。

## 模範解答と残る証明境界

模範の `groupCohomology_locRes_extArithLoc_apply_mem_continuousH1` を読み、
大域の同じ代表 cocycle を局所制限して連続性を回収する部分と、係数表現・Selmer 条件を切り分けた。
今回の DkMath 実装では、実在する Q 値の大域代表と元の F 値局所 cocycle の図式を証明した。
模範の大域 continuousH1S・Selmer 条件・F 値の大域類を新しい provider として仮定していない。

完了: D 内の慣性正規化、実際の全 G の Q 表現と連続大域 coboundary、元の慣性への制限、
F の D 表現、同じ cocycle の共役共変性、代表と H¹ 類の可換図式、分解群輸送後も残る局所非零性。
未完了: ω² 類群消滅の Herbrand/反射による算術的供給、F 値大域類の構成と Selmer/非分岐条件、
共鳴障害の排除、大域矛盾と一般 hno の無条件閉鎖。

新規27宣言（係数の位相を保持する instance を含む）の再帰依存・標準公理監査と、公開入力27件の監査を追加した。
境界検査には、ZMod25 上の位数5の作用で非零不変値が coboundary として生じる有限模型と、
正規化条件なしには共役で部分群が保存されない有限群の例を使う。
検証: `evidence/validation-note032-relative-global-origin.txt`。
模範ソース・コミット・レビュー SHA-256: `evidence/note032-relative-global-origin-reference-audit.json`。

## 教科書 Lean コード全文

### 1. DkMath.Lib.NumberTheory.ValuationInertiaNormalizer

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.InertiaKrullClosed

#print "file: DkMath.Lib.NumberTheory.ValuationInertiaNormalizer"

/-! # 元の分解群は元の慣性群を正規化する
全 Galois 群に対する正規性を主張せず、同じ付値環の分解群に限定する。 -/
namespace DkMath.Lib.NumberTheory.ValuationInertia
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- 実際の慣性群の元は同じ付値環の分解群に属する。 -/
theorem mem_decomposition_of_mem_inertia (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ inertiaSubgroupIn A K) : σ ∈ A.decompositionSubgroup K := by
  obtain ⟨s, _, rfl⟩ := hσ
  exact s.property

/-- 慣性の剰余作用の核としての正規性を、全自己同型群内の像へ輸送する。 -/
theorem decomposition_conj_mem_inertia (A : ValuationSubring L) (σ τ : L ≃ₐ[K] L)
    (hσ : σ ∈ A.decompositionSubgroup K) (hτ : τ ∈ inertiaSubgroupIn A K) :
    σ * τ * σ⁻¹ ∈ inertiaSubgroupIn A K := by
  obtain ⟨t, ht, he⟩ := hτ
  have hN : (A.inertiaSubgroup K).Normal := by
    delta ValuationSubring.inertiaSubgroup
    exact MonoidHom.normal_ker _
  let s : A.decompositionSubgroup K := ⟨σ, hσ⟩
  refine ⟨s * t * s⁻¹, hN.conj_mem t ht s, ?_⟩
  rw [map_mul, map_mul, map_inv, he]
  rfl

/-- 逆向きの共役も同じ慣性群に属する。 -/
theorem decomposition_inv_conj_mem_inertia (A : ValuationSubring L) (σ τ : L ≃ₐ[K] L)
    (hσ : σ ∈ A.decompositionSubgroup K) (hτ : τ ∈ inertiaSubgroupIn A K) :
    σ⁻¹ * τ * σ ∈ inertiaSubgroupIn A K := by
  simpa only [inv_inv] using decomposition_conj_mem_inertia A σ⁻¹ τ
    ((A.decompositionSubgroup K).inv_mem hσ) hτ
end DkMath.Lib.NumberTheory.ValuationInertia

```

### 2. DkMath.FLT.FreyGlobalUpperCoefficient

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyContinuousObstructionCertificate
import DkMath.FLT.FreyStageUpperQuotientTopology

#print "file: DkMath.FLT.FreyGlobalUpperCoefficient"

/-! # 元の有限商 Q の大域表現と連続 coboundary
Q は全 Galois 群の係数である。局所固定係数 F を大域係数に取り替えない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の全 Galois 作用による同じ有限商 Q の整数線形表現。 -/
def ResidualCyclicStage.fullGlobalCoefficient : Rep ℤ (Field.absoluteGaloisGroup ℚ) := Rep.of
  { toFun := fun σ => (T.upperQuotientAction σ).toIntLinearMap
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
        (T.upperQuotientAction.map_mul σ τ) }

/-- 元の Q の商位相を大域表現の同じ台集合に保持する。 -/
instance ResidualCyclicStage.fullGlobalCoefficientTopology : TopologicalSpace T.fullGlobalCoefficient :=
  inferInstanceAs (TopologicalSpace T.upperQuotient)

/-- 同じ点の商類 [x] の大域 coboundary。 -/
def ResidualCyclicStage.fullGlobalCocycle
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.cocycles₁ T.fullGlobalCoefficient :=
  ⟨groupCohomology.d₀₁ T.fullGlobalCoefficient ((QuotientAddGroup.mk' T.upperStage) x),
    groupCohomology.d₀₁_apply_mem_cocycles₁ _⟩

/-- 大域 cocycle の値は元の全 Galois 作用差そのもの。 -/
theorem ResidualCyclicStage.fullGlobalCocycle_apply
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : Field.absoluteGaloisGroup ℚ) :
    T.fullGlobalCocycle x σ = T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x := rfl

/-- 同じ Q の商位相で、元の Krull 位相から連続な大域代表。 -/
theorem ResidualCyclicStage.fullGlobalCocycle_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (fun σ : Field.absoluteGaloisGroup ℚ => (T.fullGlobalCocycle x σ : T.upperQuotient)) :=
  by
  change Continuous (fun σ : Field.absoluteGaloisGroup ℚ => T.upperQuotientAction σ
    ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x)
  exact (ResidualCyclicStage.upperQuotient_orbit_continuous T _).sub continuous_const

/-- この大域 Q 値の類は coboundary なので零。局所 F 値の類とは異なる。 -/
theorem ResidualCyclicStage.fullGlobalClass_zero
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x) = 0 := by
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  exact ⟨(QuotientAddGroup.mk' T.upperStage) x, rfl⟩
end
end DkMath.FLT.Frey.Source

```

### 3. DkMath.FLT.FreyGlobalInertiaRestriction

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGlobalUpperCoefficient

#print "file: DkMath.FLT.FreyGlobalInertiaRestriction"

/-! # 同じ大域 Q 係数から元の慣性 Q 係数への制限
群と係数の両方を明示して同じ代表を回収する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 全 Galois 表現を元の慣性群へ制限した係数からの恒等射。 -/
def ResidualCyclicStage.globalInertiaCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep.res (inertiaSubgroupIn A ℚ).subtype T.fullGlobalCoefficient ⟶ T.fullInertiaCoefficient A :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- 元の実際の慣性包含に沿う通常 H¹ 制限写像。 -/
def ResidualCyclicStage.globalInertiaRestriction (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  groupCohomology.map (A := T.fullGlobalCoefficient) (B := T.fullInertiaCoefficient A)
    (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A) 1

/-- 同じ大域 coboundary の制限は、以前の同じ慣性 coboundary。 -/
theorem ResidualCyclicStage.globalCocycle_restrict (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.mapCocycles₁ (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A)
      (T.fullGlobalCocycle x) = T.fullInertiaCocycle A x := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  rfl

/-- 通常 H¹ 制限も、元の同じ代表の類を回収する。 -/
theorem ResidualCyclicStage.globalClass_restrict (A : ValuationSubring (AlgebraicClosure ℚ))
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.globalInertiaRestriction A (groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x)) =
      groupCohomology.H1π (T.fullInertiaCoefficient A) (T.fullInertiaCocycle A x) := by
  unfold globalInertiaRestriction
  have he := groupCohomology.H1π_comp_map_apply
    (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A) (T.fullGlobalCocycle x)
  rw [T.globalCocycle_restrict A x] at he
  exact he
variable (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の連続 F 値代表を Q に含めた値は、同じ大域代表の慣性制限。 -/
theorem ResidualCyclicStage.continuousCocycle_global_restriction
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x σ).val = T.fullGlobalCocycle x σ.val := by
  rw [T.continuousConnectingCocycle_eq A hp5 hq hqp haddr hA x]
  exact T.fixedCocycle_include_value hp5 hq hqp haddr A hA x σ
end
end DkMath.FLT.Frey.Source

```

### 4. DkMath.FLT.FreyDecompositionFixedCoefficient

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyGlobalInertiaRestriction
import DkMath.Lib.NumberTheory.ValuationInertiaNormalizer

#print "file: DkMath.FLT.FreyDecompositionFixedCoefficient"

/-! # 分解群は同じ局所固定係数 F を保存する
全 Galois 群による保存を仮定せず、実際の慣性正規化を内部証明に使う。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 分解群の元の作用は、元の同じ慣性固定部分群を保つ。 -/
theorem ResidualCyclicStage.decomposition_preserves_fixed (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : A.decompositionSubgroup ℚ) (z : T.inertiaFixedUpperQuotient A) :
    T.upperQuotientAction σ.val z.val ∈ T.inertiaFixedUpperQuotient A := by
  intro τ hτ
  have ht := decomposition_inv_conj_mem_inertia A σ.val τ σ.property hτ
  have hf := z.property (σ.val⁻¹ * τ * σ.val) ht
  have he : τ * σ.val = σ.val * (σ.val⁻¹ * τ * σ.val) := by group
  change T.upperQuotientAction τ (T.upperQuotientAction σ.val z.val) = T.upperQuotientAction σ.val z.val
  have hm (a b : Field.absoluteGaloisGroup ℚ) (v : T.upperQuotient) :
      T.upperQuotientAction (a * b) v = T.upperQuotientAction a (T.upperQuotientAction b v) :=
    congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul a b)
  calc T.upperQuotientAction τ (T.upperQuotientAction σ.val z.val)
      = T.upperQuotientAction (τ * σ.val) z.val := (hm τ σ.val z.val).symm
    _ = T.upperQuotientAction (σ.val * (σ.val⁻¹ * τ * σ.val)) z.val :=
      congrArg (fun g => T.upperQuotientAction g z.val) he
    _ = T.upperQuotientAction σ.val (T.upperQuotientAction (σ.val⁻¹ * τ * σ.val) z.val) :=
      hm σ.val _ z.val
    _ = T.upperQuotientAction σ.val z.val := congrArg (T.upperQuotientAction σ.val) hf

/-- 元の F 上の実際の分解群作用。 -/
def ResidualCyclicStage.fixedDecompositionAction (A : ValuationSubring (AlgebraicClosure ℚ)) :
    A.decompositionSubgroup ℚ →* AddMonoid.End (T.inertiaFixedUpperQuotient A) where
  toFun σ :=
    { toFun := fun z => ⟨T.upperQuotientAction σ.val z.val, T.decomposition_preserves_fixed A σ z⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun z w => Subtype.ext (map_add _ _ _) }
  map_one' := by
    apply AddMonoidHom.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End T.upperQuotient => f z.val) T.upperQuotientAction.map_one
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End T.upperQuotient => f z.val)
      (T.upperQuotientAction.map_mul σ.val τ.val)

/-- 同じ F と同じ作用による分解群の整数線形表現。 -/
def ResidualCyclicStage.fixedDecompositionCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep ℤ (A.decompositionSubgroup ℚ) := Rep.of
  { toFun := fun σ => (T.fixedDecompositionAction A σ).toIntLinearMap
    map_one' := by
      apply LinearMap.ext
      intro z
      exact congrArg (fun f : AddMonoid.End (T.inertiaFixedUpperQuotient A) => f z)
        (T.fixedDecompositionAction A).map_one
    map_mul' := fun σ τ => by
      apply LinearMap.ext
      intro z
      exact congrArg (fun f : AddMonoid.End (T.inertiaFixedUpperQuotient A) => f z)
        ((T.fixedDecompositionAction A).map_mul σ τ) }

/-- 同じ F の分解群作用は単射である。 -/
theorem ResidualCyclicStage.fixedDecompositionAction_injective (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : A.decompositionSubgroup ℚ) : Function.Injective (T.fixedDecompositionAction A σ) := by
  intro z w he
  have hh := congrArg (T.fixedDecompositionAction A σ⁻¹) he
  change ((T.fixedDecompositionAction A σ⁻¹) * (T.fixedDecompositionAction A σ)) z =
    ((T.fixedDecompositionAction A σ⁻¹) * (T.fixedDecompositionAction A σ)) w at hh
  rw [← map_mul, inv_mul_cancel, map_one] at hh
  exact hh
end
end DkMath.FLT.Frey.Source

```

### 5. DkMath.FLT.FreyDecompositionCocycleCovariance

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionFixedCoefficient

#print "file: DkMath.FLT.FreyDecompositionCocycleCovariance"

/-! # 同じ点の cocycle の分解群共役輸送
作用差の恒等式から、元の F 値 cocycle の共変性まで輸送する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 一つの全 Galois 元による元の有限捩れ点の像。 -/
def ResidualCyclicStage.globalTranslateTorsion (σ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  representation S.rationalCurve (p ^ (n + 1 + 1)) σ x

/-- 同じ点の商類の輸送は、元の商作用と一致する。 -/
theorem ResidualCyclicStage.globalTranslate_upperClass (σ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (QuotientAddGroup.mk' T.upperStage) (ResidualCyclicStage.globalTranslateTorsion σ x) =
      T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) := rfl

/-- 同じ Q 値の作用差は、点の輸送と群の共役に関して共変。 -/
theorem ResidualCyclicStage.globalCocycle_conjugate (σ τ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fullGlobalCocycle (ResidualCyclicStage.globalTranslateTorsion σ x) τ =
      T.upperQuotientAction σ (T.fullGlobalCocycle x (σ⁻¹ * τ * σ)) := by
  change T.upperQuotientAction τ ((QuotientAddGroup.mk' T.upperStage)
    (ResidualCyclicStage.globalTranslateTorsion σ x)) -
      (QuotientAddGroup.mk' T.upperStage) (ResidualCyclicStage.globalTranslateTorsion σ x) =
    T.upperQuotientAction σ (T.upperQuotientAction (σ⁻¹ * τ * σ)
      ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x)
  rw [T.globalTranslate_upperClass]
  refine Eq.trans ?_ ((T.upperQuotientAction σ).map_sub
    (T.upperQuotientAction (σ⁻¹ * τ * σ) ((QuotientAddGroup.mk' T.upperStage) x))
    ((QuotientAddGroup.mk' T.upperStage) x)).symm
  have he : τ * σ = σ * (σ⁻¹ * τ * σ) := by group
  have hm (a b : Field.absoluteGaloisGroup ℚ) (v : T.upperQuotient) :
      T.upperQuotientAction (a * b) v = T.upperQuotientAction a (T.upperQuotientAction b v) :=
    congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul a b)
  apply congrArg (fun v : T.upperQuotient => v - T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x))
  calc T.upperQuotientAction τ (T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x))
      = T.upperQuotientAction (τ * σ) ((QuotientAddGroup.mk' T.upperStage) x) := (hm τ σ _).symm
    _ = T.upperQuotientAction (σ * (σ⁻¹ * τ * σ)) ((QuotientAddGroup.mk' T.upperStage) x) :=
      congrArg (fun g => T.upperQuotientAction g ((QuotientAddGroup.mk' T.upperStage) x)) he
    _ = T.upperQuotientAction σ (T.upperQuotientAction (σ⁻¹ * τ * σ) ((QuotientAddGroup.mk' T.upperStage) x)) := hm σ _ _
variable (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 分解群共役で輸送された同じ F 値の連続 cocycle が一致する。 -/
theorem ResidualCyclicStage.continuousCocycle_decomposition_conjugate
    (σ : A.decompositionSubgroup ℚ) (τ : inertiaSubgroupIn A ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.continuousConnectingCocycle A hp5 hq hqp haddr hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) τ =
      T.fixedDecompositionAction A σ
        (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x
          ⟨σ.val⁻¹ * τ.val * σ.val, decomposition_inv_conj_mem_inertia A σ.val τ.val σ.property τ.property⟩) := by
  apply Subtype.ext
  change (T.continuousConnectingCocycle A hp5 hq hqp haddr hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) τ).val =
    T.upperQuotientAction σ.val (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x _).val
  rw [T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA,
    T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA]
  exact T.globalCocycle_conjugate σ.val τ.val x
end
end DkMath.FLT.Frey.Source

```

### 6. DkMath.FLT.FreyRelativeGlobalOrigin

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionCocycleCovariance

#print "file: DkMath.FLT.FreyRelativeGlobalOrigin"

/-! # 同じ局所 F 障害の、係数を含めた相対的大域起源
大域 Q coboundary の制限と局所 F 非零類を同時に保持する。F 値の大域 Selmer 類は構成しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
variable (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ連続 F cocycle の係数包含は、実際の大域 Q coboundary の制限に一致。 -/
theorem ResidualCyclicStage.continuousCocycle_global_origin
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.mapCocycles₁ (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A)
      (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x) =
    groupCohomology.mapCocycles₁ (inertiaSubgroupIn A ℚ).subtype (T.globalInertiaCoefficient A)
      (T.fullGlobalCocycle x) := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  exact T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA x σ

/-- 係数包含と群制限の両経路で、同じ通常 H¹ 類に到達する。 -/
theorem ResidualCyclicStage.continuousClass_global_origin_square
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
      (groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x)) =
      T.globalInertiaRestriction A (groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x)) := by
  have hl := groupCohomology.H1π_comp_map_apply (MonoidHom.id (inertiaSubgroupIn A ℚ))
    (T.fixedCoefficientInclusion A) (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x)
  have hr := groupCohomology.H1π_comp_map_apply (inertiaSubgroupIn A ℚ).subtype
    (T.globalInertiaCoefficient A) (T.fullGlobalCocycle x)
  exact hl.trans ((congrArg (fun c : groupCohomology.cocycles₁ (T.fullInertiaCoefficient A) =>
    groupCohomology.H1π (T.fullInertiaCoefficient A) c)
      (T.continuousCocycle_global_origin A hp5 hq hqp haddr hA x)).trans hr.symm)
end
end DkMath.FLT.Frey.Source

```

### 7. DkMath.FLT.FreyRelativeGlobalObstructionCertificate

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRelativeGlobalOrigin

#print "file: DkMath.FLT.FreyRelativeGlobalObstructionCertificate"

/-! # 分解群輸送でも残る、元の局所非零類と大域零類の係数境界
局所 F 非零性と大域 Q coboundary の零性を、同じ点について同時に証明する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

variable {T} {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ障害点では、局所 F 類は非零だが大域 Q 類は零。 -/
theorem NarrowAbsorptionObstruction.relative_global_class_boundary
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over x) ≠ 0 ∧
    groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x) = 0 := by
  constructor
  · rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over]
    exact (h.fixed_H1_nonzero hp5).2
  · exact T.fullGlobalClass_zero _

/-- 分解群で点を輸送しても、同じ連続 F cocycle の非零性は失われない。 -/
theorem NarrowAbsorptionObstruction.decomposition_translate_continuous_nonzero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (σ : A.decompositionSubgroup ℚ) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    ∃ η : inertiaSubgroupIn A ℚ,
      T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
        (ResidualCyclicStage.globalTranslateTorsion σ.val x) η ≠ 0 := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  let τ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
  let η : inertiaSubgroupIn A ℚ := ⟨σ.val * τ₀ * σ.val⁻¹,
    decomposition_conj_mem_inertia A σ.val τ₀ σ.property h.inertia⟩
  refine ⟨η, ?_⟩
  intro hz
  have he := T.continuousCocycle_decomposition_conjugate A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over σ η x
  have hconj : σ.val⁻¹ * η.val * σ.val = τ₀ := by dsimp [η]; group
  have harg : (⟨σ.val⁻¹ * η.val * σ.val, decomposition_inv_conj_mem_inertia A σ.val η.val σ.property η.property⟩ :
      inertiaSubgroupIn A ℚ) = ⟨τ, h.inertia⟩ := Subtype.ext hconj
  rw [harg, hz] at he
  have hzero : T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over x
      ⟨τ, h.inertia⟩ = 0 := by
    apply T.fixedDecompositionAction_injective A σ
    simpa only [map_zero] using he.symm
  have hc := h.fixed_character_nontrivial hp5
  apply hc
  rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over] at hzero
  exact congrArg Multiplicative.ofAdd hzero

/-- 輸送後の局所 F 類も非零である一方、同じ点の大域 Q 類は零である。 -/
theorem NarrowAbsorptionObstruction.decomposition_translate_class_boundary
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (σ : A.decompositionSubgroup ℚ) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let x' := ResidualCyclicStage.globalTranslateTorsion σ.val x
    groupCohomology.H1π _ (T.continuousConnectingCocycle A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over x') ≠ 0 ∧
    groupCohomology.H1π T.fullGlobalCoefficient (T.fullGlobalCocycle x') = 0 := by
  constructor
  · rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over]
    apply TrivialCharacterH1.class_ne_zero
    obtain ⟨η, hη⟩ := h.decomposition_translate_continuous_nonzero hp5 σ
    refine ⟨η, ?_⟩
    intro he
    apply hη
    rw [T.continuousConnectingCocycle_eq A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over]
    exact congrArg Multiplicative.toAdd he
  · exact T.fullGlobalClass_zero _
end
end DkMath.FLT.Frey.Source

```

