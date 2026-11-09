# NOTE-032 教科書 — 同じ連結同型の分解群同変性と Frobenius 不変性判定

日付: 2026-11-09。最新レビューに従い、既存の Q/F≃K を作り直さず、元の D 作用と同じ cocycle に接続した。
今回は7モジュール全てが元の実際の Frey Source を扱う FLT 層である。
**D による輸送と D/I の作用を証明した。不変性そのものや F 値大域 Selmer 類の存在は結論していない。**

全7 Lean ブロックは production の全文と一致する。
各 import 群直後に必須 `#print "file: 正確なモジュール名"` を保持した。
既存 DkMath の Lake 環境で各ブロックを別ファイルにコピーして検査できる。

## 記号と結論

D は同じ付値環 A の分解群、I_D は D 内の元の inertiaSubgroup。
I はその全 Galois 群への像であり、以前から使用している実際の慣性群。
Q は元の上位有限捩れ商、F=Q^I、E=Q/F、K=ker(H¹(I,F)→H¹(I,Q))。
δ:E≃K は既存の `quotientConnectingKernelEquiv` そのものである。

今回、元の対象について

    δ(σ_E z)=σ_K δ(z),  σ∈D

を証明し、さらに F,E,K の作用を **同じ実際の D/I_D** へ降ろした。
K 上の輸送が単なる任意の同型による模型ではないことは、元の連続 cocycle の共変性から

    ev_τ(σ_K k)=σ_F(ev_(σ⁻¹τσ)(k))

を全 k・全 τ について証明することで確認している。

実際の Frobenius φ と、以前と同じ具体的な慣性生成元 γ について

    q • ev_γ(φ_K k)=φ_F(ev_γ(k))

を得る。q 倍と ev_γ の単射性から

    φ_K k=k ↔ φ_F(ev_γ(k))=q • ev_γ(k)

を証明した。右辺の固有値条件を、未証明のまま真として採用していない。

## 1. 元の Q/F に対する分解群作用

前回内部証明した F の D 安定性を使い、元の Q の作用を同じ商 E に降ろす。
整数線形商写像 `mapQ` により D→End_ℤ(E) を構成し、

    σ_E(mkQ v)=mkQ(σ_Q v)

を元の商写像そのもので示す。
元の有限捩れ点 x に対する商類を使う場合、結果は輸送した同じ点 σx の商類となる。
F の全 G 安定性は仮定しない。

## 2. 既存の連結同型 δ を D 同変化する

δ は既存の整数線形同型である。E の作用を δ で共役することで、元の同じ K 上に作用を構成する。
その乗法性は endomorphism ring の同型を通じて保持する。
既存 δ を改めて構成したのではなく、作用を輸送したのである。

輸送が正しい対象に作用していることは、元の点に関する

    σ_K(k_x)=k_(σx)

を `quotientKernelEquiv_coset` で証明して確認する。
次の段階でこの作用を元の cocycle 共役と同定する。

## 3. 全係数核の評価による共変性の検証

任意の k∈K は既存の証明により同じ有限捩れ点 x の連結像で表せる。
その表示と前回の連続 F cocycle の共変性を組み合わせ、

    ev_τ(σ_K k)=σ_F(ev_(σ⁻¹τσ)(k))

を得る。この等式は全ての元の慣性元 τ で成立し、同じ自明係数 H¹ 類の値を保持する。

また、前回完成した同じ γ による評価の単射性から、
σ_K k=k と、γ における一つの値の一致とが同値となる。
非零性が保存されるというだけで固定性を結論していない。

## 4. 同じ作用を実際の D/I_D へ降ろす

I_D は元の剰余作用の核なので正規部分群である。
F は I 固定係数だから I_D の作用が自明。
E の元の慣性作用の自明性は既存の `fixedQuotient_action_trivial` から供給する。
δ による輸送により K 上の I_D 作用も自明となる。

三つの作用を `QuotientGroup.lift` で実際の D/I_D に降ろし、
δ がこの剰余群上でも同変であることを証明した。
D/I_D を別の抽象的な巡回群と同一視したり、全体が有限だと仮定したりしていない。

## 5. 同じ全核指標の Frobenius q 倍公式

既存の tame 商の共役公式は、元の実際の φ について

    [φτφ⁻¹]=[τ]^q

を与える。既存の全核指標は同じ tame 商へ降下しているので、この等式を評価すれば

    ev_(φτφ⁻¹)(k)=q • ev_τ(k)

を得る。

第3段階の共変性を φτφ⁻¹ で評価すると、同じ φ_F と同じ k を保持して

    q • ev_τ(φ_K k)=φ_F(ev_τ(k))

となる。固定した基点の指標共役公式と、係数を輸送する公式の両方を結合した結果である。

## 6. 同じ γ の値による Frobenius 固定性の同値条件

元の濃度積の等式から |F| は p^(n+3) を割る。
p と q は異なる素数なので q は |F| と素であり、F 上の q 倍は単射となる。
ここでは F を標数 p のベクトル空間と仮定していない。F は高い p 冪指数を持ち得る。

第5段階を同じ γ で評価し、q 倍の単射性と ev_γ の単射性を使うと

    φ_K k=k ↔ φ_F(ev_γ(k))=q • ev_γ(k)

が従う。φ_F が自明とか、既知の円分固有値を持つとかいう追加仮定を置いていない。
F 上の実際の Frobenius 作用のどの条件が必要なのかを、同じ有限係数の等式に落とした。

## 7. 同じ障害元についての有限商・Frobenius 判定証明書

任意の z∈E について、δ(z) が D で固定されることは元の z が固定されることと同値。
この結果を元の障害点から構成する同じ核元 k_x に接続する。
q 上の元の住所から実際の Frobenius φ を内部選択し、

    v=ev_γ(k_x)≠0,
    φ_K(k_x)=k_x ↔ φ_F(v)=q • v

を同時に供給する。
ここで φ_K(k_x)=k_x も φ_F(v)=q•v も、単独の結論とはしていない。
これが、前回の「輸送後も非零」という事実からさらに進んだ、同じ元に対する不変性判定である。

## 模範解答との照合

模範の `ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_frobConj` の末尾を確認した。
模範は Frobenius 共役と q 乗の誤差が全根固定 tail に入ることから、その誤差に慣性内の p 冪根を取る。
DkMath の今回の実装は、すでに実装済みの同じ tame 商の共役冪等式と、全核指標の tame 降下を消費する。
さらに実際の係数作用を同じ δ と cocycle の共変性で追跡する。
外部の結論を import したり、新しい Frobenius 固有値 provider を仮定したりしていない。

## 完了したことと残る算術

完了: 元の E の D 作用、元の δ の同変化、K 上の cocycle 共役との整合、
同じ F,E,K の D/I_D 作用、Frobenius の評価関係、同じ γ の非零値による障害の固定性判定。
未完了: 実際の障害類の不変性または固有値条件の算術的判定、H¹(D,F) への持ち上げ、
F 値の大域 Selmer/Kummer 類との係数照合、ω² 類群消滅、共鳴障害排除、無条件一般 hno。
q≡±1 mod p の共鳴枝の排除を、今回の同値条件だけから結論していない。

新規23宣言の再帰依存・標準公理監査と、公開入力23件の監査を通常テストへ追加した。
有限模型では q=3、F=ZMod5、φ_F=2倍、φ_K=4倍が共変性を満たしても、非零元が不変とは限らないことを確認する。
検証: `evidence/validation-note032-decomposition-equivariance.txt`。
模範ソース・コミット・レビュー SHA-256: `evidence/note032-decomposition-equivariance-reference-audit.json`。

## 教科書 Lean コード全文

### 1. DkMath.FLT.FreyDecompositionQuotientAction

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRelativeGlobalObstructionCertificate

#print "file: DkMath.FLT.FreyDecompositionQuotientAction"

/-! # 同じ Q/F の分解群作用
元の F の D 安定性を使って商へ降ろす。F の全 G 安定性は仮定しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の Q/F 上の、同じ D の整数線形作用。 -/
def ResidualCyclicStage.quotientDecompositionAction :
    A.decompositionSubgroup ℚ →* Module.End ℤ (T.fixedQuotientCoefficient A) where
  toFun σ := (T.fixedCoefficientSubmodule A).mapQ (T.fixedCoefficientSubmodule A)
    (T.upperQuotientAction σ.val).toIntLinearMap (fun z hz => T.decomposition_preserves_fixed A σ ⟨z, hz⟩)
  map_one' := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
    exact congrArg (T.fixedCoefficientSubmodule A).mkQ
      (congrArg (fun f : AddMonoid.End T.upperQuotient => f v) T.upperQuotientAction.map_one)
  map_mul' σ τ := by
    apply LinearMap.ext
    intro z
    obtain ⟨v, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
    exact congrArg (T.fixedCoefficientSubmodule A).mkQ
      (congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul σ.val τ.val))

/-- 商作用は元の同じ商写像と可換。 -/
theorem ResidualCyclicStage.quotientDecompositionAction_mk (σ : A.decompositionSubgroup ℚ) (v : T.upperQuotient) :
    T.quotientDecompositionAction A σ ((T.fixedCoefficientSubmodule A).mkQ v) =
      (T.fixedCoefficientSubmodule A).mkQ (T.upperQuotientAction σ.val v) := rfl

/-- 元の有限捩れ点を輸送した商類との一致。 -/
theorem ResidualCyclicStage.quotientDecompositionAction_coset (σ : A.decompositionSubgroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.quotientDecompositionAction A σ ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage)
        (ResidualCyclicStage.globalTranslateTorsion σ.val x)) := rfl
end
end DkMath.FLT.Frey.Source

```

### 2. DkMath.FLT.FreyConnectingDecompositionEquivariance

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionQuotientAction

#print "file: DkMath.FLT.FreyConnectingDecompositionEquivariance"

/-! # 既存 Q/F≃K の同じ連結像を分解群同変にする
同型を作り直さず、作用の輸送と元の coset での計算を明示する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ連結核上の、既存同型を経由した D の整数線形作用。 -/
def ResidualCyclicStage.kernelDecompositionAction :
    A.decompositionSubgroup ℚ →* Module.End ℤ (T.fixedH1CoefficientKernel A) :=
  (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).conjRingEquiv.toMonoidHom.comp
    (T.quotientDecompositionAction A)

/-- 既存の同じ連結同型は D 同変。 -/
theorem ResidualCyclicStage.quotientKernelEquiv_decomposition (σ : A.decompositionSubgroup ℚ)
    (z : T.fixedQuotientCoefficient A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ
      (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA (T.quotientDecompositionAction A σ z) := by
  change (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA)
    (T.quotientDecompositionAction A σ ((T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).symm
      (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- 元の点の核元を輸送すると、輸送した同じ点の核元になる。 -/
theorem ResidualCyclicStage.kernelDecompositionAction_coset (σ : A.decompositionSubgroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ
      (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
    T.fixedCosetKernelElement hp5 hq hqp haddr A hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) := by
  rw [← T.quotientKernelEquiv_coset A hp5 hq hqp haddr hA x, T.quotientKernelEquiv_decomposition A hp5 hq hqp haddr hA]
  exact T.quotientKernelEquiv_coset A hp5 hq hqp haddr hA _
end
end DkMath.FLT.Frey.Source

```

### 3. DkMath.FLT.FreyKernelDecompositionEvaluation

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyConnectingDecompositionEquivariance

#print "file: DkMath.FLT.FreyKernelDecompositionEvaluation"

/-! # 元の全係数核の分解群輸送と評価の共変性
輸送で不変になるとは仮定しない。同じ連続代表の値で作用を検証する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ核元の同じ評価は、D の作用と慣性共役に関して共変。 -/
theorem ResidualCyclicStage.kernelDecompositionEvaluation (σ : A.decompositionSubgroup ℚ)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
      T.fixedDecompositionAction A σ (T.fixedKernelEvaluation A
        ⟨σ.val⁻¹ * τ.val * σ.val, decomposition_inv_conj_mem_inertia A σ.val τ.val σ.property τ.property⟩ k) := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  rw [T.kernelDecompositionAction_coset A hp5 hq hqp haddr hA σ x]
  change T.continuousConnectingCocycle A hp5 hq hqp haddr hA (ResidualCyclicStage.globalTranslateTorsion σ.val x) τ =
    T.fixedDecompositionAction A σ (T.continuousConnectingCocycle A hp5 hq hqp haddr hA x _)
  exact T.continuousCocycle_decomposition_conjugate A hp5 hq hqp haddr hA σ τ x

/-- 同じ具体的 γ での評価だけで、D 不変性を判定できる。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_generator_evaluation (σ : A.decompositionSubgroup ℚ)
    (k : T.fixedH1CoefficientKernel A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k ↔
    T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)
      (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
    T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  ⟨fun h => congrArg _ h, fun he => T.generator_evaluation_injective A hp5 hq hqp haddr hA he⟩
end
end DkMath.FLT.Frey.Source

```

### 4. DkMath.FLT.FreyResidueDecompositionAction

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelDecompositionEvaluation

#print "file: DkMath.FLT.FreyResidueDecompositionAction"

/-! # 同じ F・Q/F・K の作用を実際の D/I へ降ろす
ここで I は D 内の元の inertiaSubgroup。剰余群の巡回性や類の不変性は仮定しない。 -/
namespace DkMath.FLT.Frey.Source
/-- 分解群内の元の慣性は、実際の剰余作用の核として正規。 -/
instance inertiaNormalInDecomposition (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (A.inertiaSubgroup ℚ).Normal := by
  delta ValuationSubring.inertiaSubgroup
  exact MonoidHom.normal_ker _
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の I⊆D の元は、同じ F 上で自明に作用する。 -/
theorem ResidualCyclicStage.inertia_le_fixedDecomposition_kernel :
    A.inertiaSubgroup ℚ ≤ (T.fixedDecompositionAction A).ker := by
  intro σ hσ
  apply AddMonoidHom.ext
  intro z
  apply Subtype.ext
  exact z.property σ.val ⟨σ, hσ, rfl⟩
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ Q/F の D 作用でも、元の慣性の作用は自明。 -/
theorem ResidualCyclicStage.inertia_le_quotientDecomposition_kernel :
    A.inertiaSubgroup ℚ ≤ (T.quotientDecompositionAction A).ker := by
  intro σ hσ
  apply LinearMap.ext
  intro z
  exact T.fixedQuotient_action_trivial hp5 hq hqp haddr A hA ⟨σ.val, ⟨σ, hσ, rfl⟩⟩ z

/-- 同じ K の D 作用も元の慣性で零化される。 -/
theorem ResidualCyclicStage.inertia_le_kernelDecomposition_kernel :
    A.inertiaSubgroup ℚ ≤ (T.kernelDecompositionAction A hp5 hq hqp haddr hA).ker := by
  intro σ hσ
  change (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).conjRingEquiv
    (T.quotientDecompositionAction A σ) = 1
  rw [show T.quotientDecompositionAction A σ = 1 from
    T.inertia_le_quotientDecomposition_kernel A hp5 hq hqp haddr hA hσ, map_one]

/-- 元の同じ F に対する D/I の作用。 -/
def ResidualCyclicStage.fixedResidueAction :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* AddMonoid.End (T.inertiaFixedUpperQuotient A) :=
  QuotientGroup.lift _ (T.fixedDecompositionAction A) (T.inertia_le_fixedDecomposition_kernel A)

/-- 元の同じ Q/F に対する D/I の作用。 -/
def ResidualCyclicStage.quotientResidueAction :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* Module.End ℤ (T.fixedQuotientCoefficient A) :=
  QuotientGroup.lift _ (T.quotientDecompositionAction A)
    (T.inertia_le_quotientDecomposition_kernel A hp5 hq hqp haddr hA)

/-- 元の同じ K に対する D/I の作用。 -/
def ResidualCyclicStage.kernelResidueAction :
    ((A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) →* Module.End ℤ (T.fixedH1CoefficientKernel A) :=
  QuotientGroup.lift _ (T.kernelDecompositionAction A hp5 hq hqp haddr hA)
    (T.inertia_le_kernelDecomposition_kernel A hp5 hq hqp haddr hA)

/-- 実際の剰余群上でも、以前の同じ連結同型が同変。 -/
theorem ResidualCyclicStage.quotientKernelEquiv_residue
    (s : (A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) (z : T.fixedQuotientCoefficient A) :
    T.kernelResidueAction A hp5 hq hqp haddr hA s (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
    T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA (T.quotientResidueAction A hp5 hq hqp haddr hA s z) := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective s
  exact T.quotientKernelEquiv_decomposition A hp5 hq hqp haddr hA σ z
end
end DkMath.FLT.Frey.Source

```

### 5. DkMath.FLT.FreyKernelFrobeniusCovariance

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResidueDecompositionAction

#print "file: DkMath.FLT.FreyKernelFrobeniusCovariance"

/-! # 同じ全核指標での Frobenius q 倍公式
元の tame 商の実際の共役冪公式を、同じ固定基点の評価へ輸送する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 任意の同じ核元の評価は、実際の Frobenius 共役で q 倍される。 -/
theorem ResidualCyclicStage.kernelEvaluation_frobenius_conjugate
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelEvaluation A
      ⟨φ.val * τ.val * φ.val⁻¹, decomposition_conj_mem_inertia A φ.val τ.val φ.property τ.property⟩ k =
      q • T.fixedKernelEvaluation A τ k := by
  obtain ⟨hc, he⟩ := tameInertia_frobenius_power A hφ τ
  have hv := congrArg (T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k) he
  rw [map_pow] at hv
  exact congrArg Multiplicative.toAdd hv

/-- 輸送する核元と係数作用を同時に保った Frobenius 評価関係。 -/
theorem ResidualCyclicStage.kernelFrobenius_evaluation_relation
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (τ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    q • T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k) =
      T.fixedDecompositionAction A φ (T.fixedKernelEvaluation A τ k) := by
  let η : inertiaSubgroupIn A ℚ := ⟨φ.val * τ.val * φ.val⁻¹,
    decomposition_conj_mem_inertia A φ.val τ.val φ.property τ.property⟩
  have hc := T.kernelDecompositionEvaluation A hp5 hq hqp haddr hA φ η k
  have he : (⟨φ.val⁻¹ * η.val * φ.val, decomposition_inv_conj_mem_inertia A φ.val η.val φ.property η.property⟩ :
    inertiaSubgroupIn A ℚ) = τ := by
    apply Subtype.ext
    dsimp [η]
    group
  rw [he] at hc
  exact (T.kernelEvaluation_frobenius_conjugate A hp5 hq hqp haddr hA φ hφ τ _).symm.trans hc
end
end DkMath.FLT.Frey.Source

```

### 6. DkMath.FLT.FreyKernelFrobeniusFixedCriterion

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFrobeniusCovariance

#print "file: DkMath.FLT.FreyKernelFrobeniusFixedCriterion"

/-! # 同じ具体的生成元による Frobenius 不変性の判定
非零性の保存と不変性を同一視しない。q 倍の消去には元の p 冪周期を使う。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の F 上の q 倍は単射。剰余標数が p と異なるという元の条件を消費する。 -/
theorem ResidualCyclicStage.fixed_q_nsmul_injective :
    Function.Injective (fun z : T.inertiaFixedUpperQuotient A => q • z) := by
  have hd : Nat.card (T.inertiaFixedUpperQuotient A) ∣ p ^ (n + 3) := by
    refine ⟨Nat.card (T.fixedH1CoefficientKernel A), ?_⟩
    rw [mul_comm]
    exact (T.fixedKernel_card_mul_fixed A hp5 hq hqp haddr hA).symm
  have hcop : Nat.Coprime q (Nat.card (T.inertiaFixedUpperQuotient A)) :=
    ((Nat.coprime_primes hq (Fact.out : p.Prime)).mpr hqp).pow_right (n + 3) |>.of_dvd_right hd
  have hc : (Nat.card (Multiplicative (T.inertiaFixedUpperQuotient A))).Coprime q := by
    rw [Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (T.inertiaFixedUpperQuotient A) ≃ T.inertiaFixedUpperQuotient A)]
    exact hcop.symm
  intro x y he
  apply Multiplicative.ofAdd.injective
  exact (powCoprime hc).injective (congrArg Multiplicative.ofAdd he)

/-- 同じ γ での値が F の Frobenius q 固有値条件を満たすことと、元の核元の不変性は同値。 -/
theorem ResidualCyclicStage.kernelFrobenius_fixed_iff
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k := by
  have he := T.kernelFrobenius_evaluation_relation A hp5 hq hqp haddr hA φ hφ
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k
  constructor
  · intro hk
    rw [hk] at he
    exact he.symm
  · intro hk
    rw [hk] at he
    apply T.generator_evaluation_injective A hp5 hq hqp haddr hA
    exact T.fixed_q_nsmul_injective A hp5 hq hqp haddr hA he
end
end DkMath.FLT.Frey.Source

```

### 7. DkMath.FLT.FreyDecompositionInvariantObstruction

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFrobeniusFixedCriterion

#print "file: DkMath.FLT.FreyDecompositionInvariantObstruction"

/-! # 同じ障害の輸送と不変性を、同じ Q/F と単一評価で判定する
不変性や大域 F 類の存在は仮定しない。新たな hclass を供給したとは主張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の同じ核元が D で固定されることは、元の同じ剰余類の固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_quotient_fixed (σ : A.decompositionSubgroup ℚ)
    (z : T.fixedQuotientCoefficient A) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA σ
      (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z) =
        T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z ↔
    T.quotientDecompositionAction A σ z = z := by
  rw [T.quotientKernelEquiv_decomposition A hp5 hq hqp haddr hA]
  exact (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).injective.eq_iff
end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ障害核元の Frobenius 不変性を、同じ γ の一つの値だけで判定する。 -/
theorem NarrowAbsorptionObstruction.frobenius_fixed_criterion
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k :=
  T.kernelFrobenius_fixed_iff A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ hφ _
/-- 元の q 上の住所から実際の Frobenius を内部選択し、同じ障害の判定条件を供給する。 -/
theorem NarrowAbsorptionObstruction.exists_frobenius_fixed_criterion
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ∃ φ : A.decompositionSubgroup ℚ, ValuationFrobenius.IsFrobeniusAt A φ.val q ∧
      T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k ≠ 0 ∧
      (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
       T.fixedDecompositionAction A φ
         (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) =
       q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) := by
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime h.prime A h.lies_over
  refine ⟨⟨φ, hφ.mem_decompositionSubgroup⟩, hφ, ?_, h.frobenius_fixed_criterion hp5 _ hφ⟩
  intro he
  have hk := T.generator_evaluation_injective A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
    (show T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
      T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) 0 by
        simpa only [map_zero] using he)
  have hv := congrArg Subtype.val hk
  apply (h.fixed_H1_nonzero hp5).2
  exact (T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).symm.trans hv
end
end DkMath.FLT.Frey.Source

```

