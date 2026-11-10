# NOTE-032 教科書 — 実際の有限分解群作用像と Frobenius 生成

2026-11-11。最新レビューの有限表現経路を参考に、7ステップ・22宣言を実装した。
汎用2モジュールは Lib、元の同じ Frey Source の5モジュールは FLT。
末尾の全7 Lean ブロックは production 全文と一致し、各 import 群直後の必須 `#print "file: 正確なモジュール名"` を保持する。
既存 DkMath の Lake 環境で各ブロックを別ファイルとして検査できる。

## 元の対象と今回の境界

FLT 層は元の `[Fact p.Prime]`、`hp5 : 5 ≤ p`、`hq : q.Prime`、`hqp : q ≠ p`、
`haddr : q = 2 ∨ (q : ℤ) ∣ S.a*S.b*S.c`、`hA : LiesOverPrime A q` を保持する。障害終点では同じ障害証人の support と lies_over から局所条件を供給する。

D は同じ付値環 A の分解群、I_D はその中の元の慣性群。I は従来の全 Galois 群内の慣性像。
K=ker(H¹(I,F)→H¹(I,Q))、F=Q^I、既存 δ:Q/F≃K、元の障害核元 k_x と同じ γ の値 v を保持する。
元の K 作用 ρ_K から、忠実な有限作用核商と射影を構成した。

    P_K := D / ker(ρ_K^×),   π_K : D → P_K

P_K が有限・離散で、I_D が π_K の核に入ることは内部証明済みである。
今回の終点に残る入力は

    himage : ∀σ∈D, π_K(σ) ∈ Subgroup.zpowers (π_K(φ))
    hsign  : (q≡1 mod p ∧ φ_F(v)=v) ∨ (q≡−1 mod p ∧ φ_F(v)=−v)

である。π_K は全射なので himage は実際の有限群 P_K が π_K(φ) で生成されることを述べる。
**元の Source・素数・支持・局所住所条件の下で、有限性・離散性・開核を内部証明した。しかし、同じ φ の像による生成 himage と実際の符号 hsign の算術的供給は未完成。全 D の密度を終点から除いたことは、無条件 hno の完成を意味しない。**

## 1. 有限体 Galois 群の有界 Frobenius 生成

有限体 k の有限次拡大 E に対し、各 σ∈Gal(E/k) は Frob_k^m、0≤m<[E:k]。Mathlib の実際の Frobenius 全単射定理を用いる。さらに π:G→Gal(E/k)、a:Gal(E/k)→M と π(φ)=Frob_k があれば、a(πg)=a(πφ)^m を同じ次数未満の m で供給する。元の付値環での因子化は、この一般論の結論ではない。

## 2. 元の K 作用の忠実な有限群像

元の ρ_K:D→End_ℤ(K) を toHomUnits により同じ End の単元群へ持ち上げる。作用核が変わらないことを証明し、P_K=D/ker(ρ_K^×) と標準射影 π_K を構成する。第一同型定理による単元群への埋め込みの単射性と、元の K の有限性から P_K の有限性を証明する。巡回性はまだ結論しない。

## 3. 同じ作用核の開性と有限商の離散性

元の F の離散位相と、同じ γ における連続軌道評価から、各 k の固定条件は開集合となる。γ 評価の単射性を使い、作用核を有限個のこれら開集合の共通部分として同定する。したがって同じ作用核が開であり、P_K の元の商位相は離散となる。元の実際の慣性 I_D は π_K の核に含まれる。K 自体に新たな位相を仮定していない。

## 4. 明示密度から連続有限像の生成へ

連続な離散群像 ρ:G→H が N を消す場合、明示密度 closure(N∨⟨φ⟩)=G から ρg∈⟨ρφ⟩ を得る。証明は ⟨ρφ⟩ の逆像が閉部分群であることによる。有限 H での生成は自然数冪に直せ、位数 orderOf(ρφ) 未満の指数を取れる。

## 5. 実際の有限作用像への二つの供給経路

既存 hdense から同じ P_K の生成条件 himage を供給する。また、元の π_K が有限体 Galois 群を通じて因子化する実際の射 π,a と hfactor があれば、第1段階から密度を経由せず生成条件を得る。どちらも条件付きで、実際の局所住所から hfactor や hdense を構成したとはしていない。himage の下で元の線形作用そのものについて ρ_K(σ)=ρ_K(φ)^m を、m<orderOf(π_Kφ) と共に証明する。

## 6. 有限像生成による hD と同じ固有値・符号判定

himage と φ_K(k)=k から、前段の有界な作用冪を使って全 D 固定性 hD を導く。全 D の密度は不要である。さらに既存の同じ γ の Frobenius 固有値判定に接続し、元の障害値 v の共鳴符号条件と hD を、himage の下で同値化する。Frobenius 作用の符号そのものを算術的に決定したとはしていない。

## 7. 有限像生成・共鳴符号から同じ非零 D 類へ

公開終点 decomposition_lift_of_finite_image_sign は himage と hsign を入力とし、同じ障害核元の hD を内部供給する。既存の同じ明示的連続 F 値 D cocycle の持ち上げを再利用するので、元の慣性障害類への制限一致と非零性を保持する。hdense/hD/hz を終点の公開入力にしない一方、himage と hsign は未解決入力として保持する。

## 模範解答と既存の剰余作用全射性の照合

模範 `P2M/Sol/S_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le.lean` と、その `FrobeniusPowerDense` の定義を確認した。
模範は数体への制限核を通じて大域の Frobenius 冪近似を供給する。
定義では素数 ℓ、付値環、共役元を動かせる。これは固定した同じ q と同じ D の一つの Frobenius が有限局所像を生成する、今回の himage とは別の命題である。

既存 `ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime` と、その中で使う Mathlib の `Ideal.Quotient.stabilizerHom_surjective_of_profinite` も照合した。
前者は整数閉包の中心上の剰余作用を持ち上げる。全射性だけでは、今回の特定の有限作用核商 P_K が有限体 Galois 群へどう因子化するかをまだ供給しない。
今回の実装は、その欠けた因子化を hfactor として明示する条件付き橋と、既存密度からの供給経路を別々に用意した。
有限体 Galois 群の Frobenius 生成そのものは Mathlib の `bijective_frobeniusAlgEquivOfAlgebraic_pow` に基づき証明した。
外部の FLT 結論や未証明の密度・生成公理は import していない。
参照 HEAD・ソース・レビュー SHA-256 は `evidence/note032-finite-decomposition-image-reference-audit.json` に保存した。

## 残る算術と検証範囲

未完成: 同じ局所住所からの himage（または hdense / 実際の有限体因子化 hfactor）の供給、同じ v に対する hsign の算術的計算、全 G 上の係数と大域 Selmer/非分岐条件の照合、ω² 類群消滅 hclass、共鳴障害排除、無条件一般 hno。
非零 D 類の型は通常の群コホモロジー H¹(D,F) で、代表 cocycle の連続性を保持する。大域への逆向き制限や連続コホモロジーとの比較を新たに構成したとはしていない。

新規22宣言（abbrev・有限性/離散性 instance を含む）の再帰依存・公理・公開入力監査を通常入口へ追加した。
終点で himage と hsign が必須であり、hdense/hD/hz/hclass/hglobal/hselmer を新たな公開入力にしないことを確認する。
有限反例は Klein 四元群の一つの非零元が全群を生成しないことを第二座標で検査し、有限性だけから巡回生成を結論する誤りを防ぐ。
有限体拡大への具体的な特殊化と、厳密位数 p の値に対する符号の反例も検査する。
検証記録: `evidence/validation-note032-finite-decomposition-image.txt`。

## 教科書 Lean コード全文

### 1. DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.FieldTheory.Finite.Basic

#print "file: DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage"

/-! # 有限体拡大の実際の Frobenius による有界生成
元の付値環の剰余作用がこの有限体拡大へ因子化することは別の算術である。 -/
namespace DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
variable (k E : Type*) [Field k] [Fintype k] [Field E] [Algebra k E] [FiniteDimensional k E]

/-- 有限体拡大の各自己同型は、拡大次数未満の Frobenius 冪。 -/
theorem exists_bounded_power (σ : E ≃ₐ[k] E) :
    ∃ n : ℕ, n < Module.finrank k E ∧
      FiniteField.frobeniusAlgEquivOfAlgebraic k E ^ n = σ := by
  let := Module.finite_of_finite k (M := E)
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E).surjective σ
  exact ⟨n.val, n.isLt, hn⟩

/-- 有限体 Galois 作用に実際に因子化する表現の像は、対応する Frobenius の像の冪。 -/
theorem factor_image_bounded_power {G M : Type*} [Group G] [Monoid M]
    (π : G →* (E ≃ₐ[k] E)) (a : (E ≃ₐ[k] E) →* M)
    (φ : G) (hφ : π φ = FiniteField.frobeniusAlgEquivOfAlgebraic k E) (g : G) :
    ∃ n : ℕ, n < Module.finrank k E ∧ a (π g) = a (π φ) ^ n := by
  obtain ⟨n, hn, he⟩ := exists_bounded_power k E (π g)
  refine ⟨n, hn, ?_⟩
  rw [hφ, ← map_pow, he]
end DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
```

### 2. DkMath.FLT.FreyFiniteDecompositionAction

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseResonantLift
import Mathlib.Algebra.Group.Units.Hom

#print "file: DkMath.FLT.FreyFiniteDecompositionAction"

/-! # 元の K 作用の忠実な有限群像
元の作用を単元へ持ち上げ、同じ作用核で割る。巡回性は結論しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の群表現が値を取る、元の線形 endomorphism の単元。 -/
def ResidualCyclicStage.kernelDecompositionUnits :
    A.decompositionSubgroup ℚ →* (Module.End ℤ (T.fixedH1CoefficientKernel A))ˣ :=
  (T.kernelDecompositionAction A hp5 hq hqp haddr hA).toHomUnits

/-- 単元への持ち上げは作用核を変更しない。 -/
theorem ResidualCyclicStage.kernelDecompositionUnits_ker :
    (T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker = (T.kernelDecompositionAction A hp5 hq hqp haddr hA).ker := by
  ext σ
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

/-- 元の同じ K 作用の実際の群像を表す作用核商。 -/
abbrev ResidualCyclicStage.finiteDecompositionImage :=
  (A.decompositionSubgroup ℚ) ⧸ (T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker

/-- 元の同じ分解群から、その作用核商への標準射影。 -/
def ResidualCyclicStage.finiteDecompositionProjection :
    A.decompositionSubgroup ℚ →* T.finiteDecompositionImage A hp5 hq hqp haddr hA :=
  QuotientGroup.mk' _

/-- 作用核商は、元の線形自己同型の単元群に忠実に埋め込まれる。 -/
def ResidualCyclicStage.finiteDecompositionEmbedding :
    T.finiteDecompositionImage A hp5 hq hqp haddr hA →* (Module.End ℤ (T.fixedH1CoefficientKernel A))ˣ :=
  ((T.kernelDecompositionUnits A hp5 hq hqp haddr hA).range.subtype).comp (QuotientGroup.rangeKerLift (T.kernelDecompositionUnits A hp5 hq hqp haddr hA))

/-- 忠実性は同じ作用核による第一同型定理から従う。 -/
theorem ResidualCyclicStage.finiteDecompositionEmbedding_injective :
    Function.Injective (T.finiteDecompositionEmbedding A hp5 hq hqp haddr hA) :=
  Subtype.val_injective.comp (QuotientGroup.rangeKerLift_injective (T.kernelDecompositionUnits A hp5 hq hqp haddr hA))

/-- 実際の K は有限なので、その作用核商も有限。 -/
instance ResidualCyclicStage.finiteDecompositionImage_finite : Finite (T.finiteDecompositionImage A hp5 hq hqp haddr hA) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  let : Finite (Module.End ℤ (T.fixedH1CoefficientKernel A)) :=
    Finite.of_injective (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) =>
      (z : T.fixedH1CoefficientKernel A → T.fixedH1CoefficientKernel A)) DFunLike.coe_injective
  exact Finite.of_injective (T.finiteDecompositionEmbedding A hp5 hq hqp haddr hA) (T.finiteDecompositionEmbedding_injective A hp5 hq hqp haddr hA)
end
end DkMath.FLT.Frey.Source
```

### 3. DkMath.FLT.FreyOpenDecompositionActionKernel

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteDecompositionAction
import Mathlib.Topology.Algebra.Group.Quotient

#print "file: DkMath.FLT.FreyOpenDecompositionActionKernel"

/-! # 同じ γ の評価と有限性による作用核の開性
K に新たな位相を仮定せず、元の F 値連続軌道だけを用いる。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の K の各元を固定する条件は開集合でもある。 -/
theorem ResidualCyclicStage.kernelDecomposition_stabilizer_isOpen (k : T.fixedH1CoefficientKernel A) :
    IsOpen {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} := by
  have he : {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} =
      {σ | T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)
        (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
        T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k} := by
    ext σ
    exact T.kernel_fixed_iff_generator_evaluation A hp5 hq hqp haddr hA σ k
  rw [he]
  exact (isOpen_discrete {T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k}).preimage
    (T.kernelDecomposition_orbit_evaluation_continuous A hp5 hq hqp haddr hA k
      (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA))

/-- 同じ作用核は、有限個の元の開固定条件の共通部分。 -/
theorem ResidualCyclicStage.kernelDecompositionUnits_kernel_isOpen :
    IsOpen ((T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker : Set (A.decompositionSubgroup ℚ)) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  have he : ((T.kernelDecompositionUnits A hp5 hq hqp haddr hA).ker : Set (A.decompositionSubgroup ℚ)) =
      ⋂ k : T.fixedH1CoefficientKernel A,
        {σ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} := by
    ext σ
    simp only [Set.mem_iInter]
    change (T.kernelDecompositionUnits A hp5 hq hqp haddr hA) σ = 1 ↔
      ∀ k, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k
    constructor
    · intro h k
      exact congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) (congrArg Units.val h)
    · intro h
      apply Units.ext
      exact LinearMap.ext h
  rw [he]
  exact isOpen_iInter_of_finite (fun k => T.kernelDecomposition_stabilizer_isOpen A hp5 hq hqp haddr hA k)

/-- 同じ作用核商の元の商位相は離散。 -/
instance ResidualCyclicStage.finiteDecompositionImage_discrete :
    DiscreteTopology (T.finiteDecompositionImage A hp5 hq hqp haddr hA) :=
  QuotientGroup.discreteTopology (T.kernelDecompositionUnits_kernel_isOpen A hp5 hq hqp haddr hA)

/-- 元の同じ実際の慣性は、有限作用射影の核に入る。 -/
theorem ResidualCyclicStage.inertia_le_finiteDecompositionProjection_kernel :
    A.inertiaSubgroup ℚ ≤ (T.finiteDecompositionProjection A hp5 hq hqp haddr hA).ker := by
  intro σ hσ
  apply (QuotientGroup.eq_one_iff σ).mpr
  rw [T.kernelDecompositionUnits_ker A hp5 hq hqp haddr hA]
  exact T.inertia_le_kernelDecomposition_kernel A hp5 hq hqp haddr hA hσ
end
end DkMath.FLT.Frey.Source
```

### 4. DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration"

/-! # 明示的な密度から離散有限群像の Frobenius 生成へ -/
namespace DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H]

/-- 慣性 N を消す連続離散群像は、明示密度の下で φ の像で生成される。 -/
theorem mem_zpowers_of_dense (ρ : G →* H) (hρ : Continuous ρ) (N : Subgroup G)
    (hN : N ≤ ρ.ker) (φ : G)
    (hdense : (N ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) (g : G) :
    ρ g ∈ Subgroup.zpowers (ρ φ) := by
  let J := (Subgroup.zpowers (ρ φ)).comap ρ
  have hj : IsClosed (J : Set G) := by
    change IsClosed (ρ ⁻¹' (Subgroup.zpowers (ρ φ) : Set H))
    exact (isClosed_discrete _).preimage hρ
  have ht := ClosedFixedSubgroup.eq_top_of_dense_join N J φ hj
    (fun σ hσ => by change ρ σ ∈ Subgroup.zpowers (ρ φ); rw [show ρ σ = 1 from hN hσ]; exact Subgroup.one_mem _)
    (Subgroup.mem_zpowers (ρ φ)) hdense
  change g ∈ J
  rw [ht]
  exact Subgroup.mem_top g

omit [TopologicalSpace H] [DiscreteTopology H] in
/-- 有限群での一元生成は、元の Frobenius の位数未満の自然数冪で証明できる。 -/
theorem bounded_power_of_mem_zpowers [Finite H] (a b : H) (hb : b ∈ Subgroup.zpowers a) :
    ∃ n : ℕ, n < orderOf a ∧ a ^ n = b := by
  have hp : b ∈ Submonoid.powers a := mem_powers_iff_mem_zpowers.mpr hb
  obtain ⟨m, hm⟩ := hp
  exact ⟨m % orderOf a, Nat.mod_lt _ (orderOf_pos a), (pow_mod_orderOf a m).trans hm⟩
end DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration
```

### 5. DkMath.FLT.FreyFiniteFrobeniusImage

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyOpenDecompositionActionKernel
import DkMath.Lib.NumberTheory.FiniteFieldFrobeniusImage
import DkMath.Lib.RepresentationTheory.DenseFiniteImageGeneration

#print "file: DkMath.FLT.FreyFiniteFrobeniusImage"

/-! # 実際の有限作用像を Frobenius が生成するための二つの供給経路
密度または有限体 Galois 因子化は明示条件。元の住所からの無条件供給は未完成。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 元の密度入力は、必要な有限作用像の生成条件を供給する。 -/
theorem ResidualCyclicStage.finiteDecomposition_generated_of_dense
    (φ : A.decompositionSubgroup ℚ)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) :=
  DenseFiniteImageGeneration.mem_zpowers_of_dense (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) QuotientGroup.continuous_mk
    (A.inertiaSubgroup ℚ) (T.inertia_le_finiteDecompositionProjection_kernel A hp5 hq hqp haddr hA) φ hdense

/-- 有限体 Galois 作用を通じた実際の因子化があれば、密度を経由せず同じ有限像の生成を得る。 -/
theorem ResidualCyclicStage.finiteDecomposition_generated_of_field_factor
    (k E : Type*) [Field k] [Fintype k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (π : A.decompositionSubgroup ℚ →* (E ≃ₐ[k] E))
    (a : (E ≃ₐ[k] E) →* T.finiteDecompositionImage A hp5 hq hqp haddr hA)
    (hfactor : (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) = a.comp π)
    (φ : A.decompositionSubgroup ℚ)
    (hφ : π φ = FiniteField.frobeniusAlgEquivOfAlgebraic k E) :
    ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) := by
  intro σ
  obtain ⟨m, _, hm⟩ := FiniteFieldFrobeniusImage.factor_image_bounded_power k E π a φ hφ σ
  rw [hfactor]
  change a (π σ) ∈ Subgroup.zpowers (a (π φ))
  rw [hm]
  exact Subgroup.npow_mem_zpowers _ _

/-- 同じ有限像の生成条件は、元の線形作用そのものの有界な冪等式を供給する。 -/
theorem ResidualCyclicStage.finiteDecomposition_bounded_action_power
    (φ : A.decompositionSubgroup ℚ) (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ)) (σ : A.decompositionSubgroup ℚ) :
    ∃ m : ℕ, m < orderOf ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) ∧ T.kernelDecompositionAction A hp5 hq hqp haddr hA σ = (T.kernelDecompositionAction A hp5 hq hqp haddr hA φ) ^ m := by
  obtain ⟨m, hm, he⟩ := DenseFiniteImageGeneration.bounded_power_of_mem_zpowers
    ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ) ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ) (himage σ)
  have hu := congrArg (T.finiteDecompositionEmbedding A hp5 hq hqp haddr hA) he
  rw [map_pow] at hu
  have hv := congrArg Units.val hu
  exact ⟨m, hm, hv.symm⟩
end
end DkMath.FLT.Frey.Source
```

### 6. DkMath.FLT.FreyFiniteImageFixedCriterion

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteFrobeniusImage

#print "file: DkMath.FLT.FreyFiniteImageFixedCriterion"

/-! # 有限作用像の生成だけから同じ k の D 固定性へ
D 全体の密度を入力にしない。有限像の生成自体の算術的供給は別工程。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- 同じ有限作用像が生成されれば、φ 固定性から全 D 固定性が従う。 -/
theorem ResidualCyclicStage.kernel_fixed_of_finite_image
    (φ : A.decompositionSubgroup ℚ) (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ))
    (k : T.fixedH1CoefficientKernel A) (hfixed : T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k) :
    ∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k := by
  let f : Module.End ℤ (T.fixedH1CoefficientKernel A) := T.kernelDecompositionAction A hp5 hq hqp haddr hA φ
  have hp : ∀ m : ℕ, (f ^ m) k = k := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      calc (f ^ (m + 1)) k = (f ^ m) (f k) :=
            congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) (pow_succ f m)
        _ = (f ^ m) k := congrArg (fun z : T.fixedH1CoefficientKernel A => (f ^ m) z) hfixed
        _ = k := ih
  intro σ
  obtain ⟨m, _, hm⟩ := T.finiteDecomposition_bounded_action_power A hp5 hq hqp haddr hA φ himage σ
  exact (congrArg (fun z : Module.End ℤ (T.fixedH1CoefficientKernel A) => z k) hm).trans (hp m)

/-- 有限像生成の下で、全 D 固定性を同じ γ の固有値で判定する。 -/
theorem ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_finite_image
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 hq hqp haddr hA) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 hq hqp haddr hA) φ)) (k : T.fixedH1CoefficientKernel A) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  (show (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔ T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k from
    ⟨fun h => h φ, T.kernel_fixed_of_finite_image A hp5 hq hqp haddr hA φ himage k⟩).trans
      (T.kernelFrobenius_fixed_iff A hp5 hq hqp haddr hA φ hφ k)
end
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 有限像生成の下で、元の共鳴符号条件は同じ障害核元の hD と同値。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_finite_image
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) φ)) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over σ k = k) ↔ ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) := by
  have he := T.decomposition_fixed_iff_eigenvalue_of_finite_image A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over φ hφ himage (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)
  constructor
  · intro hD
    have hv := he.mp hD
    rcases h.resonance with hplus | hminus
    · exact Or.inl ⟨hplus, hv.trans (h.generatorValue_q_smul_plus hp5 hplus)⟩
    · exact Or.inr ⟨hminus, hv.trans (h.generatorValue_q_smul_minus hp5 hminus)⟩
  · intro hs
    apply he.mpr
    rcases hs with ⟨hplus, hv⟩ | ⟨hminus, hv⟩
    · exact hv.trans (h.generatorValue_q_smul_plus hp5 hplus).symm
    · exact hv.trans (h.generatorValue_q_smul_minus hp5 hminus).symm
end
end DkMath.FLT.Frey.Source
```

### 7. DkMath.FLT.FreyFiniteImageResonantLift

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteImageFixedCriterion

#print "file: DkMath.FLT.FreyFiniteImageResonantLift"

/-! # 同じ有限作用像の生成と共鳴符号から非零 D 類へ
himage と hsign は明示入力。有限性・開性だけで巡回性を結論しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 全 D の密度を入力とせず、同じ有限像の生成と符号から元の非零 D 類を構成する。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_finite_image_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (himage : ∀ σ : A.decompositionSubgroup ℚ, (T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) σ ∈ Subgroup.zpowers ((T.finiteDecompositionProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) φ))
    (hsign : let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v)) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ => (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) = (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 :=
  h.decomposition_lift_of_kernel_fixed hp5
    ((h.decomposition_fixed_iff_resonant_sign_of_finite_image hp5 φ hφ himage).mpr hsign)
end
end DkMath.FLT.Frey.Source
```

