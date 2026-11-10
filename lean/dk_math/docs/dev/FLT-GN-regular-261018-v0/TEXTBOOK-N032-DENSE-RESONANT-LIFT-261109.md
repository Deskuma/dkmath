# NOTE-032 教科書 — 閉安定化群・Frobenius 選択不変性・密度と符号からの D 持ち上げ

2026-11-09。最新レビューを参照し、7ステップ・20宣言を実装した。
汎用の2モジュールを Lib、元の Frey Source に特殊化する5モジュールを FLT に置いた。
末尾の全7 Lean ブロックは production の全文で、各 import 群直後の必須 `#print "file: 正確なモジュール名"` を保持する。
既存 DkMath の Lake 環境で各ブロックを別ファイルとして検査できる。

## 同じ対象と入力

D は同じ付値環 A の分解群、I_D は D 内の元の慣性、I は従来の全 Galois 群内の慣性像。
Q は元の上位有限捩れ商、F=Q^I、E=Q/F、K=ker(H¹(I,F)→H¹(I,Q))。
δ:E≃K と元の点 x からの k_x=δ(z_x)、同じ γ の評価値 v=ev_γ(k_x) を保持する。

今回の明示的入力は

    hdense : (I_D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤
    hsign  : (q≡1 mod p ∧ φ_F(v)=v) ∨ (q≡−1 mod p ∧ φ_F(v)=−v)

である。hdense は全 D 内の実際の部分群について述べる。
これらから

    hD : ∀σ∈D, σ_K k_x=k_x

を内部で導き、前回と同じ連続 cocycle の持ち上げを得る。
**実際の hdense/hsign の算術的供給は未完成。hD を公開入力から除いたことは、無条件の hD や無条件 hno の証明を意味しない。**

## 1. 閉部分群と密度の汎用補題

N と φ を含む閉部分群 H は、(N⊔⟨φ⟩) の位相閉包が全群なら全群となる。線形表現の元 m の安定化群を構成し、固定性へ特殊化する。さらに φ/ψ∈N なら N⊔⟨φ⟩=N⊔⟨ψ⟩ を、N の正規性なしで証明する。密度自体は明示的入力である。

## 2. 元の K の閉安定化部分群

前回の閉固定集合を、同じ線形 K 表現の安定化部分群として構成する。既存の単一 γ 評価による閉性と、元の慣性が表現の核に入る事実を接続する。K 全体に新たな位相を仮定しない。

## 3. 同じ一元固定性から全 D 固定性へ

実際の N=A.inertiaSubgroup ℚ と同じ D 元 φ について、密度と φ_K k=k から ∀σ∈D, σ_K k=k を証明する。逆向きは φ への特殊化で、密度の下で iff となる。この段階は任意の φ を扱い、Frobenius の算術は不要。

## 4. 二つの実際の Frobenius の差を慣性で検出

全剰余体上の同じ q 乗作用を与える二つの実際の持ち上げ φ,ψ は、元の剰余自己同型として一致する。慣性がその作用の核であることから φ/ψ∈I_D を証明する。新しい巡回性や密度を仮定しない。K,L は一般の体を許す。

## 5. 持ち上げによらない同じ係数作用・密度条件

同じ実際の D/I_D の剰余類の一致を使い、F、E=Q/F、K 上の Frobenius 作用が一致することを証明する。さらに I_D⊔⟨φ⟩=I_D⊔⟨ψ⟩ なので、それらの密度条件も同値となる。密度が成立するという結論は出していない。

## 6. 同じ γ の固有値・共鳴符号による hD 判定

密度の下で、全 D 固定性と φ_F(ev_γ(k))=q•ev_γ(k) を同値化する。同じ障害核元 k_x の厳密位数 p の評価値 v を使い、共鳴分岐ごとの実際の符号条件と hD が同値であることを証明する。密度が hD から逆に従うとは述べない。

## 7. 明示的な密度・符号から元の非零 D 類へ

終点 decomposition_lift_of_dense_sign は hdense と hsign から hD を内部供給し、既存の decomposition_lift_of_kernel_fixed を消費する。得るものは同じ F 値の連続 D cocycle、その通常 H¹ 類の非零性、元の同じ慣性障害類への制限一致。hD を新たな公開入力にせず、より具体的な未解決入力 hdense と hsign を保持する。

## 模範解答・一次ソースとの照合

模範 `P2M/Sol/S_ValuationSubring_exists_isFrobeniusAt_pow_of_isDiscreteValuationRing.lean` の剰余作用・有限剰余体からの持ち上げ・最終 solution を確認した。
その結論は有限中間体を固定する Frobenius の冪の存在であり、任意の D 元の Frobenius と慣性による近似という今回必要な密度を、そのまま供給するものではない。
DkMath では既存の IsFrobeniusAt の全剰余体上の作用を直接消費し、二つの持ち上げの商が慣性に入ることを証明した。
閉部分群の処理は Mathlib の `Subgroup.topologicalClosure_minimal` と `Subgroup.zpowers_le` に基づく。
外部の結論や未証明の密度 provider は import していない。
参照 HEAD とソース・レビュー SHA-256 は `evidence/note032-dense-resonant-lift-reference-audit.json` に記録した。

## 完了範囲と残る算術

完了したのは、実際の同じ安定化群への位相的橋、Frobenius 持ち上げの選択不変性、および密度と符号から同じ非零 D 類への条件付き接続である。
未完成: 実際の剰余 Galois 作用から hdense を導く算術、同じ Frey 曲線の v に対する hsign の計算、全 G 上の係数と大域 Selmer/非分岐条件の照合、ω² 類群消滅 hclass、共鳴障害排除、無条件一般 hno。
得られる類の型は通常の群コホモロジー H¹(D,F)。その代表 cocycle の連続性を証明している。
H¹(D,F) から大域 H¹(G,F) への写像を構成したとはしていない。

新規20宣言の再帰依存・標準公理監査と公開入力監査を通常入口へ追加した。
終点では hdense と hsign を必須入力とし、hD/hz/hclass/hglobal/hselmer を新たな公開入力にしていないことを確認する。
有限反例は、閉部分群が φ を含むだけでは全群にならないことと、厳密位数 p の元に対する任意の作用が符号条件を満たすとは限らないことを示す。
検証記録: `evidence/validation-note032-dense-resonant-lift.txt`。

## 教科書 Lean コード全文

### 1. DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Topology.Algebra.Group.Subgroup
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

#print "file: DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup"

/-! # 閉固定部分群と、指定部分群・一元が生成する稠密部分群
密度は明示入力。特定の算術的 Frobenius の密度を供給しない。 -/
namespace DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- N と φ を含む閉部分群は、それらの生成群が稠密なら全体である。 -/
theorem eq_top_of_dense_join (N H : Subgroup G) (φ : G)
    (hclosed : IsClosed (H : Set G)) (hN : N ≤ H) (hφ : φ ∈ H)
    (hdense : (N ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) : H = ⊤ := by
  apply top_unique
  rw [← hdense]
  exact Subgroup.topologicalClosure_minimal _ (sup_le hN (Subgroup.zpowers_le.mpr hφ)) hclosed

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- 同じ N の剰余類に属する元は、N と併せて同じ部分群を生成する。 -/
theorem join_zpowers_eq_of_div_mem (N : Subgroup G) {φ ψ : G} (h : φ / ψ ∈ N) :
    N ⊔ Subgroup.zpowers φ = N ⊔ Subgroup.zpowers ψ := by
  have hφ : φ ∈ N ⊔ Subgroup.zpowers ψ := by
    have hm := (N ⊔ Subgroup.zpowers ψ).mul_mem
      ((le_sup_left : N ≤ N ⊔ Subgroup.zpowers ψ) h)
      ((le_sup_right : Subgroup.zpowers ψ ≤ N ⊔ Subgroup.zpowers ψ) (Subgroup.mem_zpowers ψ))
    simpa only [div_mul_cancel] using hm
  have hi : ψ / φ ∈ N := by simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv] using N.inv_mem h
  have hψ : ψ ∈ N ⊔ Subgroup.zpowers φ := by
    have hm := (N ⊔ Subgroup.zpowers φ).mul_mem
      ((le_sup_left : N ≤ N ⊔ Subgroup.zpowers φ) hi)
      ((le_sup_right : Subgroup.zpowers φ ≤ N ⊔ Subgroup.zpowers φ) (Subgroup.mem_zpowers φ))
    simpa only [div_mul_cancel] using hm
  exact le_antisymm (sup_le le_sup_left (Subgroup.zpowers_le.mpr hφ))
    (sup_le le_sup_left (Subgroup.zpowers_le.mpr hψ))

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- 線形表現の一元を固定する元は部分群をなす。 -/
def linearStabilizer (ρ : G →* Module.End R M) (m : M) : Subgroup G where
  carrier := {g | ρ g m = m}
  one_mem' := by change ρ 1 m = m; rw [map_one]; rfl
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) m = m
    rw [map_mul]
    change ρ g (ρ h m) = m
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    have he := congrArg (fun f : Module.End R M => f m) (ρ.map_mul g⁻¹ g)
    change ρ (g⁻¹ * g) m = ρ g⁻¹ (ρ g m) at he
    rw [inv_mul_cancel, map_one] at he
    change m = ρ g⁻¹ (ρ g m) at he
    rw [hg] at he
    exact he.symm

/-- 閉固定条件と明示的密度から、同じ元の全群固定性を得る。 -/
theorem fixed_of_dense_join (ρ : G →* Module.End R M) (m : M) (N : Subgroup G) (φ : G)
    (hclosed : IsClosed {g : G | ρ g m = m})
    (hN : N ≤ ρ.ker) (hφ : ρ φ m = m)
    (hdense : (N ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) : ∀ g, ρ g m = m := by
  have ht := eq_top_of_dense_join N (linearStabilizer ρ m) φ hclosed
    (fun g hg => by change ρ g m = m; rw [show ρ g = 1 from hN hg]; rfl) hφ hdense
  intro g
  change g ∈ linearStabilizer ρ m
  rw [ht]
  exact Subgroup.mem_top g
end DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup
```

### 2. DkMath.FLT.FreyClosedKernelStabilizer

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResonantDecompositionLift
import DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup

#print "file: DkMath.FLT.FreyClosedKernelStabilizer"

/-! # 同じ実際の K の閉安定化部分群 -/
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

/-- 元の K 表現の、元 k の安定化部分群。 -/
def ResidualCyclicStage.kernelClosedStabilizer (k : T.fixedH1CoefficientKernel A) :
    Subgroup (A.decompositionSubgroup ℚ) :=
  ClosedFixedSubgroup.linearStabilizer (T.kernelDecompositionAction A hp5 hq hqp haddr hA) k

/-- 安定化群の閉性は、元の同じ γ の単射評価から得た閉固定条件そのもの。 -/
theorem ResidualCyclicStage.kernelClosedStabilizer_isClosed (k : T.fixedH1CoefficientKernel A) :
    IsClosed (T.kernelClosedStabilizer A hp5 hq hqp haddr hA k : Set (A.decompositionSubgroup ℚ)) :=
  T.kernelDecomposition_stabilizer_isClosed A hp5 hq hqp haddr hA k

/-- 元の実際の慣性群は各 k の安定化群に入る。 -/
theorem ResidualCyclicStage.inertia_le_kernelClosedStabilizer (k : T.fixedH1CoefficientKernel A) :
    A.inertiaSubgroup ℚ ≤ T.kernelClosedStabilizer A hp5 hq hqp haddr hA k := by
  intro σ hσ
  change T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k
  rw [show T.kernelDecompositionAction A hp5 hq hqp haddr hA σ = 1 from
    T.inertia_le_kernelDecomposition_kernel A hp5 hq hqp haddr hA hσ]
  rfl
end
end DkMath.FLT.Frey.Source
```

### 3. DkMath.FLT.FreyDenseKernelFixed

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyClosedKernelStabilizer

#print "file: DkMath.FLT.FreyDenseKernelFixed"

/-! # 明示的な密度の下で、同じ核元の一元固定性から D 全体の固定性へ -/
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

/-- 密度条件の下で、同じ元の φ 固定性が hD を供給する。 -/
theorem ResidualCyclicStage.kernel_fixed_of_dense_join
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hfixed : T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k) :
    ∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k := by
  have ht := ClosedFixedSubgroup.eq_top_of_dense_join (A.inertiaSubgroup ℚ)
    (T.kernelClosedStabilizer A hp5 hq hqp haddr hA k) φ
    (T.kernelClosedStabilizer_isClosed A hp5 hq hqp haddr hA k)
    (T.inertia_le_kernelClosedStabilizer A hp5 hq hqp haddr hA k) hfixed hdense
  intro σ
  change σ ∈ T.kernelClosedStabilizer A hp5 hq hqp haddr hA k
  rw [ht]
  exact Subgroup.mem_top σ

/-- 同じ密度入力の下で全 D 固定性は φ 固定性と同値。 -/
theorem ResidualCyclicStage.kernel_fixed_iff_of_dense_join
    (φ : A.decompositionSubgroup ℚ) (k : T.fixedH1CoefficientKernel A)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.kernelDecompositionAction A hp5 hq hqp haddr hA φ k = k :=
  ⟨fun h => h φ, T.kernel_fixed_of_dense_join A hp5 hq hqp haddr hA φ k hdense⟩
end
end DkMath.FLT.Frey.Source
```

### 4. DkMath.Lib.NumberTheory.FrobeniusInertiaCoset

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationFrobenius

#print "file: DkMath.Lib.NumberTheory.FrobeniusInertiaCoset"

/-! # 同じ剰余 Frobenius を持つ二つの持ち上げの差は、元の慣性に入る -/
namespace DkMath.Lib.NumberTheory.ValuationFrobenius
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {q : ℕ}

/-- 同じ全剰余体上の Frobenius 作用を持つ元は、同じ剰余自己同型を与える。 -/
theorem residue_action_eq_of_frobenius (φ ψ : A.decompositionSubgroup K)
    (hφ : IsFrobeniusAt A φ.val q) (hψ : IsFrobeniusAt A ψ.val q) :
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) φ =
      MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) ψ := by
  apply RingEquiv.ext
  intro x
  exact (hφ.smul_residue_eq x).trans (hψ.smul_residue_eq x).symm

/-- 二つの実際の Frobenius 持ち上げの商は、元の分解群内の慣性に属する。 -/
theorem frobenius_div_mem_inertia (φ ψ : A.decompositionSubgroup K)
    (hφ : IsFrobeniusAt A φ.val q) (hψ : IsFrobeniusAt A ψ.val q) :
    φ / ψ ∈ A.inertiaSubgroup K := by
  change MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A) (φ / ψ) = 1
  rw [map_div, residue_action_eq_of_frobenius A φ ψ hφ hψ, div_self']
end DkMath.Lib.NumberTheory.ValuationFrobenius
```

### 5. DkMath.FLT.FreyFrobeniusLiftIndependence

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseKernelFixed
import DkMath.Lib.NumberTheory.FrobeniusInertiaCoset

#print "file: DkMath.FLT.FreyFrobeniusLiftIndependence"

/-! # 実際の Frobenius 持ち上げの選択に依存しない作用と密度条件 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
variable (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ}

/-- 二つの同じ q-Frobenius は元の D/I の同じ元を与える。 -/
theorem frobeniusResidueCoset_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    (φ : (A.decompositionSubgroup ℚ) ⧸ A.inertiaSubgroup ℚ) = ψ :=
  QuotientGroup.eq_iff_div_mem.mpr (ValuationFrobenius.frobenius_div_mem_inertia A φ ψ hφ hψ)

/-- 慣性と Frobenius が生成する元の部分群も、持ち上げによらない。 -/
theorem frobeniusInertiaJoin_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ = A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers ψ :=
  DkMath.Lib.RepresentationTheory.ClosedFixedSubgroup.join_zpowers_eq_of_div_mem _
    (ValuationFrobenius.frobenius_div_mem_inertia A φ ψ hφ hψ)

/-- 密度自体は明示条件だが、その条件は実際の Frobenius の選択によらない。 -/
theorem frobeniusInertia_dense_iff (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    ((A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) ↔
      ((A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers ψ).topologicalClosure = ⊤) := by
  rw [frobeniusInertiaJoin_eq A φ ψ hφ hψ]
end DkMath.FLT.Frey.Source
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

/-- 元の同じ F 上の作用は Frobenius の持ち上げの選択によらない。 -/
theorem ResidualCyclicStage.fixedFrobenius_action_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    T.fixedDecompositionAction A φ = T.fixedDecompositionAction A ψ :=
  congrArg (T.fixedResidueAction A) (frobeniusResidueCoset_eq A φ ψ hφ hψ)

include hp5 hq hqp haddr hA
/-- 元の同じ E=Q/F 上の作用も選択によらない。 -/
theorem ResidualCyclicStage.quotientFrobenius_action_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    T.quotientDecompositionAction A φ = T.quotientDecompositionAction A ψ :=
  congrArg (T.quotientResidueAction A hp5 hq hqp haddr hA) (frobeniusResidueCoset_eq A φ ψ hφ hψ)

/-- 元の同じ K 上の作用も選択によらない。 -/
theorem ResidualCyclicStage.kernelFrobenius_action_eq (φ ψ : A.decompositionSubgroup ℚ)
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hψ : ValuationFrobenius.IsFrobeniusAt A ψ.val q) :
    T.kernelDecompositionAction A hp5 hq hqp haddr hA φ = T.kernelDecompositionAction A hp5 hq hqp haddr hA ψ :=
  congrArg (T.kernelResidueAction A hp5 hq hqp haddr hA) (frobeniusResidueCoset_eq A φ ψ hφ hψ)
end
end DkMath.FLT.Frey.Source
```

### 6. DkMath.FLT.FreyDenseResonantFixed

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFrobeniusLiftIndependence

#print "file: DkMath.FLT.FreyDenseResonantFixed"

/-! # 密度と同じ γ の値から hD を供給する正確な同値条件
密度・固有値の算術的証明はここでは与えない。 -/
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

/-- 密度の下で、元の任意の核元の全 D 固定性を同じ γ の固有値で判定する。 -/
theorem ResidualCyclicStage.decomposition_fixed_iff_eigenvalue_of_dense
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (k : T.fixedH1CoefficientKernel A)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    (∀ σ, T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k) ↔
      T.fixedDecompositionAction A φ
        (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k) =
      q • T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k :=
  (T.kernel_fixed_iff_of_dense_join A hp5 hq hqp haddr hA φ k hdense).trans
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

/-- 明示した密度の下で、共鳴二分岐の正しい符号は同じ障害核元の hD と同値。 -/
theorem NarrowAbsorptionObstruction.decomposition_fixed_iff_resonant_sign_of_dense
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    (∀ σ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over σ k = k) ↔
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v) := by
  have he := T.decomposition_fixed_iff_eigenvalue_of_dense A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over φ hφ (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) hdense
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

### 7. DkMath.FLT.FreyDenseResonantLift

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDenseResonantFixed

#print "file: DkMath.FLT.FreyDenseResonantLift"

/-! # 密度・共鳴符号から同じ非零 D 類へ
hD を新たな公開入力とせず、明示した hdense と hsign から内部供給する。
実際の hdense/hsign は算術的未解決入力として保持する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 密度と実際の符号等式から、元の点を変えずに非零連続 D cocycle を得る。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_dense_sign
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q)
    (hdense : (A.inertiaSubgroup ℚ ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hsign : let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
      ((q : ZMod p) = 1 ∧ T.fixedDecompositionAction A φ v = v) ∨
      ((q : ZMod p) = -1 ∧ T.fixedDecompositionAction A φ v = -v)) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ => (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) = (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 := by
  exact h.decomposition_lift_of_kernel_fixed hp5
    ((h.decomposition_fixed_iff_resonant_sign_of_dense hp5 φ hφ hdense).mpr hsign)
end
end DkMath.FLT.Frey.Source
```

