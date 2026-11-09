# NOTE-032 教科書 — 共鳴符号と同じ障害類の条件付き D 持ち上げ

2026-11-09。最新レビューを参考に、元の Source、点、係数、生成元、連結写像を保持して7ステップ実装した。
全7モジュールの Lean 全文を末尾に収録し、各 import 群直後の必須 `#print "file: 正確なモジュール名"` を保持する。
既存 DkMath の Lake 環境で、各ブロックを別ファイルとしてコピーし検査できる。

D は同じ付値環 A の分解群、I は元の実際の慣性群、Q は上位有限捩れ商、F=Q^I、E=Q/F、K=ker(H¹(I,F)→H¹(I,Q))。
既存の δ:E≃K と k_x=δ(z_x)、v=ev_γ(k_x) を引き続き使用する。

**完成したのは、符号による iff 判定と、明示的な D 不変性の下での実際の連続 F 値 D cocycle の構成・制限の一致である。D 不変性の算術的供給および無条件一般 hno は未完成。**

## 1. 同じ障害値の厳密位数

元の核元 k_x の厳密位数 p と、同じ具体的慣性生成元 γ の評価の単射性から、v=ev_γ(k_x) の厳密位数 p を証明する。F 全体を p で消える係数と仮定せず、この v に限って自然数倍を mod p で簡約する。

## 2. 共鳴二分岐の符号条件

q≡1 mod p なら q•v=v、q≡−1 mod p なら q•v=−v。同じ Frobenius 判定を φ_K k_x=k_x ↔ φ_F(v)=±v に簡約する。右辺の符号等式自体は証明していない。

## 3. 元の位相での軌道連続性と閉固定条件

F は元の Q の部分空間位相、Q/F は元の商位相を保持する。Rep の台集合の別名へ同じ位相を明示的に移す。D 軌道と評価後の K 軌道の連続性、k の D 固定条件が閉集合であることを証明する。D/I の Frobenius による稠密生成は供給しない。

## 4. 実際の D 上の同じ短完全列

元の F の D 安定性と元の Q/F 作用を使い、0→F→Q→Q/F→0 を D 上で構成する。包含・射影は元の部分群包含と mkQ。ModuleCat へ忘却して核・像、単射・全射を証明する。F の全 G 安定性を導入しない。

## 5. D 不変商類から連続 cocycle と連結像

元の同じ点 x の商類が D 不変という明示条件 hz の下で c_D(σ)=σ[x]−[x]∈F を構成する。cocycle 恒等式、元の F 位相での連続性、通常群コホモロジーで [c_D]=δ_D(z) を証明する。連続コホモロジー自体の新理論とはしていない。

## 6. 実際の群包含による元の I 類への制限

元の慣性群 I から D への包含、F 係数の射、通常 H¹ の制限を構成する。c_D の制限が既存の同じ連続慣性 cocycle と一致し、その類が同じ k_x.val となることを証明する。類の型が似ているだけの比較ではない。

## 7. 同じ障害への符号証明書と条件付き持ち上げ

元の住所から実際の Frobenius を内部選択し、同じ v の厳密位数 p と二分岐の iff をまとめる。さらに同じ障害核元の D 不変性 hD を入力とする場合に、その商類の hz を既存 δ の同変性から得て c_D を構成する。制限が非零 k_x.val なので [c_D]≠0。hD は結論ではなく未供給の入力である。

## 模範解答との照合と未解決境界

模範 `P2M/Sol/S_groupCohomology_map_delta_eq_delta_map.lean` を読み、群・係数の射と短完全列を通じた連結写像の自然性を照合した。
今回の DkMath は一般の高次数自然性を移植せず、同じ元の δ₀ と明示的な作用差 cocycle の一致、その実際の I⊆D に沿う制限を証明する。
外部定理の import は追加していない。参照 HEAD・ソース・レビューの SHA-256 は証跡に保存した。

残るものは、実際の φ_F(v)=±v の算術的証明、Frobenius の D/I 位相的生成性と固定性への接続、D 不変性 hD の供給、全 G 上の F 係数と Selmer/非分岐条件の照合、ω² 類群消滅 hclass の算術的供給、共鳴障害排除と無条件一般 hno。
閉固定集合と連続性だけで稠密性を結論しない。D 上の条件付き持ち上げを F 値大域 Selmer 類と同一視しない。

新規33宣言（位相 instance・abbrev を含む）の再帰依存・標準公理監査と公開入力監査を通常入口へ追加した。
入力監査は条件付き構成の hz と終点の hD を必須として検査し、これらを消去したという主張を防ぐ。
検証記録: `evidence/validation-note032-resonant-decomposition-lift.txt`。

## 教科書 Lean コード全文

### 1. DkMath.FLT.FreyPrimeOrderGeneratorValue

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionInvariantObstruction

#print "file: DkMath.FLT.FreyPrimeOrderGeneratorValue"

/-! # 同じ具体的生成元での実際の障害値の厳密位数 p
F 全体を p で消えると仮定せず、元の同じ障害核元の位数を輸送する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 単一評価の単射性により、同じ障害値は厳密位数 p を持つ。 -/
theorem NarrowAbsorptionObstruction.generatorValue_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    addOrderOf (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k) = p := by
  exact (addOrderOf_injective (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)).toAddMonoidHom
    (T.generator_evaluation_injective A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) _).trans
      (h.fixedKernel_order_eq_prime hp5)

/-- 同じ障害値への自然数倍は、その整数を p で還元しても同じ。 -/
theorem NarrowAbsorptionObstruction.generatorValue_nsmul_mod
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (m : ℕ) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    m • v = (m % p) • v := by
  have he := mod_addOrderOf_nsmul
    (T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)) m
  rw [h.generatorValue_order_eq_prime hp5] at he
  exact he.symm
end
end DkMath.FLT.Frey.Source

```

### 2. DkMath.FLT.FreyResonantFrobeniusSigns

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeOrderGeneratorValue

#print "file: DkMath.FLT.FreyResonantFrobeniusSigns"

/-! # 実際の位数 p の障害値に限った共鳴符号
F 全体の作用や Frobenius 固有値を決定したとは主張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- q≡1 mod p なら同じ障害値の q 倍は元の値。 -/
theorem NarrowAbsorptionObstruction.generatorValue_q_smul_plus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hq1 : (q : ZMod p) = 1) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    q • v = v := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hmod : q % p = 1 := by
    have hv := congrArg ZMod.val hq1
    simpa only [ZMod.val_natCast, ZMod.val_one, Nat.mod_eq_of_lt hp] using hv
  exact (h.generatorValue_nsmul_mod hp5 q).trans
    ((congrArg (fun m : ℕ => m • T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)) hmod).trans (one_nsmul _))

/-- q≡-1 mod p なら同じ障害値の q 倍は負の値。 -/
theorem NarrowAbsorptionObstruction.generatorValue_q_smul_minus
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (hqneg : (q : ZMod p) = -1) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    q • v = -v := by
  let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over)
    (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩)
  have hmod : (q + 1) % p = 0 := by
    have hz : ((q + 1 : ℕ) : ZMod p) = 0 := by push_cast; rw [hqneg]; simp
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  have hz : (q + 1) • v = 0 := by
    rw [h.generatorValue_nsmul_mod hp5 (q + 1), hmod, zero_nsmul]
  rw [add_nsmul, one_nsmul] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- 同じ障害値の Frobenius 固定性を、元の二つの共鳴枝で正確に判定する。 -/
theorem NarrowAbsorptionObstruction.frobenius_fixed_resonant_signs
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (φ : A.decompositionSubgroup ℚ) (hφ : ValuationFrobenius.IsFrobeniusAt A φ.val q) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    ((q : ZMod p) = 1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
      T.fixedDecompositionAction A φ v = v)) ∨
    ((q : ZMod p) = -1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
      T.fixedDecompositionAction A φ v = -v)) := by
  have he := h.frobenius_fixed_criterion hp5 φ hφ
  rcases h.resonance with hq1 | hqneg
  · refine Or.inl ⟨hq1, ?_⟩
    simpa only [h.generatorValue_q_smul_plus hp5 hq1] using he
  · refine Or.inr ⟨hqneg, ?_⟩
    simpa only [h.generatorValue_q_smul_minus hp5 hqneg] using he
end
end DkMath.FLT.Frey.Source

```

### 3. DkMath.FLT.FreyDecompositionOrbitContinuity

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyResonantFrobeniusSigns

#print "file: DkMath.FLT.FreyDecompositionOrbitContinuity"

/-! # 元の有限係数 F,Q/F,K の D 軌道の連続性
Frobenius の位相的生成性はここでは供給しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の Q の商位相を、同じ慣性表現の台集合に保持する。 -/
instance ResidualCyclicStage.fullInertiaCoefficientTopology : TopologicalSpace (T.fullInertiaCoefficient A) :=
  inferInstanceAs (TopologicalSpace T.upperQuotient)

/-- 元の離散 Q の位相を保持する。 -/
instance ResidualCyclicStage.fullInertiaCoefficientDiscrete : DiscreteTopology (T.fullInertiaCoefficient A) :=
  inferInstanceAs (DiscreteTopology T.upperQuotient)

/-- 元の Q/F の標準商位相を保持する。 -/
instance ResidualCyclicStage.fixedQuotientCoefficientTopology : TopologicalSpace (T.fixedQuotientCoefficient A) :=
  inferInstanceAs (TopologicalSpace (T.upperQuotient ⧸ T.inertiaFixedUpperQuotient A))

/-- 元の Q/F は標準商位相で離散。 -/
instance ResidualCyclicStage.fixedQuotientCoefficientDiscrete : DiscreteTopology (T.fixedQuotientCoefficient A) :=
  inferInstanceAs (DiscreteTopology (T.upperQuotient ⧸ T.inertiaFixedUpperQuotient A))

/-- 同じ F の D 軌道写像は、元の位相で連続。 -/
theorem ResidualCyclicStage.fixedDecomposition_orbit_continuous (z : T.inertiaFixedUpperQuotient A) :
    Continuous (fun σ : A.decompositionSubgroup ℚ => T.fixedDecompositionAction A σ z) := by
  apply Continuous.subtype_mk
  exact (T.upperQuotient_orbit_continuous z.val).comp continuous_subtype_val

/-- 同じ Q/F の D 軌道写像も商位相から連続。 -/
theorem ResidualCyclicStage.quotientDecomposition_orbit_continuous (z : T.fixedQuotientCoefficient A) :
    Continuous (fun σ : A.decompositionSubgroup ℚ => T.quotientDecompositionAction A σ z) := by
  obtain ⟨v, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
  exact (continuous_of_discreteTopology : Continuous (T.fixedCoefficientSubmodule A).mkQ).comp
    ((T.upperQuotient_orbit_continuous v).comp continuous_subtype_val)
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ K の軌道は、有限商から既存同型で運んだ値に関して連続。 -/
theorem ResidualCyclicStage.kernelDecomposition_orbit_evaluation_continuous
    (k : T.fixedH1CoefficientKernel A) (τ : inertiaSubgroupIn A ℚ) :
    Continuous (fun σ : A.decompositionSubgroup ℚ =>
      T.fixedKernelEvaluation A τ (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k)) := by
  have hc := T.quotientDecomposition_orbit_continuous A
    ((T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).symm k)
  exact (continuous_of_discreteTopology : Continuous (fun z : T.fixedQuotientCoefficient A =>
    T.fixedKernelEvaluation A τ (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA z))).comp hc
/-- 同じ具体的 γ の評価により、K の D 固定元条件は閉集合になる。 -/
theorem ResidualCyclicStage.kernelDecomposition_stabilizer_isClosed (k : T.fixedH1CoefficientKernel A) :
    IsClosed {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} := by
  have he : {σ : A.decompositionSubgroup ℚ | T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k = k} =
      {σ | T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)
        (T.kernelDecompositionAction A hp5 hq hqp haddr hA σ k) =
        T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA) k} := by
    ext σ
    exact T.kernel_fixed_iff_generator_evaluation A hp5 hq hqp haddr hA σ k
  rw [he]
  exact isClosed_eq (T.kernelDecomposition_orbit_evaluation_continuous A hp5 hq hqp haddr hA k _) continuous_const
end
end DkMath.FLT.Frey.Source

```

### 4. DkMath.FLT.FreyDecompositionCoefficientSequence

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionOrbitContinuity

#print "file: DkMath.FLT.FreyDecompositionCoefficientSequence"

/-! # 同じ短完全列 0→F→Q→Q/F→0 を実際の D 上で構成する
F の D 安定性を内部証明から供給し、全 G 上へ拡張しない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の F の部分空間位相を同じ D 表現の台集合に保持する。 -/
instance ResidualCyclicStage.fixedDecompositionCoefficientTopology : TopologicalSpace (T.fixedDecompositionCoefficient A) :=
  inferInstanceAs (TopologicalSpace (T.inertiaFixedUpperQuotient A))

/-- 元の全 G の Q 係数を同じ D へ制限した表現。 -/
abbrev ResidualCyclicStage.fullDecompositionCoefficient : Rep ℤ (A.decompositionSubgroup ℚ) :=
  Rep.res (A.decompositionSubgroup ℚ).subtype T.fullGlobalCoefficient

/-- 元の同じ Q/F の D 表現。 -/
def ResidualCyclicStage.quotientDecompositionCoefficient : Rep ℤ (A.decompositionSubgroup ℚ) :=
  Rep.of (T.quotientDecompositionAction A)

/-- 同じ F→Q の D 同変な包含。 -/
def ResidualCyclicStage.decompositionCoefficientInclusion :
    T.fixedDecompositionCoefficient A ⟶ T.fullDecompositionCoefficient A :=
  Rep.ofHom ⟨(T.inertiaFixedUpperQuotient A).subtype.toIntLinearMap, fun _ => rfl⟩

/-- 同じ Q→Q/F の D 同変な商写像。 -/
def ResidualCyclicStage.decompositionCoefficientProjection :
    T.fullDecompositionCoefficient A ⟶ T.quotientDecompositionCoefficient A :=
  Rep.ofHom ⟨(T.fixedCoefficientSubmodule A).mkQ, fun _ => rfl⟩

/-- 同じ包含と商写像を持つ D 上の短複体。 -/
def ResidualCyclicStage.decompositionCoefficientSequence : ShortComplex (Rep ℤ (A.decompositionSubgroup ℚ)) :=
  ShortComplex.mk (T.decompositionCoefficientInclusion A) (T.decompositionCoefficientProjection A) (by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro z
    exact (Submodule.Quotient.mk_eq_zero _).mpr z.property)

attribute [local instance 2000] Rep.hV2
/-- 元の同じ係数による D 上の短完全性。 -/
theorem ResidualCyclicStage.decompositionCoefficientSequence_shortExact :
    (T.decompositionCoefficientSequence A).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((T.decompositionCoefficientSequence A).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ (A.decompositionSubgroup ℚ)) (ModuleCat ℤ))).mp
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro z hz
    exact ⟨⟨z, (Submodule.Quotient.mk_eq_zero _).mp hz⟩, rfl⟩
  · exact (Rep.mono_iff_injective _).mpr Subtype.val_injective
  · exact (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
end
end DkMath.FLT.Frey.Source

```

### 5. DkMath.FLT.FreyDecompositionConnectingCocycle

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionCoefficientSequence

#print "file: DkMath.FLT.FreyDecompositionConnectingCocycle"

/-! # D 不変な同じ剰余類に対する、実際の F 値連結 cocycle
D 不変性は明示条件。存在を仮定した大域 Selmer provider へ置き換えない。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ短完全列の D 上の連結写像。 -/
abbrev ResidualCyclicStage.decompositionConnecting :=
  groupCohomology.δ (T.decompositionCoefficientSequence_shortExact A) 0 1 rfl

/-- 元の同じ点の商類が D 不変である場合の H⁰ 元。 -/
def ResidualCyclicStage.decompositionCosetH0
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :=
  (groupCohomology.H0Iso (T.quotientDecompositionCoefficient A)).inv
    ⟨(T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x), hz⟩

/-- D 不変剰余類の持ち上げの作用差は、元の F に属する。 -/
theorem ResidualCyclicStage.decomposition_difference_mem_fixed
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x))
    (σ : A.decompositionSubgroup ℚ) :
    T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x ∈ T.inertiaFixedUpperQuotient A := by
  apply (Submodule.Quotient.mk_eq_zero (T.fixedCoefficientSubmodule A)).mp
  change (T.fixedCoefficientSubmodule A).mkQ
    (T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x) = 0
  exact ((T.fixedCoefficientSubmodule A).mkQ.map_sub _ _).trans (sub_eq_zero.mpr (hz σ))

/-- D 不変性から実際の作用差を F 値 cocycle として構成する。 -/
def ResidualCyclicStage.decompositionConnectingCocycle
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A) :=
  ⟨fun σ => ⟨_, T.decomposition_difference_mem_fixed A x hz σ⟩,
    (groupCohomology.mem_cocycles₁_iff _).mpr (fun σ τ => by
      apply Subtype.ext
      let g : Field.absoluteGaloisGroup ℚ := σ.val
      let t : Field.absoluteGaloisGroup ℚ := τ.val
      let v : T.upperQuotient := (QuotientAddGroup.mk' T.upperStage) x
      change T.upperQuotientAction (g * t) v - v =
        T.upperQuotientAction g (T.upperQuotientAction t v - v) + (T.upperQuotientAction g v - v)
      have hm : T.upperQuotientAction (g * t) v = T.upperQuotientAction g (T.upperQuotientAction t v) :=
        congrArg (fun f : AddMonoid.End T.upperQuotient => f v) (T.upperQuotientAction.map_mul g t)
      calc T.upperQuotientAction (g * t) v - v
          = T.upperQuotientAction g (T.upperQuotientAction t v) - v := congrArg (fun z => z - v) hm
        _ = (T.upperQuotientAction g (T.upperQuotientAction t v) - T.upperQuotientAction g v) +
            (T.upperQuotientAction g v - v) := by abel
        _ = T.upperQuotientAction g (T.upperQuotientAction t v - v) + (T.upperQuotientAction g v - v) :=
          congrArg (fun z => z + (T.upperQuotientAction g v - v)) ((T.upperQuotientAction g).map_sub _ _).symm)⟩

/-- 元の F の部分空間位相に関して、この D cocycle は連続。 -/
theorem ResidualCyclicStage.decompositionConnectingCocycle_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    Continuous (fun σ : A.decompositionSubgroup ℚ =>
      (T.decompositionConnectingCocycle A x hz σ : T.inertiaFixedUpperQuotient A)) := by
  change Continuous (fun σ : A.decompositionSubgroup ℚ =>
    (⟨T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
      (QuotientAddGroup.mk' T.upperStage) x, T.decomposition_difference_mem_fixed A x hz σ⟩ : T.inertiaFixedUpperQuotient A))
  have hc : Continuous (fun σ : A.decompositionSubgroup ℚ =>
      T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) - (QuotientAddGroup.mk' T.upperStage) x) :=
    ((T.upperQuotient_orbit_continuous _).comp
      (continuous_subtype_val : Continuous (fun σ : A.decompositionSubgroup ℚ =>
        (σ.val : Field.absoluteGaloisGroup ℚ)))).sub continuous_const
  exact hc.subtype_mk _

/-- 同じ D cocycle の類は、元の同じ D 上の δ₀ の像。 -/
theorem ResidualCyclicStage.decompositionConnectingCocycle_class
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    groupCohomology.H1π _ (T.decompositionConnectingCocycle A x hz) =
      T.decompositionConnecting A (T.decompositionCosetH0 A x hz) := by
  symm
  exact groupCohomology.δ₀_apply (T.decompositionCoefficientSequence_shortExact A)
    ⟨(T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x), hz⟩
    ((QuotientAddGroup.mk' T.upperStage) x) rfl
    (T.decompositionConnectingCocycle A x hz) rfl
end
end DkMath.FLT.Frey.Source

```

### 6. DkMath.FLT.FreyDecompositionConnectingRestriction

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionConnectingCocycle

#print "file: DkMath.FLT.FreyDecompositionConnectingRestriction"

/-! # D 上の連結類を同じ I 上の実際の類へ制限する
D 不変性を保持したまま、群包含・係数射・同じ代表を明示する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory.ValuationInertia
/-- 元の全自己同型群内の慣性像から、同じ分解群への包含。 -/
def inertiaToDecomposition (A : ValuationSubring (AlgebraicClosure ℚ)) :
    inertiaSubgroupIn A ℚ →* A.decompositionSubgroup ℚ where
  toFun σ := ⟨σ.val, mem_decomposition_of_mem_inertia A σ.val σ.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
end DkMath.FLT.Frey.Source
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ F の D 表現を I へ制限すると、元の自明係数に一致する。 -/
def ResidualCyclicStage.decompositionInertiaCoefficient :
    Rep.res (inertiaToDecomposition A) (T.fixedDecompositionCoefficient A) ⟶
      TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A) :=
  Rep.ofHom ⟨LinearMap.id, fun σ => by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact z.property σ.val σ.property⟩

/-- 元の I⊆D に沿う、同じ F 係数での通常 H¹ 制限。 -/
def ResidualCyclicStage.decompositionInertiaRestriction :=
  groupCohomology.map (A := T.fixedDecompositionCoefficient A)
    (B := TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))
    (inertiaToDecomposition A) (T.decompositionInertiaCoefficient A) 1
variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ D 連結 cocycle の制限は、元の同じ連続 I cocycle。 -/
theorem ResidualCyclicStage.decompositionCocycle_restrict
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    groupCohomology.mapCocycles₁ (inertiaToDecomposition A) (T.decompositionInertiaCoefficient A)
      (T.decompositionConnectingCocycle A x hz) =
    T.continuousConnectingCocycle A hp5 hq hqp haddr hA x := by
  apply groupCohomology.cocycles₁_ext
  intro σ
  apply Subtype.ext
  exact (T.continuousCocycle_global_restriction A hp5 hq hqp haddr hA x σ).symm

/-- 同じ点の D 上の類を制限すると、元の同じ核元の類を回収する。 -/
theorem ResidualCyclicStage.decompositionClass_restrict_kernel
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hz : ∀ σ : A.decompositionSubgroup ℚ, T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) :
    T.decompositionInertiaRestriction A (groupCohomology.H1π _ (T.decompositionConnectingCocycle A x hz)) =
      (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x).val := by
  have he := groupCohomology.H1π_comp_map_apply (inertiaToDecomposition A)
    (T.decompositionInertiaCoefficient A) (T.decompositionConnectingCocycle A x hz)
  rw [T.decompositionCocycle_restrict A hp5 hq hqp haddr hA x hz,
    T.continuousConnectingCocycle_eq A hp5 hq hqp haddr hA x] at he
  exact he.trans (T.fixedCosetKernelElement_val hp5 hq hqp haddr A hA x).symm
end
end DkMath.FLT.Frey.Source

```

### 7. DkMath.FLT.FreyResonantDecompositionLift

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDecompositionConnectingRestriction

#print "file: DkMath.FLT.FreyResonantDecompositionLift"

/-! # 元の障害値の共鳴符号と、D 不変性の下での同じ類の持ち上げ
符号等式や D 不変性は供給しない。条件を明示して実際の D cocycle を構成する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の共鳴二分岐で、同じ厳密位数 p の値による判定を供給する。 -/
theorem NarrowAbsorptionObstruction.exists_prime_sign_frobenius_criterion
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    let v := T.fixedKernelEvaluation A (InertiaRadical.generator (Fact.out : p.Prime) h.prime h.ne_torsion_prime.symm A h.lies_over) k
    ∃ φ : A.decompositionSubgroup ℚ, ValuationFrobenius.IsFrobeniusAt A φ.val q ∧ addOrderOf v = p ∧
      (((q : ZMod p) = 1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
        T.fixedDecompositionAction A φ v = v)) ∨
       ((q : ZMod p) = -1 ∧ (T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over φ k = k ↔
        T.fixedDecompositionAction A φ v = -v))) := by
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime h.prime A h.lies_over
  exact ⟨⟨φ, hφ.mem_decompositionSubgroup⟩, hφ, h.generatorValue_order_eq_prime hp5,
    h.frobenius_fixed_resonant_signs hp5 _ hφ⟩

/-- 元の同じ障害核元が D 全体で固定される場合に限る、非零で連続な D 類の具体的持ち上げ。 -/
theorem NarrowAbsorptionObstruction.decomposition_lift_of_kernel_fixed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hD : ∀ σ : A.decompositionSubgroup ℚ, T.kernelDecompositionAction A hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) h.lies_over σ
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
        T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) :
    ∃ c : groupCohomology.cocycles₁ (T.fixedDecompositionCoefficient A),
      Continuous (fun σ : A.decompositionSubgroup ℚ => (c σ : T.inertiaFixedUpperQuotient A)) ∧
      T.decompositionInertiaRestriction A (groupCohomology.H1π _ c) =
        (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩).val ∧
      groupCohomology.H1π _ c ≠ 0 := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  have hz (σ : A.decompositionSubgroup ℚ) : T.quotientDecompositionAction A σ
      ((T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x) := by
    apply (T.kernel_fixed_iff_quotient_fixed A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over σ _).mp
    exact hD σ
  let c := T.decompositionConnectingCocycle A x hz
  have hr := T.decompositionClass_restrict_kernel A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over x hz
  refine ⟨c, T.decompositionConnectingCocycle_continuous A x hz, hr, ?_⟩
  intro hc
  rw [hc, map_zero] at hr
  apply (h.fixed_H1_nonzero hp5).2
  exact (T.fixedCosetKernelElement_val hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).symm.trans hr.symm
end
end DkMath.FLT.Frey.Source

```

