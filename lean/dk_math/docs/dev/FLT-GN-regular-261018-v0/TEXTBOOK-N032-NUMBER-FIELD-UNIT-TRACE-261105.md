# NOTE-032 教科書：単元 Galois 作用のトレースと Dirichlet 対数

日付：2026-11-05。前段：`TEXTBOOK-N032-CYCLOTOMIC-UNIT-DIMENSION-261105.md`。
今回の2ステップは、①捩れ部分と自由商への作用とトレースの加法性、
②Dirichlet 対数を通した自由商の整数トレースと無限素点の固定点数の比較である。
最後に、同じ `rootField ζ` の既存 `unitAction` へ接続する。

以下の2つの Lean ブロックは production ファイルの著作権・通知を含む全文である。
順にモジュールとして配置して利用する。コードの個別コピー後コンパイルも検証する。
ファイル同定に必須の import 直後の `#print "file: …"` を省略しない。

## 今回の到達点

- 同じ整数環への実際の制限 `integerAut σ` から単元群の作用を作る。
- 捩れ群が安定であることを証明し、実際の自由商へ作用を降ろす。
- `freeUnitAction` は同じ自由商の整数線形自己準同型への実際の群準同型である。
- 同じ単元冪商のトレースを、捩れ成分と自由商の整数トレースに分ける。
- 全無限素点の重み付き対数により、自由商の整数トレースを固定素点数−1 と証明する。
- 同じ円分指標の d に対し、既存の作用について `trace(ρ_d)=d+#Fix(d)−1` を証明する。

**未完成なのは、円分体の #Fix(d) の ±1 による分類と、その後の射影子の重み付き和である。**
従って `trace(e₂)=1`、一般 hrank、一般 hno はまだ閉じていない。

## ステップ1：同じ作用とトレースの加法性

任意の数体 F と σ∈Gal(F/ℚ) に対し、実際の整数環作用による

    unitsMap σ : 𝓞 Fˣ →* 𝓞 Fˣ

を取る。有限位数の元は有限位数へ写るので、捩れ単元群 T は安定である。
したがって、自由商 A=Additive(𝓞 Fˣ/T) への加法写像 `quotMap` と
整数線形写像 `quotMapLin` が定まり、合成則から `freeUnitAction` も構成できる。
自由商 A は、以前の単元 p 乗商 U=Additive(UnitClass (𝓞 F) p) とは別の対象である。
両者を暗黙に同一視せず、トレースの比較で関連づける。

素数 p が |T| を割り、整数環のすべての p 乗根に σ が n 乗で作用すると仮定する。
この一般形の仮定 `hdiv`・`hσ` は、後段で指定された円分根の指標から内部供給する。
以前構成した、捩れ生成元 t と基本単元による U の基底を利用する。

T の生成元の位数を pq とし、σ(t)=t^e と書く。
位数 p の元 t^q に対する作用を比較すると、e≡n mod p が従う。
これは q の逆元を mod p で仮定する議論ではない。整数の合同式で非零の q を消去する。
よって捩れ成分の対角係数は n となる。

各基本単元の像には捩れ因子が混ざってよい。
Dirichlet 分解の自由指数を比較すれば、残りの対角係数は
A 上の同じ整数作用行列の対角係数を mod p に写したものとなる。
**基本単元が Galois 不変であるとは仮定しない。**
この基底の対角和を取り、次の実際の等式を得る。

    trace_𝔽p(vMap σ) = n + (trace_ℤ(quotMapLin σ) : 𝔽p)

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Unit action and trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: use the SAME DkMath integerAut, UnitClass, unitProjection and proved
Dirichlet basis; no external ModP or trace theorem is imported.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension
import Mathlib.LinearAlgebra.Trace

#print "file: DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace"

/-!
# 同じ単元作用の捩れ成分と自由成分のトレース

整数環自己同型は既存の integerAut。捩れ群の安定性を証明して自由商へ作用を降ろす。
実際の UnitClass の捩れ・基本単元基底の対角成分を計算し、mod p の trace を
捩れ成分 n と整数上の自由商作用の trace の和として証明する。
基本単元が Galois 不変とは仮定しない。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace

open NumberField NumberField.Units NumberFieldUnitPowerDimension
open CyclotomicKummerEquivariance KummerSelmerUnitEquivariance KummerSelmerExact
open scoped NumberField
noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]
variable (F : Type*) [Field F] [NumberField F]

/-- Mathlib の Dirichlet 自由商を同じ群構造で明示する。 -/
instance freeUnitsCommGroup : CommGroup ((𝓞 F)ˣ ⧸ torsion F) :=
  QuotientGroup.Quotient.commGroup _
instance freeUnitsAddCommGroup : AddCommGroup (Additive ((𝓞 F)ˣ ⧸ torsion F)) :=
  Additive.addCommGroup
instance freeUnitsIntModule : Module ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) :=
  AddCommGroup.toIntModule _

/-- 同じ整数環への実際の制限が与える単元群の作用。 -/
def unitsMap (σ : F ≃ₐ[ℚ] F) : (𝓞 F)ˣ →* (𝓞 F)ˣ :=
  Units.map (integerAut σ).integers.toMonoidHom

/-- 指定した元の数体自己同型と可換する。 -/
theorem unitsMap_coe (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    ((unitsMap F σ u : 𝓞 F) : F) = σ ((u : 𝓞 F) : F) := rfl

/-- 有限位数の単元は同じ整数環作用で有限位数に保たれる。 -/
lemma unitsMap_torsion_le (σ : F ≃ₐ[ℚ] F) :
    torsion F ≤ (torsion F).comap (unitsMap F σ) := by
  intro t ht
  rw [Subgroup.mem_comap]
  rw [torsion, CommGroup.mem_torsion] at ht ⊢
  exact MonoidHom.isOfFinOrder _ ht

/-- 実際の有限捩れ群による同じ自由商への作用。 -/
def quotMap (σ : F ≃ₐ[ℚ] F) : Additive ((𝓞 F)ˣ ⧸ torsion F) →+ Additive ((𝓞 F)ˣ ⧸ torsion F) :=
  MonoidHom.toAdditive
    (QuotientGroup.map (torsion F) (torsion F) (unitsMap F σ) (unitsMap_torsion_le F σ))

lemma quotMap_mk (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    quotMap F σ (Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ torsion F))) =
      Additive.ofMul (QuotientGroup.mk (unitsMap F σ u)) := rfl

set_option backward.isDefEq.respectTransparency false in

/-- 同じ自由商の加法作用を整数線形写像として読む。 -/
def quotMapLin (σ : F ≃ₐ[ℚ] F) : Additive ((𝓞 F)ˣ ⧸ torsion F) →ₗ[ℤ] Additive ((𝓞 F)ˣ ⧸ torsion F) :=
  (quotMap F σ).toIntLinearMap

lemma quotMapLin_apply (σ : F ≃ₐ[ℚ] F) (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) :
    quotMapLin F σ x = quotMap F σ x := rfl


/-- 同じ単元上の実際の自己同型の合成則。 -/
theorem unitsMap_mul (σ τ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    unitsMap F (σ * τ) u = unitsMap F σ (unitsMap F τ u) := by
  apply Units.ext
  apply NumberField.RingOfIntegers.coe_injective
  rfl

/-- 捩れを除いた同じ自由商上にも、実際の Galois 群作用を与える。 -/
def freeUnitAction : (F ≃ₐ[ℚ] F) →*
    Module.End ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) where
  toFun σ := quotMapLin F σ
  map_one' := by
    ext x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (torsion F) x.toMul
    have he : Additive.ofMul ((QuotientGroup.mk' (torsion F)) u) = x := congrArg Additive.ofMul hu
    rw [← he]
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (torsion F) x.toMul
    have he : Additive.ofMul ((QuotientGroup.mk' (torsion F)) u) = x := congrArg Additive.ofMul hu
    rw [← he]
    change Additive.ofMul (QuotientGroup.mk (unitsMap F (σ * τ) u)) =
      Additive.ofMul (QuotientGroup.mk (unitsMap F σ (unitsMap F τ u)))
    rw [unitsMap_mul]


/-- 既存 unitClassLinearMap そのものによる同じ単元 p 乗商上の作用。 -/
def vMap (σ : F ≃ₐ[ℚ] F) :
    Additive (UnitClass (𝓞 F) p) →ₗ[ZMod p] Additive (UnitClass (𝓞 F) p) :=
  unitClassLinearMap p (integerAut σ)

theorem vMap_proj (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    vMap p F σ (unitProjection (F := F) p (Additive.ofMul u)) =
      unitProjection (F := F) p (Additive.ofMul (unitsMap F σ u)) := rfl

/-- 実際の捩れ成分 n と自由商の整数 trace を足した、同じ作用の trace。 -/
theorem trace_vMap (hdiv : p ∣ torsionOrder F) (σ : F ≃ₐ[ℚ] F) (n : ℕ)
    (hσ : ∀ x : 𝓞 F, x ^ p = 1 → (integerAut σ).integers x = x ^ n) :
    LinearMap.trace (ZMod p) _ (vMap p F σ) =
      (n : ZMod p) + ((LinearMap.trace ℤ _ (quotMapLin F σ) : ℤ) : ZMod p) := by
  classical
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := torsion F)
  have hord : orderOf t = torsionOrder F := by
    rw [torsionOrder]
    exact orderOf_eq_card_of_forall_mem_zpowers ht
  obtain ⟨b, hb_none, hb_some⟩ := exists_unitClass_basis (p := p) F hdiv t ht
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.mp
    (ht ⟨unitsMap F σ (t : (𝓞 F)ˣ), unitsMap_torsion_le F σ t.2⟩)
  have he' : unitsMap F σ (t : (𝓞 F)ˣ) = (t : (𝓞 F)ˣ) ^ e := by
    have := congrArg (fun x : torsion F => (x : (𝓞 F)ˣ)) he
    simpa only [Subgroup.coe_zpow] using this.symm
  obtain ⟨q, hq⟩ := hdiv
  have hqpos : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp [torsionOrder_ne_zero F] at hq)
  have he_n : (e : ZMod p) = (n : ZMod p) := by
    -- 全捩れ生成元の適切な冪が位数 p の元を与え、その作用が e≡n を強制する。
    set y : (𝓞 F)ˣ := (t : (𝓞 F)ˣ) ^ q with hy
    have hyp : (y : 𝓞 F) ^ p = 1 := by
      rw [hy, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, ← hq, ← hord,
        ← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, pow_orderOf_eq_one]
      rfl
    have h1 : unitsMap F σ y = y ^ n := by
      ext
      rw [Units.val_pow_eq_pow_val, ← hσ _ hyp]
      rfl
    have h2 : unitsMap F σ y = (t : (𝓞 F)ˣ) ^ ((q : ℤ) * e) := by
      rw [hy, map_pow, he', ← zpow_natCast, ← zpow_mul, mul_comm]
    have h3 : (t : (𝓞 F)ˣ) ^ ((q : ℤ) * e) = (t : (𝓞 F)ˣ) ^ ((q : ℤ) * n) := by
      rw [← h2, h1, hy, ← pow_mul, ← zpow_natCast, Nat.cast_mul]
    rw [zpow_eq_zpow_iff_modEq, Subgroup.orderOf_coe, hord, hq, Nat.cast_mul,
      mul_comm (p : ℤ) (q : ℤ)] at h3
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
    have hmod : e ≡ (n : ℤ) [ZMOD (p : ℤ)] := Int.ModEq.mul_left_cancel' hq0 h3
    rw [← Int.cast_natCast n]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  have row_none : b.repr (vMap p F σ (b none)) none = n := by
    rw [hb_none, vMap_proj, he', ofMul_zpow, map_zsmul, ← hb_none,
      ← Int.cast_smul_eq_zsmul (ZMod p), map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one, he_n]
  -- 基本単元が作用で不変でなくても、商作用の整数行列と対角係数が一致する。
  have row_some : ∀ i, b.repr (vMap p F σ (b (some i))) (some i) =
      (((basisModTorsion F).repr (quotMapLin F σ (basisModTorsion F i)) i : ℤ) : ZMod p) := by
    intro i
    set w : (𝓞 F)ˣ := unitsMap F σ (fundSystem F i) with hw_def
    obtain ⟨⟨ζw, ew⟩, hw, -⟩ := exist_unique_eq_mul_prod F w
    dsimp only at hw
    have hrepr : ew = (basisModTorsion F).repr (quotMapLin F σ (basisModTorsion F i)) := by
      rw [fun_eq_repr F ζw.2 hw, quotMapLin_apply, ← fundSystem_mk, quotMap_mk]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζw)
    have hζw : (ζw : (𝓞 F)ˣ) = (t : (𝓞 F)ˣ) ^ m := by
      rw [← hm, Subgroup.coe_zpow]
    have hvw : vMap p F σ (b (some i)) =
        (m : ZMod p) • b none + ∑ j, ((ew j : ℤ) : ZMod p) • b (some j) := by
      rw [hb_some, vMap_proj, ← hw_def, hw, hζw, ofMul_mul, ofMul_zpow, ofMul_prod, map_add,
        map_zsmul, map_sum, hb_none, Int.cast_smul_eq_zsmul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ofMul_zpow, map_zsmul, hb_some, Int.cast_smul_eq_zsmul]
    rw [hvw, map_add, map_sum, Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
      Option.some.injEq, reduceCtorEq, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_false,
      zero_add, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hrepr]
  rw [LinearMap.trace_eq_matrix_trace (ZMod p) b, LinearMap.trace_eq_matrix_trace ℤ
    (basisModTorsion F)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fintype.sum_option, row_none,
    row_some, Int.cast_sum]

end
end DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace
```

## ステップ2：対数と無限素点の固定点数

S=InfinitePlace F とし、単元 u の全対数を

    logFull(u)(w)=mult(w) log(w(u))

とする。`mult(w)` は実素点で1、複素素点で2という重みである。
単元の積公式により座標の和は零となる。
同じ対数の核が捩れ単元 T であることを証明して、実際の自由商 A に

    logQuot : A →+ (S → ℝ)

を降ろす。代表元を任意に選んだだけの関数ではない。

σ の無限素点への作用に対応する実線形写像を

    permL(σ)(f)(w)=f(σ⁻¹ • w)

と置く。同じ整数単元作用と対数について

    logQuot(quotMap(σ)(x))=permL(σ)(logQuot(x))

を証明する。複素／実素点の重みはこの作用で保たれる。

### 整数・実数の作用行列を明示的に比較する

A の Dirichlet 基底の logQuot 像が張る実部分空間を W とする。
この像の族の線形独立性・生成性を Mathlib の単元格子から証明する。
W は座標和零の部分空間で、定数関数1の直線 L と補空間になる。
両方が同じ permL(σ) で安定であり、L 上の作用は恒等写像である。

A 上の整数作用行列を B とする。
logQuot 基底の同変性から、W 上の実作用行列が厳密に `B.map (Int.cast : ℤ → ℝ)` と一致する。
従って、W 上の実トレースは整数 `B.trace` の実数への像となる。
ここで整数のトレースと実数のトレースを無条件に同一視していない。

全座標空間 S→ℝ での permL(σ) のトレースは、座標基底の行列の対角和により

    #{w | σ • w=w}

となる。一方、補空間 W⊕L 上のトレースの加法性から

    trace_ℝ(permL σ) = (trace_ℤ(quotMapLin σ) : ℝ)+1

を得る。最後は ℤ→ℝ の係数写像を通した等式から、整数の等式

    trace_ℤ(quotMapLin σ) = (#{w | σ • w=w} : ℤ)−1

を復元する。これが `trace_quotMap_eq` である。

### 同じ円分体の既存 unitAction へ戻す

同じ原始根 ζ で生成した F=rootField ζ を固定し、既存の
`characterEquiv hζ` の逆で d∈𝔽pˣ に対応する σd を取る。
指定した根の整数環での原始根性により、任意の x^p=1 は同じ根の冪で書ける。
既存の指標の根への作用から、σd はそのすべての x に d.val 乗で作用する。
したがって一般形の `hσ` と `hdiv` を内部供給できる。

整数の自由商トレースを明示的に mod p へ写すと、既存の同じ `unitAction` に対して

    trace(ρ_d) = d + (#{w | σd • w=w} : 𝔽p)−1

を得る。`trace_unitAction_eq_character_add_fixedPlaces` は、固定点数の値や
トレース公式を provider として要求しない。公開入力は同じ hζ と d のみである。
この等式は素数 p 全般で成立し、まだ p≥5 や d=±1 の分類を必要としない。

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Dirichlet logarithmic trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: compare the SAME integer free-unit action with the actual infinite-place
permutation via the Dirichlet logarithm; cast the SAME integer trace explicitly.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitGaloisTrace
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector

#print "file: DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace"

/-!
# 同じ自由単元作用の Dirichlet 対数と無限素点上のトレース

全無限素点への重み付き対数の像は座標和が零の超平面を張る。
同じ整数作用行列を実係数へ写して比較し、自由商の整数 trace が固定素点数−1となる。
円分体の固定点の分類や射影子の trace=1 はまだ証明しない。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem Module
open NumberFieldUnitGaloisTrace
open scoped NumberField
noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- 全無限素点に対する、重み付きの同じ単元の対数。 -/
def logFull : Additive ((𝓞 F)ˣ) →+ (InfinitePlace F → ℝ) where
  toFun x w := mult w * Real.log (w (x.toMul : F))
  map_zero' := by
    funext w
    simp
  map_add' x y := by
    funext w
    simp only [toMul_add, Units.val_mul, Pi.add_apply, map_mul]
    have hx : w (algebraMap (𝓞 F) F (x.toMul : 𝓞 F)) ≠ 0 :=
      ne_of_gt (pos_iff.mpr (by simp))
    have hy : w (algebraMap (𝓞 F) F (y.toMul : 𝓞 F)) ≠ 0 :=
      ne_of_gt (pos_iff.mpr (by simp))
    rw [Real.log_mul hx hy, mul_add]

omit [NumberField F] in
theorem logFull_apply (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    logFull F (Additive.ofMul u) w = mult w * Real.log (w (u : F)) := rfl

theorem sum_logFull (x : Additive ((𝓞 F)ˣ)) : ∑ w, logFull F x w = 0 :=
  sum_mult_mul_log x.toMul

/-- 全対数が零であることは、同じ元が捩れ単元であることと同値。 -/
theorem logFull_eq_zero_iff {u : (𝓞 F)ˣ} :
    logFull F (Additive.ofMul u) = 0 ↔ u ∈ torsion F := by
  constructor
  · intro h
    refine (logEmbedding_eq_zero_iff (K := F)).mp ?_
    funext w
    exact congrFun h w.1
  · intro h
    funext w
    have hw : w ((u : 𝓞 F) : F) = 1 := (mem_torsion F).mp h w
    simp [logFull_apply, hw]

/-- 対数の実際の核が捩れ単元であることを用いて自由商へ降ろす。 -/
def logQuot : Additive ((𝓞 F)ˣ ⧸ torsion F) →+ (InfinitePlace F → ℝ) :=
  MonoidHom.toAdditiveLeft <|
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logFull F))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext u
        rw [MonoidHom.mem_ker, AddMonoidHom.toMultiplicativeRight_apply_apply, ofAdd_eq_one,
          ← logFull_eq_zero_iff (F := F)])).toMonoidHom

theorem logQuot_mk (u : (𝓞 F)ˣ) :
    logQuot F (Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ torsion F))) =
      logFull F (Additive.ofMul u) := rfl

omit [NumberField F] in
private lemma logQuot_surjective_rep (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) :
    ∃ u : (𝓞 F)ˣ,
      x = Additive.ofMul ((QuotientGroup.mk u : (𝓞 F)ˣ ⧸ torsion F)) := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (x.toMul)
  refine ⟨u, ?_⟩
  rw [hu]
  exact (ofMul_toMul x).symm

/-- 同じ Galois 元による無限素点の置換表現。 -/
def permL (σ : F ≃ₐ[ℚ] F) : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) :=
  LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w)

private lemma mult_smul' (σ : F ≃ₐ[ℚ] F) (w : InfinitePlace F) : mult (σ • w) = mult w := by
  classical
  simp only [mult]
  exact if_congr isReal_smul_iff rfl rfl

theorem logFull_unitsMap (σ : F ≃ₐ[ℚ] F) (u : (𝓞 F)ˣ) :
    logFull F (Additive.ofMul (unitsMap F σ u)) = permL F σ (logFull F (Additive.ofMul u)) := by
  funext w
  simp only [permL, LinearMap.funLeft_apply, logFull_apply, unitsMap_coe]
  have h1 : (σ⁻¹ • w) ((u : 𝓞 F) : F) = w (σ ((u : 𝓞 F) : F)) := by
    rw [NumberField.InfinitePlace.smul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_symm]
  rw [mult_smul' F σ⁻¹ w, h1]

/-- 整数自由商の同じ作用と、実際の対数・素点置換との同変性。 -/
theorem logQuot_quotMap (σ : F ≃ₐ[ℚ] F) (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) :
    logQuot F (quotMap F σ x) = permL F σ (logQuot F x) := by
  obtain ⟨u, rfl⟩ := logQuot_surjective_rep F x
  rw [quotMap_mk, logQuot_mk, logQuot_mk, logFull_unitsMap]

private def vFam : Fin (rank F) → (InfinitePlace F → ℝ) := fun i => logQuot F (basisModTorsion F i)

private def restr : (InfinitePlace F → ℝ) →ₗ[ℝ] logSpace F :=
  LinearMap.funLeft ℝ ℝ (Subtype.val : {w : InfinitePlace F // w ≠ w₀} → InfinitePlace F)

private lemma restr_logFull (x : Additive ((𝓞 F)ˣ)) :
    restr F (logFull F x) = logEmbedding F x := rfl

private lemma restr_vFam (i : Fin (rank F)) :
    restr F (vFam F i) = (basisUnitLattice F i : logSpace F) := by
  obtain ⟨u, hu⟩ := logQuot_surjective_rep F (basisModTorsion F i)
  rw [vFam, hu, logQuot_mk, restr_logFull, basisUnitLattice, Basis.map_apply, hu,
    logEmbeddingEquiv_apply]

private lemma span_restr_vFam :
    Submodule.span ℝ (Set.range ((restr F) ∘ (vFam F))) = ⊤ := by
  rw [← unitLattice_span_eq_top (K := F)]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    rw [Function.comp_apply, restr_vFam]
    exact Submodule.subset_span (basisUnitLattice F i).2
  · rw [Submodule.span_le]
    intro y hy
    set z : unitLattice F := ⟨y, hy⟩ with hzdef
    have hz : y = ((∑ i, (basisUnitLattice F).repr z i • basisUnitLattice F i :
        unitLattice F) : logSpace F) := by
      rw [(basisUnitLattice F).sum_repr z]
    rw [hz]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine zsmul_mem (Submodule.subset_span ?_) _
    refine Set.mem_range.mpr ⟨i, ?_⟩
    rw [Function.comp_apply, restr_vFam]

private lemma linearIndependent_vFam : LinearIndependent ℝ (vFam F) := by
  classical
  refine LinearIndependent.of_comp (restr F) ?_
  refine linearIndependent_of_top_le_span_of_card_eq_finrank
    (le_of_eq (span_restr_vFam F).symm) ?_
  rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq, rank]

private lemma sum_vFam_eq_zero (i : Fin (rank F)) : ∑ w, vFam F i w = 0 := by
  obtain ⟨u, hu⟩ := logQuot_surjective_rep F (basisModTorsion F i)
  rw [vFam, hu, logQuot_mk]
  exact sum_logFull F _

private abbrev Wv : Submodule ℝ (InfinitePlace F → ℝ) := Submodule.span ℝ (Set.range (vFam F))

private abbrev Lone : Submodule ℝ (InfinitePlace F → ℝ) :=
  Submodule.span ℝ {(fun _ => (1 : ℝ) : InfinitePlace F → ℝ)}

private def sFun : (InfinitePlace F → ℝ) →ₗ[ℝ] ℝ := ∑ w, LinearMap.proj w

private lemma sFun_apply (f : InfinitePlace F → ℝ) : sFun F f = ∑ w, f w := by
  simp [sFun]

private lemma sFun_vanish_Wv {x : InfinitePlace F → ℝ} (hx : x ∈ Wv F) : sFun F x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; rw [sFun_apply]; exact sum_vFam_eq_zero F i
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private lemma isCompl_Wv_Lone : IsCompl (Wv F) (Lone F) := by
  have hcard : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  have hdisj : Disjoint (Wv F) (Lone F) := by
    rw [Submodule.disjoint_def]
    intro x hxW hxL
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxL
    have h0 := sFun_vanish_Wv F hxW
    rw [map_smul, sFun_apply] at h0
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with hc | hc
    · rw [hc, zero_smul]
    · exact absurd hc (Nat.cast_ne_zero.mpr hcard.ne')
  have hone : (fun _ => (1 : ℝ) : InfinitePlace F → ℝ) ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary _)
    norm_num at this
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Wv F) (Lone F)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at hsum
  have hWv : Module.finrank ℝ (Wv F) = rank F := by
    rw [Wv, finrank_span_eq_card (linearIndependent_vFam F), Fintype.card_fin]
  have hLone : Module.finrank ℝ (Lone F) = 1 := by
    rw [Lone, finrank_span_singleton hone]
  rw [hWv, hLone] at hsum
  rw [hsum, Module.finrank_fintype_fun_eq_card, rank]
  omega

private lemma permL_one_const (σ : F ≃ₐ[ℚ] F) :
    permL F σ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := rfl

private lemma logQuot_mem_Wv (x : Additive ((𝓞 F)ˣ ⧸ torsion F)) : logQuot F x ∈ Wv F := by
  have hx := (basisModTorsion F).sum_repr x
  rw [← hx, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _

private lemma permL_mem_Wv (σ : F ≃ₐ[ℚ] F) {x : InfinitePlace F → ℝ} (hx : x ∈ Wv F) :
    permL F σ x ∈ Wv F := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    rw [show vFam F i = logQuot F (basisModTorsion F i) from rfl, ← logQuot_quotMap]
    exact logQuot_mem_Wv F _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private lemma permL_mem_Lone (σ : F ≃ₐ[ℚ] F) {_x : InfinitePlace F → ℝ} (hx : _x ∈ Lone F) :
    permL F σ _x ∈ Lone F := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, permL_one_const]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma one_ne_zero' : (fun _ => (1 : ℝ) : InfinitePlace F → ℝ) ≠ 0 := by
  intro h
  have := congrFun h (Classical.arbitrary _)
  norm_num at this

private lemma finrank_Lone : Module.finrank ℝ (Lone F) = 1 := by
  rw [Lone, finrank_span_singleton (one_ne_zero' F)]

/-- 座標の引き戻し作用の実トレースは、実際の固定座標数。 -/
theorem trace_funLeft (g : InfinitePlace F → InfinitePlace F) :
    LinearMap.trace ℝ (InfinitePlace F → ℝ) (LinearMap.funLeft ℝ ℝ g) =
      Nat.card {w // g w = w} := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (InfinitePlace F)), Matrix.trace]
  have hdiag : ∀ i, (LinearMap.toMatrix (Pi.basisFun ℝ (InfinitePlace F))
      (Pi.basisFun ℝ (InfinitePlace F)) (LinearMap.funLeft ℝ ℝ g)).diag i =
      if g i = i then 1 else 0 := by
    intro i
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_repr,
      LinearMap.funLeft_apply, Pi.basisFun_apply]
    simp [Pi.single_apply]
  rw [Finset.sum_congr rfl fun i _ => hdiag i, Finset.sum_boole]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma trace_eq_trace_restrict_add_trace_restrict
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p q : Submodule R M} (h : IsCompl p q) (f : M →ₗ[R] M)
    (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q)
    [Module.Finite R p] [Module.Free R p] [Module.Finite R q] [Module.Free R q] :
    LinearMap.trace R M f =
      LinearMap.trace R p (f.restrict hp) + LinearMap.trace R q (f.restrict hq) := by
  have key : (Submodule.prodEquivOfIsCompl p q h).symm.conj f =
      LinearMap.prodMap (f.restrict hp) (f.restrict hq) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_symm]
    rw [LinearEquiv.symm_apply_eq]
    rw [LinearMap.prodMap_apply, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', map_add]
    rw [LinearMap.coe_restrict_apply, LinearMap.coe_restrict_apply]
  calc LinearMap.trace R M f
      = LinearMap.trace R (p × q) ((Submodule.prodEquivOfIsCompl p q h).symm.conj f) :=
        (LinearMap.trace_conj' f _).symm
    _ = _ := by rw [key, LinearMap.trace_prodMap']

private lemma permL_vFam_eq (σ : F ≃ₐ[ℚ] F) (j : Fin (rank F)) :
    permL F σ (vFam F j) =
      ∑ i, ((LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F)
        (quotMapLin F σ)) i j : ℝ) • vFam F i := by
  have h0 : permL F σ (vFam F j) = logQuot F (quotMapLin F σ (basisModTorsion F j)) := by
    rw [quotMapLin_apply, show vFam F j = logQuot F (basisModTorsion F j) from rfl,
      logQuot_quotMap]
  rw [h0]
  conv_lhs => rw [← (basisModTorsion F).sum_repr (quotMapLin F σ (basisModTorsion F j))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, LinearMap.toMatrix_apply]
  exact (Int.cast_smul_eq_zsmul ℝ _ _).symm

private lemma trace_restrict_Lone (σ : F ≃ₐ[ℚ] F) :
    LinearMap.trace ℝ (Lone F)
      ((permL F σ).restrict (fun _x hx => permL_mem_Lone F σ hx)) = 1 := by
  have hid : (permL F σ).restrict (fun _x hx => permL_mem_Lone F σ hx) = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨_x, hx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, LinearMap.id_coe, id_eq, map_smul, permL_one_const]
  rw [hid, LinearMap.trace_id, finrank_Lone]
  norm_num

private lemma trace_restrict_Wv (σ : F ≃ₐ[ℚ] F) :
    LinearMap.trace ℝ (Wv F)
      ((permL F σ).restrict (fun _x hx => permL_mem_Wv F σ hx)) =
      ((LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F)
        (quotMapLin F σ)).trace : ℝ) := by
  classical
  set A := LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F) (quotMapLin F σ)
    with hA
  set bW : Basis (Fin (rank F)) ℝ (Wv F) :=
    (Basis.span (linearIndependent_vFam F) : _) with hbW
  have hcoe : ∀ j, (bW j : InfinitePlace F → ℝ) = vFam F j := by
    intro j
    rw [hbW]
    exact congrArg Subtype.val (Basis.span_apply (linearIndependent_vFam F) j)
  have hW : ∀ j, ((permL F σ).restrict (fun _x hx => permL_mem_Wv F σ hx)) (bW j) =
      ∑ k, (A k j : ℝ) • bW k := by
    intro j
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, hcoe, permL_vFam_eq]
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => by rw [SetLike.val_smul, hcoe]
  have hmat : LinearMap.toMatrix bW bW
      ((permL F σ).restrict (fun _x hx => permL_mem_Wv F σ hx)) =
      A.map (Int.cast : ℤ → ℝ) := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, hW j, map_sum]
    simp [Basis.repr_self, Finsupp.single_apply]
  rw [LinearMap.trace_eq_matrix_trace ℝ bW, hmat, Matrix.trace, Matrix.trace]
  push_cast
  rfl

/-- 同じ自由単元商の整数 trace は、実際の無限素点の固定点数−1。 -/
theorem trace_quotMap_eq (σ : F ≃ₐ[ℚ] F) :
    LinearMap.trace ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) (quotMapLin F σ) =
      (Nat.card {w : InfinitePlace F // σ • w = w} : ℤ) - 1 := by
  classical
  set A := LinearMap.toMatrix (basisModTorsion F) (basisModTorsion F) (quotMapLin F σ)
    with hA
  have h1 : LinearMap.trace ℤ (Additive ((𝓞 F)ˣ ⧸ torsion F)) (quotMapLin F σ) = A.trace := by
    rw [hA]
    exact LinearMap.trace_eq_matrix_trace ℤ (basisModTorsion F) _
  have h2 : LinearMap.trace ℝ (InfinitePlace F → ℝ) (permL F σ) =
      (Nat.card {w : InfinitePlace F // σ • w = w} : ℝ) := by
    rw [show permL F σ = LinearMap.funLeft ℝ ℝ (fun w => σ⁻¹ • w) from rfl, trace_funLeft]
    congr 1
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun w => ?_
    rw [inv_smul_eq_iff, eq_comm]
  have h3 := trace_eq_trace_restrict_add_trace_restrict (isCompl_Wv_Lone F) (permL F σ)
    (fun _x hx => permL_mem_Wv F σ hx) (fun _x hx => permL_mem_Lone F σ hx)
  rw [trace_restrict_Wv, trace_restrict_Lone, h2, ← hA] at h3
  rw [h1]
  have h4 : ((A.trace : ℤ) : ℝ) =
      ((Nat.card {w : InfinitePlace F // σ • w = w} : ℤ) : ℝ) - 1 := by
    push_cast
    rw [h3]
    ring
  exact_mod_cast h4


/-- 同じ UnitClass の mod p trace を、捩れ成分と実際の固定素点数へ接続する。 -/
theorem trace_vMap_eq_exponent_add_fixedPlaces (p : ℕ) [Fact p.Prime]
    (hdiv : p ∣ torsionOrder F) (σ : F ≃ₐ[ℚ] F) (n : ℕ)
    (hσ : ∀ x : 𝓞 F, x ^ p = 1 →
      (CyclotomicKummerEquivariance.integerAut σ).integers x = x ^ n) :
    LinearMap.trace (ZMod p) _ (vMap p F σ) =
      (n : ZMod p) + (Nat.card {w : InfinitePlace F // σ • w = w} : ZMod p) - 1 := by
  rw [trace_vMap p F hdiv σ n hσ, trace_quotMap_eq, Int.cast_sub,
    Int.cast_natCast, Int.cast_one]
  ring

end

section Cyclotomic

open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
open CyclotomicKummerEquivariance

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
noncomputable section

/-- 同じ指標で選んだ自己同型は、整数環のすべての p 乗根に d 乗で作用する。 -/
theorem integerAut_on_pth_roots (d : (ZMod p)ˣ) (x : 𝓞 (rootField ζ)) (hx : x ^ p = 1) :
    (integerAut ((characterEquiv hζ).symm d)).integers x = x ^ (d : ZMod p).val := by
  have hroot := (baseRoot_primitive hζ).toInteger_isPrimitiveRoot
  obtain ⟨a, _, ha⟩ := hroot.eq_pow_of_pow_eq_one hx
  have he : (integerAut ((characterEquiv hζ).symm d)).integers
      (baseRoot_primitive hζ).toInteger = (baseRoot_primitive hζ).toInteger ^ (d : ZMod p).val := by
    apply NumberField.RingOfIntegers.coe_injective
    exact characterEquiv_symm_root hζ d
  rw [← ha, map_pow, he, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- 同じ既存 unitAction の実際の trace。固定素点数の ±1 分類はまだ入力しない。 -/
theorem trace_unitAction_eq_character_add_fixedPlaces (d : (ZMod p)ˣ) :
    LinearMap.trace (ZMod p) _ (unitAction (p := p) ((characterEquiv hζ).symm d)) =
      (d : ZMod p) +
        (Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} : ZMod p) - 1 := by
  have hdiv : p ∣ torsionOrder (rootField ζ) :=
    dvd_torsionOrder_of_isPrimitiveRoot (baseRoot_primitive hζ)
  have h := trace_vMap_eq_exponent_add_fixedPlaces (rootField ζ) p hdiv
    ((characterEquiv hζ).symm d) (d : ZMod p).val (integerAut_on_pth_roots hζ d)
  rw [ZMod.natCast_zmod_val] at h
  exact h

end
end Cyclotomic
end DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace
```

## 回帰・依存監査

`DkMathTest.FLT.NumberFieldUnitLogTrace` は、実際の座標置換のトレースを確認する。
有理数体の無限素点上の恒等作用と、3座標のうち2つだけを交換する置換を使う。
後者は位数2でも trace=1 であり、置換の位数と固定座標数を区別する。

実際の原始5乗根と同じ rootField において、非自明な d=2 に対応する σd を取る。
整数環の全5乗根に対する2乗作用、同じ実単元の対数との同変性、
自由商の整数 trace と同じ mod 5 の unitAction の trace の接続を確認する。
ここでは #Fix(2)=0 自体は主張しない。
恒等 Galois 元に対しては、以前証明した単元商の次元2から実際に trace=2 を確認する。

主要11宣言について公理報告と再帰的な型・構成子・不透明証明本体の監査を行う。
公開入力監査は、一般のトレース分解の hdiv/hσ が明示されること、
自由商の固定点数公式にそれらが不要なこと、円分体への接続で内部供給されることを確認する。
構文的 import 閉包と公理・証明監査は別の検証である。
検証記録：`evidence/validation-note032-number-field-unit-trace.txt`。

## 残る2つの具体的な計算

次は円分体の無限素点を分類し、p≥5 に対して

    #Fix(d)=(p−1)/2  if d=±1,  and 0 otherwise

を同じ指標同型と同じ素点作用について証明する。
その後、既存の omegaSquareProjector の重み付きトレースを有限体の冪和で計算し、
trace(e₂)=1 を得る必要がある。
今回の最終公式はその直前までの無条件な接続であり、trace(e₂)=1 自体は未証明である。
前段の trace→hrank→hunit の条件付き経路はそのまま使えるが、一般 hrank はまだ閉じていない。
hclass・hbad・巡回塔の反復も残り、**一般 hno は未完成**である。

## 出典と同じ型を保つ変更

ローカルの `anthropics/fermats-last-theorem` の
`P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean`
（blob `6801f82a5eec740ce4d5d658b7a1dc35040f2aba`）を参考に、
捩れ・自由部分のトレース分解と Dirichlet 対数のトレース比較を適応した。
両 production と本稿のコード全文に Apache 著作権・License・NOTICE・blob を保持する。
DkMath の既存 integerAut、UnitClass、unitProjection、同じ Dirichlet 基底、
同じ rootField と characterEquiv を利用し、外部 ModP・作用・トレース定理を import しない。
外部 checkout をビルドしたり、公理監査したりしたという主張はしない。
