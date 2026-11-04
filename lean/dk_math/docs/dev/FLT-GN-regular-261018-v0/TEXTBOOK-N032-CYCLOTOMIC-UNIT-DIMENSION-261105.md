# NOTE-032 教科書：実際の単元商の有限次元性と正確な次元

日付：2026-11-05。前段：`TEXTBOOK-N032-CYCLOTOMIC-OMEGA-SQUARE-DETECTION-261104.md`。
今回の2ステップは、①Dirichlet の有限生成性から同じ UnitClass の有限次元性、
②捩れ・自由部分の基底から円分体の同じ商の自然数次元 `(p−1)/2` の証明である。
その後、既存の同じ射影子の trace と hrank の正確な関係も接続した。
**射影子の trace=1 という算術的計算自体は未証明である。**

以下の2つの Lean ブロックは production ファイルの著作権表示を含む全文である。
それぞれモジュールとして順に配置して利用する。個別のコピペ後コンパイルを検証する。
正確なモジュール情報を保持するため、import 直後の `#print "file: …"` は省略しない。

## ステップ1：有限次元性を実際の商へ移す

任意の数体 F に対し U₀=Additive(𝓞 Fˣ)、U=Additive(UnitClass (𝓞 F) p) と置く。
`unitProjection` は既存の乗法記法の p 乗商の射影を加法記法にした、実際の準同型である。
外部実装の ModP を別に作って同一視する必要はない。

Dirichlet の単元定理により U₀ は有限生成 ℤ 加群である。
同じ射影の全射性から U も有限生成 ℤ 加群となり、
スカラーを ZMod p に拡大しても有限生成である。
これが `unitClassFinite` で、**p の素数性すら不要**である。
したがって、素数 p では同じ U が有限次元ベクトル空間となる。

## ステップ2の基礎：捩れと自由部分を両方含む基底

r=NumberField.Units.rank F、T=NumberField.Units.torsion F とする。
T は有限巡回群である。生成元 t を選び、p が |T| を割る場合、

    [t], [fundSystem 0], …, [fundSystem (r−1)]

は同じ単元冪商 U の基底になる。添字は `Option (Fin r)` とし、
`none` が捩れ生成元のクラス、`some i` が同じ基本単元のクラスである。

線形独立性では、mod p の一次関係を整数係数へ持ち上げ、

    u^p = t^a ∏ fundSystem(i)^bᵢ

という同じ単元群内の式に戻す。
Dirichlet 分解の一意性により bᵢ は p の倍数となり、mod p で零になる。
捩れの係数 a についても、t の位数が |T| で p∣|T| であることから零になる。
捩れのクラスを黙って捨てず、自由部分と同時に独立性を確認している。
生成性は、すべての元の Dirichlet 分解そのものから従う。

従って一般の数体でも、素数 p が実際の捩れ位数を割るときは

    dim(U)=r+1

を得る。この一般形の hdiv は本当の数学的仮定である。
次の円分体への適用では hdiv を原始根から内部供給する。

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Basis argument adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: use the SAME DkMath UnitClass and its actual quotient map,
prove finite-dimensionality directly from Dirichlet's finite generation.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

#print "file: DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension"

/-!
# 実際の整数環単元冪商の有限次元性と基底

任意の数体で有限生成性を証明する。素数 p が捩れ単元群の位数を割る場合は、
捩れ群の巡回生成元1個と Dirichlet の基本単元から実際の UnitClass の基底を作る。
Galois 作用の指標・固有空間の次元をここで仮定しない。
-/

namespace DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension

open KummerSelmerExact DkMath.Lib.Algebra NumberField NumberField.Units
open scoped NumberField
noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- 既存の単元冪商への実際の加法準同型。別の商を定義しない。 -/
def unitProjection (p : ℕ) : Additive (𝓞 F)ˣ →+ Additive (UnitClass (𝓞 F) p) :=
  (QuotientGroup.mk' (powerSubgroup (𝓞 F)ˣ p)).toAdditive

omit [NumberField F] in
theorem unitProjection_surjective (p : ℕ) : Function.Surjective (unitProjection (F := F) p) := by
  intro x
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (powerSubgroup (𝓞 F)ˣ p) x.toMul
  exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩

omit [NumberField F] in
/-- 零類は、同じ単元群の実際の p 倍（乗法記法では p 乗）と同値。 -/
theorem unitProjection_eq_zero_iff (p : ℕ) (a : Additive (𝓞 F)ˣ) :
    unitProjection p a = 0 ↔ ∃ b : Additive (𝓞 F)ˣ, p • b = a := by
  change (a.toMul : UnitClass (𝓞 F) p) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul hu⟩
  · rintro ⟨b, hb⟩
    exact ⟨b.toMul, congrArg Additive.toMul hb⟩

/-- Dirichlet の有限生成性の全射像。p の素数性すら不要。 -/
instance unitClassFinite (p : ℕ) : Module.Finite (ZMod p) (Additive (UnitClass (𝓞 F) p)) := by
  have : Module.Finite ℤ (Additive (UnitClass (𝓞 F) p)) :=
    Module.Finite.of_surjective (unitProjection p).toIntLinearMap (unitProjection_surjective p)
  exact Module.Finite.of_restrictScalars_finite ℤ (ZMod p) _

variable {p : ℕ} [hp : Fact p.Prime]

/-- 捩れ生成元と同じ基本単元の類からなる、実際の単元冪商の基底。 -/
theorem exists_unitClass_basis (F : Type*) [Field F] [NumberField F] (hdiv : p ∣ torsionOrder F) (t : torsion F)
    (ht : ∀ x : torsion F, x ∈ Subgroup.zpowers t) :
    ∃ b : Module.Basis (Option (Fin (rank F))) (ZMod p) (Additive (UnitClass (𝓞 F) p)),
      b none = unitProjection (F := F) p (Additive.ofMul (t : (𝓞 F)ˣ)) ∧
      ∀ i, b (some i) = unitProjection (F := F) p (Additive.ofMul (fundSystem F i)) := by
  classical
  have hord : orderOf t = torsionOrder F := by
    rw [torsionOrder]
    exact orderOf_eq_card_of_forall_mem_zpowers ht
  -- 捩れ部分の生成元と自由部分の基本単元を同じ族にまとめる。
  let a : Option (Fin (rank F)) → Additive (𝓞 F)ˣ := fun o =>
    o.elim (Additive.ofMul ((t : (𝓞 F)ˣ))) (fun i => Additive.ofMul (fundSystem F i))
  let v : Option (Fin (rank F)) → Additive (UnitClass (𝓞 F) p) := fun o => unitProjection (F := F) p (a o)
  have ha_none : Additive.toMul (a none) = (t : (𝓞 F)ˣ) := rfl
  have ha_some : ∀ i, Additive.toMul (a (some i)) = fundSystem F i := fun i => rfl
  -- 一次関係を実際の単元群の p 乗関係へ戻す。
  have hli : LinearIndependent (ZMod p) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have key : ∑ o, g o • v o = unitProjection (F := F) p (∑ o, (g o).val • a o) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    rw [key, unitProjection_eq_zero_iff] at hg
    obtain ⟨b, hb⟩ := hg
    set u : (𝓞 F)ˣ := Additive.toMul b with hu_def
    -- 同じ単元について、Dirichlet 分解の一意性を適用する。
    have hb' : u ^ p = (t : (𝓞 F)ˣ) ^ (g none).val *
        ∏ i, fundSystem F i ^ (((g (some i)).val : ℕ) : ℤ) := by
      have := congrArg Additive.toMul hb
      rw [toMul_nsmul, toMul_sum, Fintype.prod_option] at this
      simp only [toMul_nsmul, ha_none, ha_some, zpow_natCast] at this ⊢
      exact this
    -- 自由部分の指数と捩れ部分の指数をそれぞれ比較する。
    obtain ⟨⟨ζu, eu⟩, hu, -⟩ := exist_unique_eq_mul_prod F u
    have h1 : u ^ p = ((⟨t ^ (g none).val, fun i => (((g (some i)).val : ℕ) : ℤ)⟩ :
        torsion F × (Fin (rank F) → ℤ))).1 * ∏ i, fundSystem F i ^
          ((⟨t ^ (g none).val, fun i => (((g (some i)).val : ℕ) : ℤ)⟩ :
            torsion F × (Fin (rank F) → ℤ))).2 i := by
      simpa only [Subgroup.coe_pow] using hb'
    have h2 : u ^ p = ((⟨ζu ^ p, fun i => (p : ℤ) * eu i⟩ :
        torsion F × (Fin (rank F) → ℤ))).1 * ∏ i, fundSystem F i ^
          ((⟨ζu ^ p, fun i => (p : ℤ) * eu i⟩ : torsion F × (Fin (rank F) → ℤ))).2 i := by
      simp only [Subgroup.coe_pow]
      conv_lhs => rw [hu]
      rw [mul_pow, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
    have huniq := (exist_unique_eq_mul_prod F (u ^ p)).unique h1 h2
    simp only [Prod.mk.injEq] at huniq
    obtain ⟨htor, hfun⟩ := huniq
    intro o
    cases o with
    | some i =>
      have hi := congrFun hfun i
      -- 自由部分の係数は p の倍数なので mod p で零になる。
      rw [← ZMod.natCast_zmod_val (g (some i)), ← Int.cast_natCast, hi]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    | none =>
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζu)
      have : t ^ ((g none).val : ℤ) = t ^ (m * p) := by
        rw [zpow_natCast, htor, ← hm, ← zpow_natCast, ← zpow_mul]
      rw [zpow_eq_zpow_iff_modEq, hord] at this
      have hmod := this.of_dvd (Int.natCast_dvd_natCast.mpr hdiv)
      rw [← ZMod.natCast_zmod_val (g none), ← Int.cast_natCast,
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod]
      push_cast
      rw [ZMod.natCast_self, mul_zero]
  -- 任意の単元の Dirichlet 分解が、この族の生成性も与える。
  have hsp : ⊤ ≤ Submodule.span (ZMod p) (Set.range v) := by
    rintro x -
    obtain ⟨y, rfl⟩ := unitProjection_surjective (F := F) p x
    obtain ⟨⟨ζu, eu⟩, hu, -⟩ := exist_unique_eq_mul_prod F (Additive.toMul y)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ht ζu)
    have hy : y = m • a none + ∑ i, eu i • a (some i) := by
      apply Additive.toMul.injective
      rw [toMul_add, toMul_zsmul, toMul_sum, ha_none]
      simp only [toMul_zsmul, ha_some]
      rw [hu, ← hm, Subgroup.coe_zpow]
    rw [hy, map_add, map_zsmul, map_sum]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => ?_)
    · rw [← Int.cast_smul_eq_zsmul (ZMod p)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)
    · rw [map_zsmul, ← Int.cast_smul_eq_zsmul (ZMod p)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨some i, rfl⟩)
  refine ⟨Module.Basis.mk hli hsp, ?_, fun i => ?_⟩
  · rw [Module.Basis.mk_apply]; rfl
  · rw [Module.Basis.mk_apply]; rfl

/-- p が実際の捩れ位数を割るとき、単元商の次元は単元階数+1。 -/
theorem finrank_unitClass (F : Type*) [Field F] [NumberField F] (hdiv : p ∣ torsionOrder F) :
    Module.finrank (ZMod p) (Additive (UnitClass (𝓞 F) p)) = rank F + 1 := by
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := torsion F)
  obtain ⟨b, -, -⟩ := exists_unitClass_basis (p := p) F hdiv t ht
  rw [Module.finrank_eq_card_basis b, Fintype.card_option, Fintype.card_fin]


end
end DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension
```

## ステップ2：同じ円分体で自然数としての次元を計算する

p≥5、F が p 次円分拡大で、同じ指定根 ζ が原始 p 乗根であるとする。
その根は整数環の捩れ単元として位数 p を持つので、p∣torsionOrder F が従う。
これを前段の一般基底定理へ渡す。

Mathlib の円分体の無限素点の計算により

    nrRealPlaces F = 0,
    nrComplexPlaces F = φ(p)/2 = (p−1)/2

となる。Dirichlet の階数 r は無限素点の個数−1 なので、

    r=(p−3)/2,
    dim(U)=r+1=(p−1)/2

を自然数の等式として証明する。
`finrank_unitClass_cyclotomic` は一般の指定数体・根、
`root_unitClass_finrank` は同じ `rootField ζ` に対する定理である。
新しい次元 provider や捩れ位数 provider を要求しない。

## 既存の射影子との接続

W=weightSquareSpace hζ、e₂=omegaSquareProjector hζ とする。
有限次元性は U に加え、その同じ部分空間 W にも供給される。
前段の具体的な g=e₂[1+ζ]≠0 と合わせて、今回は初めて

    0 < finrank(W) ≤ (p−1)/2 < p

を得る。非零元の存在だけから、有限次元性を抜かして正の finrank を導いていない。

同じ射影子の冪等性と `range(e₂)=W` に Mathlib の射影の trace 定理を適用し、

    trace(e₂)=(finrank(W) : ZMod p)

を証明する。
ここで `trace(e₂)=1` の等式が別途証明されたなら、ZMod.val を取ることで

    finrank(W) mod p = 1

となる。既に finrank(W)<p が証明済みなので、自然数の finrank(W)=1 を復元できる。
その逆向きも成立し、`trace_eq_one_iff_finrank_eq_one` が正確な同値を示す。

この同値は残条件の整理であり、**trace(e₂)=1 そのものの証明ではない**。
また、`primaryWeightSquareSpace_eq_bot_of_trace` はその等式を htrace 入力として保持する。
従って、この条件付き定理をもって hunit や一般 hno が無条件に閉じたとは主張しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitPowerDimension
import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.LinearAlgebra.Trace

#print "file: DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank"

/-!
# 単元冪商の実際の次元と、同じ ω² 射影子のトレースによる次元判定

Dirichlet の基底と円分体の無限素点数から dim U=(p−1)/2 を無条件に証明する。
有限次元性を確立してから同じ非零固有元を利用し、1≤dim W<p を得る。
同じ射影子の trace=1 と dim W=1 の同値は証明するが、trace=1 自体は残る算術。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank

open NumberFieldUnitPowerDimension CyclotomicKernelField CyclotomicKummerWeight
open CyclotomicPrimaryUnitSpace CyclotomicOmegaSquareProjector CyclotomicPrimaryLogNonzero
open KummerSelmerExact
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- 指定した数体・指定した原始根の単元商の、自然数としての正確な次元。 -/
theorem finrank_unitClass_cyclotomic {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (Additive (UnitClass (𝓞 F) p)) = (p - 1) / 2 := by
  have hdiv : p ∣ NumberField.Units.torsionOrder F :=
    NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot hζ
  rw [finrank_unitClass F hdiv, NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero F (by omega : 2 < p),
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p,
    Nat.totient_prime (Fact.out : p.Prime)]
  omega

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 同じ rootField の実際の単元冪商は有限次元。trace や rank provider は不要。 -/
theorem unitClass_finite : Module.Finite (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) :=
  inferInstance

/-- 既存の同じ固有空間も実際に有限次元である。 -/
theorem weightSquareSpace_finite : Module.Finite (ZMod p) (weightSquareSpace hζ) :=
  inferInstance

include hζ in
/-- 同じ原始根で生成した体における、実際の単元商の次元公式。 -/
theorem root_unitClass_finrank (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) = (p - 1) / 2 := by
  let := rootField_isCyclotomic hζ
  exact finrank_unitClass_cyclotomic (baseRoot_primitive hζ) hp5

/-- 有限次元性を確立した後、前段の同じ非零固有元から正の次元を得る。 -/
theorem weightSquareSpace_finrank_pos (hp5 : 5 ≤ p) :
    0 < Module.finrank (ZMod p) (weightSquareSpace hζ) := by
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨projectedCyclotomicUnit hζ hp5, projectedCyclotomicUnit_ne_zero hζ hp5⟩

/-- 固有空間の自然数次元の上界。位数 p の法での比較と混同しない。 -/
theorem weightSquareSpace_finrank_le (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) ≤ (p - 1) / 2 := by
  rw [← root_unitClass_finrank hζ hp5]
  exact Submodule.finrank_le _

/-- 標数 p の trace から自然数次元を復元するための厳密な上界。 -/
theorem weightSquareSpace_finrank_lt_prime (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) < p := by
  have := weightSquareSpace_finrank_le hζ hp5
  omega

/-- 同じ冪等射影子の trace は、同じ既存の固有空間の次元の mod p 像。 -/
theorem trace_omegaSquareProjector_eq_finrank :
    LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) =
      (Module.finrank (ZMod p) (weightSquareSpace hζ) : ZMod p) := by
  have hid : IsIdempotentElem (omegaSquareProjector hζ) := omegaSquareProjector_idempotent hζ
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rwa [omegaSquareProjector_range] at h

/-- trace=1 の算術的証明が得られれば、mod p の一致から自然数の次元1を復元する。 -/
theorem weightSquareSpace_finrank_eq_one_of_trace (hp5 : 5 ≤ p)
    (htrace : LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) = 1 := by
  rw [trace_omegaSquareProjector_eq_finrank] at htrace
  have h := congrArg ZMod.val htrace
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (weightSquareSpace_finrank_lt_prime hζ hp5),
    ZMod.val_one] at h
  exact h

/-- 未解決の trace 値の計算と、従来の hrank の正確な同値。 -/
theorem trace_eq_one_iff_finrank_eq_one (hp5 : 5 ≤ p) :
    LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1 ↔
      Module.finrank (ZMod p) (weightSquareSpace hζ) = 1 := by
  constructor
  · exact weightSquareSpace_finrank_eq_one_of_trace hζ hp5
  · intro hrank
    rw [trace_omegaSquareProjector_eq_finrank, hrank, Nat.cast_one]

/-- 同じ実際の射影子の trace を明示入力として、証明済みの非零検出と合成する。 -/
theorem primaryWeightSquareSpace_eq_bot_of_trace (hp5 : 5 ≤ p)
    (htrace : LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1) :
    primaryWeightSquareSpace hζ = ⊥ :=
  primaryWeightSquareSpace_eq_bot_of_rank_one hζ hp5
    (weightSquareSpace_finrank_eq_one_of_trace hζ hp5 htrace)

end
end DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank
```

## 回帰例と公開経路

`DkMathTest.FLT.CyclotomicOmegaSquareUnitRank` は実際の原始5乗根・7乗根を選び、
それぞれ同じ rootField の整数環単元商の次元を **2 と3** として確認する。
同じ ω² 固有空間の次元の正値と上界、および実際の射影子の trace 等式も確認する。
trace=1 からの消滅を確認する回帰例には、欠けている等式を引き続き明示入力として残す。
さらに 6=1 in ZMod 5 だが 6≠1 in ℕ という反例で、自然数の厳密な上界の必要性を示す。
一般の有限生成性は p=0 と p=3 の有理数体の商についても確認する。

新しい2 production は Lib から通常の DkMath root へ公開する。
既存の Frey の `residual_cyclic_extension_has_stable_complement_of_unit_rank_one` には、
新しい `weightSquareSpace_finrank_eq_one_of_trace` の結論を渡せる。
その際も hbad・hclass と同じ巡回段の安定性・位数・底の包含条件は必要なままである。

主要13宣言の公理報告・再帰的な型／構成子／不透明証明本体の依存監査を行う。
入力監査では無条件な有限次元性・次元公式に htrace/hrank が不要であることと、
trace による条件付き次元1・消滅には htrace が残ることを確認する。
コード全文一致、正確なモジュール表示、Lib/root/test の到達性は別に検証する。
記録：`evidence/validation-note032-cyclotomic-unit-dimension.txt`。

## 次に残る算術と出典

次は、同じ `unitAction` のトレースを捩れ・自由部分の作用へ分け、
Dirichlet の対数埋め込みと無限素点の置換作用を比較して、
同じ `omegaSquareProjector hζ` の trace=1 を証明する必要がある。
今回その作用のトレース公式や無限素点上の固定点数は証明していない。
hclass・hbad・巡回塔の反復も残り、**一般 hno は引き続き未完成**である。

基底構成はローカルの `anthropics/fermats-last-theorem` の
`P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean`
（blob `6801f82a5eec740ce4d5d658b7a1dc35040f2aba`）を参考に適応した。
該当 production と本稿の全文コードに Apache 著作権・License・NOTICE・blob を保持する。
DkMath 自身の UnitClass と実際の射影を使用し、外部の ModP や最終次元1定理を import しない。
外部実装の最終消滅や Galois トレース公式を今回証明したとは主張しない。
外部 checkout は source を参照しており、ビルドや公理監査は実施していない。
