# NOTE-032 教科書: 狭い吸収失敗点の局所幾何と Cofixed 候補への入力限定

更新日: 2026-11-07。前回の条件付き hno を前提に、残る吸収障害を４ステップ解析する。
今回は新しい算術入力の無条件供給を完成したとは扱わない。
実装するのは、滑らかな配置から吸収を導く定理、実際の失敗点の幾何、
それらを同じ類群・Cofixed 条件へ接続する証明書、量化を弱めた hno 入口である。

## 模範解答で何を確認したか

ローカル checkout `/home/deskuma/develop/github/fermats-last-theorem` の
`P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean` を確認した。
`htoric`（867行付近）は、巡回段の p 捩れの零成分所属と、
同じ次数の零成分捩れが段へ入ることを併せて供給する。
1110–1158行付近では、p・y∈K を保ち、高い倍点の滑らかさから差点の次数を下げて吸収する。
公開の `AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy` は、
底の作用係数が ±1 と異なる条件を使って滑らかな配置を導く。
共鳴分岐の配置には同じ単純な符号分離を使えず、模範の大域部分が必要となる。

今回は DkMath の既存の非共鳴証明から、配置が既知の場合に使える部分を独立させる。
模範の `htoric` 全体や共鳴分岐の配置、大域 Step Three を移植したわけではない。
参照コミットと SHA-256 は `evidence/note032-frey-obstruction-reference-audit.json` に保存する。
外部 P2M/P2MW を production に import しない。

## 1. 同じ段が滑らかなら狭い吸収が成立する

元の ResidualCyclicStage T は濃度 p^(n+1)、巡回性、安定性、底の包含を保つ。
その実際の座標生成元 T.coordinates(1) が部分群 H に入ることと、T 全体が H に入ることは同値。
座標逆写像の値を自然数倍として読み、元の同じ点の所属を証明する。

同じ悪い住所 A で T が滑らかな部分群に入るなら、次数 p^(n+1) の滑らかな捩れ全体に一致する。
含まれる方向は配置仮定から従い、逆は既存の幾何学的濃度上界と T の実際の濃度を比較して得る。
共鳴・非共鳴に依存しないが、T の滑らかな配置そのものは明示入力である。

p・y∈T なら y は p^(n+2) で消え、高い倍点 p^(n+1)・y は T 内の p 捩れ点となる。
配置によってこの高い倍点は滑らかなので慣性固定。
差点 τy−y は元から滑らかで、上の固定性により p^(n+1) で消える。
滑らかな同次数捩れ全体=T の一致から、差点は T に入る。
p・y∈T という狭い前提を、全高位捩れ条件に取り替えていない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia
import DkMath.FLT.FreyCyclicTowerCharacter
import DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll

#print "file: DkMath.FLT.FreySmoothStageAbsorption"

/-!
# 同じ巡回段の滑らかな配置から狭い吸収を導く

共鳴・非共鳴に依存しない配置判定。配置そのものは明示入力であり、
Cofixed 条件から全ての段が滑らかだとは結論しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 同じ段が部分群に入ることは、その実際の座標生成元の所属だけで判定できる。 -/
theorem ResidualCyclicStage.le_iff_generator_mem (T : S.ResidualCyclicStage L n)
    (H : AddSubgroup (Points S.rationalCurve)) :
    T.carrier ≤ H ↔ (T.coordinates 1).val ∈ H := by
  constructor
  · intro h
    exact h (T.coordinates 1).property
  · intro h x hx
    let z : T.carrier := ⟨x, hx⟩
    have he : ((T.coordinates.symm z).val) • T.coordinates 1 = z := by
      rw [← map_nsmul]
      simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, AddEquiv.apply_symm_apply]
    have hv := congrArg T.carrier.subtype he
    rw [map_nsmul] at hv
    change ((T.coordinates.symm z).val) • (T.coordinates 1).val = x at hv
    rw [← hv]
    exact H.nsmul_mem h _

/-- 滑らかな同じ巡回段は、同じ次数の滑らかな捩れ全体に一致する。 -/
theorem ResidualCyclicStage.eq_smooth_torsion_of_le (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hsm : T.carrier ≤ S.valuationSmoothSubgroup A) :
    T.carrier = AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  have hle : T.carrier ≤ AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A) :=
    fun x hx => ⟨T.killed x hx, hsm hx⟩
  have hbound : Nat.card (AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A)) ≤ p ^ (n + 1) := by
    apply EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion (S.valuationModel A)
      _ (S.valuationModel_map A) C D (pow_pos (Fact.out : p.Prime).pos _)
      (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA n) Subtype.val Subtype.val_injective
    · intro y
      exact (S.mem_valuationSmoothSubgroup_iff A y.val).mp y.property.2
    · intro y
      exact y.property.1
  let : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
  let : Finite (TorsionMultiplication.Kernel (Points S.rationalCurve) (p ^ (n + 1))) :=
    finite_torsion_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : Finite (AbsorbingTorsionFiltration.stage p (n + 1) (S.valuationSmoothSubgroup A)) :=
    AbsorbingTorsionFiltration.finiteStage p (n + 1) (S.valuationSmoothSubgroup A)
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, SetLike.coe_sort_coe, T.card]
  exact hbound

/-- 滑らかな配置なら、p•y∈T を保ったまま狭い慣性吸収が成立する。 -/
theorem ResidualCyclicStage.preimage_absorbs_of_smooth (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hsm : T.carrier ≤ S.valuationSmoothSubgroup A)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier) :
    pointAction S.rationalCurve τ y - y ∈ T.carrier := by
  have hyt : p ^ (n + 1 + 1) • y = 0 := by
    rw [pow_succ, mul_nsmul']
    exact T.killed _ hy
  have htop : p ^ (n + 1) • y ∈ T.carrier := by
    rw [pow_succ, mul_nsmul']
    exact T.carrier.nsmul_mem hy _
  have hptop : p • (p ^ (n + 1) • y) = 0 := by rwa [← mul_nsmul', ← pow_succ']
  have hs : HasSmoothReduction (S.valuationModel A) (p ^ (n + 1) • y) :=
    (S.mem_valuationSmoothSubgroup_iff A _).mp (hsm htop)
  have hf : pointAction S.rationalCurve τ (p ^ (n + 1) • y) = p ^ (n + 1) • y :=
    congrArg Subtype.val (S.residual_fixed_of_smooth_reduction hq hqp A hA τ hτ
      (⟨p ^ (n + 1) • y, hptop⟩ : S.ResidualSpace) hs)
  rw [T.eq_smooth_torsion_of_le hp5 hq hqp haddr A hA hsm]
  refine ⟨?_, (S.mem_valuationSmoothSubgroup_iff A _).mpr
    (S.inertia_difference_smooth_at_bad_address hp5 hq haddr A hA τ hτ y)⟩
  change p ^ (n + 1) • (pointAction S.rationalCurve τ y - y) = 0
  rw [nsmul_sub, ← map_nsmul, hf, sub_self]

end
end DkMath.FLT.Frey.Source
```

## 2. 失敗点について独立に証明できる局所算術

実際の同じ y が p・y∈T と δ=τy−y∉T を満たすとする。
ここには hclass や全段 hbad を入力しない。

- y と δ は p^(n+2) で消える。これは次数の上界であり、厳密位数の主張ではない。
- δ は滑らかに還元する。同じ慣性群のすべての元が δ を固定する。
- p・δ は元の T に属する。T の実際の安定性と p・y∈T から従う。
- δ は非零である。零なら T に属してしまう。
- 同じ座標生成元は滑らかに還元しない。もし滑らかならステップ1が失敗を排除する。

さらに同じモデルの臨界中心 C と接方向を構成し、生成元を実際の有限点 (x,z) として表示する。
既存の非滑らかさの判定により v_A(x−C.x)<1 を得る。
座標や q を数値計算しているのではなく、同じ幾何学的点についての存在証明である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreySmoothStageAbsorption

#print "file: DkMath.FLT.FreyNarrowFailureGeometry"

/-!
# 狭い吸収失敗点の同じ局所幾何

p•y∈T と τy−y∉T を保持する。差は滑らかな捩れ点であり慣性固定だが、
元の段の生成元は特異な剰余円板へ落ちる。類群消滅はこの局所解析には不要。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticGoodReductionSeparation ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 失敗点と差点の次数上界、差点の滑らかさ・全慣性固定性、p倍の元の段への所属。 -/
theorem ResidualCyclicStage.narrow_failure_profile (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier)
    (hfail : pointAction S.rationalCurve τ y - y ∉ T.carrier) :
    p ^ (n + 1 + 1) • y = 0 ∧
    p ^ (n + 1 + 1) • (pointAction S.rationalCurve τ y - y) = 0 ∧
    HasSmoothReduction (S.valuationModel A) (pointAction S.rationalCurve τ y - y) ∧
    (∀ σ ∈ inertiaSubgroupIn A ℚ, pointAction S.rationalCurve σ
      (pointAction S.rationalCurve τ y - y) = pointAction S.rationalCurve τ y - y) ∧
    p • (pointAction S.rationalCurve τ y - y) ∈ T.carrier ∧
    pointAction S.rationalCurve τ y - y ≠ 0 := by
  have hk : p ^ (n + 1 + 1) • y = 0 := by
    rw [pow_succ, mul_nsmul']
    exact T.killed _ hy
  have hd : p ^ (n + 1 + 1) • (pointAction S.rationalCurve τ y - y) = 0 := by
    rw [nsmul_sub, ← map_nsmul, hk, map_zero, sub_self]
  have hs := S.inertia_difference_smooth_at_bad_address hp5 hq haddr A hA τ hτ y
  refine ⟨hk, hd, hs, ?_, ?_, ?_⟩
  · intro σ hσ
    exact congrArg Subtype.val
      (EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction S.rationalCurve _ A
        (S.valuationModel A) (S.valuationModel_map A)
        (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA (n + 1)) σ hσ
        ⟨pointAction S.rationalCurve τ y - y, hd⟩ hs)
  · rw [nsmul_sub, ← map_nsmul]
    exact T.carrier.sub_mem (T.stable τ _ hy) hy
  · intro he
    exact hfail (he ▸ T.carrier.zero_mem)

/-- 狭い吸収が失敗した同じ段の座標生成元は、滑らかに還元しない。 -/
theorem ResidualCyclicStage.generator_not_smooth_of_narrow_failure (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier)
    (hfail : pointAction S.rationalCurve τ y - y ∉ T.carrier) :
    ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val := by
  intro hs
  have hsm := (T.le_iff_generator_mem (S.valuationSmoothSubgroup A)).mpr
    ((S.mem_valuationSmoothSubgroup_iff A _).mpr hs)
  exact hfail (T.preimage_absorbs_of_smooth hp5 hq hqp haddr A hA hsm τ hτ hy)

/-- 同じ非滑らかな生成元を、同じ臨界中心に対する実際の座標と付値不等式で記述する。 -/
theorem ResidualCyclicStage.exists_generator_depth_of_narrow_failure (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p • y ∈ T.carrier)
    (hfail : pointAction S.rationalCurve τ y - y ∉ T.carrier) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      Nonempty (TangentDirections C) ∧
      ∃ x z : AlgebraicClosure ℚ,
      ∃ h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x z,
        (T.coordinates 1).val = WeierstrassCurve.Affine.Point.some x z h ∧ A.valuation (x - C.x) < 1 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, hD⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  refine ⟨C, hD, ?_⟩
  have hg := T.generator_not_smooth_of_narrow_failure hp5 hq hqp haddr A hA τ hτ hy hfail
  generalize he : (T.coordinates 1).val = P at hg ⊢
  cases P with
  | zero => exact (hg (hasSmoothReduction_zero (S.valuationModel A) _)).elim
  | some x z h =>
    exact ⟨x, z, h, rfl, (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
      (S.valuationModel A) _ (S.valuationModel_map A) C h).mp hg⟩

end
end DkMath.FLT.Frey.Source
```

## 3. hclass と Cofixed から同じ幾何学的障害を取り出す

既存の狭い吸収失敗定理の q,A,τ,y,T をそのまま使う。
新しい NarrowAbsorptionObstruction は、それらの対象を外部パラメータに持つ命題であり、
点・差点・生成元の性質と臨界中心での深さを一緒に保持する。

hclass は実際の ClassModP と Galois 作用の ω² 固有条件に対する消滅仮定のまま使う。
同じ一次元 Cofixed 直線から、全段 hbad や配置を新しく仮定せず証明書の存在を導く。
この証明書は計算可能な数値証人を生成するアルゴリズムではない。
証明書の存在をもって、障害を排除したとは扱わない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNarrowFailureGeometry
import DkMath.FLT.FreyConditionalCofixedExclusion

#print "file: DkMath.FLT.FreyCofixedArithmeticObstruction"

/-!
# 類群消滅と Cofixed から生じる狭い吸収の幾何学的障害

失敗点は p 倍逆像の領域内。差点は滑らかで慣性固定、元の段生成元は非滑らか。
この配置の排除を証明したとは扱わない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticGoodReductionSeparation
open EllipticCriticalCentre EllipticTangentDirections ValuationInertia
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 狭い吸収の失敗を、同じ段・点・差点・生成元の幾何と一緒に保持する論理的証明書。
数値的な証人計算アルゴリズムではなく、実際の対象に対する存在証明の出力である。 -/
structure NarrowAbsorptionObstruction (L : Submodule (ZMod p) S.ResidualSpace)
    {n : ℕ} (T : S.ResidualCyclicStage L n) (q : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (τ : Field.absoluteGaloisGroup ℚ) (y : Points S.rationalCurve) : Prop where
  prime : q.Prime
  ne_torsion_prime : q ≠ p
  five_le : 5 ≤ q
  support : (q : ℤ) ∣ S.a * S.b * S.c
  resonance : (q : ZMod p) = 1 ∨ (q : ZMod p) = -1
  lies_over : LiesOverPrime A q
  inertia : τ ∈ inertiaSubgroupIn A ℚ
  preimage : p • y ∈ T.carrier
  escapes : pointAction S.rationalCurve τ y - y ∉ T.carrier
  killed : p ^ (n + 1 + 1) • y = 0
  difference_killed : p ^ (n + 1 + 1) • (pointAction S.rationalCurve τ y - y) = 0
  difference_smooth : HasSmoothReduction (S.valuationModel A) (pointAction S.rationalCurve τ y - y)
  difference_fixed : ∀ σ ∈ inertiaSubgroupIn A ℚ, pointAction S.rationalCurve σ
    (pointAction S.rationalCurve τ y - y) = pointAction S.rationalCurve τ y - y
  difference_p_mem : p • (pointAction S.rationalCurve τ y - y) ∈ T.carrier
  difference_ne_zero : pointAction S.rationalCurve τ y - y ≠ 0
  generator_not_smooth : ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val
  generator_depth : ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
    Nonempty (TangentDirections C) ∧ ∃ x z : AlgebraicClosure ℚ,
    ∃ h : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x z,
      (T.coordinates 1).val = WeierstrassCurve.Affine.Point.some x z h ∧ A.valuation (x - C.x) < 1
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- hclass と同じ Cofixed 候補から、実際の狭い失敗点の幾何学的証明書を得る。
全段 hbad や生成元の配置を入力しない。 -/
theorem residual_exists_narrow_geometric_obstruction
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), S.NarrowAbsorptionObstruction L T q A τ y := by
  obtain ⟨n, T, q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail⟩ :=
    S.residual_exists_narrow_absorption_counterexample L hline hζ hp5 hclass hcofixed
  obtain ⟨hk, hd, hsm, hfix, hpmem, hne⟩ :=
    T.narrow_failure_profile hp5 hq hqp (Or.inr hs) A hA τ hτ hy hfail
  refine ⟨n, T, q, A, τ, y, ⟨hq, hqp, hq5, hs, hr, hA, hτ, hy, hfail,
    hk, hd, hsm, hfix, hpmem, hne, ?_, ?_⟩⟩
  · exact T.generator_not_smooth_of_narrow_failure hp5 hq hqp (Or.inr hs) A hA τ hτ hy hfail
  · exact T.exists_generator_depth_of_narrow_failure hp5 hq hqp (Or.inr hs) A hA τ hτ hy hfail

end
end DkMath.FLT.Frey.Source
```

## 4. hno の算術入力を Cofixed 候補へ限定する

従来の hbadAll は全一次元直線の全段で狭い吸収を要求していた。
最終証明が使用するのは Cofixed 候補だけなので、hbadCandidate はその候補に限って要求する。
まず安定性を重複要求しない Cofixed 排除を証明し、既存 hno と同じ型へ接続する。
これは仮定の量化を弱めた条件付き endpoint であり、候補の吸収自体を証明したものではない。

配置側の十分条件も公開する。候補段の実際の生成元が各共鳴住所で滑らかなら、
ステップ1から狭い吸収を内部証明し、候補限定 endpoint に渡せる。
hplacement は未証明の算術的配置を表す明示入力である。
この定理を hplacement の構成や無条件 hno の完成と同一視してはならない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedArithmeticObstruction

#print "file: DkMath.FLT.FreyCandidateCofixedExclusion"

/-!
# Cofixed 候補だけの算術入力で足りる hno

全直線の吸収入力を Cofixed 候補に限定する。滑らかな生成元による十分条件も公開するが、
配置を実装したとは主張しない。無条件の一般 hno は依然として別工程。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hζ hp5 hclass in
/-- 狭い吸収を全直線でなく Cofixed 候補だけに要求する hno。
Cofixed から安定性が従うので、強い結論では安定性を重複要求しない。 -/
theorem residual_no_cofixed_of_candidate_absorption
    (hbadCandidate : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 → IsCofixedOn S.residualRepresentation L' →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n), S.ResonantAbsorptionAt T.carrier) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L' = 1 ∧ IsCofixedOn S.residualRepresentation L' := by
  rintro ⟨L', hline', hc⟩
  exact S.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
    L' hline' hζ hp5 hclass (hbadCandidate L' hline' hc) hc

include hζ hp5 hclass in
/-- 既存 hno と同じ形への接続。候補以外の直線の吸収を要求しない。 -/
theorem residual_hno_of_candidate_absorption
    (hbadCandidate : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 → IsCofixedOn S.residualRepresentation L' →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n), S.ResonantAbsorptionAt T.carrier) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L' = 1 ∧
      S.IsGaloisStable L' ∧ IsCofixedOn S.residualRepresentation L' := by
  rintro ⟨L', hline', _, hc⟩
  exact S.residual_no_cofixed_of_candidate_absorption hζ hp5 hclass hbadCandidate ⟨L', hline', hc⟩

include hζ hp5 hclass in
/-- 候補段の座標生成元の滑らかな配置が供給されれば、狭い吸収は内部証明できる。
この配置条件そのものは未証明の算術入力として明示する。 -/
theorem residual_no_cofixed_of_candidate_smooth_generators
    (hplacement : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 → IsCofixedOn S.residualRepresentation L' →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n),
      ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        EllipticGoodReductionSeparation.HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L' = 1 ∧ IsCofixedOn S.residualRepresentation L' := by
  apply S.residual_no_cofixed_of_candidate_absorption hζ hp5 hclass
  intro L' hl hc n T q hq hqp hq5 hs hr A hA τ hτ y hy
  have hsm := (T.le_iff_generator_mem (S.valuationSmoothSubgroup A)).mpr
    ((S.mem_valuationSmoothSubgroup_iff A _).mpr (hplacement L' hl hc n T q hq hqp hq5 hs hr A hA))
  exact T.preimage_absorbs_of_smooth hp5 hq hqp (Or.inr hs) A hA hsm τ hτ hy

end
end DkMath.FLT.Frey.Source
```

## 定義域の注意と残る境界

狭い吸収の対象は p・y∈K_n を満たす点で、位数 p^(n+2) の点を含み得る。
高位吸収の対象は E[p^(n+1)] で、p・y∉K_n となる点を含み得る。
一般には両対象は包含関係にないので、吸収命題を単純な強弱関係として扱わない。
回帰例は G=(ZMod125)^2、同じ K=〈(5,0)〉を使い、両方向の非包含を確認する。

今回、元の段生成元の非滑らかさと中心への付値不等式まで障害を具体化した。
差点が滑らかで慣性固定でも、別の部分群 T に属するとは限らない。
この配置の障害を Frey 判別式の算術や大域 Step Three で排除する工程は残る。
hclass の供給も未完成であり、算術入力を除去した一般 hno は未完成である。

## 検証とコピー

新規４モジュールを FLT/root、２つの test を通常入口へ公開する。
11宣言の公理・再帰依存・公開入力監査で、構造体の構成子と証明書の全フィールドも確認する。
４つの Lean ブロックは production 各ファイル全文と同一である。
各 import 直後の #print はコピー時にも元モジュールを特定できるよう保持する。
実行結果は `evidence/validation-note032-frey-arithmetic-obstruction.txt` に記録する。
