# NOTE-032 教科書: 実際の交叉生成元・厳密位数・慣性差分準同型

更新日: 2026-11-07。レビューの生成元・差分準同型の提案を４ステップで形式化する。
元の点・段・座標・慣性群を保持し、新しい配置や吸収条件を導入しない。

## 模範解答と、今回閉じない分岐条件

ローカル checkout `/home/deskuma/develop/github/fermats-last-theorem` の
`S_FreyPackage_frey_no_cofixed_large.lean` にある htoric は、元の巡回段と零成分捩れの配置を保持する。
今回も元の段を別の同濃度の群へ取り替えず、同じ生成元を使う。

Frobenius 共役については、公開の
`ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime` も確認した。
この結論は φτφ⁻¹(τ^q)⁻¹ が慣性に属し、体の全非零元への作用比が1に合同となる条件である。
それだけで、その誤差が今回の有限捩れ商に自明に作用するとは結論できない。
参照コミットと SHA-256 は `evidence/note032-frey-generator-reference-audit.json` に保存した。
外部定理を production に import したり、野生誤差の作用消滅を新しく仮定したりしない。

## 1. 同じ巡回座標から交叉の実際の生成元を求める

K の濃度が p^m、同じ座標が e:ZMod(p^m)≃+K とする。
g=e(1) の実際の値は元の K 全体を生成する。
したがって G/H における g の像は K の商像全体を生成し、
その厳密位数は商像の実際の濃度と等しい。

交叉濃度が p^r、r≤m なら、前回の濃度積から商生成元の位数は p^(m−r)。
その倍点 p^(m−r)・g は H に入り、K にも属する。
この倍点の厳密位数を元の g の位数と nsmul の公式で計算し、濃度 p^r を得る。
元の交叉への包含と同じ濃度から、K∩H=〈p^(m−r)・g〉を証明する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FiniteSubgroupIntersection
import Mathlib.GroupTheory.SpecificGroups.Cyclic

#print "file: DkMath.Lib.Algebra.CyclicIntersectionGenerator"

/-!
# 同じ巡回群の交叉生成元と商生成元の厳密位数

同じ ZMod 座標の1を生成元とし、濃度指数を実際の倍点へ戻す。
-/
namespace DkMath.Lib.Algebra.CyclicIntersectionGenerator
variable {G : Type*} [AddCommGroup G] {p m : ℕ} [Fact p.Prime]
    (K H : AddSubgroup G) (e : ZMod (p ^ m) ≃+ K)

/-- 実際の座標生成元は元の同じ K 全体を生成する。 -/
theorem zmultiples_generator : AddSubgroup.zmultiples (e 1).val = K := by
  apply le_antisymm (AddSubgroup.zmultiples_le.mpr (e 1).property)
  intro x hx
  let z : K := ⟨x, hx⟩
  have he : (e.symm z).val • e 1 = z := by
    rw [← map_nsmul]
    simp only [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, AddEquiv.apply_symm_apply]
  refine ⟨((e.symm z).val : ℤ), ?_⟩
  have hv := congrArg K.subtype he
  rw [map_nsmul] at hv
  change (e.symm z).val • (e 1).val = x at hv
  simpa only [natCast_zsmul] using hv

/-- 同じ局所商生成元の位数は、元の K の実際の商像濃度。 -/
theorem quotient_generator_order :
    addOrderOf ((QuotientAddGroup.mk' H) (e 1).val) = Nat.card (K.map (QuotientAddGroup.mk' H)) := by
  have hs := congrArg (fun J : AddSubgroup G => J.map (QuotientAddGroup.mk' H)) (zmultiples_generator K e)
  rw [AddMonoidHom.map_zmultiples] at hs
  have hc := congrArg (fun J : AddSubgroup (G ⧸ H) => Nat.card J) hs
  rwa [Nat.card_zmultiples] at hc

/-- 交叉の濃度 p^r が既知なら、商生成元の位数は正確に p^(m-r)。 -/
theorem quotient_generator_order_prime_power (hK : Nat.card K = p ^ m)
    {r : ℕ} (hr : r ≤ m) (hI : Nat.card ↥(K ⊓ H) = p ^ r) :
    addOrderOf ((QuotientAddGroup.mk' H) (e 1).val) = p ^ (m - r) := by
  rw [quotient_generator_order K H e]
  apply mul_left_cancel₀ (pow_ne_zero r (Fact.out : p.Prime).ne_zero)
  rw [← hI, ← FiniteSubgroupIntersection.card_intersection_mul_image, hK, hI,
    ← pow_add, Nat.add_sub_of_le hr]

/-- 元の同じ交叉は、座標生成元の p^(m-r) 倍が生成する部分群そのもの。 -/
theorem intersection_eq_zmultiples (hK : Nat.card K = p ^ m)
    {r : ℕ} (hr : r ≤ m) (hI : Nat.card ↥(K ⊓ H) = p ^ r) :
    K ⊓ H = AddSubgroup.zmultiples (p ^ (m - r) • (e 1).val) := by
  have hqo := quotient_generator_order_prime_power K H e hK hr hI
  have hz : p ^ (m - r) • (QuotientAddGroup.mk' H) (e 1).val = 0 := by
    rw [← hqo]
    exact addOrderOf_nsmul_eq_zero _
  have hmem : p ^ (m - r) • (e 1).val ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    change (QuotientAddGroup.mk' H) (p ^ (m - r) • (e 1).val) = 0
    rwa [map_nsmul]
  have hle : AddSubgroup.zmultiples (p ^ (m - r) • (e 1).val) ≤ K ⊓ H :=
    AddSubgroup.zmultiples_le.mpr ⟨K.nsmul_mem (e 1).property _, hmem⟩
  have hgo : addOrderOf (e 1).val = p ^ m := by
    rw [← Nat.card_zmultiples, zmultiples_generator K e, hK]
  have hd : p ^ (m - r) ∣ addOrderOf (e 1).val := by
    rw [hgo]
    exact pow_dvd_pow p (by omega)
  have hcard : Nat.card (AddSubgroup.zmultiples (p ^ (m - r) • (e 1).val)) = p ^ r := by
    rw [Nat.card_zmultiples, addOrderOf_nsmul_of_dvd
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hd,
      hgo, Nat.pow_div (by omega) (Fact.out : p.Prime).pos]
    congr 1
    omega
  let : Finite K := Nat.finite_of_card_ne_zero (hK ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : Finite ↥(K ⊓ H) := Finite.of_injective
    (AddSubgroup.inclusion (show K ⊓ H ≤ K from inf_le_left)) (AddSubgroup.inclusion_injective _)
  exact (AddSubgroup.eq_of_le_of_card_ge hle (by rw [hI, hcard])).symm

end DkMath.Lib.Algebra.CyclicIntersectionGenerator
```

## 2. 積零の差分を通常の加法的準同型へ

実際の表現 ρ で (ρ(σ)−I)(ρ(τ)−I)=0 が全ての σ,τ に対して成立するとする。
固定した同じ点 x の差 c_x(τ)=ρ(τ)x−x は全ての σ に固定される。
一般の作用差分の積公式にこの固定性を代入すると、
c_x(στ)=c_x(σ)+c_x(τ) となる。
したがって通常の群準同型 Γ→Multiplicative(V) を構成できる。
Multiplicative は元の加法群を群準同型の型に合わせて包むだけである。
以前の単元値 Tate 指標 χ∞ や d と同じ種類の指標と誤認しない。

共役についても、任意の表現で成立する輸送恒等式を証明する。

ρ(φτφ⁻¹)(ρ(φ)x)−ρ(φ)x = ρ(φ)(ρ(τ)x−x)

基点が x から ρ(φ)x へ動く点が重要である。
この恒等式に Frobenius 性や差分積零性は不要である。
元の同じ基点での q 倍関係、野生慣性の自明性、外部分解群での共役不変性を結論しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

#print "file: DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter"

/-!
# 積零の作用差分は通常の加法的準同型になる

値は Multiplicative で包んだ元の加法群。共役輸送では基点も動かす。
Frobenius の q 倍関係や野生慣性の消滅は仮定しない。
-/
namespace DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
variable {R Γ V : Type*} [Ring R] [Group Γ] [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) (hprod : ∀ σ τ, (ρ σ - 1) * (ρ τ - 1) = 0)

include hprod

/-- 同じ差点は全作用元に固定される。 -/
theorem difference_fixed (σ τ : Γ) (x : V) : ρ σ (ρ τ x - x) = ρ τ x - x := by
  have h := congrArg (fun f : Module.End R V => f x) (hprod σ τ)
  change ρ σ (ρ τ x - x) - (ρ τ x - x) = 0 at h
  exact sub_eq_zero.mp h

/-- 二次の差分積が零なら、固定した同じ基点の差分は加法的。 -/
theorem difference_mul (σ τ : Γ) (x : V) :
    ρ (σ * τ) x - x = (ρ σ x - x) + (ρ τ x - x) := by
  rw [map_mul]
  change ρ σ (ρ τ x) - x = _
  calc
    ρ σ (ρ τ x) - x = ρ σ (ρ τ x - x) + (ρ σ x - x) := by rw [map_sub]; abel
    _ = _ := by rw [difference_fixed ρ hprod σ τ x]; abel

/-- 元の同じ加法群への通常の群準同型。 -/
def character (x : V) : Γ →* Multiplicative V where
  toFun σ := Multiplicative.ofAdd (ρ σ x - x)
  map_one' := by change ρ 1 x - x = 0; rw [map_one]; exact sub_self x
  map_mul' σ τ := difference_mul ρ hprod σ τ x

omit hprod in
/-- 共役の作用差分を輸送する恒等式。基点を ρ(φ)x へ動かすことが必要。 -/
theorem difference_conjugate (φ τ : Γ) (x : V) :
    ρ (φ * τ * φ⁻¹) (ρ φ x) - ρ φ x = ρ φ (ρ τ x - x) := by
  change (ρ (φ * τ * φ⁻¹) * ρ φ) x - ρ φ x = _
  rw [← map_mul, show (φ * τ * φ⁻¹) * φ = φ * τ by simp [mul_assoc], map_mul, map_sub]
  rfl

end DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
```

## 3. 同じ Frey 段の局所商生成元と、最初に滑らかになる指数

同じ段 T の座標 T.coordinates と、同じ滑らかな部分群 H_A を使う。
その座標生成元 g の局所商像の厳密位数は、前回の localComponentImage の濃度そのもの。
任意の自然数 k に対して、k・g が滑らかである条件は、この位数が k を割ることと同値である。

非滑らかな生成元の場合、前回の r≤n と濃度 p^r を使い、次を同時に得る。

- 同じ局所商生成元の厳密位数は p^(n+1−r)。
- 元の交叉は、元の生成元の p^(n+1−r) 倍が生成する部分群。
- p^k・g が滑らかであることと n+1−r≤k は同値。

濃度指数を単に記号として置くのでなく、実際の同じ倍点の所属条件へ戻した。
この局所群論には hclass・Cofixed・hbad は不要である。
Néron 成分群との同定や、判別式付値からの指数制約はここでは扱わない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageLocalComponent
import DkMath.Lib.Algebra.CyclicIntersectionGenerator

#print "file: DkMath.FLT.FreyStageIntersectionGenerator"

/-!
# 同じ交叉指数を実際の生成元・倍点・厳密位数へ戻す

滑らかな部分群での局所商を保持する。判別式や Néron 成分群の次数公式は含まない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open EllipticGoodReductionSeparation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 同じ局所商における実際の座標生成元の厳密位数。 -/
theorem ResidualCyclicStage.local_generator_order (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    addOrderOf ((QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val) =
      Nat.card (T.localComponentImage A) :=
  CyclicIntersectionGenerator.quotient_generator_order T.carrier (S.valuationSmoothSubgroup A) T.coordinates

/-- 交叉指数 r が与えられたとき、元の同じ交叉の実際の生成倍点。 -/
theorem ResidualCyclicStage.smooth_intersection_generator (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {r : ℕ} (hr : r ≤ n + 1)
    (hI : Nat.card (T.smoothIntersection A) = p ^ r) :
    T.smoothIntersection A = AddSubgroup.zmultiples (p ^ (n + 1 - r) • (T.coordinates 1).val) :=
  CyclicIntersectionGenerator.intersection_eq_zmultiples T.carrier (S.valuationSmoothSubgroup A)
    T.coordinates T.card hr hI

/-- 同じ生成元の k 倍が滑らかになる条件を、厳密位数による整数可除性で判定する。 -/
theorem ResidualCyclicStage.generator_multiple_smooth_iff (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (k : ℕ) :
    HasSmoothReduction (S.valuationModel A) (k • (T.coordinates 1).val) ↔
      Nat.card (T.localComponentImage A) ∣ k := by
  rw [← S.mem_valuationSmoothSubgroup_iff]
  calc
    k • (T.coordinates 1).val ∈ S.valuationSmoothSubgroup A ↔
        (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (k • (T.coordinates 1).val) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).symm
    _ ↔ k • (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val = 0 := by rw [map_nsmul]
    _ ↔ addOrderOf ((QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val) ∣ k :=
      addOrderOf_dvd_iff_nsmul_eq_zero.symm
    _ ↔ _ := by rw [T.local_generator_order A]

/-- 非滑らかな同じ生成元について、最初に滑らかになる p 冪指数まで確定する。 -/
theorem ResidualCyclicStage.local_generator_profile_of_not_smooth (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hg : ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val) :
    ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
      addOrderOf ((QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (T.coordinates 1).val) = p ^ (n + 1 - r) ∧
      T.smoothIntersection A = AddSubgroup.zmultiples (p ^ (n + 1 - r) • (T.coordinates 1).val) ∧
      ∀ k : ℕ, HasSmoothReduction (S.valuationModel A) (p ^ k • (T.coordinates 1).val) ↔ n + 1 - r ≤ k := by
  obtain ⟨r, hr, hI, hQ, _⟩ := T.local_component_profile_of_not_smooth A hg
  refine ⟨r, hr, hI, (T.local_generator_order A).trans hQ,
    T.smooth_intersection_generator A (by omega) hI, ?_⟩
  intro k
  rw [T.generator_multiple_smooth_iff A, hQ, Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt]

end
end DkMath.FLT.Frey.Source
```

## 4. 実際の Frey 慣性群から非自明な商値準同型へ

同じ悪い住所 q≠p の全有限捩れ作用について、慣性群の任意の二元の差分積零性を内部証明する。
臨界中心・接方向と p 冪の付値単元性は、既存の同じ Frey 幾何から供給する。
ステップ2を同じ慣性群への制限表現に適用し、有限点 x を基点とする差分準同型を得る。
すべての値は元の同じ慣性作用に固定される。

さらに同じ T による一段上の有限捩れ商へ合成する。
これは単なる点ごとの写像ではなく、慣性群から元の同じ商加法群への群準同型である。
同じ商作用の全慣性元が、その全ての値を固定する。

前回の障害証明書の点 y を基点に取ると、証人 τ での値は同じ δ=τy−y の商類となる。
δ∉T、p・δ∈T により、この値は非零で厳密位数 p を持つ。
最後に hclass と同じ一次元 Cofixed 候補から、この同じ準同型と非自明な値の存在を出力する。
新しい hbad・配置・準同型・位数を provider として追加しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedArithmeticObstruction
import DkMath.FLT.FreyStageUpperQuotient
import DkMath.Lib.NumberTheory.EllipticNodalUnipotence
import DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter

#print "file: DkMath.FLT.FreyInertiaDifferenceCharacter"

/-!
# 同じ慣性差分から通常の非自明な商値準同型へ

局所積零性を内部供給する。値は慣性固定、証人での商値は厳密位数 p。
Frobenius 共役を q 倍と同定したり、野生慣性を消去したりしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

section Local
variable (n : ℕ) (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
local notation "irep" => MonoidHom.comp (representation S.rationalCurve (p ^ (n + 1)))
  (Subgroup.subtype (inertiaSubgroupIn A ℚ))
include hp5 hq hqp haddr hA

/-- 同じ慣性群の任意の二元についての、実際の有限捩れ差分の積零性。 -/
theorem prime_power_inertia_difference_product_zero (σ τ : inertiaSubgroupIn A ℚ) :
    (irep σ - 1) * (irep τ - 1) = 0 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  exact EllipticNodalUnipotence.inertia_difference_product_zero S.rationalCurve _ A
    (S.valuationModel A) (S.valuationModel_map A) C D
    (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA n) σ.val τ.val σ.property τ.property

/-- 固定した同じ有限点 x の作用差分は、元の有限捩れ加法群への群準同型。 -/
def inertiaDifferenceCharacter (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    inertiaSubgroupIn A ℚ →* Multiplicative (Torsion S.rationalCurve (p ^ (n + 1))) :=
  UnipotentDifferenceCharacter.character irep
    (S.prime_power_inertia_difference_product_zero n hp5 hq hqp haddr A hA) x

/-- 同じ差分準同型の値はすべて、同じ全慣性群に固定される。 -/
theorem inertiaDifferenceCharacter_fixed (σ τ : inertiaSubgroupIn A ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    irep σ (Multiplicative.toAdd (S.inertiaDifferenceCharacter n hp5 hq hqp haddr A hA x τ)) =
      Multiplicative.toAdd (S.inertiaDifferenceCharacter n hp5 hq hqp haddr A hA x τ) :=
  UnipotentDifferenceCharacter.difference_fixed irep
    (S.prime_power_inertia_difference_product_zero n hp5 hq hqp haddr A hA) σ τ x
end Local

section Stage
variable {S}
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ上位有限捩れ商への実際の差分準同型。 -/
def ResidualCyclicStage.inertiaQuotientDifferenceCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    inertiaSubgroupIn A ℚ →* Multiplicative T.upperQuotient :=
  (QuotientAddGroup.mk' T.upperStage).toMultiplicative.comp
    (S.inertiaDifferenceCharacter (n + 1) hp5 hq hqp haddr A hA x)

/-- 値は元の同じ点作用差の商類。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_apply
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (τ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ) =
      (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve (p ^ (n + 1 + 1)) τ.val x - x) := rfl

/-- 商値準同型の全ての値は、同じ商作用の全慣性元に固定される。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_values_fixed
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ τ : inertiaSubgroupIn A ℚ) :
    T.upperQuotientAction σ.val
      (Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ)) =
      Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ) := by
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 hq hqp haddr A hA x τ]
  apply T.upperClass_fixed
  exact congrArg Subtype.val (S.inertiaDifferenceCharacter_fixed (n + 1) hp5 hq hqp haddr A hA σ τ x)
end Stage

variable {S} {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ狭い失敗点を基点とすると、同じ慣性元で非自明かつ厳密位数 p の商値を持つ。 -/
theorem NarrowAbsorptionObstruction.inertia_character_nontrivial
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  have ho := T.upperClass_order_eq_prime
    (representation S.rationalCurve (p ^ (n + 1 + 1)) τ x - x) h.escapes h.difference_p_mem
  constructor
  · intro he
    have hz := congrArg Multiplicative.toAdd he
    exact h.escapes ((QuotientAddGroup.eq_zero_iff (N := T.upperStage) _).mp hz)
  · exact ho

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
/-- hclass と同じ Cofixed 候補から、通常の非自明な慣性商値準同型を内部構成する。 -/
theorem residual_exists_nontrivial_inertia_quotient_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.inertia_character_nontrivial hp5⟩

end
end DkMath.FLT.Frey.Source
```

## 今回の結果で結論できないこと

この非自明な準同型の存在自体は矛盾ではない。
q≠p というだけで慣性群の p 部分が消えるとは言えず、商群全体の慣性自明性とも異なる。
今回、商値準同型の連続性や Frobenius の q 倍共役公式は新たに証明していない。

一般 hno の無条件化には、同じ配置・準同型に追加の Frey 固有の算術制約を与えること、
hclass の必要範囲での算術的供給が依然として残る。
今回の最終存在定理は従来の hclass と Cofixed を明示的に保持する。

## 検証とコピー

回帰例では ZMod25 の同じ座標生成元1、交叉〈5〉、商生成元の厳密位数5を確認する。
また (ZMod25)^2 の実際の剪断表現を使い、差分準同型の値 (t,0) と、
t=5 での非零・厳密位数5を検査する。

新規４モジュールを Lib/FLT/root、２つの test を通常入口へ公開する。
新規20宣言の公理・再帰依存監査と16件の公開入力監査を行う。
４つの Lean ブロックは各 production ファイル全文と同一である。
各 import 直後の #print は、コードだけをコピーしても元のモジュールを特定できるよう保持する。
実行結果は `evidence/validation-note032-frey-generator-character.txt` に記録する。
