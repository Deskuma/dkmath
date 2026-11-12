# NOTE-032 教科書: 同じ巡回段の交叉・局所商像・位数 p の慣性固定商元

更新日: 2026-11-07。前回の狭い吸収障害を、４ステップで局所 Galois 加群と濃度へ接続する。
新しい配置仮定や吸収仮定を追加せず、既存の実際の証人から導く。
無条件 hno の算術的な排除が完成したという意味ではない。

## 模範解答で保持されているデータとの照合

ローカル checkout `/home/deskuma/develop/github/fermats-last-theorem` の
`S_FreyPackage_frey_no_cofixed_large.lean` の htoric、hKdown、滑らかな捩れの所属を調べた。
1291–1308行付近では、同じ次数・同じ段 K・滑らかな差点の条件を保ったまま差点を K へ戻す。
公開定理 `AddSubgroup.mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub`
も、K の濃度・零化条件・同じ零成分と追加の Step Three 条件を明示している。

DkMath では今回、その入力を無条件に供給したとは扱わない。
元の段と滑らかな部分群の交叉・商像を正確に数え、前回の差点がどの商で何を表すかを記述する。
外部の Step Three・分類・零成分所属定理の proof body を移植したわけではない。
参照コミットと SHA-256 は `evidence/note032-frey-component-reference-audit.json` に保存した。

## 1. 元の同じ部分群の交叉と実際の商像

可換加法群 G の部分群 K,H を考える。
K→G/H の核は K∩H と実際の同じ点で加法同型になり、像は K.map(mk_H) そのものである。
第一同型定理と濃度積公式から

|K| = |K∩H|・|image(K→G/H)|

を得る。さらに |K|=p^m で p が素数なら、ある r≤m が存在して

|K∩H|=p^r、|image(K→G/H)|=p^(m−r)

となる。交叉の濃度が p^m の約数であることと、元の同じ積公式を使う。
別の同濃度のモデルへ取り替えない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.Lib.Algebra.FiniteSubgroupIntersection"

/-!
# 同じ部分群の交叉と実際の商像の濃度

交叉・商像を元の群の中で保持する。素数冪の濃度を持つ場合は、
二つの濃度を相補的な指数に分解する。商を局所成分群と同定する算術は含まない。
-/
namespace DkMath.Lib.Algebra.FiniteSubgroupIntersection
variable {G : Type*} [AddCommGroup G] (K H : AddSubgroup G)

/-- 同じ K の H による商像への写像の核は、元の同じ交叉である。 -/
def intersectionKerEquiv :
    ↥(K ⊓ H) ≃+ ((QuotientAddGroup.mk' H).comp K.subtype).ker where
  toFun x := ⟨⟨x.val, x.property.1⟩, (QuotientAddGroup.eq_zero_iff x.val).mpr x.property.2⟩
  invFun x := ⟨x.val.val, ⟨x.val.property, (QuotientAddGroup.eq_zero_iff x.val.val).mp x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 第一同型定理による実際の濃度積。 -/
theorem card_intersection_mul_image :
    Nat.card K = Nat.card ↥(K ⊓ H) * Nat.card (K.map (QuotientAddGroup.mk' H)) := by
  let f := (QuotientAddGroup.mk' H).comp K.subtype
  have hr : f.range = K.map (QuotientAddGroup.mk' H) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  calc
    Nat.card K = Nat.card (K ⧸ f.ker) * Nat.card f.ker :=
      f.ker.card_eq_card_quotient_mul_card_addSubgroup
    _ = Nat.card f.range * Nat.card ↥(K ⊓ H) := by
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv,
        ← Nat.card_congr (intersectionKerEquiv K H).toEquiv]
    _ = _ := by rw [hr, Nat.mul_comm]

/-- 濃度 p^m の部分群の交叉と商像は p^r と p^(m-r) に正確に分かれる。 -/
theorem prime_power_profile {p m : ℕ} (hp : p.Prime) (hcard : Nat.card K = p ^ m) :
    ∃ r ≤ m, Nat.card ↥(K ⊓ H) = p ^ r ∧
      Nat.card (K.map (QuotientAddGroup.mk' H)) = p ^ (m - r) := by
  have hd : Nat.card ↥(K ⊓ H) ∣ p ^ m := by
    rw [← hcard]
    exact AddSubgroup.card_dvd_of_le inf_le_left
  obtain ⟨r, hr, he⟩ := (Nat.dvd_prime_pow hp).mp hd
  refine ⟨r, hr, he, ?_⟩
  have hc := card_intersection_mul_image K H
  rw [hcard, he] at hc
  apply mul_left_cancel₀ (pow_ne_zero r hp.ne_zero)
  calc
    p ^ r * Nat.card (K.map (QuotientAddGroup.mk' H)) = p ^ m := hc.symm
    _ = p ^ r * p ^ (m - r) := by rw [← pow_add, Nat.add_sub_of_le hr]

end DkMath.Lib.Algebra.FiniteSubgroupIntersection
```

## 2. 同じ段と滑らかな部分群の配置を濃度で記述する

同じ Source の実際の点群を G、既存の滑らかな部分群を H とする。
第 n 段 T の濃度は p^(n+1)。smoothIntersection と localComponentImage は
それぞれ実際の T∩H と、実際の G/H における T の像である。

一般の分解では r≤n+1。
同じ座標生成元が滑らかでない場合、r=n+1 なら交叉と T は濃度・包含から一致し、
生成元も滑らかになってしまう。したがって r≤n であり、局所商像は少なくとも p 元を持つ。

ここで使う局所商は、実際の全点群を実装済みの滑らかな部分群で割った商である。
Néron モデルの成分群との同定、判別式付値による次数公式、Frey 固有の配置排除は含まない。
この濃度解析には hclass、Cofixed、hbad は不要である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreySmoothStageAbsorption
import DkMath.Lib.Algebra.FiniteSubgroupIntersection

#print "file: DkMath.FLT.FreyStageLocalComponent"

/-!
# 同じ巡回段の滑らかな交叉と局所商像

局所商は元の実際の点群を既存の滑らかな部分群で割った商。
Néron 成分群との同定や判別式による成分群次数の公式を仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory EllipticTorsionRepresentation
open EllipticGoodReductionSeparation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 元の同じ段と同じ滑らかな部分群の交叉。 -/
def ResidualCyclicStage.smoothIntersection (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) : AddSubgroup (Points S.rationalCurve) :=
  T.carrier ⊓ S.valuationSmoothSubgroup A

/-- 元の段の、同じ局所点群商における実際の像。 -/
def ResidualCyclicStage.localComponentImage (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup (Points S.rationalCurve ⧸ S.valuationSmoothSubgroup A) :=
  T.carrier.map (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A))

/-- 同じ二つの濃度を相補的な p 冪指数で正確に記述する。 -/
theorem ResidualCyclicStage.local_component_profile (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ∃ r ≤ n + 1, Nat.card (T.smoothIntersection A) = p ^ r ∧
      Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) :=
  FiniteSubgroupIntersection.prime_power_profile T.carrier (S.valuationSmoothSubgroup A)
    (Fact.out : p.Prime) T.card

/-- 生成元が非滑らかなら、交叉は真に小さく、局所商像は少なくとも p 元を持つ。 -/
theorem ResidualCyclicStage.local_component_profile_of_not_smooth (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hg : ¬ HasSmoothReduction (S.valuationModel A) (T.coordinates 1).val) :
    ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
      Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) ∧
      p ≤ Nat.card (T.localComponentImage A) := by
  obtain ⟨r, hr, hI, hQ⟩ := T.local_component_profile A
  have hlt : r < n + 1 := by
    by_contra h
    have he : r = n + 1 := by omega
    let := T.finite
    have hc : Nat.card ↥(T.carrier ⊓ S.valuationSmoothSubgroup A) = Nat.card T.carrier := by
      simpa only [smoothIntersection, he, T.card] using hI
    have hEq : T.carrier ⊓ S.valuationSmoothSubgroup A = T.carrier :=
      AddSubgroup.eq_of_le_of_card_ge inf_le_left hc.ge
    have hmem : (T.coordinates 1).val ∈ T.carrier ⊓ S.valuationSmoothSubgroup A :=
      hEq.symm ▸ (T.coordinates 1).property
    exact hg ((S.mem_valuationSmoothSubgroup_iff A _).mp hmem.2)
  refine ⟨r, by omega, hI, hQ, ?_⟩
  rw [hQ]
  calc
    p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ (n + 1 - r) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)

end
end DkMath.FLT.Frey.Source
```

## 3. 一段上の有限捩れ商に実際の Galois 作用を構成する

E[p^(n+2)] 内で、元の T をその点の所属により部分群として読む。
これを upperStage とし、同じ群の商 upperQuotient を作る。
実際の E[p^(n+2)] は有限なので、同じ商も有限である。
T の元の Galois 安定性により、同じ有限捩れ作用は商上の群準同型へ降りる。
新しい商作用や安定性 provider を入力しない。

点 x が元の T の外にあり、p・x が T に入るなら、その商類は非零で p 倍が零。
p が素数なので、この商類の位数はちょうど p となる。
点そのものの位数が p だと主張しているのではない。
同じ実際の点が Galois 元に固定されるなら、同じ商作用もその類を固定する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTowerCharacter
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.FLT.FreyStageUpperQuotient"

/-!
# 元の同じ段による一段上の有限捩れ商と実際の Galois 作用

E[p^(n+2)] の中で元の T を保ち、その商を作る。
非零で p 倍が元の T に入る点は、この商で厳密位数 p を持つ。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 元の段を、一段上の同じ有限捩れ群内の部分群として読む。 -/
def ResidualCyclicStage.upperStage (T : S.ResidualCyclicStage L n) :
    AddSubgroup (Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  T.carrier.comap (torsionGroup S.rationalCurve (p ^ (n + 1 + 1))).subtype

/-- 同じ有限捩れ群による商。 -/
abbrev ResidualCyclicStage.upperQuotient (T : S.ResidualCyclicStage L n) :=
  Torsion S.rationalCurve (p ^ (n + 1 + 1)) ⧸ T.upperStage

/-- 一段上の実際の捩れ群が有限なので、この同じ商も有限。 -/
theorem ResidualCyclicStage.upperQuotient_finite (T : S.ResidualCyclicStage L n) :
    Finite T.upperQuotient := by
  let : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
  let : Finite (Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
    finite_torsion_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  infer_instance

/-- 同じ実際の Galois 作用は元の安定段を保ち、商上の群準同型を与える。 -/
def ResidualCyclicStage.upperQuotientAction (T : S.ResidualCyclicStage L n) :
    Field.absoluteGaloisGroup ℚ →* AddMonoid.End T.upperQuotient where
  toFun σ := QuotientAddGroup.map T.upperStage T.upperStage
    (representation S.rationalCurve (p ^ (n + 1 + 1)) σ).toAddMonoidHom
    (fun x hx => T.stable σ x.val hx)
  map_one' := by
    ext z
    refine QuotientAddGroup.induction_on z ?_
    intro x
    change (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve _ 1 x) =
      (QuotientAddGroup.mk' T.upperStage) x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    ext z
    refine QuotientAddGroup.induction_on z ?_
    intro x
    change (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve _ (σ * τ) x) =
      (QuotientAddGroup.mk' T.upperStage)
        (representation S.rationalCurve _ σ (representation S.rationalCurve _ τ x))
    rw [map_mul]
    rfl

/-- 元の段の外にあり p 倍が段に入る同じ点の剰余類は、厳密位数 p。 -/
theorem ResidualCyclicStage.upperClass_order_eq_prime (T : S.ResidualCyclicStage L n)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : x.val ∉ T.carrier) (hp : p • x.val ∈ T.carrier) :
    addOrderOf ((QuotientAddGroup.mk' T.upperStage) x) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · rw [← map_nsmul]
    apply (QuotientAddGroup.eq_zero_iff (N := T.upperStage) (p • x)).mpr
    exact hp
  · intro h
    exact hx ((QuotientAddGroup.eq_zero_iff (N := T.upperStage) x).mp h)

/-- 同じ有限点の固定性は、同じ商作用の固定性へ降りる。 -/
theorem ResidualCyclicStage.upperClass_fixed (T : S.ResidualCyclicStage L n)
    (σ : Field.absoluteGaloisGroup ℚ) (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : pointAction S.rationalCurve σ x.val = x.val) :
    T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
      (QuotientAddGroup.mk' T.upperStage) x := by
  exact congrArg (QuotientAddGroup.mk' T.upperStage) (Subtype.ext hx)

end
end DkMath.FLT.Frey.Source
```

## 4. 前回の同じ証明書から位数 p の慣性固定元を取り出す

既存の NarrowAbsorptionObstruction は、同じ T,q,A,τ,y と差点 δ=τy−y を保持する。
δ は滑らかで、δ∉T、p・δ∈T、p^(n+2)・δ=0、全慣性元に固定される。
ステップ2と3へこの同じ証明書を渡すことで、次のデータを同時に得る。

- 同じ交叉の濃度は p^r、r≤n。
- 同じ局所商像の濃度は p^(n+1−r)≥p。
- δ は G/H では零になる。
- 同じ δ の E[p^(n+2)]/T における類は厳密位数 p であり、全慣性群に固定される。

最後の存在定理は、従来の hclass と同じ一次元 Cofixed 直線からこれらを一緒に出力する。
新しい hbad・hplacement・商元の存在・濃度分解を仮定していない。
hclass は実際の ClassModP の ω² 固有条件消滅の型のまま保持する。
数値座標を計算するアルゴリズムではなく、古典的な存在証明である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedArithmeticObstruction
import DkMath.FLT.FreyStageLocalComponent
import DkMath.FLT.FreyStageUpperQuotient

#print "file: DkMath.FLT.FreyIntersectionQuotientObstruction"

/-!
# 同じ障害の交叉・局所商像・有限捩れ商による記述

差点は局所滑らか商では零だが、元の段による有限商では厳密位数 p の慣性固定元。
類群消滅と Cofixed のもとで同じ証人を保って接続する。配置障害の排除は未証明。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ}
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害の滑らかな交叉は p^r (r≤n)、局所商像は p^(n+1-r)≥p。 -/
theorem NarrowAbsorptionObstruction.intersection_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
      Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) ∧
      p ≤ Nat.card (T.localComponentImage A) :=
  T.local_component_profile_of_not_smooth A h.generator_not_smooth

/-- 同じ差点の局所滑らか商での像は零。有限捩れ商の非零元と取り違えない。 -/
theorem NarrowAbsorptionObstruction.difference_component_zero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (pointAction S.rationalCurve τ y - y) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr
    ((S.mem_valuationSmoothSubgroup_iff A _).mpr h.difference_smooth)

/-- 同じ差点は、一段上の有限捩れ商で厳密位数 p の全慣性固定元を与える。 -/
theorem NarrowAbsorptionObstruction.finite_quotient_witness
    (h : S.NarrowAbsorptionObstruction L T q A τ y) :
    ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
      x.val = pointAction S.rationalCurve τ y - y ∧
      addOrderOf ((QuotientAddGroup.mk' T.upperStage) x) = p ∧
      ∀ σ ∈ inertiaSubgroupIn A ℚ,
        T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
          (QuotientAddGroup.mk' T.upperStage) x := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) :=
    ⟨pointAction S.rationalCurve τ y - y, h.difference_killed⟩
  refine ⟨x, rfl, T.upperClass_order_eq_prime x h.escapes h.difference_p_mem, ?_⟩
  intro σ hσ
  exact T.upperClass_fixed σ x (h.difference_fixed σ hσ)

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
/-- 同じ Cofixed 候補の障害を交叉濃度と厳密位数 p の商元で強化する。
新しい配置・吸収・商元の存在を provider として追加しない。 -/
theorem residual_exists_intersection_quotient_obstruction
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve),
      S.NarrowAbsorptionObstruction L T q A τ y ∧
      ∃ r ≤ n, Nat.card (T.smoothIntersection A) = p ^ r ∧
        Nat.card (T.localComponentImage A) = p ^ (n + 1 - r) ∧
        p ≤ Nat.card (T.localComponentImage A) ∧
        (QuotientAddGroup.mk' (S.valuationSmoothSubgroup A)) (pointAction S.rationalCurve τ y - y) = 0 ∧
      ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
        x.val = pointAction S.rationalCurve τ y - y ∧
        addOrderOf ((QuotientAddGroup.mk' T.upperStage) x) = p ∧
        ∀ σ ∈ inertiaSubgroupIn A ℚ,
          T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
            (QuotientAddGroup.mk' T.upperStage) x := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  obtain ⟨r, hr, hI, hQ, hbound⟩ := h.intersection_profile
  exact ⟨n, T, q, A, τ, y, h, r, hr, hI, hQ, hbound, h.difference_component_zero, h.finite_quotient_witness⟩

end
end DkMath.FLT.Frey.Source
```

## 二つの商を混同しない

δ の像が一方の商で零、他方の商で非零という結果は矛盾ではない。
G/H の核は滑らかな部分群 H、有限捩れ商の核は元の段 T であり、異なる部分群だからである。
今回の障害は、この元の T と H の配置の不一致を記述している。

回帰例では G=(ZMod25)^2、K=第一軸、H=第一座標が法5で零になる部分群を使う。
δ=(0,5) は G/H では零だが G/K では位数ちょうど5。
同じ K の濃度は25、同じ交叉は5、同じ商像は5となることを確認する。
このような配置が一般の群で起こり得ることを保ったまま、Frey 固有の算術で排除する必要がある。

## 残る境界と検証

交叉・局所商像の濃度分解、実際の商 Galois 作用、厳密位数 p の慣性固定商元は実装済み。
その局所配置を排除する成分群・判別式の算術、hclass の無条件供給、一般 hno の無条件閉鎖は未完成。
前回の候補限定吸収・滑らかな配置を今回新たに仮定してはいない。

新規４モジュールを Lib/FLT/root、２つの test を通常入口へ公開する。
17宣言の公理・再帰依存監査と13件の公開入力監査を行う。
４つの Lean ブロックは production 各ファイル全文と同一であり、
各 import 直後の #print は元のモジュール名を保持する。
実行結果は `evidence/validation-note032-frey-intersection-quotient.txt` に記録する。
