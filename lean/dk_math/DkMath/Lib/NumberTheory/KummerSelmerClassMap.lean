/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmer

#print "file: DkMath.Lib.NumberTheory.KummerSelmerClassMap"

/-!
# Selmer 群から実際の類群への写像

同じ代表元の主分数イデアルの冪根を選び、その類群の像を取る。
非零冪根の一意性により、代表元独立性と積の保存を証明する。
正の指数の仮定を保ち、Frey の Selmer 所属や類群成分の消滅は仮定しない。
-/

namespace DkMath.Lib.NumberTheory.KummerSelmerClassMap

open CyclotomicKummerWeight KummerSelmer IsDedekindDomain
open DkMath.Lib.Algebra
open scoped nonZeroDivisors
noncomputable section

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]

/-- 元の同じ商における `S=∅` Selmer 群。 -/
abbrev Selmer (R F : Type*) [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (p : ℕ) :=
  IsDedekindDomain.selmerGroup (R := R) (K := F) (S := (∅ : Set (HeightOneSpectrum R))) (n := p)

/-- 実際の類群の `p` 捩れ部分群。自明な類も含む。 -/
abbrev ClassTorsion (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) : Subgroup (ClassGroup R) :=
  (powMonoidHom p : ClassGroup R →* ClassGroup R).ker

/-- 同じ代表元の主分数イデアルの非零 `p` 乗根。 -/
def rootIdeal (p : ℕ) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    (FractionalIdeal R⁰ F)ˣ :=
  let h := exists_principal_fractionalIdeal_pow p x hx
  Units.mk0 h.choose h.choose_spec.1

theorem rootIdeal_pow (p : ℕ) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p) :
    rootIdeal p x hx ^ p = toPrincipalIdeal R F x := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_toPrincipalIdeal]
  exact (exists_principal_fractionalIdeal_pow p x hx).choose_spec.2

/-- 正の指数では単元化した非零分数イデアルの冪も単射。 -/
theorem idealUnits_pow_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (fun I : (FractionalIdeal R⁰ F)ˣ => I ^ p) := by
  intro I J h
  apply Units.ext
  exact fractionalIdeal_pow_injective hp I.ne_zero J.ne_zero (congrArg Units.val h)

theorem principal_class_eq_one (x : Fˣ) : ClassGroup.mk F (toPrincipalIdeal R F x) = 1 := by
  apply ClassGroup.mk_eq_one_iff.mpr
  exact ⟨⟨(x : F), by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩⟩

/-- 同じ Kummer 類の代表元を変えると、冪根は実際の主イデアル倍だけ変わる。 -/
theorem rootIdeal_change_representative {p : ℕ} (hp : 0 < p) (x y c : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p)
    (hy : Additive.ofMul (y : KummerClass F p) ∈ valuationSpace (R := R) p)
    (he : x = c ^ p * y) :
    rootIdeal p x hx = toPrincipalIdeal R F c * rootIdeal p y hy := by
  apply idealUnits_pow_injective hp
  dsimp only
  rw [mul_pow, rootIdeal_pow, rootIdeal_pow, ← map_pow, ← map_mul, he]

/-- 冪根の類群像は Kummer 代表元によらない。 -/
theorem rootClass_independent {p : ℕ} (hp : 0 < p) (x y : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p)
    (hy : Additive.ofMul (y : KummerClass F p) ∈ valuationSpace (R := R) p)
    (he : (x : KummerClass F p) = (y : KummerClass F p)) :
    ClassGroup.mk F (rootIdeal p x hx) = ClassGroup.mk F (rootIdeal p y hy) := by
  obtain ⟨c, hc⟩ := QuotientGroup.eq_iff_div_mem.mp he
  have he' : x = c ^ p * y := by
    change c ^ p = x / y at hc
    rw [hc, div_mul_cancel]
  rw [rootIdeal_change_representative hp x y c hx hy he', map_mul,
    principal_class_eq_one, one_mul]

/-- 同じ代表元から得た積の冪根も、実際のイデアルの積である。 -/
theorem rootIdeal_mul {p : ℕ} (hp : 0 < p) (x y : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p)
    (hy : Additive.ofMul (y : KummerClass F p) ∈ valuationSpace (R := R) p)
    (hxy : Additive.ofMul ((x * y : Fˣ) : KummerClass F p) ∈ valuationSpace (R := R) p) :
    rootIdeal p (x * y) hxy = rootIdeal p x hx * rootIdeal p y hy := by
  apply idealUnits_pow_injective hp
  dsimp only
  rw [rootIdeal_pow, mul_pow, rootIdeal_pow, rootIdeal_pow, map_mul]

private def representative (p : ℕ) (z : Selmer R F p) : Fˣ :=
  (QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z.val).choose

private theorem representative_eq (p : ℕ) (z : Selmer R F p) :
    (representative p z : KummerClass F p) = z.val :=
  (QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z.val).choose_spec

private theorem representative_mem (p : ℕ) (z : Selmer R F p) :
    Additive.ofMul (representative p z : KummerClass F p) ∈ valuationSpace (R := R) p := by
  rw [representative_eq]
  exact (mem_valuationSpace_iff_selmer p z.val).mpr z.property

/-- 代表元と冪根を実際に選んで定義した、類群への関数。 -/
def classMapValue (p : ℕ) (z : Selmer R F p) : ClassGroup R :=
  ClassGroup.mk F (rootIdeal p (representative p z) (representative_mem p z))

/-- 任意の同じ代表元でこの関数を計算できる。 -/
theorem classMapValue_eq {p : ℕ} (hp : 0 < p) (z : Selmer R F p) (x : Fˣ)
    (hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p)
    (he : (x : KummerClass F p) = z.val) :
    classMapValue p z = ClassGroup.mk F (rootIdeal p x hx) :=
  rootClass_independent hp _ x (representative_mem p z) hx ((representative_eq p z).trans he.symm)

/-- 同じ Selmer 群から実際の類群への準同型。 -/
def toClassGroup (p : ℕ) (hp : 0 < p) : Selmer R F p →* ClassGroup R where
  toFun := classMapValue p
  map_one' := by
    let hx : Additive.ofMul ((1 : Fˣ) : KummerClass F p) ∈ valuationSpace (R := R) p :=
      (valuationSpace (R := R) (F := F) p).zero_mem
    rw [classMapValue_eq hp 1 1 hx rfl]
    have h : rootIdeal p (1 : Fˣ) hx = 1 := idealUnits_pow_injective hp (by
      dsimp only
      rw [rootIdeal_pow, map_one, one_pow])
    rw [h, map_one]
  map_mul' z w := by
    let x := representative p z
    let y := representative p w
    have hx := representative_mem p z
    have hy := representative_mem p w
    have he : ((x * y : Fˣ) : KummerClass F p) = (z * w).val := by
      rw [QuotientGroup.mk_mul, representative_eq, representative_eq]
      rfl
    have hxy := (mem_valuationSpace_iff_selmer p _).mpr ((z * w).property)
    rw [← he] at hxy
    rw [classMapValue_eq hp (z * w) (x * y) hxy he,
      rootIdeal_mul hp x y hx hy hxy, map_mul]
    rfl

/-- 像は実際に `p` 捩れである。 -/
theorem toClassGroup_pow (p : ℕ) (hp : 0 < p) (z : Selmer R F p) :
    toClassGroup p hp z ^ p = 1 := by
  change ClassGroup.mk F (rootIdeal p _ _) ^ p = 1
  rw [← map_pow, rootIdeal_pow]
  exact principal_class_eq_one _

/-- 類群の `p` 捩れ部分群へ値域を制限した実際の写像。 -/
def toClassTorsion (p : ℕ) (hp : 0 < p) : Selmer R F p →* ClassTorsion R p :=
  (toClassGroup (R := R) (F := F) p hp).codRestrict _ (toClassGroup_pow p hp)

/-- 実際の類群の捩れ部分群を `ZMod p` 加群として読む。 -/
instance classTorsionModule (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) :
    Module (ZMod p) (Additive (ClassTorsion R p)) :=
  AddCommGroup.zmodModule (by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.toMul.val ^ p = 1
    exact a.toMul.property)

/-- 元の付値部分加群の同じベクトルを Selmer 群の元として読む。 -/
def ofValuationSpace (p : ℕ) (w : valuationSpace (R := R) (F := F) p) : Selmer R F p :=
  ⟨w.val.toMul, (mem_valuationSpace_iff_selmer p w.val.toMul).mp w.property⟩

/-- 同じ部分加群から同じ類群捩れへ向かう加法準同型。 -/
def toClassTorsionAdd (p : ℕ) (hp : 0 < p) :
    valuationSpace (R := R) (F := F) p →+ Additive (ClassTorsion R p) where
  toFun w := Additive.ofMul (toClassTorsion p hp (ofValuationSpace p w))
  map_zero' := by
    apply Additive.toMul.injective
    change toClassTorsion p hp (1 : Selmer R F p) = 1
    exact map_one _
  map_add' w z := by
    apply Additive.toMul.injective
    change toClassTorsion p hp (ofValuationSpace p w * ofValuationSpace p z) = _
    exact map_mul _ _ _

/-- Kummer の同じ付値部分加群から類群捩れへの `ZMod p` 線形写像。 -/
def toClassTorsionLinear (p : ℕ) (hp : 0 < p) :
    valuationSpace (R := R) (F := F) p →ₗ[ZMod p] Additive (ClassTorsion R p) :=
  (toClassTorsionAdd p hp).toZModLinearMap p

end
end DkMath.Lib.NumberTheory.KummerSelmerClassMap
