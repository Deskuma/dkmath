/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmerClassMap

#print "file: DkMath.Lib.NumberTheory.KummerSelmerExact"

/-!
# Selmer 群・整数環の単元冪商・類群捩れの完全性

代表元によらない実際の類群写像について、核が整数環の単元由来であることを示す。
類群の捩れの任意の元から逆に Selmer 類を構成し、右側の全射性も証明する。
Frey の局所算術による Selmer 所属や、Galois 同変性・消滅とは区別する。
-/

namespace DkMath.Lib.NumberTheory.KummerSelmerExact

open CyclotomicKummerWeight KummerSelmer KummerSelmerClassMap IsDedekindDomain
open DkMath.Lib.Algebra
open scoped nonZeroDivisors
noncomputable section

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]

/-- 正整数次数における整数環の単元冪商。 -/
abbrev UnitClass (R : Type*) [CommRing R] (p : ℕ) := Rˣ ⧸ powerSubgroup Rˣ p

/-- 類群の零条件を、同じ分数体の実際の主イデアル生成元へ戻す。 -/
theorem principal_of_class_eq_one (J : (FractionalIdeal R⁰ F)ˣ)
    (h : ClassGroup.mk F J = 1) : ∃ c : Fˣ, toPrincipalIdeal R F c = J := by
  have hp := ClassGroup.mk_eq_one_iff.mp h
  obtain ⟨c, hc⟩ := (FractionalIdeal.isPrincipal_iff (J : FractionalIdeal R⁰ F)).mp hp
  have hc0 : c ≠ 0 := by
    intro hz
    apply J.ne_zero
    rw [hc, hz, FractionalIdeal.spanSingleton_zero]
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [coe_toPrincipalIdeal]
  exact hc.symm

omit [IsDedekindDomain R] in
/-- 整数環の単元が生成する同じ分数イデアルは1である。 -/
theorem principal_of_unit (u : Rˣ) :
    toPrincipalIdeal R F (Units.map (algebraMap R F).toMonoidHom u) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R F (u : R)) = 1
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr u.isUnit, FractionalIdeal.coeIdeal_top]

/-- 同じ Selmer 類の類群像が零なら、元の類自身が実際の整数環単元から来る。 -/
theorem toClassGroup_eq_one_iff_unit (p : ℕ) (hp : 0 < p) (z : Selmer R F p) :
    toClassGroup p hp z = 1 ↔
      ∃ u : Rˣ, IsDedekindDomain.selmerGroup.fromUnit (K := F) (n := p) u = z := by
  obtain ⟨x, he⟩ := QuotientGroup.mk'_surjective (powerSubgroup Fˣ p) z.val
  change (x : KummerClass F p) = z.val at he
  have hx : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p := by
    rw [he]
    exact (mem_valuationSpace_iff_selmer p z.val).mpr z.property
  change classMapValue p z = 1 ↔ _
  rw [classMapValue_eq hp z x hx he]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := principal_of_class_eq_one (rootIdeal p x hx) h
    have hi : toPrincipalIdeal R F (c ^ p) = toPrincipalIdeal R F x := by
      rw [map_pow, hc, rootIdeal_pow]
    have his : FractionalIdeal.spanSingleton R⁰ ((c : F) ^ p) =
        FractionalIdeal.spanSingleton R⁰ (x : F) := by
      simpa only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] using congrArg Units.val hi
    obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp his
    have hxu : x = Units.map (algebraMap R F).toMonoidHom u * c ^ p := by
      apply Units.ext
      change (u : R) • (c : F) ^ p = (x : F) at hu
      rw [Algebra.smul_def] at hu
      exact hu.symm
    refine ⟨u, Subtype.ext ?_⟩
    change ((Units.map (algebraMap R F).toMonoidHom u : Fˣ) : KummerClass F p) = z.val
    rw [← he, hxu, QuotientGroup.mk_mul]
    have hcq : ((c ^ p : Fˣ) : KummerClass F p) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨c, rfl⟩
    rw [hcq, mul_one]
  · rintro ⟨u, hu⟩
    let y := Units.map (algebraMap R F).toMonoidHom u
    have hy := unit_mem_valuationSpace (F := F) p u
    have hey : (y : KummerClass F p) = z.val := congrArg Subtype.val hu
    rw [rootClass_independent hp x y hx hy (he.trans hey.symm)]
    have hr : rootIdeal p y hy = 1 := idealUnits_pow_injective hp (by
      dsimp only
      rw [rootIdeal_pow, one_pow]
      exact principal_of_unit u)
    rw [hr, map_one]

/-- 類群像が零なら、同じ代表元を実際の整数環単元と分数体の冪に分解する。 -/
theorem unit_decomposition (p : ℕ) (hp : 0 < p) (z : Selmer R F p)
    (hzero : toClassGroup p hp z = 1) (x : Fˣ) (he : (x : KummerClass F p) = z.val) :
    ∃ (u : Rˣ) (c : Fˣ), x = Units.map (algebraMap R F).toMonoidHom u * c ^ p := by
  obtain ⟨u, hu⟩ := (toClassGroup_eq_one_iff_unit p hp z).mp hzero
  have hq : (x : KummerClass F p) =
      ((Units.map (algebraMap R F).toMonoidHom u : Fˣ) : KummerClass F p) :=
    he.trans (congrArg Subtype.val hu).symm
  obtain ⟨c, hc⟩ := QuotientGroup.eq_iff_div_mem.mp hq
  refine ⟨u, c, ?_⟩
  change c ^ p = x / Units.map (algebraMap R F).toMonoidHom u at hc
  rw [hc]
  rw [← mul_div_assoc, mul_comm (Units.map (algebraMap R F).toMonoidHom u) x, mul_div_cancel_right]

/-- 単元冪商から同じ Selmer 群への自然な写像。 -/
def unitInclusion (p : ℕ) (hp : 0 < p) : UnitClass R p →* Selmer R F p := by
  let : Fact (0 < p) := ⟨hp⟩
  exact QuotientGroup.lift (powerSubgroup Rˣ p)
    (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := F) (n := p))
    (by rw [IsDedekindDomain.selmerGroup.fromUnit_ker]; exact le_rfl)

theorem unitInclusion_mk (p : ℕ) (hp : 0 < p) (u : Rˣ) :
    unitInclusion p hp (u : UnitClass R p) =
      IsDedekindDomain.selmerGroup.fromUnit (K := F) (n := p) u := rfl

/-- 正の指数の仮定と Dedekind 整域の整閉性により、単元冪商は単射に入る。 -/
theorem unitInclusion_injective (p : ℕ) (hp : 0 < p) :
    Function.Injective (unitInclusion (R := R) (F := F) p hp) := by
  let : Fact (0 < p) := ⟨hp⟩
  have hk : powerSubgroup Rˣ p ≤
      (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := F) (n := p)).ker := by
    rw [IsDedekindDomain.selmerGroup.fromUnit_ker]
    exact le_rfl
  change Function.Injective (QuotientGroup.lift (powerSubgroup Rˣ p)
    (IsDedekindDomain.selmerGroup.fromUnit (R := R) (K := F) (n := p)) hk)
  apply (QuotientGroup.injective_lift_iff _ _ hk).mpr
  exact (IsDedekindDomain.selmerGroup.fromUnit_ker (R := R) (K := F) (n := p)).symm

/-- 実際の類群捩れへの写像の核は、単元冪商の像と一致する。 -/
theorem kernel_eq_unit_range (p : ℕ) (hp : 0 < p) :
    (toClassTorsion (R := R) (F := F) p hp).ker = (unitInclusion (R := R) (F := F) p hp).range := by
  ext z
  constructor
  · intro hz
    have hzero : toClassGroup p hp z = 1 := congrArg Subtype.val hz
    obtain ⟨u, hu⟩ := (toClassGroup_eq_one_iff_unit p hp z).mp hzero
    exact ⟨(u : UnitClass R p), (unitInclusion_mk p hp u).trans hu⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (powerSubgroup Rˣ p) q
    apply Subtype.ext
    apply (toClassGroup_eq_one_iff_unit p hp _).mpr
    exact ⟨u, (unitInclusion_mk p hp u).symm⟩

/-- 類群の任意の `p` 捩れ元は、実際の Selmer 類から来る。 -/
theorem toClassTorsion_surjective (p : ℕ) (hp : 0 < p) :
    Function.Surjective (toClassTorsion (R := R) (F := F) p hp) := by
  have hs : ∀ a : ClassGroup R, a ^ p = 1 → ∃ z : Selmer R F p, toClassGroup p hp z = a := by
    intro a
    refine ClassGroup.induction F (fun J => ?_) a
    intro ha
    have hj : ClassGroup.mk F (J ^ p) = 1 := by rw [map_pow]; exact ha
    obtain ⟨x, hx⟩ := principal_of_class_eq_one (J ^ p) hj
    have hval : Additive.ofMul (x : KummerClass F p) ∈ valuationSpace (R := R) p := by
      apply (mem_valuationSpace_mk_iff p x).mpr
      intro v
      have he := congrArg Units.val hx
      rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] at he
      exact count_dvd_of_eq_pow p he v
    let z : Selmer R F p := ⟨(x : KummerClass F p), (mem_valuationSpace_iff_selmer p _).mp hval⟩
    refine ⟨z, ?_⟩
    change classMapValue p z = _
    rw [classMapValue_eq hp z x hval rfl]
    have hr : rootIdeal p x hval = J := idealUnits_pow_injective hp (by
      dsimp only
      rw [rootIdeal_pow, hx])
    rw [hr]
  intro a
  obtain ⟨z, hz⟩ := hs a.val a.property
  exact ⟨z, Subtype.ext hz⟩

/-- `1 → Rˣ/(Rˣ)^p → Selmer(∅,p) → Cl(R)[p] → 1` の三つの完全性条件。 -/
theorem short_exact (p : ℕ) (hp : 0 < p) :
    Function.Injective (unitInclusion (R := R) (F := F) p hp) ∧
      (toClassTorsion (R := R) (F := F) p hp).ker = (unitInclusion (R := R) (F := F) p hp).range ∧
      Function.Surjective (toClassTorsion (R := R) (F := F) p hp) :=
  ⟨unitInclusion_injective p hp, kernel_eq_unit_range p hp, toClassTorsion_surjective p hp⟩

end
end DkMath.Lib.NumberTheory.KummerSelmerExact
