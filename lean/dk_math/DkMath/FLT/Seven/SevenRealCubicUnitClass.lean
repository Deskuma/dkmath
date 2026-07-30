/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCoprimeExtraction
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

#print "file: DkMath.FLT.Seven.SevenRealCubicUnitClass"

namespace DkMath.FLT.Seven

open scoped NumberField

noncomputable section

namespace SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Constant coefficient in the `1, theta, theta²` basis, reduced modulo
seven. -/
def thetaConstModSeven (x : SevenRealCubicInt) : ZMod 7 :=
  (x.fst + 3 * x.snd + 9 * x.thd : ℤ)

/-- Linear coefficient in the `1, theta, theta²` basis, reduced modulo
seven. -/
def thetaLinearModSeven (x : SevenRealCubicInt) : ZMod 7 :=
  (x.snd + 6 * x.thd : ℤ)

/-- Quadratic coefficient in the `1, theta, theta²` basis, reduced modulo
seven. -/
def thetaSquareModSeven (x : SevenRealCubicInt) : ZMod 7 :=
  x.thd

@[simp] theorem thetaConstModSeven_one :
    thetaConstModSeven 1 = 1 := by
  norm_num [thetaConstModSeven]

@[simp] theorem thetaLinearModSeven_one :
    thetaLinearModSeven 1 = 0 := by
  norm_num [thetaLinearModSeven]

@[simp] theorem thetaSquareModSeven_one :
    thetaSquareModSeven 1 = 0 := by
  norm_num [thetaSquareModSeven]

theorem thetaConstModSeven_mul (x y : SevenRealCubicInt) :
    thetaConstModSeven (x * y) =
      thetaConstModSeven x * thetaConstModSeven y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  simp [thetaConstModSeven]
  have hseven : (7 : ZMod 7) = 0 := by decide
  linear_combination
    -((b : ZMod 7) * (f : ZMod 7) +
      5 * (f : ZMod 7) * (c : ZMod 7) +
      (c : ZMod 7) * (e : ZMod 7)) * hseven

theorem thetaLinearModSeven_mul (x y : SevenRealCubicInt) :
    thetaLinearModSeven (x * y) =
      thetaConstModSeven x * thetaLinearModSeven y +
        thetaLinearModSeven x * thetaConstModSeven y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  simp [thetaConstModSeven, thetaLinearModSeven]
  have hseven : (7 : ZMod 7) = 0 := by decide
  linear_combination
    -(2 * (e : ZMod 7) * (c : ZMod 7) +
      2 * (b : ZMod 7) * (f : ZMod 7) +
      11 * (f : ZMod 7) * (c : ZMod 7)) * hseven

theorem thetaSquareModSeven_mul (x y : SevenRealCubicInt) :
    thetaSquareModSeven (x * y) =
      thetaConstModSeven x * thetaSquareModSeven y +
        thetaLinearModSeven x * thetaLinearModSeven y +
        thetaSquareModSeven x * thetaConstModSeven y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  simp [thetaConstModSeven, thetaLinearModSeven,
    thetaSquareModSeven]
  have hseven : (7 : ZMod 7) = 0 := by decide
  linear_combination
    -((f : ZMod 7) * (b : ZMod 7) +
      7 * (f : ZMod 7) * (c : ZMod 7) +
      (e : ZMod 7) * (c : ZMod 7)) * hseven

/-- The constant `theta`-coordinate of a global unit is nonzero modulo
seven. -/
theorem thetaConstModSeven_unit_ne_zero
    (u : SevenRealCubicIntˣ) :
    thetaConstModSeven (u : SevenRealCubicInt) ≠ 0 := by
  have hmul :
      thetaConstModSeven (u : SevenRealCubicInt) *
          thetaConstModSeven (↑u⁻¹ : SevenRealCubicInt) = 1 := by
    rw [← thetaConstModSeven_mul]
    simp
  intro hu
  rw [hu, zero_mul] at hmul
  exact zero_ne_one hmul

/-- First normalized nilpotent coordinate of a global unit modulo seven. -/
def unitNilpotentX (u : SevenRealCubicIntˣ) : ZMod 7 :=
  thetaLinearModSeven (u : SevenRealCubicInt) /
    thetaConstModSeven (u : SevenRealCubicInt)

/-- Second normalized nilpotent coordinate of a global unit modulo seven. -/
def unitNilpotentY (u : SevenRealCubicIntˣ) : ZMod 7 :=
  thetaSquareModSeven (u : SevenRealCubicInt) /
    thetaConstModSeven (u : SevenRealCubicInt)

@[simp] theorem unitNilpotentX_one :
    unitNilpotentX (1 : SevenRealCubicIntˣ) = 0 := by
  simp [unitNilpotentX]

@[simp] theorem unitNilpotentY_one :
    unitNilpotentY (1 : SevenRealCubicIntˣ) = 0 := by
  simp [unitNilpotentY]

theorem unitNilpotentX_mul
    (u v : SevenRealCubicIntˣ) :
    unitNilpotentX (u * v) =
      unitNilpotentX u + unitNilpotentX v := by
  rw [unitNilpotentX, unitNilpotentX, unitNilpotentX,
    Units.val_mul, thetaLinearModSeven_mul,
    thetaConstModSeven_mul]
  field_simp [thetaConstModSeven_unit_ne_zero]
  ring

theorem unitNilpotentY_mul
    (u v : SevenRealCubicIntˣ) :
    unitNilpotentY (u * v) =
      unitNilpotentY u + unitNilpotentY v +
        unitNilpotentX u * unitNilpotentX v := by
  rw [unitNilpotentY, unitNilpotentY, unitNilpotentY,
    unitNilpotentX, unitNilpotentX,
    Units.val_mul, thetaSquareModSeven_mul,
    thetaConstModSeven_mul]
  field_simp [thetaConstModSeven_unit_ne_zero]
  ring

/-- The truncated logarithm of a global unit in
`F_7[tau]/(tau^3)`, with the scalar coordinate removed. -/
def projectiveLogMul :
    SevenRealCubicIntˣ →*
      Multiplicative (ZMod 7 × ZMod 7) where
  toFun u :=
    Multiplicative.ofAdd
      (unitNilpotentX u,
        unitNilpotentY u - unitNilpotentX u ^ 2 / 2)
  map_one' := by
    ext <;> simp
  map_mul' u v := by
    change
      (unitNilpotentX (u * v),
          unitNilpotentY (u * v) -
            unitNilpotentX (u * v) ^ 2 / (2 : ZMod 7)) =
        (unitNilpotentX u,
            unitNilpotentY u -
              unitNilpotentX u ^ 2 / (2 : ZMod 7)) +
          (unitNilpotentX v,
            unitNilpotentY v -
              unitNilpotentX v ^ 2 / (2 : ZMod 7))
    ext
    · exact unitNilpotentX_mul u v
    · simp only [Prod.snd_add]
      rw [unitNilpotentX_mul, unitNilpotentY_mul]
      simp only [div_eq_mul_inv]
      rw [show (2 : ZMod 7)⁻¹ = 4 by decide]
      have hseven : (7 : ZMod 7) = 0 := by decide
      linear_combination
        -(unitNilpotentX u * unitNilpotentX v) * hseven

/-- Additive form of the projective truncated logarithm. -/
def projectiveLog :
    Additive SevenRealCubicIntˣ →+
      ZMod 7 × ZMod 7 :=
  projectiveLogMul.toAdditive

theorem projectiveLog_apply (u : SevenRealCubicIntˣ) :
    projectiveLog (Additive.ofMul u) =
      (unitNilpotentX u,
        unitNilpotentY u -
          unitNilpotentX u ^ 2 / (2 : ZMod 7)) :=
  rfl

theorem projectiveLog_pow_seven
    (u : SevenRealCubicIntˣ) :
    projectiveLog (Additive.ofMul (u ^ 7)) = 0 := by
  rw [ofMul_pow, map_nsmul]
  ext
  · simp only [nsmul_eq_mul, Nat.cast_ofNat,
      Prod.fst_mul, Prod.fst_ofNat, Prod.fst_zero,
      mul_eq_zero]
    exact Or.inl (by decide)
  · simp only [nsmul_eq_mul, Nat.cast_ofNat,
      Prod.snd_mul, Prod.snd_ofNat, Prod.snd_zero,
      mul_eq_zero]
    exact Or.inl (by decide)

theorem projectiveLog_neg_one :
    projectiveLog
      (Additive.ofMul (-1 : SevenRealCubicIntˣ)) = 0 := by
  rw [projectiveLog_apply]
  ext <;>
    norm_num [unitNilpotentX, unitNilpotentY,
      thetaConstModSeven, thetaLinearModSeven,
      thetaSquareModSeven]

/-- The explicit unit with value `alpha`. -/
def alphaUnit : SevenRealCubicIntˣ :=
  alpha_isUnit.unit

/-- The explicit unit with value `1 + alpha`. -/
def alphaAddOneUnit : SevenRealCubicIntˣ :=
  alphaAddOne_isUnit.unit

@[simp] theorem alphaUnit_val :
    (alphaUnit : SevenRealCubicInt) = alpha :=
  alpha_isUnit.unit_spec

@[simp] theorem alphaAddOneUnit_val :
    (alphaAddOneUnit : SevenRealCubicInt) = 1 + alpha :=
  alphaAddOne_isUnit.unit_spec

theorem projectiveLog_alpha :
    projectiveLog (Additive.ofMul alphaUnit) = (5, 5) := by
  ext <;>
    norm_num [projectiveLog_apply, unitNilpotentX,
      unitNilpotentY, thetaConstModSeven, thetaLinearModSeven,
      thetaSquareModSeven, alphaUnit, alpha] <;>
    decide

theorem projectiveLog_alphaAddOne :
    projectiveLog (Additive.ofMul alphaAddOneUnit) = (2, 5) := by
  ext <;>
    norm_num [projectiveLog_apply, unitNilpotentX,
      unitNilpotentY, thetaConstModSeven, thetaLinearModSeven,
      thetaSquareModSeven, alphaAddOneUnit, alpha] <;>
    decide

theorem projectiveLog_generator_det :
    (5 : ZMod 7) * 5 - 2 * 5 = 1 := by
  decide

theorem thetaConstModSeven_pow
    (x : SevenRealCubicInt) (n : ℕ) :
    thetaConstModSeven (x ^ n) =
      thetaConstModSeven x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, thetaConstModSeven_mul, ih]

theorem thetaLinearModSeven_pow_seven
    (x : SevenRealCubicInt) :
    thetaLinearModSeven (x ^ 7) = 0 := by
  simp only [show x ^ 7 = x * x * x * x * x * x * x by ring]
  rw [thetaLinearModSeven_mul, thetaConstModSeven_mul]
  rw [thetaLinearModSeven_mul, thetaConstModSeven_mul]
  rw [thetaLinearModSeven_mul, thetaConstModSeven_mul]
  rw [thetaLinearModSeven_mul, thetaConstModSeven_mul]
  rw [thetaLinearModSeven_mul, thetaConstModSeven_mul]
  rw [thetaLinearModSeven_mul]
  have hseven : (7 : ZMod 7) = 0 := by decide
  linear_combination
    thetaConstModSeven x ^ 6 *
      thetaLinearModSeven x * hseven

theorem thetaSquareModSeven_pow_seven
    (x : SevenRealCubicInt) :
    thetaSquareModSeven (x ^ 7) = 0 := by
  simp only [show x ^ 7 = x * x * x * x * x * x * x by ring]
  repeat'
    first
    | rw [thetaSquareModSeven_mul]
    | rw [thetaLinearModSeven_mul]
    | rw [thetaConstModSeven_mul]
  have hseven : (7 : ZMod 7) = 0 := by decide
  linear_combination
    (thetaConstModSeven x ^ 6 *
      thetaSquareModSeven x +
      3 * thetaConstModSeven x ^ 5 *
        thetaLinearModSeven x ^ 2) * hseven

theorem thetaConstModSeven_linearSource_ne_zero
    (a b : ℤ) (hab : IsCoprime a b)
    (hb : (7 : ℤ) ∣ b) :
    thetaConstModSeven (linearSource a b) ≠ 0 := by
  intro hzero
  have hbcast : (b : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mpr
      (by simpa using hb)
  have hacast : (a : ZMod 7) = 0 := by
    simpa [thetaConstModSeven, linearSource, hbcast] using hzero
  have ha : (7 : ℤ) ∣ a := by
    simpa using
      (ZMod.intCast_zmod_eq_zero_iff_dvd a 7).mp hacast
  have hunit : IsUnit (7 : ℤ) :=
    hab.isUnit_of_dvd' ha hb
  rw [Int.isUnit_iff] at hunit
  omega

/-- If a primitive seven-loaded linear source is a unit times a seventh
power, the unit has trivial projective logarithm modulo seven. -/
theorem projectiveLog_eq_zero_of_linearSource_eq_unit_mul_pow_seven
    (a b : ℤ) (hab : IsCoprime a b)
    (hb : (7 : ℤ) ∣ b)
    (u : SevenRealCubicIntˣ) (root : SevenRealCubicInt)
    (hsource :
      linearSource a b =
        (u : SevenRealCubicInt) * root ^ 7) :
    projectiveLog (Additive.ofMul u) = 0 := by
  have hsourceA :
      thetaConstModSeven (linearSource a b) ≠ 0 :=
    thetaConstModSeven_linearSource_ne_zero a b hab hb
  have hA :
      thetaConstModSeven (linearSource a b) =
        thetaConstModSeven (u : SevenRealCubicInt) *
          thetaConstModSeven root ^ 7 := by
    rw [hsource, thetaConstModSeven_mul,
      thetaConstModSeven_pow]
  have hrootA : thetaConstModSeven root ≠ 0 := by
    intro hzero
    apply hsourceA
    rw [hA, hzero]
    simp
  have hsourceB :
      thetaLinearModSeven (linearSource a b) = 0 := by
    have hbcast : (b : ZMod 7) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd b 7).mpr
        (by simpa using hb)
    simp [thetaLinearModSeven, linearSource, hbcast]
  have huB :
      thetaLinearModSeven (u : SevenRealCubicInt) = 0 := by
    have hproduct :
        thetaLinearModSeven (u : SevenRealCubicInt) *
            thetaConstModSeven root ^ 7 = 0 := by
      calc
        _ = thetaLinearModSeven
              ((u : SevenRealCubicInt) * root ^ 7) := by
          rw [thetaLinearModSeven_mul,
            thetaLinearModSeven_pow_seven,
            thetaConstModSeven_pow]
          ring
        _ = thetaLinearModSeven (linearSource a b) := by
          rw [← hsource]
        _ = 0 := hsourceB
    exact
      (mul_eq_zero.mp hproduct).resolve_right
        (pow_ne_zero 7 hrootA)
  have huC :
      thetaSquareModSeven (u : SevenRealCubicInt) = 0 := by
    have hsourceC :
        thetaSquareModSeven (linearSource a b) = 0 := by
      simp [thetaSquareModSeven, linearSource]
    have hproduct :
        thetaSquareModSeven (u : SevenRealCubicInt) *
            thetaConstModSeven root ^ 7 = 0 := by
      calc
        _ = thetaSquareModSeven
              ((u : SevenRealCubicInt) * root ^ 7) := by
          rw [thetaSquareModSeven_mul,
            thetaSquareModSeven_pow_seven,
            thetaLinearModSeven_pow_seven,
            thetaConstModSeven_pow]
          ring
        _ = thetaSquareModSeven (linearSource a b) := by
          rw [← hsource]
        _ = 0 := hsourceC
    exact
      (mul_eq_zero.mp hproduct).resolve_right
        (pow_ne_zero 7 hrootA)
  rw [projectiveLog_apply]
  ext
  · simp [unitNilpotentX, huB]
  · simp [unitNilpotentX, unitNilpotentY, huB, huC]

#print axioms thetaConstModSeven_mul
#print axioms projectiveLog_pow_seven
#print axioms projectiveLog_alpha
#print axioms projectiveLog_alphaAddOne
#print axioms
  projectiveLog_eq_zero_of_linearSource_eq_unit_mul_pow_seven

end SevenRealCubicInt

namespace SevenRealCubic

open SevenRealCubicInt

/-- Equivalence of unit groups induced by the explicit maximal-order
equivalence. -/
def modelUnitsEquivRingOfIntegers :
    SevenRealCubicIntˣ ≃* (𝓞 Field)ˣ :=
  Units.mapEquiv modelEquivRingOfIntegers.toMulEquiv

/-- Projective logarithm transported to units of the full ring of
integers. -/
def ringOfIntegersProjectiveLogMul :
    (𝓞 Field)ˣ →*
      Multiplicative (ZMod 7 × ZMod 7) :=
  projectiveLogMul.comp
    modelUnitsEquivRingOfIntegers.symm.toMonoidHom

private theorem field_finrank_odd :
    Odd (Module.finrank ℚ Field) := by
  rw [finrank_eq_three]
  norm_num

theorem torsion_le_ringOfIntegersProjectiveLogMul_ker :
    NumberField.Units.torsion Field ≤
      ringOfIntegersProjectiveLogMul.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  have hzpm :=
    NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
      field_finrank_odd ⟨z, hz⟩
  rcases hzpm with hz1 | hzneg
  · have hz1' : z = 1 := by simpa using hz1
    rw [hz1']
    simp [ringOfIntegersProjectiveLogMul]
  · have hmodel :
        modelUnitsEquivRingOfIntegers.symm z =
          (-1 : SevenRealCubicIntˣ) := by
      have hzneg' : z = -1 := by simpa using hzneg
      rw [hzneg']
      apply Units.ext
      change
        modelEquivRingOfIntegers.symm (-1) =
          (-1 : SevenRealCubicInt)
      rw [map_neg, map_one]
    change
      Multiplicative.ofAdd
        (projectiveLog
          (Additive.ofMul
            (modelUnitsEquivRingOfIntegers.symm z))) = 1
    rw [hmodel, projectiveLog_neg_one]
    rfl

/-- Projective logarithm after quotienting the global unit group by its
torsion subgroup. -/
def projectiveLogModTorsion :
    Additive
        ((𝓞 Field)ˣ ⧸
          NumberField.Units.torsion Field) →+
      ZMod 7 × ZMod 7 :=
  MonoidHom.toAdditive <|
    QuotientGroup.lift
      (NumberField.Units.torsion Field)
      ringOfIntegersProjectiveLogMul
      torsion_le_ringOfIntegersProjectiveLogMul_ker

/-- Global unit classes modulo torsion and seventh powers. -/
abbrev UnitClassModSeven : Type :=
  ModN
    (Additive
      ((𝓞 Field)ˣ ⧸
        NumberField.Units.torsion Field)) 7

/-- The projective logarithm descends through multiplication by seven. -/
def unitClassProjectiveLog :
    UnitClassModSeven →+
      ZMod 7 × ZMod 7 :=
  ModN.liftEquiv.symm
    ⟨projectiveLogModTorsion, fun q => by
      ext
      · simp only [nsmul_eq_mul, Prod.fst_mul,
          Prod.fst_zero]
        change
          (7 : ZMod 7) *
            (projectiveLogModTorsion q).1 = 0
        have hseven : (7 : ZMod 7) = 0 := by decide
        rw [hseven, zero_mul]
      · simp only [nsmul_eq_mul, Prod.snd_mul,
          Prod.snd_zero]
        change
          (7 : ZMod 7) *
            (projectiveLogModTorsion q).2 = 0
        have hseven : (7 : ZMod 7) = 0 := by decide
        rw [hseven, zero_mul]⟩

/-- Linear form of the descended projective logarithm. -/
def unitClassProjectiveLogLinear :
    UnitClassModSeven →ₗ[ZMod 7]
      ZMod 7 × ZMod 7 :=
  unitClassProjectiveLog.toZModLinearMap 7

/-- The class modulo torsion and seventh powers represented by a unit in
the concrete coordinate model. -/
def unitClassOfModel
    (u : SevenRealCubicIntˣ) :
    UnitClassModSeven :=
  ModN.mkQ 7 <|
    Additive.ofMul <|
      QuotientGroup.mk
        (modelUnitsEquivRingOfIntegers u)

@[simp] theorem unitClassProjectiveLog_unitClassOfModel
    (u : SevenRealCubicIntˣ) :
    unitClassProjectiveLog (unitClassOfModel u) =
      projectiveLog (Additive.ofMul u) := by
  have hcomp :
      unitClassProjectiveLog.comp (ModN.mkQ 7) =
        projectiveLogModTorsion := by
    exact congrArg Subtype.val <|
      ModN.liftEquiv.apply_symm_apply
        ⟨projectiveLogModTorsion, fun q => by
          ext
          · simp only [nsmul_eq_mul, Prod.fst_mul,
              Prod.fst_zero]
            change
              (7 : ZMod 7) *
                (projectiveLogModTorsion q).1 = 0
            rw [show (7 : ZMod 7) = 0 by decide, zero_mul]
          · simp only [nsmul_eq_mul, Prod.snd_mul,
              Prod.snd_zero]
            change
              (7 : ZMod 7) *
                (projectiveLogModTorsion q).2 = 0
            rw [show (7 : ZMod 7) = 0 by decide, zero_mul]⟩
  change
    unitClassProjectiveLog
        ((ModN.mkQ 7)
          (Additive.ofMul
            (QuotientGroup.mk
              (modelUnitsEquivRingOfIntegers u)))) =
      projectiveLog (Additive.ofMul u)
  rw [← AddMonoidHom.comp_apply, hcomp]
  change
    projectiveLog
        (Additive.ofMul
          (modelUnitsEquivRingOfIntegers.symm
            (modelUnitsEquivRingOfIntegers u))) =
      projectiveLog (Additive.ofMul u)
  rw [modelUnitsEquivRingOfIntegers.symm_apply_apply]

@[simp] theorem unitClassProjectiveLogLinear_unitClassOfModel
    (u : SevenRealCubicIntˣ) :
    unitClassProjectiveLogLinear (unitClassOfModel u) =
      projectiveLog (Additive.ofMul u) :=
  unitClassProjectiveLog_unitClassOfModel u

theorem unitClassProjectiveLog_surjective :
    Function.Surjective unitClassProjectiveLog := by
  rintro ⟨x, y⟩
  let i : ZMod 7 := 5 * x + 5 * y
  let j : ZMod 7 := 2 * x + 5 * y
  refine
    ⟨i • unitClassOfModel alphaUnit +
        j • unitClassOfModel alphaAddOneUnit, ?_⟩
  change
    unitClassProjectiveLogLinear
        (i • unitClassOfModel alphaUnit +
          j • unitClassOfModel alphaAddOneUnit) =
      (x, y)
  rw [map_add, map_smul, map_smul]
  rw [unitClassProjectiveLogLinear_unitClassOfModel,
    unitClassProjectiveLogLinear_unitClassOfModel]
  rw [projectiveLog_alpha, projectiveLog_alphaAddOne]
  ext
  · simp [i, j]
    ring_nf
    rw [show (29 : ZMod 7) = 1 by decide,
      show (35 : ZMod 7) = 0 by decide]
    ring
  · simp [i, j]
    ring_nf
    rw [show (35 : ZMod 7) = 0 by decide,
      show (50 : ZMod 7) = 1 by decide]
    ring

theorem unit_rank_eq_two :
    NumberField.Units.rank Field = 2 := by
  rw [NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrComplexPlaces_eq_zero]
  have hsignature :=
    NumberField.InfinitePlace.card_add_two_mul_card_eq_rank Field
  rw [nrComplexPlaces_eq_zero, finrank_eq_three] at hsignature
  omega

theorem unitClassModSeven_natCard :
    Nat.card UnitClassModSeven = 49 := by
  rw [ModN.natCard_eq,
    NumberField.Units.rank_modTorsion,
    unit_rank_eq_two]
  norm_num

theorem unitClassProjectiveLog_bijective :
    Function.Bijective unitClassProjectiveLog := by
  classical
  letI : Fintype UnitClassModSeven :=
    Fintype.ofFinite UnitClassModSeven
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨unitClassProjectiveLog_surjective, ?_⟩
  rw [← Nat.card_eq_fintype_card,
    unitClassModSeven_natCard,
    ← Nat.card_eq_fintype_card]
  norm_num

theorem unitClassProjectiveLog_injective :
    Function.Injective unitClassProjectiveLog :=
  unitClassProjectiveLog_bijective.injective

private theorem exists_ringOfIntegers_unit_pow_seven_of_class_eq_zero
    (u : (𝓞 Field)ˣ)
    (h :
      (ModN.mkQ 7)
          (Additive.ofMul
            (QuotientGroup.mk u :
              (𝓞 Field)ˣ ⧸
                NumberField.Units.torsion Field)) = 0) :
    ∃ v : (𝓞 Field)ˣ, u = v ^ 7 := by
  change
    Submodule.Quotient.mk
        (Additive.ofMul
          (QuotientGroup.mk u :
            (𝓞 Field)ˣ ⧸
              NumberField.Units.torsion Field)) = 0 at h
  rw [Submodule.Quotient.mk_eq_zero] at h
  rcases h with ⟨q, hq⟩
  simp only [LinearMap.lsmul_apply] at hq
  obtain ⟨v, hv⟩ :=
    QuotientGroup.mk'_surjective
      (NumberField.Units.torsion Field)
      (Additive.toMul q)
  have hquot :
      (QuotientGroup.mk (v ^ 7) :
          (𝓞 Field)ˣ ⧸
            NumberField.Units.torsion Field) =
        QuotientGroup.mk u := by
    have hvadd :
        Additive.ofMul
            (QuotientGroup.mk v :
              (𝓞 Field)ˣ ⧸
                NumberField.Units.torsion Field) = q := by
      apply Additive.toMul.injective
      simpa using hv
    apply Additive.ofMul.injective
    rw [QuotientGroup.mk_pow, ofMul_pow, hvadd]
    simpa using hq
  have hmem :
      u / v ^ 7 ∈
        NumberField.Units.torsion Field :=
    QuotientGroup.eq_iff_div_mem.mp hquot.symm
  have hpm :=
    NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank
      field_finrank_odd ⟨u / v ^ 7, hmem⟩
  rcases hpm with hplus | hminus
  · exact ⟨v, div_eq_one.mp (by simpa using hplus)⟩
  · refine ⟨-v, ?_⟩
    calc
      u = (u / v ^ 7) * v ^ 7 :=
        (div_mul_cancel u (v ^ 7)).symm
      _ = (-1) * v ^ 7 := by
        rw [show u / v ^ 7 = -1 by simpa using hminus]
      _ = (-v) ^ 7 := by
        rw [neg_pow]
        norm_num

/-- A concrete global unit is a seventh power exactly when its
two-coordinate projective logarithm modulo seven vanishes. -/
theorem unit_isSeventhPower_iff_projectiveLog_eq_zero
    (u : SevenRealCubicIntˣ) :
    (∃ v : SevenRealCubicIntˣ, u = v ^ 7) ↔
      projectiveLog (Additive.ofMul u) = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact projectiveLog_pow_seven v
  · intro hlog
    have hclass : unitClassOfModel u = 0 := by
      apply unitClassProjectiveLog_injective
      simpa using hlog
    obtain ⟨v, hv⟩ :=
      exists_ringOfIntegers_unit_pow_seven_of_class_eq_zero
        (modelUnitsEquivRingOfIntegers u) hclass
    refine
      ⟨modelUnitsEquivRingOfIntegers.symm v, ?_⟩
    apply modelUnitsEquivRingOfIntegers.injective
    simp [hv]

#print axioms unitClassModSeven_natCard
#print axioms unitClassProjectiveLog_bijective
#print axioms unit_isSeventhPower_iff_projectiveLog_eq_zero

end SevenRealCubic

namespace RamifiedRealCubicUpToUnitPacket

open SevenRealCubicInt

theorem leftUnit_projectiveLog_eq_zero
    (p : RamifiedRealCubicUpToUnitPacket) :
    projectiveLog (Additive.ofMul p.leftUnit) = 0 := by
  apply
    projectiveLog_eq_zero_of_linearSource_eq_unit_mul_pow_seven
      p.normPacket.quadratic.innerRoot.fst
      (-p.normPacket.quadratic.innerRoot.snd)
      p.normPacket.leftSource_coordinates_isCoprime
      (dvd_neg.mpr p.normPacket.innerSnd_seven_dvd)
      p.leftUnit p.leftPowerRoot
  simpa only [leftSource_eq_linearSource] using
    p.leftSource_eq

theorem rightUnit_projectiveLog_eq_zero
    (p : RamifiedRealCubicUpToUnitPacket) :
    projectiveLog (Additive.ofMul p.rightUnit) = 0 := by
  apply
    projectiveLog_eq_zero_of_linearSource_eq_unit_mul_pow_seven
      (p.normPacket.quadratic.innerRoot.fst +
        p.normPacket.quadratic.innerRoot.snd)
      p.normPacket.quadratic.innerRoot.snd
      p.normPacket.rightSource_coordinates_isCoprime
      p.normPacket.innerSnd_seven_dvd
      p.rightUnit p.rightPowerRoot
  simpa only [rightSource_eq_linearSource] using
    p.rightSource_eq

theorem exists_leftUnit_pow_seven
    (p : RamifiedRealCubicUpToUnitPacket) :
    ∃ v : SevenRealCubicIntˣ, p.leftUnit = v ^ 7 :=
  (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
    p.leftUnit).mpr p.leftUnit_projectiveLog_eq_zero

theorem exists_rightUnit_pow_seven
    (p : RamifiedRealCubicUpToUnitPacket) :
    ∃ v : SevenRealCubicIntˣ, p.rightUnit = v ^ 7 :=
  (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero
    p.rightUnit).mpr p.rightUnit_projectiveLog_eq_zero

end RamifiedRealCubicUpToUnitPacket

/-- RAMIFIED-012 output: the two real-cubic sources are exact seventh
powers, and their difference is the pure second-case equation. -/
structure RamifiedRealCubicExactPowerPacket : Type where
  upToUnit : RamifiedRealCubicUpToUnitPacket
  leftRoot : SevenRealCubicInt
  leftSource_eq :
    SevenRealCubicInt.leftSource
        upToUnit.normPacket.quadratic.innerRoot.fst
        upToUnit.normPacket.quadratic.innerRoot.snd =
      leftRoot ^ 7
  rightRoot : SevenRealCubicInt
  rightSource_eq :
    SevenRealCubicInt.rightSource
        upToUnit.normPacket.quadratic.innerRoot.fst
        upToUnit.normPacket.quadratic.innerRoot.snd =
      rightRoot ^ 7
  pureDifference_eq :
    rightRoot ^ 7 - leftRoot ^ 7 =
      SevenRealCubicInt.normalizedAxis ^ 6 *
        SevenRealCubicInt.normalizedWitness
          upToUnit.normPacket.innerSndRoot ^ 7

namespace RamifiedRealCubicUpToUnitPacket

open SevenRealCubicInt

/-- Every unit-times-power packet canonically advances to an exact-power
packet after absorbing seventh roots of the two units. -/
theorem nonempty_exactPower
    (p : RamifiedRealCubicUpToUnitPacket) :
    Nonempty RamifiedRealCubicExactPowerPacket := by
  obtain ⟨leftUnitRoot, hleftUnit⟩ :=
    p.exists_leftUnit_pow_seven
  obtain ⟨rightUnitRoot, hrightUnit⟩ :=
    p.exists_rightUnit_pow_seven
  let leftRoot : SevenRealCubicInt :=
    (leftUnitRoot : SevenRealCubicInt) * p.leftPowerRoot
  let rightRoot : SevenRealCubicInt :=
    (rightUnitRoot : SevenRealCubicInt) * p.rightPowerRoot
  have hleft :
      leftSource p.normPacket.quadratic.innerRoot.fst
          p.normPacket.quadratic.innerRoot.snd =
        leftRoot ^ 7 := by
    calc
      _ = (p.leftUnit : SevenRealCubicInt) *
            p.leftPowerRoot ^ 7 := p.leftSource_eq
      _ = ((leftUnitRoot : SevenRealCubicInt) ^ 7) *
            p.leftPowerRoot ^ 7 := by
        rw [hleftUnit]
        rfl
      _ = leftRoot ^ 7 := by
        simp only [leftRoot, mul_pow]
  have hright :
      rightSource p.normPacket.quadratic.innerRoot.fst
          p.normPacket.quadratic.innerRoot.snd =
        rightRoot ^ 7 := by
    calc
      _ = (p.rightUnit : SevenRealCubicInt) *
            p.rightPowerRoot ^ 7 := p.rightSource_eq
      _ = ((rightUnitRoot : SevenRealCubicInt) ^ 7) *
            p.rightPowerRoot ^ 7 := by
        rw [hrightUnit]
        rfl
      _ = rightRoot ^ 7 := by
        simp only [rightRoot, mul_pow]
  exact ⟨{
    upToUnit := p
    leftRoot := leftRoot
    leftSource_eq := hleft
    rightRoot := rightRoot
    rightSource_eq := hright
    pureDifference_eq := by
      rw [← hright, ← hleft]
      exact
        RamifiedRealCubicNormPacket.sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven
          p.normPacket }⟩

end RamifiedRealCubicUpToUnitPacket

namespace RamifiedRealCubicNormPacket

/-- Every RAMIFIED-009 norm packet reaches the exact RAMIFIED-012 pure
seventh-power equation. -/
theorem nonempty_exactPower
    (p : RamifiedRealCubicNormPacket) :
    Nonempty RamifiedRealCubicExactPowerPacket :=
  p.nonempty_upToUnit.elim
    RamifiedRealCubicUpToUnitPacket.nonempty_exactPower

end RamifiedRealCubicNormPacket

#print axioms
  RamifiedRealCubicUpToUnitPacket.leftUnit_projectiveLog_eq_zero
#print axioms
  RamifiedRealCubicUpToUnitPacket.nonempty_exactPower
#print axioms RamifiedRealCubicNormPacket.nonempty_exactPower

end

end DkMath.FLT.Seven
