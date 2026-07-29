/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.CubicSecondCoordinateSplit

#print "file: DkMath.FLT.Seven.SevenRealCubicInt"

namespace DkMath.FLT.Seven

/-- Integral coordinates `a + b * alpha + c * alpha^2` in the real cubic
order defined by `alpha^3 = 2 * alpha^2 + alpha - 1`. -/
structure SevenRealCubicInt where
  fst : ℤ
  snd : ℤ
  thd : ℤ
deriving DecidableEq, Repr

namespace SevenRealCubicInt

def ofInt (a : ℤ) : SevenRealCubicInt := ⟨a, 0, 0⟩
def alpha : SevenRealCubicInt := ⟨0, 1, 0⟩

@[simp] theorem ofInt_fst (a : ℤ) : (ofInt a).fst = a := rfl
@[simp] theorem ofInt_snd (a : ℤ) : (ofInt a).snd = 0 := rfl
@[simp] theorem ofInt_thd (a : ℤ) : (ofInt a).thd = 0 := rfl

def mul (x y : SevenRealCubicInt) : SevenRealCubicInt :=
  ⟨x.fst * y.fst - (x.snd * y.thd + x.thd * y.snd) -
      2 * x.thd * y.thd,
    x.fst * y.snd + x.snd * y.fst +
      (x.snd * y.thd + x.thd * y.snd) + x.thd * y.thd,
    x.fst * y.thd + x.snd * y.snd + x.thd * y.fst +
      2 * (x.snd * y.thd + x.thd * y.snd) +
      5 * x.thd * y.thd⟩

instance : Zero SevenRealCubicInt := ⟨⟨0, 0, 0⟩⟩
instance : One SevenRealCubicInt := ⟨⟨1, 0, 0⟩⟩
instance : Add SevenRealCubicInt :=
  ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd, x.thd + y.thd⟩⟩
instance : Neg SevenRealCubicInt :=
  ⟨fun x => ⟨-x.fst, -x.snd, -x.thd⟩⟩
instance : Sub SevenRealCubicInt :=
  ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd, x.thd - y.thd⟩⟩
instance : Mul SevenRealCubicInt := ⟨mul⟩

@[ext] theorem ext {x y : SevenRealCubicInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd)
    (hthd : x.thd = y.thd) : x = y := by
  cases x
  cases y
  simp_all

@[simp] theorem fst_zero : (0 : SevenRealCubicInt).fst = 0 := rfl
@[simp] theorem snd_zero : (0 : SevenRealCubicInt).snd = 0 := rfl
@[simp] theorem thd_zero : (0 : SevenRealCubicInt).thd = 0 := rfl
@[simp] theorem fst_one : (1 : SevenRealCubicInt).fst = 1 := rfl
@[simp] theorem snd_one : (1 : SevenRealCubicInt).snd = 0 := rfl
@[simp] theorem thd_one : (1 : SevenRealCubicInt).thd = 0 := rfl
@[simp] theorem fst_add (x y : SevenRealCubicInt) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_add (x y : SevenRealCubicInt) :
    (x + y).snd = x.snd + y.snd := rfl
@[simp] theorem thd_add (x y : SevenRealCubicInt) :
    (x + y).thd = x.thd + y.thd := rfl
@[simp] theorem fst_neg (x : SevenRealCubicInt) :
    (-x).fst = -x.fst := rfl
@[simp] theorem snd_neg (x : SevenRealCubicInt) :
    (-x).snd = -x.snd := rfl
@[simp] theorem thd_neg (x : SevenRealCubicInt) :
    (-x).thd = -x.thd := rfl
@[simp] theorem fst_sub (x y : SevenRealCubicInt) :
    (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem snd_sub (x y : SevenRealCubicInt) :
    (x - y).snd = x.snd - y.snd := rfl
@[simp] theorem thd_sub (x y : SevenRealCubicInt) :
    (x - y).thd = x.thd - y.thd := rfl
@[simp] theorem fst_mul (x y : SevenRealCubicInt) :
    (x * y).fst =
      x.fst * y.fst - (x.snd * y.thd + x.thd * y.snd) -
        2 * x.thd * y.thd := rfl
@[simp] theorem snd_mul (x y : SevenRealCubicInt) :
    (x * y).snd =
      x.fst * y.snd + x.snd * y.fst +
        (x.snd * y.thd + x.thd * y.snd) +
        x.thd * y.thd := rfl
@[simp] theorem thd_mul (x y : SevenRealCubicInt) :
    (x * y).thd =
      x.fst * y.thd + x.snd * y.snd + x.thd * y.fst +
        2 * (x.snd * y.thd + x.thd * y.snd) +
        5 * x.thd * y.thd := rfl

instance addCommGroup : AddCommGroup SevenRealCubicInt := by
  refine
    { sub := fun x y =>
        ⟨x.fst - y.fst, x.snd - y.snd, x.thd - y.thd⟩
      nsmul := @nsmulRec SevenRealCubicInt inferInstance inferInstance
      zsmul := @zsmulRec SevenRealCubicInt inferInstance inferInstance
        inferInstance (@nsmulRec SevenRealCubicInt inferInstance inferInstance)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]

instance addGroupWithOne : AddGroupWithOne SevenRealCubicInt :=
  { addCommGroup with
    natCast := fun n => ⟨n, 0, 0⟩
    intCast := fun z => ⟨z, 0, 0⟩ }

@[simp] theorem fst_natCast (n : ℕ) :
    (n : SevenRealCubicInt).fst = n := rfl
@[simp] theorem snd_natCast (n : ℕ) :
    (n : SevenRealCubicInt).snd = 0 := rfl
@[simp] theorem thd_natCast (n : ℕ) :
    (n : SevenRealCubicInt).thd = 0 := rfl
@[simp] theorem fst_intCast (z : ℤ) :
    (z : SevenRealCubicInt).fst = z := rfl
@[simp] theorem snd_intCast (z : ℤ) :
    (z : SevenRealCubicInt).snd = 0 := rfl
@[simp] theorem thd_intCast (z : ℤ) :
    (z : SevenRealCubicInt).thd = 0 := rfl

instance commRing : CommRing SevenRealCubicInt := by
  refine
    { addGroupWithOne with
      add_comm := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;> simp <;> ring

@[simp] theorem intCast_eq (a : ℤ) :
    (a : SevenRealCubicInt) = ofInt a := rfl

@[simp] theorem alpha_fst : alpha.fst = 0 := rfl
@[simp] theorem alpha_snd : alpha.snd = 1 := rfl
@[simp] theorem alpha_thd : alpha.thd = 0 := rfl

/-- Defining relation of the discriminant-49 cubic order. -/
theorem alpha_cube :
    alpha ^ 3 = 2 * alpha ^ 2 + alpha - 1 := by
  change alpha ^ 3 = ofInt 2 * alpha ^ 2 + alpha - ofInt 1
  ext <;> norm_num [pow_succ, mul]

/-- Determinant of multiplication by an integral cubic element. -/
def norm (x : SevenRealCubicInt) : ℤ :=
  x.fst ^ 3 + 2 * x.fst ^ 2 * x.snd +
    6 * x.fst ^ 2 * x.thd - x.fst * x.snd ^ 2 +
    x.fst * x.snd * x.thd + 5 * x.fst * x.thd ^ 2 -
    x.snd ^ 3 - 2 * x.snd ^ 2 * x.thd +
    x.snd * x.thd ^ 2 + x.thd ^ 3

@[simp] theorem norm_intCast (a : ℤ) :
    norm (a : SevenRealCubicInt) = a ^ 3 := by
  simp [norm]

theorem norm_mul (x y : SevenRealCubicInt) :
    norm (x * y) = norm x * norm y := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  simp [norm]
  ring

/-- Left and right norm-source elements attached to the two cubic factors. -/
def leftSource (a n : ℤ) : SevenRealCubicInt :=
  ⟨a, -n, 0⟩

def rightSource (a n : ℤ) : SevenRealCubicInt :=
  ⟨a + n, n, 0⟩

theorem leftSource_eq (a n : ℤ) :
    leftSource a n =
      (a : SevenRealCubicInt) - alpha * (n : SevenRealCubicInt) := by
  ext <;> simp [leftSource, alpha]

theorem rightSource_eq (a n : ℤ) :
    rightSource a n =
      (a : SevenRealCubicInt) +
        (1 + alpha) * (n : SevenRealCubicInt) := by
  ext <;> simp [rightSource, alpha]

theorem norm_leftSource (a n : ℤ) :
    norm (leftSource a n) = seventhPowerSndLeftCubic a n := by
  simp [leftSource, norm, seventhPowerSndLeftCubic]
  ring

theorem norm_rightSource (a n : ℤ) :
    norm (rightSource a n) = seventhPowerSndRightCubic a n := by
  simp [rightSource, norm, seventhPowerSndRightCubic]
  ring

/-- The two monic cubic forms have discriminant 49. -/
theorem leftPolynomial_discriminant_eq :
    (-2 : ℤ) ^ 2 * (-1) ^ 2 - 4 * (-1) ^ 3 -
      4 * (-2) ^ 3 * 1 - 27 * 1 ^ 2 +
      18 * (-2) * (-1) * 1 = 49 := by
  norm_num

theorem rightPolynomial_discriminant_eq :
    (5 : ℤ) ^ 2 * 6 ^ 2 - 4 * 6 ^ 3 -
      4 * 5 ^ 3 * 1 - 27 * 1 ^ 2 +
      18 * 5 * 6 * 1 = 49 := by
  norm_num

/-- Ramified axis, its unit factor, and an explicit inverse of that factor. -/
def ramifiedAxis : SevenRealCubicInt := ⟨1, 2, 0⟩

def ramifiedUnit : SevenRealCubicInt :=
  ⟨-1, 2, 4⟩

def ramifiedUnitInv : SevenRealCubicInt :=
  ⟨-9, 22, -8⟩

theorem ramifiedAxis_eq :
    ramifiedAxis = 1 + 2 * alpha := by
  change ramifiedAxis = ofInt 1 + ofInt 2 * alpha
  ext <;> norm_num [ramifiedAxis, alpha, mul]

theorem norm_ramifiedAxis : norm ramifiedAxis = -7 := by
  norm_num [ramifiedAxis, norm]

theorem ramifiedUnit_eq :
    ramifiedUnit = alpha * (1 + alpha) ^ 2 := by
  ext <;> norm_num [ramifiedUnit, alpha, mul, pow_two]

theorem ramifiedAxis_cube :
    ramifiedAxis ^ 3 = 7 * ramifiedUnit := by
  change ramifiedAxis ^ 3 = ofInt 7 * ramifiedUnit
  ext <;> norm_num [ramifiedAxis, ramifiedUnit, mul, pow_succ]

theorem norm_ramifiedUnit : norm ramifiedUnit = -1 := by
  norm_num [ramifiedUnit, norm]

theorem ramifiedUnit_mul_inv :
    ramifiedUnit * ramifiedUnitInv = 1 := by
  ext <;> norm_num [ramifiedUnit, ramifiedUnitInv, mul]

theorem ramifiedUnit_isUnit : IsUnit ramifiedUnit :=
  IsUnit.of_mul_eq_one ramifiedUnitInv ramifiedUnit_mul_inv

/-- The difference of the two norm sources is exactly the cubic ramified
axis times the quadratic inner second coordinate. -/
theorem rightSource_sub_leftSource (a n : ℤ) :
    rightSource a n - leftSource a n =
      ramifiedAxis * (n : SevenRealCubicInt) := by
  ext <;> simp [rightSource, leftSource, ramifiedAxis]
  ring

/-- Axis normalized so that the final source difference has no external unit
coefficient. -/
def normalizedAxis : SevenRealCubicInt :=
  ramifiedUnit ^ 4 * ramifiedAxis

def normalizedWitness (m : ℤ) : SevenRealCubicInt :=
  ramifiedUnitInv ^ 8 * normalizedAxis * (m : SevenRealCubicInt)

private theorem ramifiedAxis_pow_twelve :
    ramifiedAxis ^ 12 = 7 ^ 4 * ramifiedUnit ^ 4 := by
  calc
    ramifiedAxis ^ 12 = (ramifiedAxis ^ 3) ^ 4 := by ring
    _ = (7 * ramifiedUnit) ^ 4 := by rw [ramifiedAxis_cube]
    _ = 7 ^ 4 * ramifiedUnit ^ 4 := by ring

private theorem ramifiedUnit_pow_mul_inv_pow :
    ramifiedUnit ^ 52 * ramifiedUnitInv ^ 56 =
      ramifiedUnitInv ^ 4 := by
  calc
    ramifiedUnit ^ 52 * ramifiedUnitInv ^ 56 =
        (ramifiedUnit * ramifiedUnitInv) ^ 52 *
          ramifiedUnitInv ^ 4 := by ring
    _ = ramifiedUnitInv ^ 4 := by rw [ramifiedUnit_mul_inv]; simp

private theorem mul_five_rearrange
    (a b c d e : SevenRealCubicInt) :
    a * (d * b) * c * e = (a * b) * c * (d * e) := by
  ring

/-- Pure ramified-axis normalization of a depth-four signed seventh power. -/
theorem ramifiedAxis_mul_seven_pow_four_mul_pow_seven (m : ℤ) :
    ramifiedAxis *
        ((7 ^ 4 * m ^ 7 : ℤ) : SevenRealCubicInt) =
      normalizedAxis ^ 6 * normalizedWitness m ^ 7 := by
  rw [show
      ((7 ^ 4 * m ^ 7 : ℤ) : SevenRealCubicInt) =
        (7 : SevenRealCubicInt) ^ 4 *
          (m : SevenRealCubicInt) ^ 7 by norm_cast]
  unfold normalizedAxis normalizedWitness
  symm
  calc
    (ramifiedUnit ^ 4 * ramifiedAxis) ^ 6 *
          (ramifiedUnitInv ^ 8 *
            (ramifiedUnit ^ 4 * ramifiedAxis) *
            (m : SevenRealCubicInt)) ^ 7 =
        (ramifiedUnit ^ 52 * ramifiedUnitInv ^ 56) *
          ramifiedAxis ^ 13 * (m : SevenRealCubicInt) ^ 7 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow]
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
      rw [show ramifiedUnit ^ 52 =
          ramifiedUnit ^ 24 * ramifiedUnit ^ 28 by
            rw [← pow_add],
        show ramifiedAxis ^ 13 =
          ramifiedAxis ^ 6 * ramifiedAxis ^ 7 by
            rw [← pow_add]]
      generalize ramifiedUnit ^ 24 = u24
      generalize ramifiedUnit ^ 28 = u28
      generalize ramifiedUnitInv ^ 56 = v56
      generalize ramifiedAxis ^ 6 = p6
      generalize ramifiedAxis ^ 7 = p7
      generalize (m : SevenRealCubicInt) ^ 7 = m7
      ring
    _ = ramifiedUnitInv ^ 4 * ramifiedAxis ^ 13 *
          (m : SevenRealCubicInt) ^ 7 := by
      rw [ramifiedUnit_pow_mul_inv_pow]
    _ = ramifiedUnitInv ^ 4 *
          (7 ^ 4 * ramifiedUnit ^ 4) * ramifiedAxis *
          (m : SevenRealCubicInt) ^ 7 := by
      rw [show ramifiedAxis ^ 13 =
          ramifiedAxis ^ 12 * ramifiedAxis by ring,
        ramifiedAxis_pow_twelve]
      simp only [mul_assoc]
    _ = ramifiedAxis *
          (7 ^ 4 * (m : SevenRealCubicInt) ^ 7) := by
      have hcancel :
          ramifiedUnitInv ^ 4 * ramifiedUnit ^ 4 = 1 := by
        rw [← mul_pow, mul_comm, ramifiedUnit_mul_inv]
        simp
      rw [mul_five_rearrange,
        hcancel]
      simp

#print axioms SevenRealCubicInt.norm_mul
#print axioms SevenRealCubicInt.norm_leftSource
#print axioms SevenRealCubicInt.norm_rightSource
#print axioms SevenRealCubicInt.ramifiedAxis_cube
#print axioms SevenRealCubicInt.ramifiedUnit_isUnit
#print axioms
  SevenRealCubicInt.ramifiedAxis_mul_seven_pow_four_mul_pow_seven

end SevenRealCubicInt

end DkMath.FLT.Seven
