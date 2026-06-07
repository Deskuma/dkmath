/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Sequence.Arithmetic
import DkMath.KUS.Coeff

#print "file: DkMath.KUS.DynamicArithmeticSequence"

namespace DkMath
namespace KUS

/-!
# Dynamic arithmetic sequences on `GKUS`

The dynamic parameter belongs to the coefficient layer.  The `US` support is
kept fixed, so zero/specialized coefficients do not erase structural data.
-/

universe u v

variable {C : Type*}
variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-- Ordinary arithmetic term packaged as a `GKUS` value over fixed support. -/
def gArithmeticTerm [Semiring C]
    (support : US U Blueprint) (a d : C) (i : ℕ) :
    GKUS C U Blueprint :=
  mkGWith (DkMath.Sequence.arithmeticTerm a d i) support

/-- Dynamic arithmetic term packaged as a `GKUS` value over fixed support. -/
def gDynamicTerm [Semiring C]
    (support : US U Blueprint) (a d k : C) (i : ℕ) :
    GKUS C U Blueprint :=
  mkGWith (DkMath.Sequence.dynamicTerm a d k i) support

/-- First `n` dynamic terms as `GKUS` values over the same support. -/
def gDynamicSequence [Semiring C]
    (support : US U Blueprint) (a d k : C) (n : ℕ) :
    List (GKUS C U Blueprint) :=
  (List.range n).map fun i => gDynamicTerm support a d k i

@[simp] theorem toCoeff_gArithmeticTerm
    [Semiring C] (support : US U Blueprint) (a d : C) (i : ℕ) :
    toCoeff (gArithmeticTerm support a d i) =
      DkMath.Sequence.arithmeticTerm a d i := by
  rfl

@[simp] theorem extract_g_gArithmeticTerm
    [Semiring C] (support : US U Blueprint) (a d : C) (i : ℕ) :
    extract_g (gArithmeticTerm support a d i) = support := by
  simp [gArithmeticTerm]

@[simp] theorem toCoeff_gDynamicTerm
    [Semiring C] (support : US U Blueprint) (a d k : C) (i : ℕ) :
    toCoeff (gDynamicTerm support a d k i) =
      DkMath.Sequence.dynamicTerm a d k i := by
  rfl

@[simp] theorem extract_g_gDynamicTerm
    [Semiring C] (support : US U Blueprint) (a d k : C) (i : ℕ) :
    extract_g (gDynamicTerm support a d k i) = support := by
  simp [gDynamicTerm]

/-- `GKUS` dynamic arithmetic is ordinary arithmetic with common difference `d * k`. -/
@[simp] theorem gDynamicTerm_eq_gArithmeticTerm_scaledDiff
    [Semiring C] (support : US U Blueprint) (a d k : C) (i : ℕ) :
    gDynamicTerm support a d k i = gArithmeticTerm support a (d * k) i := by
  simp [gDynamicTerm, gArithmeticTerm]

/-- The `k = 1` specialization recovers the ordinary `GKUS` arithmetic term. -/
@[simp] theorem gDynamicTerm_one
    [Semiring C] (support : US U Blueprint) (a d : C) (i : ℕ) :
    gDynamicTerm support a d 1 i = gArithmeticTerm support a d i := by
  simp [gDynamicTerm, gArithmeticTerm]

/-- Even at zero scale, the support is still retained. -/
@[simp] theorem gDynamicTerm_zeroScale
    [Semiring C] (support : US U Blueprint) (a d : C) (i : ℕ) :
    gDynamicTerm support a d 0 i = mkGWith a support := by
  simp [gDynamicTerm, DkMath.Sequence.dynamicTerm, DkMath.Sequence.dynamicGenerator,
    DkMath.Sequence.arithmeticGenerator, DkMath.Sequence.dynamicStep,
    DkMath.Sequence.AdditiveGenerator.term]

end KUS
end DkMath
