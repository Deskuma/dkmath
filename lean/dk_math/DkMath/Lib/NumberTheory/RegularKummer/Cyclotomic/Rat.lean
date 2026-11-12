/-
Adapted for DkMath from leanprover-community/flt-regular, commit
b8a5f23ab44a7be9fd49f6e3c831da54573c3c89, FltRegular/NumberTheory/Cyclotomic/Rat.lean.
Original and adapted material licensed under Apache-2.0; see LICENSE in this directory tree.
DkMath changes: isolated namespace, Lean 4.34 compatibility, and mathematical commentary.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# The cyclotomic extension instance for `CyclotomicField n ℚ`

Mathlib's instance `IsCyclotomicExtension {n} K (CyclotomicField n K)` for a field `K` of
characteristic zero is stated using the algebra structure `CyclotomicField.algebra n K`. For
`K = ℚ` the algebra structure found by instance search is instead `DivisionRing.toRatAlgebra`,
which is not reducibly defeq to it, so goals stated over `ℚ` do not find the Mathlib instance.
We record the instance in the form that instance search expects.
-/

public section

namespace DkMath.Lib.NumberTheory.RegularKummer

/-!
円分体の ℚ-algebra を統一する。補助拡大で使用する標準円分体の instance を固定する。
-/

#print "file: DkMath.Lib.NumberTheory.RegularKummer.Cyclotomic.Rat"


instance (n : ℕ) [NeZero n] : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

end DkMath.Lib.NumberTheory.RegularKummer
