/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.CoreNestedTransport
import Mathlib.Data.ZMod.Basic

#print "file: DkMathTest.Lib.Cosmic.CoreNested"

open DkMath.Lib.Cosmic DkMath.CosmicFormula

-- Edge cases do not assume positivity, cancellation, or characteristic zero.
example (a b c : ℤ) : powerCore 0 a (b + c) = 0 := by simp
example (d : ℕ) (a : ℤ) : powerCore d a 0 = 0 := by simp
example : powerCore 3 (0 : ℤ) (-2) = -8 := by norm_num [powerCore]
example : powerCore 3 (-2 : ℤ) 5 = 35 := by norm_num [powerCore]
example : powerCore 0 (0 : ℤ) 0 = 0 := by simp
example : powerCore 3 (2 : ZMod 5) 4 = 3 := by decide

example (d : ℕ) (t a b : ZMod 5) :
    powerCore d t a + powerCore d (t + a) b =
      powerCore d t b + powerCore d (t + b) a := powerCore_swap d t a b

example (d : ℕ) (S T U : Finset ℕ) (t a b : ℤ) :
    selectedGap d S (a + b) t + selectedBody d S (a + b) t - t ^ d =
      (selectedGap d T a t + selectedBody d T a t - t ^ d) +
        (selectedGap d U b (t + a) + selectedBody d U b (t + a) - (t + a) ^ d) :=
  selected_nested_transport d S T U t a b

-- The historical wrong formula is not the base/increment telescoping law.
example : powerCore 2 (1 + 2 : ℤ) 3 ≠ powerCore 2 1 (2 + 3) + powerCore 2 2 3 := by
  norm_num [powerCore]

#print axioms powerCore_split
#print axioms powerCore_swap
#print axioms powerCore_split_three
#print axioms mul_gtail_one_split
#print axioms selected_nested_transport
