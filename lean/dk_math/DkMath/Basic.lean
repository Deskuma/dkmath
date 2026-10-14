/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Choose.Basic

#print "file: DkMath.Basic"

/-! # Example Code Style

This sample code serves as an example of the coding style used
for Lean implementations within this project.

The `#print "file: <module name>"` line immediately following
the `import` statement is a convention of this project;
it ensures the module filename is evident from the code itself,
even if that information is otherwise missing. Please do not omit it.

For the license notice at the beginning of the module,
please use the comment at the top of the `License.lean` file
exactly as it appears.

-/

namespace DkMath.Basic

def hello := "Hello! DkMath world."

class Printable (α : Type) where
  print : α → String

instance PrintableString : Printable String where
  print s := s

def printValue {α : Type} [Printable α] (value : α) : String :=
  Printable.print value

#eval printValue hello  -- This should output "world"

-- ============================================================================

section AdditionalBasicLemmas

/-- choose d 0 = 1 を Nat 名前空間に定義する（simp 用） -/
theorem Nat.choose_zero (d : ℕ) : Nat.choose d 0 = 1 := by
  induction d with
  | zero => rfl
  | succ d _ => rfl

end AdditionalBasicLemmas

-- ============================================================================

end DkMath.Basic
