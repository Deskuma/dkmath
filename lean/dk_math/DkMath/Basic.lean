/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath.Basic

def hello := "world"

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
