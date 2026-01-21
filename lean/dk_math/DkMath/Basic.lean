/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

namespace DkMath.Basic

def hello := "world"

class Printable (α : Type) where
  print : α → String

instance PrintableString : Printable String where
  print s := s

def printValue {α : Type} [Printable α] (value : α) : String :=
  Printable.print value

#eval printValue hello  -- This should output "world"

end DkMath.Basic
