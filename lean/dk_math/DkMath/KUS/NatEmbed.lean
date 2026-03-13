/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Core

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-- Nat から KUS への埋め込み。support は固定し、可視係数だけを与える。 -/
@[simp] def ofNat (support : US U Blueprint) (n : Nat) : KUS U Blueprint :=
  mkWith n support

/-- KUS から観測される可視係数を取り出す忘却写像。 -/
@[simp] def toNat (x : KUS U Blueprint) : Nat :=
  x.coeff

@[simp] theorem toNat_ofNat (support : US U Blueprint) (n : Nat) :
    toNat (ofNat support n) = n := rfl

@[simp] theorem ofNat_zero (support : US U Blueprint) :
    ofNat support 0 = zeroState support := rfl

end DkMath.KUS
