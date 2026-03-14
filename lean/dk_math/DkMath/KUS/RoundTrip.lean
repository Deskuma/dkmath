/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Extract

#print "file: DkMath.KUS.RoundTrip"

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/-- Nat 埋め込みの往復は可視係数を保存する。 -/
@[simp] theorem roundTrip_nat (support : US U Blueprint) (n : Nat) :
    toNat (ofNat support n) = n :=
  toNat_ofNat support n

/-- Nat 埋め込み後に extract すると、元の support を回収する。 -/
@[simp] theorem roundTrip_support (support : US U Blueprint) (n : Nat) :
    extract (ofNat support n) = support :=
  extract_ofNat support n

/-- 任意の KUS は、extract した support と可視係数から再構成できる。 -/
@[simp] theorem reconstruct_from_extract (x : KUS U Blueprint) :
    ofNat (extract x) (toNat x) = x := by
  cases x
  rfl

/-- 構造保持零は、extract した support 上の `0` 埋め込みに一致する。 -/
@[simp] theorem zeroState_eq_ofNat_extract (x : KUS U Blueprint) :
    zeroState (extract x) = ofNat (extract x) 0 := by
  rfl

end DkMath.KUS
