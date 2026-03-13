/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.RoundTrip

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/--
固定 support 上の係数 fiber。

phase-02 では最小実装として、fiber は `Nat` 係数層で表す。
KUS 本体との接続は `toKUS` / `extract_toKUS` で与える。
-/
abbrev Fiber (_support : US U Blueprint) : Type := Nat

namespace Fiber

variable (support : US U Blueprint)

/-- fixed fiber の係数を KUS 本体へ戻す。 -/
@[simp] def toKUS (n : Fiber support) : KUS U Blueprint :=
  KUS.ofNat support n

/-- fixed fiber の観測係数。phase-02 では恒等。 -/
@[simp] def toNat (n : Fiber support) : Nat :=
  n

@[simp] theorem toNat_toKUS (n : Fiber support) :
    KUS.toNat (toKUS support n) = n := by
  simp [toKUS]

@[simp] theorem extract_toKUS (n : Fiber support) :
    KUS.extract (toKUS support n) = support := by
  simp [toKUS]

@[simp] theorem roundTrip_nat (n : Fiber support) :
    KUS.toNat (toKUS support n) = toNat support n := by
  simp [toNat]

/-- fixed fiber は `Nat` と同じ加法可換モノイド構造を持つ。 -/
instance : AddCommMonoid (Fiber support) := inferInstance

end Fiber

end DkMath.KUS
