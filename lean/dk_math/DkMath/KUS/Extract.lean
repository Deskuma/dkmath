/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.NatEmbed

namespace DkMath.KUS

universe u v

variable {U : Type u}
variable {Blueprint : BlueprintFamily U}

/--
零状態や一般の KUS から、unit と blueprint だけを取り出す特異操作。

これは通常の除法ではなく、構造保持側への forgetful extraction である。
-/
@[simp] def extract (x : KUS U Blueprint) : US U Blueprint :=
  toUS x

@[simp] theorem extract_ofNat (support : US U Blueprint) (n : Nat) :
    extract (ofNat support n) = support := by
  simp [extract]

@[simp] theorem extract_zeroState (support : US U Blueprint) :
    extract (zeroState support) = support := by
  simp [extract]

end DkMath.KUS
