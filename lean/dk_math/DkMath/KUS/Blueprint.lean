/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.Unit

namespace DkMath.KUS

universe u v

variable {U : Type u}

/-- KUS で扱う blueprint family。各 unit ごとに別の型を持てる。 -/
abbrev BlueprintFamily (U : Type u) := U → Type v

/-- 固定 unit 上の blueprint fiber を名前付きで参照するための別名。 -/
abbrev BlueprintAt (Blueprint : BlueprintFamily U) (u : U) : Type v :=
  Blueprint u

end DkMath.KUS
