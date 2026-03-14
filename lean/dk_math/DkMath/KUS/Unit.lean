/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

#print "file: DkMath.KUS.Unit"

namespace DkMath.KUS

universe u v

/--
`US` は、unit とその unit に従属する blueprint を束ねた最小構造である。

これは KUS の「構造保持側」を切り出した核であり、`extract` の返り値になる。
-/
@[ext] structure US (U : Type u) (Blueprint : U → Type v) where
  unit : U
  blueprint : Blueprint unit

namespace US

variable {U : Type u} {Blueprint : U → Type v}

/-- blueprint を忘れずに保持したまま unit を取り出す。 -/
@[simp] def fst (x : US U Blueprint) : U :=
  x.unit

end US

end DkMath.KUS
