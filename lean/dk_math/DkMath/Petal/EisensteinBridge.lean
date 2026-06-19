/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.GNBridge
import DkMath.FLT.GEisensteinBridge

#print "file: DkMath.Petal.EisensteinBridge"

/-!
# Petal Eisenstein Bridge

This file exposes the existing Eisenstein norm route through the Petal package.

The bridge is intentionally thin: the arithmetic facts already live in
`DkMath.FLT.GEisensteinBridge`; this file gives them Petal-facing names so that
later S0/GN/Zsigmondy code can import `DkMath.Petal.*` without depending on the
FLT file layout.

## Refactor note: this import direction is temporary

This file currently imports `DkMath.FLT.GEisensteinBridge`.  That is intentional
for the present stage: the Eisenstein norm lemmas already exist there, and this
file is only a stable Petal-facing alias surface.

The final library direction should not be:

```text
Petal -> FLT
```

For the mature hierarchy, the expected direction is closer to:

```text
DkMath.Lib.* or DkMath.NumberTheory.*
  -> Petal.EisensteinBridge
  -> FLT
```

or, more explicitly:

```text
Eisenstein core facts live in a neutral library layer.
Petal imports that neutral layer and exposes Petal-facing names.
FLT imports Petal or the neutral layer for the degree-three application.
```

The current reverse-looking dependency is acceptable only because `S0_nat` and
the already-proved shifted Eisenstein norm facts still live under
`DkMath.FLT.*`.  During the planned `DkMath.Lib.*` promotion refactor, move the
neutral arithmetic pieces first, then update this file to import the new neutral
home instead of `DkMath.FLT.GEisensteinBridge`.

Do not treat this file as evidence that Petal conceptually depends on FLT.  It
is a migration window: the theorem names here are the API that should survive
after the dependency direction is corrected.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom
open DkMath.FLT.PetalDetect

/--
Petal-facing alias for the shifted Eisenstein norm on `S0_nat`.

The cubic Petal face `S0_nat a b` is the Eisenstein norm of the shifted pair
`(a + b, b)`.
-/
theorem petal_S0_eq_eisensteinNorm_shift (a b : ℕ) :
    S0_nat a b = DkMath.FLT.eisensteinNormNat (a + b) b :=
  DkMath.FLT.S0_eq_eisensteinNorm_shift a b

/--
Petal-facing alias for the degree-three GN/Eisenstein norm bridge.

After the boundary substitution `x = a - b`, `u = b`, the degree-three GN
kernel is the shifted Eisenstein norm.
-/
theorem petal_GN3_sub_eq_eisensteinNorm_shift
    (a b : ℕ) (hab : b ≤ a) :
    GN 3 (a - b) b = DkMath.FLT.eisensteinNormNat (a + b) b :=
  DkMath.FLT.GN3_sub_eq_eisensteinNorm_shift a b hab

/--
For strict Petal coordinates, the visible degree-three GN face is the shifted
Eisenstein norm.
-/
theorem petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
    {c b : ℕ} (hbc : b < c) :
    GN 3 (c - b) b = DkMath.FLT.eisensteinNormNat (c + b) b :=
  petal_GN3_sub_eq_eisensteinNorm_shift c b hbc.le

/--
For strict Petal coordinates, the S0 detector is the shifted Eisenstein norm.
-/
theorem petal_S0_nat_eq_eisensteinNorm_shift_of_lt
    {c b : ℕ} (_hbc : b < c) :
    S0_nat c b = DkMath.FLT.eisensteinNormNat (c + b) b :=
  petal_S0_eq_eisensteinNorm_shift c b

end Petal
end DkMath
