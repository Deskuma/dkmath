/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.GEisensteinBridge
import DkMath.FLT.Kummer
import DkMath.FLT.Main
import DkMath.FLT.PrimeProvider

#print "file: DkMath.FLT"

set_option linter.style.longLine false

/-!
# DkMath FLT Aggregator

`DkMath.FLT` は、FLT 関連の公開面をまとめる top-level import 入口。

主な役割:
- `Main` 側の `d = 3` 公開 API を束ねる
- `Kummer` 側の regular-prime / class-group route を公開面へ載せる
- `PrimeProvider` 側の provider chain を同じ入口から辿れるようにする

## public/provider 導線の現状

`RegularPrimeRoute` には、
`TriominoSquarefreeGNBridgeProvider` を concrete に持てる branch 向けの
provider-facing theorem として次を用意している。

- `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
- `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`

これらは
`FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
を既存の core bridge
`triominoCosmic_globalProvider_of_FLTPrimeGe5`
/
`triominoPrimeProvider_of_FLTPrimeGe5`
へ合成した薄い wrapper であり、
`DkMath.FLT` を import すれば top-level 公開面からそのまま使える。

住み分け:
- abstract theorem-parameterized route:
  `FLTPrimeGe5Target_of_refinedRegularPrimeRoute`
- provider concrete route:
  `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
  /
  `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`

したがって、
`TriominoSquarefreeGNBridgeProvider` を持てる branch では、
上の provider concrete route を canonical な public/provider 導線として使う。
-/
