/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProviderCore
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGN
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferich
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichDefault
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNNoWieferichResearch
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentBQuarantine
import DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB
import DkMath.FLT.PrimeProvider.TriominoCosmic
import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5Core
import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA
import DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant
import DkMath.FLT.PrimeProvider.TriominoSquarefreeGNBridgeProvider
import DkMath.FLT.PrimeProvider.TriominoCosmicPrimeGe5
import DkMath.FLT.TriominoPrimeProvider

#print "file: DkMath.FLT.PrimeProvider"

set_option linter.style.longLine false

/-!
# FLT Prime Provider Aggregator

Prime-provider 系の lower layer / staging / bridge / public entry を
一箇所から辿れるようにする束ねファイル。

目的:
- `DkMath.FLT` 側の import を整理する
- `GN -> GTail` のような refactor 時に、provider 系の build coverage を明示化する
- `Main` と `Basic` とは別軸の provider chain を見通しやすくする

備考:
- `PrimeProviderCore` が `FLT.Core` を import するのは、
  provider の型 alias が `FermatLastTheoremFor` / `FermatLastTheorem`
  を参照するため。
- 将来さらに薄い statement-only 層を切るなら、その時に `Core` 依存を再分解する。
-/
