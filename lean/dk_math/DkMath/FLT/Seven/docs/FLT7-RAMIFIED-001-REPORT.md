# FLT7-RAMIFIED-001 実装レポート

## Outcome A

計画された三つの境界を Lean で完遂しました。

1. `PrimitiveRamifiedSummitPacket` を実装し、terminal Row-Y と Row-Z の
   両方から inhabit しました。共通 endpoint はそれぞれ `(z,x,y)` と
   `(x,-y,z)` で、gap/residual の exact power split、primitive 性、
   quadratic root と norm source を保持します。
2. `ramifiedGapQuotient` の展開を証明し、第二座標から
   `root.snd` の exact depth transfer
   `padicValNat 7 |root.snd| = 5 + 7 * padicValNat 7 gapRoot`
   を得ました。
3. `ramifiedSeventhSnd` の linear-cubic-cubic 分解、左右 cubic の差と
   norm の関係、和の三線形因子分解、および endpoint product bridge
   を証明しました。

## 公開 API

```lean
AwaySevenBaseTerminalUnitSectorPacket.ramifiedSummit
PrimitiveRamifiedSummitPacket.rootSnd_padicValNat
ramifiedSeventhSnd_factorization
ramifiedRightCubic_sub_left
ramifiedLeftCubic_add_right
PrimitiveRamifiedSummitPacket.endpoint_product_eq
```

## 証明境界

この checkpoint は common ramified summit と exact depth を閉じます。
新しい ramified 3 x 3 routing board は得られましたが、そこから小さい
Fermat 解を構成する descent はまだ証明していません。`sorry`、追加
axiom、`native_decide` は使用していません。
