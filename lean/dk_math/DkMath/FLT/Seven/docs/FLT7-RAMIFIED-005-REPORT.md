# FLT7-RAMIFIED-005 実装レポート

## Outcome A

canonical ramified unit class を residual root の mod `49` principal digit
一つへ完全に還元しました。

## 実装内容

- `root.snd = 0` in `ZMod 49`
- `ramifiedGapQuotient.snd = -endpointRight^2`
- `residualRoot = root.fst^2`
- `seventhPowerSndCore = residualRoot^3`
- residual root の明示 inverse witness
- `explicitUnit = -endpointRight^2 * residualRootInverse^2`
- `root.fst^7 = -endpointRight^3`
- `residualRoot = 1` in `ZMod 7`
- `residualRoot^7 = 1` in `ZMod 49`
- residual-root 七 residue classifier
- seventh-power class と `residualRoot = 1` の同値
- canonical seventh-power unit の三 residue classifier

## 公開 API

```lean
PrimitiveRamifiedSummitPacket.root_snd_cast_mod49_eq_zero
PrimitiveRamifiedSummitPacket
  .ramifiedGapQuotient_snd_mod49_eq_neg_endpointRight_sq
PrimitiveRamifiedSummitPacket.residualRoot_mod49_eq_rootFst_sq
PrimitiveRamifiedSummitPacket.sndCore_mod49_eq_residualRoot_cube
PrimitiveRamifiedSummitPacket.residualRootInverseMod49
PrimitiveRamifiedSummitPacket.explicitUnit_mod49_eq
PrimitiveRamifiedSummitPacket.rootFst_pow_seven_mod49
PrimitiveRamifiedSummitPacket.residualRoot_mod7_eq_one
PrimitiveRamifiedSummitPacket.residualRoot_seventh_eq_one_mod49
PrimitiveRamifiedSummitPacket.residualRoot_mod49_classifier
PrimitiveRamifiedSummitPacket
  .isSeventhPowerMod49_iff_residualRoot_eq_one
PrimitiveRamifiedSummitPacket
  .isSeventhPowerMod49_iff_three_residues
```

## 推論結果

generic bridge の六 residue は canonical summit では三 residue
`{19,31,48}` に縮みます。真の branch selector は explicit unit そのもの
ではなく:

```text
residualRoot = 1 mod 49
```

です。非自明 branch は `8,15,22,29,36,43` の六 residue です。

## 停止境界

mod `49` 判定から全 `7^k` に compatible な seventh roots を構成するには、
別個の Hensel/Kummer lifting theorem が必要です。さらに、その局所 root
は整数・自然数の seventh root ではありません。

non-seventh branch を矛盾にする root-cubic gap shape receiver も未実装
です。

`sorry`、追加 axiom、`native_decide` は使用していません。
