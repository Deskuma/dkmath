# FLT7-RAMIFIED-004 実装レポート

## Outcome C

`explicitUnit` の全 `7^k` reduction coherence と mod `49` seventh-power
class の完全な有限分類を証明しました。一般の common summit がどの
residue branch に入るかは、現在の packet fields だけでは未確定です。

## 実装内容

- `sevenPowerReductionHom k` を定義
- adjacent level の整数 cast compatibility を証明
- unit inverse の一意性を使って `explicitUnit_reduction` を証明
- `IsSeventhPowerMod49` を定義
- unit `U : ZMod 49` について `U` が seventh power であることと
  `U^7 = U` が同値であることを有限検証
- seventh-power unit image を完全分類

```text
U ∈ {1, 18, 19, 30, 31, 48}
```

有限検証には kernel reduction の `decide` を使用しています。
`native_decide` は使用していません。

## 公開 API

```lean
sevenPowerReductionHom
RamifiedGapUnitBridgePacket.explicitUnit_reduction
RamifiedGapUnitBridgePacket.IsSeventhPowerMod49
RamifiedGapUnitBridgePacket.isSeventhPowerMod49_iff
RamifiedGapUnitBridgePacket.isSeventhPowerMod49_iff_residue
RamifiedGapUnitBridgePacket.seventhPowerMod49_or_not
```

## 推論結果と停止境界

RAMIFIED-003 の unit は level ごとの独立な選択ではなく、一つの coherent
seven-adic unit system です。その最初の class は mod `49` の六 residue
へ完全に還元されました。

ただし現在の `PrimitiveRamifiedSummitPacket` は、canonical
`explicitUnit 2` がこの六 residue に入るかを直接固定する residue field
を持ちません。次に必要なのは summit の `Q`、`sndCore`、`norm(root)`
を mod `49` で同時に正規化する theorem です。

また non-seventh-power branch だけから `False` は従いません。矛盾には
root-cubic gap 自身が seventh-power shape を持つという別 receiver が
必要です。

`sorry`、追加 axiom、`native_decide` は使用していません。
