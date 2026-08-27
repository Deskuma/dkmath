# FLT7-RAMIFIED-003 実装レポート

## Outcome A

endpoint gap と root-cubic gap の equal depth を、division-free な整数
恒等式と任意の `ZMod (7^k)` 上の明示 unit equality へ昇格しました。

## 実装内容

- `(R-L) * S = (c-e) * Q * norm(root)` を整数上で証明
- `S = seventhPowerSndCore` が 7-unit であることを再利用
- `Q * norm(root)` が 7-unit であることを証明
- `RamifiedGapUnitBridgePacket` に gap、unit、整数 bridge を固定
- 任意の `k : ℕ` に対して両 unit の `ZMod (7^k)` unit 性を証明
- `rightUnit * leftUnit⁻¹` を明示 unit として定義
- `cubicGap = endpointGap * explicitUnit` を証明

`k = 0` も定理に含まれます。Lean の `ZMod` inverse については、
`leftUnit_isUnit.unit` の逆元を明示し、unit cancellation を証明に使用
しています。

## 公開 API

```lean
PrimitiveRamifiedSummitPacket
  .cubicGap_mul_sndCore_eq_endpointGap_mul_bridge
RamifiedGapUnitBridgePacket
PrimitiveRamifiedSummitPacket.ramifiedGapUnitBridge
RamifiedGapUnitBridgePacket.explicitUnit
RamifiedGapUnitBridgePacket.explicitUnit_isUnit
RamifiedGapUnitBridgePacket.cubicGap_eq_endpointGap_mul_explicitUnit
```

## 証明境界

exact ramified gap-unit bridge は完成しました。これは七進局所 unit
equivalence です。小さい Fermat 解、descent seed、descent provider、
recursive descent は構成していません。

`sorry`、追加 axiom、`native_decide` は使用していません。
