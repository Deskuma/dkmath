# FLT7-RAMIFIED-002 実装レポート

## Outcome A

ramified factor grid を正式な `CoprimeTripleRouting` へ昇格し、gap depth
synchronization を証明しました。

## 実装内容

- common summit に endpoint 非零性と cyclotomic coordinate coprimality を保持
- root coordinates `(u,v)` の coprimality を回収
- `T`, `L`, `R` の非零性と 7-unit 性を証明
- `T`, `L`, `R` の pairwise coprimality を証明
- `|c|`, `|e|`, `|c+e|` の非零性と pairwise coprimalityを証明
- endpoint/root の `natAbs` product equality を構成
- `RamifiedCubicRoutingPacket` を terminal packet から inhabit
- endpoint gap と root-cubic gap の exact depth equality を証明

root cubic coprimalityでは、共通素因子をそれぞれ `49*v^3` と
`49*v^4` へ押し込む二つの多項式恒等式を使用しました。これにより
候補素因子は 7 または primitive root coordinates の共通因子に限定され、
双方を排除できます。

## 公開 API

```lean
RamifiedCubicRoutingPacket
AwaySevenBaseTerminalUnitSectorPacket.ramifiedCubicRouting
PrimitiveRamifiedSummitPacket.root_coordinates_isCoprime
PrimitiveRamifiedSummitPacket.coprime_linear_left
PrimitiveRamifiedSummitPacket.coprime_linear_right
PrimitiveRamifiedSummitPacket.coprime_left_right
PrimitiveRamifiedSummitPacket.cubicGap_depth_eq_endpointGap_depth
```

## 証明境界

formal 3 x 3 routing packet と gap depth synchronization は完成しました。
小さい Fermat 解、descent seed、descent provider は構成していません。
`sorry`、追加 axiom、`native_decide` は使用していません。
