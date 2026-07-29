# FLT7-017 作業レポート

日時: 2026-07-23 04:57 JST
判定: **Outcome A**

## 完了内容

- `AwaySevenPivotDepthPacket` を追加し、既存の seven pivot と depth packet
  の provenance を同期したまま、選択 row、唯一の `.sevenV` cell、完全深度
  `k`、`k = 1 + v7(vPart)` を固定した。
- `upperModulus = 7^k`、`lowerModulus = 7^(k-1)` を定義し、pivot、carrier、
  `vPart` に対する上下の exact divisibility と
  `upperModulus = 7 * lowerModulus` を証明した。
- 一様な恒等式

  ```text
  seventhPowerFst u v
    = u^7 + 4*v^7
      - 14*v^2*(u+v)*(3*u^4 + 2*u^3*v - 7*u^2*v^2 - 2*u*v^3 + v^4)
  ```

  および `7^m | v` から residual が `7^(m+1)` で割れることを証明した。
- `AwaySevenPivotPrimePowerSolution` と実 reduction
  `AwaySevenPivotDepthPacket.toPrimePowerSolution` を構築した。これは
  `ZMod (7^k)` を体とせず、endpoint と root-linear の非退化性を
  `IsUnit` で保持し、`7*v = 0` と `v != 0` を同時に持つ。
- base layer (`k=1`) は既存 `AwayRootResidueSector` の三 sector を保持した。
- lifted layer (`1<k`) では root second coordinate の七乗が
  `ZMod (7^k)` で 0、root first coordinate が unit であることを証明し、
  row Y の `(u,z)`、row Z/Sum の `(-u,y)` を weight-(3,7) unit orbit に分類した。
- signed kernel packet を構築し、符号を `unitPart : Int` に保持したまま

  ```text
  root.snd = 7^(k-1) * unitPart
  7 does not divide unitPart
  ```

  と `unitPart` の `ZMod (7^k)` 上の unit 性を証明した。
- `SevenPivotSummitRoute` を追加し、各 `CounterexamplePack` を ramified branch、
  または non-seven 完全 orbit 分類・seven 完全深度解・terminal/step audit を
  全て保持する away branch へ送った。

## Closure の正直な境界

`AwayDescentClosureProvider` は構築していない。データ不足を隠さず、監査結果を
次の二つに分離した。

- `k = 1`: 新しい depth-zero away packet を作らず、source
  `CounterexamplePack` の terminal arithmetic exclusion を exact obligation
  として保持する。
- `1 < k`: signed top-layer kernel と unit orbit を保持し、新しい primitive
  counterexample を組み立てる `AwayDescentClosureProvider` の存在を exact
  reconstruction obligation として保持する。

したがって、本 checkpoint は seven-pivot ramified local layer と監査境界を
完了するが、recursive descent や FLT7 を主張しない。

## 検証

成功:

```text
lake build DkMath.FLT.Seven.SevenPivotDepthPacket
lake build DkMath.FLT.Seven.SevenPivotPrimePowerSystem
lake build DkMath.FLT.Seven.SevenPivotDescentAudit
lake build DkMathTest.FLT.SevenSevenPivotDepthPacket
           DkMathTest.FLT.SevenSevenPivotDescentAudit
           DkMath.FLT.Seven DkMath.FLT
git diff --check
```

Focused tests は generic diagonal counterexample、三 pivot row constructor、
depth/modulus、symbolic residual identity、実 full-depth reduction、非体の
`ZMod 49` における `7 != 0` かつ `7^7 = 0`、lifted nilpotence、unit orbit、
signed kernel、summit route を含む。`native_decide` は使用していない。

公開 summit と主要 API の axiom audit はすべて標準の
`propext`, `Classical.choice`, `Quot.sound` のみで、独自 axiom はない。

## 次 checkpoint の推奨

まず base layer の三 residue sector ごとの terminal arithmetic exclusion を
狙う。その後 lifted branch について、局所 orbit の独立 scale だけでは不足する
signed integer synchronization と primitive reconstruction を独立 checkpoint
として設計し、実際に `AwayDescentClosureProvider` を構築できる場合だけ
recursive descent を閉じる。
