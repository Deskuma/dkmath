# FLT7-016 作業レポート

日付: 2026-07-23  
結果: **Outcome A — prime-power unit-orbit classification 完了**

## FLT7-015P との差分

FLT7-015P は、実際の full-depth solution と同じ row/column に明示的モデルが
存在することを示した。FLT7-016 ではこれを強化し、各実解が canonical model
を unit `s` で root weight 3、endpoint weight 7 に拡大したものと厳密に等しい
ことを証明した。既存の source classification の意味は変更していない。

## 実装

- 任意の `CommRing` について、unit witnesses の内部で
  `s = v^5 * (w⁻¹)^2` を構成する generic 3/7 parametrization を実装した。
  `w^3 = C*v^7` から `v = C^2*s^3`、`w = C^5*s^7` を得る。
- arbitrary ring には inverse operation がないため、公開 surface は unit witness
  から環へ戻した scale を保持する `ThreeSevenUnitParametrization` とした。
  field assumption は使用していない。
- `scalePrimePowerSolution` を実装し、全 endpoint/root/first-coordinate equation
  と `IsUnit` 非退化条件が weight-(3,7) action で保存されることを証明した。
- sevenV、leftCubic、rightCubic の canonical model を全3 row について直接定義した。
  以前の `Nonempty` からの `Classical.choice` は使っていない。
- cubic 列では `t = u*v⁻¹`、homogeneous correction identity、signed coefficient
  `C` を用いて 3/7 parametrization を適用した。
- 9ケースすべてについて、実解と scaled canonical model の構造体としての
  exact equality を証明した。
- 強分類 `AwayNonSevenPrimePowerOrbitSource` と、CounterexamplePack から
  ramified / awayOrbitClassified へ進む `primePowerOrbitAuditResult_of_pack` を追加した。

## 検証

以下を成功確認した。

```text
lake build DkMathTest.FLT.SevenPrimePowerUnitOrbit \
  DkMathTest.FLT.SevenPrimePowerOrbitAudit DkMath.FLT.Seven DkMath.FLT
```

テストは非体 `ZMod (5^2)` 上の generic theorem、全 row/column の weighted action、
9 orbit cases、exact equality、FLT7-015 generic diagonal counterexample、最終 route を含む。
Axiom audit は標準の `propext`, `Classical.choice`, `Quot.sound` の範囲で、追加公理はない。
対象差分に `sorry`、宣言 `axiom`、`native_decide` はない。

## 残る境界

各 specialized prime address で得た unit scale が、異なる素数間で同時に貼り合わさる
ことは示していない。global signed reconstruction、AwayDescentClosureProvider、recursive
descent、FLT7 contradiction は本 checkpoint の結論ではない。
