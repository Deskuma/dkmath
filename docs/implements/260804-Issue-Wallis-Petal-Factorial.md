# 260804 Issue: Wallis–Petal 階乗経路

- Status: Implemented (finite Petal–Wallis route and dependency audit)
- Date: 2026-08-04
- Completed: 2026-08-29
- Conversation CID: `6a70c207-6590-83e8-83ff-cfc11d956da4`

## 目的

Wallis–Cosmic 有限積の中央階乗比を、`Nat.factorial` の直接利用ではなく、
`DkMath.Petal` の正単位核・可変 lap-base・階乗 Petal を正本として再構成する。

特に、

```text
core = 0:
  0 角形の退化核。Petal は成長しない。

lap = 0:
  有効な初期単位核だけが残る。

factorialPetal 0 = 1:
  最小有効単位核 1 の零周保存。
```

を形式的に分離する。

## 開発文書

- [改修計画書](../../lean/dk_math/docs/dev/cf-wallis-bridge-260704/260804-Issue-Wallis-Petal-Factorial-Remediation-Plan.md)
- [設計書](../../lean/dk_math/docs/dev/cf-wallis-bridge-260704/260804-Issue-Wallis-Petal-Factorial-Design.md)
- [旧 Wallis 設計記録](../../lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-design.md)
- [Wallis growth route](../../lean/dk_math/docs/dev/cf-wallis-bridge-260704/cf-wallis-growth-route.md)

## 実装した中心

```text
DkMath.Petal.Counting
  -> valid / degenerate Petal core
  -> canonical petalOrbitTotal

DkMath.Petal.Factorial
  -> unitPetalCore
  -> factorialPetal
  -> factorialPetal_zero / succ
  -> Nat.factorial compatibility

DkMath.Pascal.WallisCosmicPetalBridge
  -> petalCentralRatioQ
  -> Wallis half-product
  -> Cosmic gap product
```

## 受入条件の要点

- [x] `0! = 1` を零核ではなく最小単位核の零周として定理化する。
- [x] 有効 Petal 核を `0 < n` または安定した `PNat` 型で表す。
- [x] 固定 Petal の等比成長を可変基底 Petal の特殊化として回収する。
- [x] 階乗を基底列 `1, 2, 3, ...` の Petal orbit として構成する。
- [x] Wallis 主有限 theorem は Petal 階乗再帰を使用する。
- [x] `Nat.factorial` / `Nat.choose` は compatibility layer に限定する。
- [x] Mathlib Wallis 極限定理の Gamma 依存有無を別 checkpoint で監査する。

## 実装・検証結果

- `DkMath.Petal.Counting` に valid / degenerate core、`PositivePetalCore`、
  `petalOrbitTotal` を実装した。
- `DkMath.Petal.Factorial` に unit core 起点の `factorialPetal`、零周・再帰・正値定理、
  `Nat.factorial` compatibility theorem を実装した。
- `DkMath.Pascal.WallisCosmicPetalBridge` の主有限経路を
  `petalCentralRatioQ` → Wallis half-product → Cosmic gap product に接続した。
- `WallisLimitBridge` で `Real.Wallis.tendsto_W_nhds_pi_div_two` に接続し、
  Wallis ソースは sine-power 積分・評価・squeeze に基づき Gamma/Stirling を参照しないことを監査した。
- 対象モジュールの `import Mathlib` を限定 import に置換し、`lake build DkMath` が
  `9778 jobs` で成功した。

なお、`DkMath.Basic` など既存の共有基盤に残るリポジトリ全体の umbrella import 撤去、
および Wallis 極限の独立再証明は本 Issue の完了範囲外である。
