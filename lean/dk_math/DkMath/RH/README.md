# DkMath.RH

`DkMath.RH` は、Riemann Hypothesis 周辺の解析を
「prime-local contribution（素数ごとの局所寄与）」で観測するための Lean モジュール群です。

ここでの実装目標は、RH の即時証明主張ではなく、次を機械検証可能な API として整備することです。

- 位相ドリフト骨格（`phaseVel`, `driftFreeAt`, `phaseCurv`）
- Euler 因子の局所観測（`w_p`, factor phase velocity）
- 有限 Euler 積での停留・非退化停留判定
- CFBRC と接続可能な HOPC 観測量（寄与総和）公開

## 入口

- 実装トップ: `DkMath/RH.lean`
- 詳細解説（長文）: `DkMath/RH/docs/README.md`
- 方針文書: `DkMath/RH/docs/HOPC-RH.txt`
- CFBRC 連携議論: `DkMath/RH/docs/RH-CFBRC-Discussion.md`
- 実装履歴: `DkMath/RH/docs/RH_Implements_History.md`

## ファイル構成（実装）

- `Defs.lean`
  - `vertical`, `torque`, `phaseVel`, `phaseUnwrap`, `driftFreeAt`, `phaseCurv`
- `Lemmas.lean`
  - 位相速度の代数公式、積・商・逆数法則、停留同値
- `Theorems.lean`
  - `phaseUnwrap` の微分に関する基礎定理
- `EulerZeta.lean`
  - Euler 因子 / 有限積 / 局所位相寄与
  - HOPC 公開定義:
    - `hopcPrimeLocalContribution`
    - `hopcPrimeContributionSum`
- `EulerZetaLemmas.lean`
  - 単一素数因子の導関数・位相速度
  - 有限積の積→和補題
  - `driftFreeAt` / `stationaryAt` / `nondegenerateStationaryAt` と
    HOPC 寄与総和の同値
- `EulerZetaConvergence.lean`
  - `σ > 1` での magnitude 無限積収束と正値

## 主要 API（RH-H1 時点）

- HOPC 観測量:
  - `hopcPrimeLocalContribution p σ t`
  - `hopcPrimeContributionSum S σ t`
- 停留判定（有限 Euler 積）:
  - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`

## 利用例（import）

```lean
import DkMath.RH

open DkMath.RH.EulerZeta
```

必要最小だけ使う場合:

```lean
import DkMath.RH.EulerZeta
import DkMath.RH.EulerZetaLemmas
```

## 注意

- 本層は「観測器 API の整備」を主目的とし、RH の完全証明を主張しません。
- `arg` の枝問題は避け、`phaseVel` / `phaseUnwrap` 中心で整理します。
