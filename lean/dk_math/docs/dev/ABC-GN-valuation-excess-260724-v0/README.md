# ABC–GN Valuation Excess Workbench

作成日: 2026-07-24

Repository: `Deskuma/dkmath`

## 1. 目的

この作業場は、DkMath に既に存在する一般 `GN`、`padicValNat`、primitive prime、factorization、`rad` / `supportMass` の各 API を、ABC の決定論的な主線として再接続するための開発領域である。

中心となる観測は次である。

$$
(x+u)^n-u^n=x\,GN_n(x,u)
$$

ABC triple の座標 `a + b = c` では、

$$
c^n-b^n=a\,GN_n(a,b)
$$

となる。

本プロジェクトでは、この分解を用いて、素数 support と valuation multiplicity を分離する。

```text
GN support
  -> primitive / Petal prime channels
  -> supportMass / rad

GN multiplicity
  -> padicValNat
  -> exponent-exception layer q | n
  -> non-exceptional high-lift layer q ∤ n
  -> valuation excess
```

最終的な研究目標は、ABC quality が大きくなる原因を `GN` 上の valuation concentration として可視化し、既存の確率・質量 route を、可能な限り決定論的な GN route へ置き換えることである。

## 2. 現時点で主張しないこと

この作業場の設置だけでは、次を主張しない。

- `abc_main_axiom` の除去
- ABC 予想の証明
- 一般 `GN` の squarefree 性
- 非例外高持ち上がり prime の一様排除
- `rad (GN n a b) ≤ rad (a * b * c)` のような一般には成立しない輸送
- 既存の確率・密度 route が不要になったという結論

Lean が認可した局所定理だけを積み、残った Gap を明示する。

## 3. Branch 構成

```text
develop
  └─ feature/ABC-GN-valuation-excess-260724-v0
       └─ wip/ABC-GN-valuation-excess-260724-Codex
```

役割:

- `develop`: 開始基準
- `feature/...`: 賢狼レビューで採用された checkpoint の統合先
- `wip/...-Codex`: Codex 第2 Brain の現場実装・試行錯誤領域

WIP から feature への draft PR を常設する。

## 4. 並行開発との共存

同じ `develop` 系列では、現在 FLT7 の別作業が並行している。

```text
wip/FLT7-magic-core-260722-WiseWolf
```

ABC–GN 作業では次を守る。

- `DkMath/FLT/Seven/**` および FLT7 専用 docs を変更しない。
- FLT7 側の theorem・命名・import 構造を整理目的で変更しない。
- 原則として `DkMath/ABC/**`、必要な `NumberTheory` bridge、当作業場 docs のみに変更を限定する。
- `DkMath.lean`、`DkMath/ABC.lean`、共有 aggregator の変更が必要な場合は最小一行に限定し、report に明記する。
- 並行 branch の成果を先取りして import しない。必要な共通 API は現在の ABC–GN branch 上に存在するものだけを使用する。
- feature への採用時または develop への統合前に、並行変更との compare / merge-base を再確認する。

両 branch が `develop` から派生しているため、対象領域を守る限り通常は独立に進められる。競合が生じた場合は、ABC–GN 側で FLT7 実装を改変して解決せず、賢狼レビューへ戻す。

## 5. 開発サイクル

```text
賢狼が instruction-NNN.md を追加
  ↓
D. が Codex の起動トリガーを実行
  ↓
Codex が current source を調査して実装
  ↓
Codex が report-NNN.md と commit を追加
  ↓
Lean CI
  ↓
賢狼が PR diff と数学的意味をレビュー
  ↓
次の instruction-NNN.md を追加
```

Codex は単なる写経担当ではない。現場の current source を読み、既存 theorem の再利用、命名、配置、依存方向を判断してよい。ただし、instruction の数学的境界を越える強い主張は追加しない。

## 6. 資料の読み順

最初に次を読む。

```text
README.md
AGENT.md
SUMMARY.md
```

その後、GitHub current source を優先して調査する。

必要に応じて以下を参照する。

```text
__dkmath-all.lean.txt.gz
__summary_report_data.tar.gz
__theorems-heading.txt
```

巨大な raw agent log、会話全文 dump、統合ログは開かない。必要な事実は current source、整理済み docs、対象 theorem から取得する。

## 7. 主な既存資産の候補

実際の import と theorem 名は current source で再確認すること。

```text
DkMath.CosmicFormulaBinom.GN / GTail
DkMath.NumberTheory.Gcd.GN
DkMath.NumberTheory.PrimitiveBeam
DkMath.NumberTheory.UniqueFactorizationGN
DkMath.NumberTheory.ValuationFlow.*
DkMath.ABC.Rad
DkMath.ABC.MassBridge
DkMath.ABC.ValuationFlowBridge
DkMath.Petal.ABCBridge
```

既存定理の wrapper で済むものを再証明しない。

## 8. Checkpoint 方針

当面の登山路は次である。

```text
ABC-GN-001  ABC triple の GN power lift
ABC-GN-002  lift の coprime / support separation
ABC-GN-003  ABC 座標の padic boundary–GN split
ABC-GN-004  q | n / q ∤ n の例外層分離
ABC-GN-005  valuation excess の有限 factorization API
ABC-GN-006  high quality -> GN excess 強制 bridge
ABC-GN-007  non-exceptional high-lift obstruction
ABC-GN-008  finite exceptional absorption
ABC-GN-009  K_epsilon construction
ABC-GN-010  abc_main_axiom replacement audit
```

この番号は研究地図であり、各 checkpoint の実装量は current source に応じて分割・統合してよい。

## 9. 実装規律

- 新しい `axiom` を追加しない。
- target module に `sorry` を追加しない。
- `native_decide` による証明を追加しない。
- `abc_main_axiom` を今回の局所実装の証明材料として使わない。
- `DkMath.ABC.*` は翻訳・bridge 層を基本とし、一般数論定理は適切な `NumberTheory` 側へ置く。
- import cycle を作らない。
- theorem statement は現在証明できる最小の強さにする。
- 既存 API と重複する場合は、新定理ではなく薄い namespace wrapper を検討する。
- README や report では、Lean-confirmed fact、数学的解釈、未証明 Gap を分ける。

## 10. 報告契約

各 `report-NNN.md` には最低限、次を記録する。

```text
- 調査した既存 module / theorem
- 追加・変更した file
- 新規 theorem / def / structure
- 数学的に何が閉じたか
- 何はまだ言えていないか
- build / CI の結果
- 次 checkpoint 候補
- commit SHA
- 並行 FLT7 branch と共有領域を触れたか
```

## 11. 現在の起動指示

起動入口:

```text
CODEX_START.md
```

現在の指示書:

```text
instruction-001.md
```

Codex の実装は、D. が明示的に起動したときだけ開始する。
