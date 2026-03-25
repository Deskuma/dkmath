# AGENT

## 1. 目的

本ドキュメントは、DkMath 研究プロジェクトにおける
ライブラリ整備・リファクタリング・公開移行の基本方針を定める
エージェント向け運用マニュアルである。

本プロジェクトでは、研究中の実験的実装を `DkMath.*` に保持しつつ、
段階的な整理・抽象化・公開準備を `DkMath.Lib.*` に集約し、
最終的に公開ライブラリ `DkMathlib.*` として切り出す。

移行の基本経路は次の通りとする。

$$
\mathrm{DkMath.*} \;\to\; \mathrm{DkMath.Lib.*} \;\to\; \mathrm{DkMathlib.*}
$$

---

## 2. 基本理念

### 2.1. 研究と公開を分離する

- `DkMath.*`
  - 研究中の実装、実験的補題、暫定設計、検証途中のモジュールを置く。
  - `sorry` を含み得る。
  - 命名、依存、配置は将来の整理対象であることを許容する。

- `DkMath.Lib.*`
  - `DkMath.*` から抽出した公開候補 API を整理する場所。
  - 研究補題から再利用される「安定した中間層」を作る。
  - 公開を見据え、命名規則・依存方向・入口ファイルを整備する。
  - 原則として、ここには研究用の局所都合を持ち込まない。

- `DkMathlib.*`
  - 一般公開される安定ライブラリ。
  - `DkMath.Lib.*` で整備・安定化された内容を移す。
  - 公開後、研究側は原則として `DkMathlib.*` を import する。

### 2.2. 公開名を先に意識する

`DkMath.Lib.*` は単なる退避場所ではない。
将来 `DkMathlib.*` にそのまま移せるように、名前・階層・依存方向を
最初から公開仕様に近づけて整備する。

### 2.3. 依存方向を固定する

依存方向の原則は次の通り。

$$
\mathrm{Research} \;\to\; \mathrm{Lib} \;\to\; \mathrm{Public}
$$

逆方向依存は禁止する。

- `DkMath.Lib.*` は `DkMath.*` の研究用実装詳細に依存しすぎてはならない。
- `DkMathlib.*` は `DkMath.*` を import してはならない。
- 研究補題は段階的に `DkMath.Lib.*` を import するよう移す。
- 公開後は研究補題も `DkMathlib.*` を import する構成へ切り替える。

---

## 3. 理論コアの扱い

本プロジェクトの理論コアは、動的調和数論（DHNT）を中心に置く。

主体は指数対数

$$
e^k \;\Leftrightarrow\; e_k
$$

によるスケーリング視点であり、固定単位「1」だけでなく、
生成元 \(u^d\) を含む多層的単位構造を扱う。

また、宇宙式

$$
N + 1 = (P + 1)^2
$$

およびその一般化

$$
(P+u)^2 = P^2 + 2Pu + u^2,
\qquad
(x+u)^n
$$

さらに defect 構造

$$
(x+u)^d - u^d=
x \cdot \sum_{k=0}^{d-1} \binom{d}{k} x^{d-1-k} u^k
$$

を重要な核 API として扱う。

したがって、リファクタリング時には
DHNT・Cosmic Formula・単位構造・相対化・調和写像の関係を
分断せず、公開可能な抽象 API として切り出すことを優先する。

---

## 4. 名前空間の移行方針

### 4.1. 研究名前空間

```lean
DkMath.*
```

- 研究用。
- 暫定・実験・会話由来の設計を含む。
- 完全公開前提ではない。

### 4.2. 整理用名前空間

```lean
DkMath.Lib.*
```

- リファクタリングの作業場所。
- 公開候補 API を先行整備する。
- 命名とディレクトリ構成を安定化する。
- `DkMath.*` 側の研究補題から参照されることを想定する。

### 4.3. 公開名前空間

```lean
DkMathlib.*
```

- 一般公開用。
- `DkMath.Lib.*` の内容を移植・整理した完成形。
- 最終的な利用者向け import 入口を提供する。

---

## 5. 移行手順

### 5.1. 第1段階. 研究実装の棚卸し

- 既存 `DkMath.*` のうち、公開候補となる定義・補題・定理を抽出する。
- `def` / `lemma` / `theorem` 単位で責務を確認する。
- 研究補題・暫定補題・公開候補補題を分別する。
- `INDEX.md` や自動抽出スクリプト等を活用し、現状の地図を把握する。

### 5.2. 第2段階. `DkMath.Lib.*` へ移設

- 公開候補 API を `DkMath.Lib.*` に新設する。
- ここでは次を必ず行う。

  - 命名の整理
  - docstring の付与
  - import の整理
  - 依存方向の正常化
  - 型の世界（`Nat`, `ℤ`, `ℚ`, `ℝ` など）の切り分け
- 元の `DkMath.*` 側は、必要なら wrapper として残す。

### 5.3. 第3段階. 研究側 import の付け替え

- 研究モジュールは、可能なものから順に `DkMath.Lib.*` を import する。
- 研究モジュールが安定 API を参照する構造に変える。
- 研究途中の詳細は `DkMath.*` に残してよいが、
  基本定義や再利用補題は `DkMath.Lib.*` に寄せる。

### 5.4. 第4段階. `DkMathlib.*` へ公開

- `DkMath.Lib.*` の内容が安定し、命名と依存が確定したら
  `DkMathlib.*` として公開する。
- 公開後は研究側も原則 `DkMathlib.*` を import する。
- `DkMath.Lib.*` は移行用バッファとして段階的に縮小する。

---

## 6. 公開入口の設計

公開時の入口は、理論のまとまりごとに top-level import を提供する。

### 6.1. DHNT 入口

```lean
-- DkMathlib/DHNT.lean
import DkMathlib.DHNT.Core
import DkMathlib.DHNT.Unit
import DkMathlib.DHNT.Relative
import DkMathlib.DHNT.Defect
import DkMathlib.DHNT.Harmonic
import DkMathlib.DHNT.Laws
```

### 6.2. Cosmic Formula 入口

```lean
-- DkMathlib/CosmicFormula.lean
import DkMathlib.CosmicFormula.BigBodyGap
import DkMathlib.CosmicFormula.Tromino2D
import DkMathlib.CosmicFormula.UnitDenomPow2
import DkMathlib.CosmicFormula.ExpBridge
```

### 6.3. 設計原則

- top-level ファイルは「利用者向け目次」とする。
- 下位モジュールは責務ごとに分割する。
- `Core` は最小依存で保つ。
- `Laws` は基本恒等式・同値変形・主要補題を束ねる。
- `Bridge` 系は他理論との接続層として分離する。

---

## 7. 推奨ディレクトリ方針

### 7.1. 研究側

```text
lean/dk_math/DkMath/
```

- 研究本体。
- 実験・検証・暫定実装を含む。

### 7.2. 整理側

```text
lean/dk_math/DkMath/Lib/
```

- 公開候補 API の整理場所。
- 研究側から段階的に参照される中間層。

### 7.3. 公開側

将来的には別パッケージまたは別トップレベルとして

```text
DkMathlib/
```

を持つ。

必要に応じて、リポジトリ分離または package 分離を行う。

---

## 8. Codex / Agent 向け作業規則

### 8.1. 変更時に必ず意識すること

- その変更は `DkMath.*` に置くべきか、`DkMath.Lib.*` に置くべきかを先に判断する。
- 再利用される定義・補題は `DkMath.Lib.*` を優先する。
- 研究ローカルな補題や一時的補助は `DkMath.*` に残してよい。
- 将来 `DkMathlib.*` に出したいものは、最初から公開 API 名で設計する。

### 8.2. import の原則

- 新規研究補題は、可能であれば `DkMath.Lib.*` を import して構築する。
- `DkMath.Lib.*` では、不要な研究モジュール import を避ける。
- `DkMathlib.*` では `DkMath.*` を import しない。

### 8.3. ドキュメントの原則

- 会話・議論・設計判断は積極的に文書化する。
- 実装だけでなく、設計意図を残す。
- リファクタリングでは「どこへ移したか」だけでなく、
  「なぜそこへ移したか」を残す。

---

## 9. AGENT.md の配置方針

### 9.1. 基本マニュアル

本ドキュメントのような全体方針は、リポジトリ全体に効くため、
プロジェクトトップで管理するのを推奨する。

例：

```text
/AGENT.md
```

### 9.2. Lean 実装用ローカル補助

Lean プロジェクト固有の補足運用は、Lean 側にも局所版を置いてよい。

例：

```text
/lean/dk_math/AGENT.md
```

### 9.3. notes 配下の位置づけ

`notes/chatgpt_projects/.../AGENT.md` のような場所は、
会話由来の設計記録や試案ログとしては有用である。
ただし、全体の基本マニュアルを置く場所としては局所的であり、
新規参加者や自動エージェントには見つけにくい。

そのため、

- 全体基本方針はプロジェクトトップへ昇格
- notes 配下版は履歴・会話起源資料として残す
- Lean 固有版は `lean/` 側へ補助的に置く

という二層または三層管理を推奨する。

---

## 10. 当面の実務タスク

### 10.1. 最初に行うこと

- `DkMath.Lib.*` 名前空間を新設する
- `DkMath.Lib.DHNT.*` を最初の整備対象とする
- `DkMath.Lib.CosmicFormula.*` を次の整備対象とする
- `DkMath.DHNT` / `DkMath.CosmicFormula` の研究側入口を薄い wrapper に寄せる

### 10.2. 優先公開対象

まずは次を公開候補コアとして整備する。

- `DHNT.Core`
- `DHNT.Unit`
- `DHNT.Relative`
- `DHNT.Defect`
- `DHNT.Harmonic`
- `DHNT.Laws`

および

- `CosmicFormula.BigBodyGap`
- `CosmicFormula.Tromino2D`
- `CosmicFormula.UnitDenomPow2`
- `CosmicFormula.ExpBridge`

### 10.3. 完了条件

- 研究側の主要補題が `DkMath.Lib.*` を参照する
- `DkMath.Lib.*` が公開 API として読める構造になる
- `DkMathlib.*` へ機械的に移せる段階まで命名と構成が固定される

---

## 11. まとめ

本プロジェクトのリファクタリングは、単なる名前変更ではない。
研究中の宇宙を、公開可能な理論 API へ鍛え直す作業である。

したがって、すべての移行判断は

$$
\mathrm{DkMath.*} \;\to\; \mathrm{DkMath.Lib.*} \;\to\; \mathrm{DkMathlib.*}
$$

という流れの中で、

- 再利用性
- 命名の安定性
- 依存方向の健全性
- 公開後の読みやすさ
- 研究継続のしやすさ

を基準に行うこと。
