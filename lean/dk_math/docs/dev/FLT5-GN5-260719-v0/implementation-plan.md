# FLT5 / GN5 standalone-first 実装計画

作業ブランチ: `hackathon/feature-gn5-flt5-260719-v0`

## 1. 方針

指数 `5` に固定した局所実験塔を新設し、各段階を Lean に認可させる。

既存の一般 `p ≥ 5` research route は証明戦略の参考資料として読むが、本塔から research-only theorem は import しない。重複は許容し、standalone 化と Lean Comparator Live への移植を優先する。

完成後にのみ、安定した一般部品を `DkMath.Lib.*` へ昇華する。

## 2. 数学的中核

五次専用多項式を

```text
GN5(g,y)
  = g^4 + 5 g^3 y + 10 g^2 y^2 + 10 g y^3 + 5 y^4
```

と定義する。

中心恒等式は

```text
(g+y)^5 - y^5 = g * GN5(g,y)
```

である。

FLT5 反例候補 `x^5 + y^5 = z^5` に対し `g = z-y` と置けば、

```text
x^5 = z^5 - y^5 = (z-y) * GN5(z-y,y)
```

となる。

clean channel `q` の契約は次とする。

```text
q is prime
q divides GN5(g,y)
q does not divide g
q^2 does not divide GN5(g,y)
```

この局所入力から完全五乗を否定する。

## 3. ファイル構成

```text
DkMath/FLT/Five/
├── Basic.lean
├── GN5.lean
├── CleanChannel.lean
├── Valuation.lean
├── BranchB.lean
├── BranchA.lean
├── Provider.lean
├── Main.lean
├── CheckAxioms.lean
└── Standalone.lean

DkMath/FLT/Five.lean
```

初回 checkpoint では `Basic`, `GN5`, `CleanChannel`, `BranchB` の代数 spine を作る。

## 4. 定理チェーン

```text
Fermat5Equation
  -> y < z
  -> z = (z-y) + y
  -> z^5 - y^5 = (z-y) * GN5(z-y,y)
  -> z^5 - y^5 = x^5
  -> clean GN5 channel
  -> direct divisibility contradiction
  -> independent padicValNat contradiction
```

## 5. checkpoint

### cp-000: structure and algebra spine

- `Fermat5Equation`
- `CounterexamplePack`
- `GN5`
- 五次差冪因数分解
- `GN5 1 1 = 31`
- `CleanGN5Channel`
- Fermat equation から `Body5 = x^5` への橋

### cp-001: direct divisibility refuter

- clean channel から Body が完全五乗でないことを直接整除で証明
- FLT5 equation との接続

### cp-002: padicValNat refuter

- 完全五乗側の valuation 下界 `5`
- clean channel 側の valuation 上界 `1`
- 同一 statement の第二証明

### cp-003: Branch-B provider

- existential clean channel provider を定義
- provider と refuter を分離

### cp-004: Branch-A normal form

- `5 ∣ z-y` 領域の五進正規形を Lean で観測
- 初手から `False` を要求しない

### cp-005: standalone

- `import Mathlib` のみ
- DkMath import なし
- Lean Comparator Live 用 single file

## 6. Lean 認可 gate

1. 対象ファイルが build する
2. target theorem に `sorry` がない
3. research-only theorem を import しない
4. theorem statement が仮定を超えない
5. `#print axioms` で `sorryAx` が出ない

重複は欠陥ではなく、依存と命題境界を観測するための装置として扱う。
