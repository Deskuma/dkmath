# dev report

---

## 2026/03/30 — 状況整理レポート (第1回)

### 1. 現在のブランチ

| ブランチ | 状態 |
|---|---|
| `dev/FLT-witness-260328-v0` | **HEAD** (現作業ブランチ) |
| `dev/FLT-Primitive-260327-v0` | develop へマージ済 |
| `dev/FLT-Wieferich-260327-v1` | final_report あり / 独立 |
| `dev/GN-Tail-260327-v0` | 独立 |
| `develop` | 安定版ベース |

現在の作業ブランチ `dev/FLT-witness-260328-v0` には develop からのコミットが 5 本積まれている。

---

### 2. 主要 Lean ファイルの状況

#### `DkMath/FLT/PrimeProvider/` 三点セット

| ファイル | 行数 | 定義・定理数 | `sorry` 数 | 備考 |
|---|---|---|---|---|
| `TriominoCosmicBranchA.lean` | 5,033 | 378 | **1** | `primeGe5BranchANormalFormNePSupportKernel_default` に残存 |
| `TriominoCosmicBranchAExceptional.lean` | 3,707 | 492 | **0** | Two-witness route 実装済 |
| `TriominoCosmicGapInvariant.lean` | 2,992 | 393 | 0 (コメント内のみ) | BranchA adapter 含む |

**合計 11,732 行、1,263 定義・定理。**

---

### 3. 各 dev セッションの要約

#### 3.1. `flt-abc-260325-v0`

- valuation peel 路線を試みたが、smaller packet の直接構成には到達せず。
- 収穫：
  1. **比較対象の固定** — `GTail p 2` の差として error term が explicit 化
  2. **canonical tail 段の発見** — seed → canonical tail → comparison の流れが確立
  3. **合同の厳密式への持ち上げ** — `p*B = C + (p^(p-1)*t₁^p)*E` が得られた
  4. **peel の役割確定** — smaller packet 直接構成器ではなく obstruction extraction 装置
- 結論：**primitive packet descent が本命 route** と判断。

#### 3.2. `GN-Tail-260326-v0`

- `GTail` 周辺の補題候補を整理。
- 既存実装 (`GTail_zero_eq_add_pow` 等) との突き合わせ完了。
- 実装優先順：`higher_tail_eq_pow_mul_GTail` → `Gbinom_tail_rec` / `zero_eval` → `pow_dvd_higher_tail` → `padicValNat_tail_exact_of_head_unit`。

#### 3.3. `GN-Tail-260327-v0`

- 上記の具体実装 review (review-001 ～ 010)。
- 引き続き GTail 周辺の整備中。

#### 3.4. `FLT-Wieferich-260327-v1`

- Branch A で得られた `y^(p-1) ≡ 1 [MOD p²]` witness を Wieferich refuter へ接続する設計。
- `BranchAWieferichAdapterTarget` を `TriominoCosmicGapInvariant.lean` に追加。
- 欠けているのは `PrimeGe5BranchAWieferichRefuterTarget` の clean concrete 実装 1 本のみ。
- **final report** 作成済 (`!_final_report-999.md`)。

#### 3.5. `FLT-Primitive-260327-v0`

- `PrimeGe5BranchAPrimitivePacketDescentTarget` を本命 route として開始。
- `TriominoCosmicBranchAExceptional.lean` を新規作成し、exceptional branch を分離。
- **主な作業のまとめ：**
  - `PrimeGe5BranchAExceptionalExistenceMainlineTarget` の concrete proof 入口を固定
  - `PrimeGe5BranchAPrimitiveWieferichPacketTarget` を BranchA に追加
  - 反例検証 → same-`q` route が偽と Lean 上で確定
  - `ExceptionalBoundaryDatumConcrete` 系の datum 群を整備
  - develop へマージ済。

#### 3.6. `FLT-witness-260328-v0` ← **現在の作業ブランチ**

**目的：** same-`q` route を正式に捨て、two-witness route へ切り替える。

- **2026/03/28** `review-001` : same-`q` route を反例で偽と確認 → two-witness route への切り替えを推奨。
- **2026/03/28 22:23 JST** : `counterexample_not_dvd_bodyCore_two/three` ほかを追加。`(d,x,u)=(5,5,7)` で same-`q` route が偽と Lean 上で確定。
- **2026/03/28** `review-002` : same-`q` 系を打ち切り、two-witness route への正式移行を指示。
- **2026/03/30 02:24 JST** : two-witness系 target と clean interface を複数追加。
  - 追加 target：
    - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceTarget`
    - `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget`
    - `PrimeGe5BranchAExceptionalPracticalTwoWitnessConcreteTarget`
    - `PrimeGe5BranchAExceptionalBodyCoreWitnessToPrimitivePacketDescentTarget`
    - `PrimeGe5BranchAExceptionalBodyCoreWitnessToExistenceMainlineTarget`
  - adapters / bridge 系も `TriominoCosmicGapInvariant.lean` に追加。
  - `lake build` はいずれも成功確認済。

---

### 4. 現在の open task（次の課題）

| 優先度 | 課題 | 関連ファイル |
|---|---|---|
| **最高** | `PrimeGe5BranchAExceptionalBodyCoreWitnessExistenceConcreteTarget` の concrete 本体を証明する | `TriominoCosmicBranchAExceptional.lean` |
| **高** | body/core witness → primitive packet descent / existence mainline への clean bridge statement を数論形に正規化する | 同上 |
| **中** | `TriominoCosmicBranchA.lean` に残る `sorry` 1 箇所 (`primeGe5BranchANormalFormNePSupportKernel_default`) を埋める | `TriominoCosmicBranchA.lean` |
| **中** | GTail 周辺補題 (`pow_dvd_higher_tail`, `padicValNat_tail_exact_of_head_unit`) の実装 | `DkMath/CosmicFormula/GTail.lean` |
| **低** | `BranchAWieferichAdapterTarget` の concrete 実装 | `TriominoCosmicGapInvariant.lean` |

---

### 5. two-witness route の全体像（現時点）

```
Branch A Exceptional の仮定
  ↓
  ┌── arithmetic witness q_arith : q_arith ∣ x+1, q_arith ∤ x
  └── body/core witness q_body : q_body ∣ cyclotomicPrimeCore(d,1,u-1)
         [← ここが ConcreteTarget で未証明]
  ↓
PrimeGe5BranchAExceptionalBodyCoreWitnessToPrimitivePacketDescentTarget (bridge)
  ↓
PrimeGe5BranchAPrimitivePacketDescentTarget
  ↓
FermatLastTheoremFor p (p ≥ 5)
```

`same-q` route（q_arith = q_body を要求する枝）は `(d,x,u)=(5,5,7)` の反例で偽と確定。
`BodyCoreWitnessExistenceConcreteTarget` の concrete proof が次の最重要 missing piece。

---

### 6. ファイル規模サマリ

```
lean/dk_math/DkMath/FLT/PrimeProvider/
├── TriominoCosmicBranchA.lean              5,033行  (sorry×1)
├── TriominoCosmicBranchAExceptional.lean   3,707行  (sorry×0) ← 現在の主戦場
├── TriominoCosmicGapInvariant.lean         2,992行
└── ... (他 PrimeProvider ファイル多数)
```

---

## 2026/03/30 — `BodyCoreWitnessExistenceConcreteTarget` 分析 (第2回)

### 7. 致命的発見：`BodyCoreWitnessExistenceConcreteTarget` は偽である

#### 7.1. 反例

**`(d, x, u) = (5, 5, 1)` で全仮定が満たされるが、結論が偽。**

| 仮定 | 値 | 判定 |
|---|---|---|
| `Nat.Prime d` | `Prime 5` | ✓ |
| `5 ≤ d` | `5 ≤ 5` | ✓ |
| `0 < x` | `0 < 5` | ✓ |
| `0 < u` | `0 < 1` | ✓ |
| `Coprime x u` | `Coprime 5 1` | ✓ |
| `d ∣ x` | `5 ∣ 5` | ✓ |
| `u^(d-1) ≡ 1 [MOD d²]` | `1^4 ≡ 1 [MOD 25]` | ✓ (自明) |

結論：`∃ q, Prime q ∧ q ∣ cyclotomicPrimeCore 5 1 (1-1)`

- `cyclotomicPrimeCore 5 1 0 = ∑_{k=0}^{4} 1^k · 0^{4-k} = 0 + 0 + 0 + 0 + 1·1 = 1`
- **1 を割る素数は存在しない → 結論は偽**

#### 7.2. `BodyCoreDatum` が `x` を使わない構造的問題

```lean
abbrev PrimeGe5BranchAExceptionalPracticalBodyCoreDatum (d x u q : ℕ) : Prop :=
  let _ := x   -- x は未使用
  q ∣ DkMath.CFBRC.cyclotomicPrimeCore d 1 (u - 1)
```

`cyclotomicPrimeCore d 1 (u-1) = u^d - (u-1)^d`（代数的恒等式）。

- `u ≥ 2` のとき：`u^d - (u-1)^d ≥ 2^5 - 1 = 31 ≥ 2` → 素因数あり ✓
- `u = 1` のとき：`1 - 0 = 1` → 素因数なし ✗

**BodyCoreDatum は `x` に依存しないため、`u = 1` で必ず壊れる。**

> **結論：`BodyCoreWitnessExistenceConcreteTarget` は same-`q` route に続き、
> body/core datum route も偽と確定した。**

---

### 8. 正しい証明経路の特定

#### 8.1. 二つの cyclotomicPrimeCore

| target | 対象の式 | 意味 |
|---|---|---|
| `BodyCoreWitnessExistence` | `cyclotomicPrimeCore d 1 (u-1)` = `u^d - (u-1)^d` | u のみに依存、u=1 で崩壊 |
| `ExceptionalBoundaryDatumPreparedArithmeticCore` | `cyclotomicPrimeCore d x u` = `((x+u)^d - u^d) / x` | x,u 両方に依存、u=1 でも生きる |

#### 8.2. `ExceptionalBoundaryDatumPreparedArithmeticCoreTarget` は証明可能

この target の statement：

```
∀ {d x u}, Prime d → 5 ≤ d → 0 < x → 0 < u → Coprime x u →
  d ∣ x → u^(d-1) ≡ 1 [MOD d²] →
  ∃ q, Prime q ∧ q ∣ cyclotomicPrimeCore d x u ∧ ¬ q ∣ x
```

**これは Mathlib.FLT を使わずに証明できる。** 以下に証明戦略を示す。

---

### 9. 証明戦略（Mathlib.FLT 非依存）

#### Step 1. 各項の合同評価

`d ∣ x` より `x = d·m`。素数 `p ≠ d` が `p ∣ x` のとき：

> `x+u ≡ u [MOD p]`（`p ∣ x` より）

各項について：

$$
(x+u)^k \cdot u^{d-1-k} \equiv u^k \cdot u^{d-1-k} = u^{d-1} \pmod{p}
$$

`d` 項の和により：

$$
\text{cyclotomicPrimeCore}(d, x, u) \equiv d \cdot u^{d-1} \pmod{p}
$$

`p ∤ d`（`p ≠ d` で両方素数）、`p ∤ u`（`Coprime(x,u)` と `p ∣ x`）より：

> **`p ∣ x`, `p ≠ d` ⟹ `p ∤ cyclotomicPrimeCore d x u`** ✓

#### Step 2. `d` の付値の精密評価（LTE / mod d²）

二項展開 `(dm+u)^k = u^k + k·d·m·u^{k-1} + O(d²)` より：

$$
\text{cyclotomicPrimeCore}(d, x, u) \equiv d \cdot u^{d-1} \pmod{d^2}
$$

Wieferich 条件 `u^{d-1} ≡ 1 [MOD d²]` を代入すると：

$$
\text{cyclotomicPrimeCore}(d, x, u) \equiv d \pmod{d^2}
$$

したがって：

- `v_d(cyclotomicPrimeCore d x u) = 1` （`d ∣ core` だが `d² ∤ core`）
- `core / d ≡ 1 [MOD d]` なので **`d ∤ (core / d)`**

#### Step 3. 合成して GCD 結論

- 素数 `p ∣ x`, `p ≠ d` → `p ∤ core` → `p ∤ core/d`
- 素数 `p = d` → `d ∤ core/d`（Step 2 より）

> **`gcd(core/d, x) = 1`** ✓

#### Step 4. サイズ下界

`d ≥ 5, x ≥ 5, u ≥ 1` のとき：

$$
\text{core} = \sum_{k=0}^{d-1} (x+u)^k \cdot u^{d-1-k} \geq (x+u)^{d-1} \geq 6^4 = 1296
$$

$$
\text{core}/d \geq 1296/5 = 259.2 > 2
$$

#### Step 5. 素因数の取得

`Nat.exists_prime_and_dvd`（Mathlib 基本補題）により：

$$
\exists q,\; \text{Prime}(q) \land q \mid \text{core}/d
$$

`gcd(core/d, x) = 1` より `¬ q ∣ x`。
`q ∣ core/d` より `q ∣ core`。

**QED** ∎

---

### 10. 既存インフラストラクチャとの接続

#### 10.1. 使える既存補題

| 補題 | ファイル | 用途 |
|---|---|---|
| `sub_eq_mul_cyclotomicPrimeCore_nat` | `CFBRC/Basic.lean` | `(x+u)^d - u^d = x · core` |
| `Nat.exists_prime_and_dvd` | Mathlib | `n ≠ 1 → ∃ q prime, q ∣ n` |
| `Nat.Coprime` 関連 | Mathlib | `Coprime(x,u)` の諸帰結 |

#### 10.2. 新たに必要な中間補題

1. **`cyclotomicPrimeCore_modEq_mul_pow_of_dvd`**：
   `d ∣ x → cyclotomicPrimeCore d x u ≡ d · u^{d-1} [MOD p]`（各素因数 p ≠ d に対して）

2. **`cyclotomicPrimeCore_modEq_mul_pow_mod_sq`**：
   `d ∣ x → cyclotomicPrimeCore d x u ≡ d · u^{d-1} [MOD d²]`（二項展開の精密版）

3. **`cyclotomicPrimeCore_div_prime_coprime_of_wieferich`**（合成定理）：
   上記 1 + 2 + Wieferich条件 → `gcd(core/d, x) = 1`

#### 10.3. 閉じ先の最短パス

```
ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget
  ↓ (= ExceptionalBoundaryDatumPreparedArithmeticCoreTarget)
  ↓ exceptional_boundary_datum_arithmetic_core_of_prepared
ExceptionalBoundaryDatumArithmeticCoreTarget
  ↓ exceptional_boundary_datum_concrete_of_arithmeticCore
ExceptionalBoundaryDatumConcreteTarget
  ↓ primeGe5BranchAExceptionalExistenceMainline_of_datumConcrete
PrimeGe5BranchAExceptionalExistenceMainlineTarget ← proof file mainline
```

**全てのブリッジは既に実装済み。`PreparedArithmeticCoreConcrete` ただ 1 本を埋めれば mainline まで自動的に閉じる。**

---

### 11. open task の改訂

| 優先度 | 課題 | 状態 |
|---|---|---|
| ~~最高~~ | ~~`BodyCoreWitnessExistenceConcreteTarget`~~ | **偽と判明。打ち切り** |
| **最高** | `ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` を証明する | 証明戦略確定（§9）|
| **高** | 中間補題の Lean 実装（`cyclotomicPrimeCore_modEq_*` 系 2-3 本） | 未着手 |
| **中** | `TriominoCosmicBranchA.lean` の `sorry` 1 箇所 | 変更なし |
| **低** | `BodyCoreWitnessExistenceTarget` に `1 < u` を追加して修正し、`two-witness` route を salvage する（任意） | 事後整理 |

---

### 12. 検算：`u = 1` での boundary target の通過確認

`(d, x, u) = (5, 5, 1)` での `cyclotomicPrimeCore 5 5 1`：

$$
\sum_{k=0}^{4} 6^k \cdot 1^{4-k} = 1 + 6 + 36 + 216 + 1296 = 1555
$$

- `1555 = 5 × 311`
- `311` は素数、`311 ∤ 5` → **witness `q = 311` が存在 ✓**
- boundary target は `u = 1` でも通過する ✓

> body/core datum route が壊れる `u = 1` でも、boundary route は生きる。
> これが boundary target を証明すべき根本的理由。

---

*次回更新予定：中間補題（`cyclotomicPrimeCore_modEq_*` 系）の Lean 実装時*
