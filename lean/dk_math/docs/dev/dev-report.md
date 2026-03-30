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

## 2026/03/30 — boundary-core route 完遂レポート (第3回)

### 13. ブランチ進行状況

| 項目 | 前回 (第2回) | 今回 (第3回) |
|---|---|---|
| コミット数 (develop→HEAD) | 5 | **21** |
| `BranchAExceptional.lean` 行数 | 3,707 | **4,159** (+452) |
| `GapInvariant.lean` 行数 | 2,992 | **3,081** (+89) |
| `BranchA.lean` 行数 | 5,033 | 5,033 (変更なし) |
| **合計行数** | 11,732 | **12,273** (+541) |
| **定義・定理数** | 1,263 | **1,316** (+53) |
| sorry（コード内） | 1 (`BranchA.lean`) | 1 (`BranchA.lean`, 同一箇所) |

### 14. `dev/FLT-witness-260328-v0` の全履歴

develop からの 21 コミットを時系列で整理する。

| # | コミット | 日時 | 内容 |
|---|---|---|---|
| 1 | `faf9bde3` | 03/28 | review-001 作成（same-`q` route 偽の確認） |
| 2 | `5f757eb7` | 03/28 | History.md 作成 |
| 3 | `f4e10e1a` | 03/28 | same-`q` route の反例 `(5,5,7)` 追加 |
| 4 | `3725247f` | 03/28 | review-002 作成（same-`q` 打ち切り） |
| 5 | `96fffc36` | 03/30 02:24 | two-witness route target/interface 追加 |
| 6 | `b6c6faf1` | 03/30 | dev-report.md 初版作成 |
| 7 | `05b404e5` | 03/30 | BodyCoreWitnessExistence 分析改訂 |
| 8 | `5f67f498` | 03/30 02:42 | body-only/two-witness 反例確定 `(5,5,1)` |
| 9 | `9f4d5757` | 03/30 | consider-003 作成 |
| 10 | `5014993a` | 03/30 03:03 | proof-004 作成（証明戦略文書） |
| 11 | `845a6d9c` | 03/30 03:03 | boundary canonical route へ切替 + sanity check |
| 12 | `84798e0e` | 03/30 03:26 | **Step 1 実装** — `core ≡ d·u^{d-1} [MOD q]`, `q∣x ∧ q∣core → q=d` |
| 13 | `93c6692b` | 03/30 | review-005 作成 |
| 14 | `248483ba` | 03/30 03:46 | **Step 4-5 実装** — `div_data → concrete witness`, bridge 完了 |
| 15 | `1a1605d8` | 03/30 | review-006 作成 |
| 16 | `f4d98570` | 03/30 | **Step 2-3 実装** — `core ≡ d [MOD d²]` の actual theorem |
| 17 | `3e0fc72a` | 03/30 | math-007 作成 |
| 18 | `b7990bfd` | 03/30 | review-007 作成 |
| 19 | `e8f619c8` | 03/30 12:32 | canonical alias → mainline default bridge |
| 20 | `b7990bfd` | 03/30 | review-008 作成 |
| 21 | `203dbc9e` | 03/30 12:46 | canonical alias → downstream direct bridge |

### 15. 到達点：boundary-core route は **no-sorry で mainline まで閉じた**

```
exceptional assumptions (d ∣ x, Wieferich, Coprime)
  ↓
exceptional_boundary_datum_prepared_arithmetic_core_divData_default   [★ 数学核]
  │  二項和の head/tail 分解:
  │    core = d·u^{d-1} + B,  d² ∣ B,  Wieferich → core ≡ d [MOD d²]
  │  → d ∣ core, ¬ d ∣ core/d, 1 < core/d
  ↓
exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_divData
  │  Nat.exists_prime_and_dvd で core/d の素因数 q を取得
  │  Step 1 (q≠d なら q∤core) + Step 2 (d∤core/d) → ¬ q ∣ x
  ↓
PrimeGe5BranchAExceptionalBoundaryCoreWitnessConcreteTarget  [canonical alias]
  ↓ (= ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget)
  ↓ primeGe5BranchAExceptionalExistenceMainline_of_boundaryCoreWitnessConcreteDefault
PrimeGe5BranchAExceptionalExistenceMainlineTarget  [✓ no-sorry]
```

**`lake build` は全ファイルで成功確認済み。sorry はこの route に含まれない。**

---

### 16. 切り捨てた枝の一覧

| route | 反例 | 確定日 | 定理名 |
|---|---|---|---|
| same-`q` (q_arith = q_body) | `(5,5,7)` | 03/28 | `not_..PracticalBodyCoreWitnessConcreteTarget` |
| body-only witness | `(5,5,1)` | 03/30 02:42 | `not_..BodyCoreWitnessExistenceConcreteTarget` |
| two-witness (body + arith) | `(5,5,1)` | 03/30 02:42 | `not_..PracticalTwoWitnessConcreteTarget` |
| selected core on datum | `(5,5,7,2)` | develop | `not_..SelectedCoreOnDatumConcreteTarget` |

全て `TriominoCosmicBranchAExceptional.lean` 内に actual theorem として保持。

---

### 17. 全プロジェクト視点での残存 sorry

| ファイル | 行 | 定理名 | 性質 |
|---|---|---|---|
| `TriominoCosmicBranchA.lean` | L3936 | `primeGe5BranchANormalFormNePCoprimeKernel_default` | 設計マーカー（comparison route 終了判定） |

これは Branch A の `q ≠ p` comparison route の末端であり、今回の boundary-core route とは直交する。
コメントにも「comparison route を正式終了するなら adapter に置き換える」と書かれており、
boundary-core route の成功により、設計転換で消える見込みのある sorry じゃ。

---

### 18. 懸念点

#### 18.1. **`PrimitivePacketRestoreFromArithmeticTarget` が未証明**

boundary-core route は mainline (existence) まで no-sorry で通ったが、
**primitive packet descent** へ流すには `hRestore` 仮定が必要。
この target は 21 回にわたり仮定として参照されているが、concrete 証明は存在しない。

```lean
-- BranchA.lean L876
abbrev PrimitivePacketRestoreFromArithmeticTarget : Prop :=
  ∀ {p x y z t s}, Pack p x y z →
    p ∣ (z-y) → z-y = p^(p-1)*t^p → GN p (z-y) y = p*s^p →
    x = p*(t*s) → Coprime t s → ... →
    ∀ {q}, Prime q → q ∣ s → ¬ q ∣ t → ... →
    ∃ pkt', pkt'.z < z
```

これは「原始素因子 witness `q` から、より小さい反例 pack を再構成する」部分であり、
arithmetic witness の存在（今回証明済み）とは独立した数学核。

**影響：** existence mainline は閉じたが、FLT 全体の最終矛盾を出すには
restore / descent の鎖がもう 1 本必要。

#### 18.2. `BranchA.lean` L3936 の sorry は「設計マーカー」だが残存

公式コメントにより「穴というより route 終了判定用」と位置づけられているが、
形式的には sorry が 1 箇所残っている。

#### 18.3. native_decide / linter warnings

`TriominoCosmicBranchAExceptional.lean` 内の sanity check 定理に
`native_decide` 由来の linter warning が残る可能性がある（build failure ではない）。

---

### 19. open task の改訂（第3回）

| 優先度 | 課題 | 状態 |
|---|---|---|
| ~~最高~~ | ~~`BodyCoreWitnessExistenceConcreteTarget`~~ | 偽と判明。打ち切り |
| ~~最高~~ | ~~`ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget`~~ | **✅ 証明完了 (no-sorry)** |
| **最高** | `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` の concrete 証明 | 未着手 |
| **高** | `dev/FLT-witness-260328-v0` を develop へマージする | review 完了待ち |
| **中** | `BranchA.lean` L3936 の sorry を設計転換で消す | boundary route 成功により方向が見えた |
| **低** | linter warning の整理 | 運用レベル |

---

### 20. 次の一手：賢狼の提案

#### 20.1. 第一候補：develop へマージ → 新 branch で restore を攻める

boundary-core route は数学核から downstream mainline まで no-sorry で通った。
これは十分にマージ可能な成果じゃ。

```
git checkout develop
git merge --no-ff dev/FLT-witness-260328-v0
```

マージ後、新ブランチ `dev/FLT-restore-260330-v0` を切って
`PrimitivePacketRestoreFromArithmeticTarget` を攻める。

**理由：**

- 21 コミットが develop に未反映のまま積み上がっている
- boundary-core route の成果は他の探索にも再利用可能
- restore は独立した数学核であり、独自の branch で追うべき

#### 20.2. 第二候補：restore の前段として BranchA sorry を消す

`BranchA.lean` L3936 の sorry は comparison route の末端にある。
boundary-core route で existence mainline を直接閉じた今、
この sorry を `...of_divDataDefault` 系の adapter で置き換えれば、
BranchA 全体が sorry-free になる可能性がある。

#### 20.3. 第三候補：FLT 全体の dependency graph を再描画

```
FermatLastTheoremFor p (p ≥ 5)
  ↑
PrimitivePacketDescentTarget
  ↑                              ↑
ExistenceMainline [✅ 証明済]   RestoreFromArithmetic [❌ 未証明]
```

restore 側の数学的内容を precision audit し、
実際に何が必要かを `proof-005` として文書化する。

> **わっちの推薦は 20.1 じゃ。** まずマージして成果を安定化させ、それから新しい数学核を掘るのが正道じゃよ。

---

*次回更新予定：develop マージ完了後、または restore 探索開始時*
