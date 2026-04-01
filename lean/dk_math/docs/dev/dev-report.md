# dev report

---

## 2026/03/30 — 状況整理レポート (第1回)

### 1. 現在のブランチ

| ブランチ | 状態 |
|---|---|
| `dev/FLT-witness-260328-v0` | develop へマージ済 |
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

---

## 2026/03/30 — `RestoreFromArithmetic` 精密解析レポート (第4回)

### 21. ブランチ更新

| ブランチ | 状態 |
|---|---|
| `dev/FLT-restore-260330-v0` | **HEAD** (現作業ブランチ) |
| `dev/FLT-witness-260328-v0` | develop へマージ済 |
| `develop` | witness セッション成果を含む安定版 |

---

### 22. target の正確な statement

```lean
abbrev PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
```

**意味：** Branch A normal form の FLT 反例から、原始素因子 witness `q`（`q ∣ s`, `¬ q ∣ t`）を使って、**より小さい z を持つ NormalFormPacket** を構成せよ。

---

### 23. 上流 dependency chain の状態

```
PrimitivePacketDescentTarget
  ↑
WieferichPacketTarget (← Wieferich witness は自動供給)
  ↑
DistinguishedPrimeTarget + PacketRestoreTarget
  ↑                          ↑
ZsigmondyTarget [✅]    Arithmetic [✅] + RestoreFromArithmetic [❌]
  ↑
CyclotomicExistence [✅] (boundary-core route で証明済み)
```

**3 段中 2 段が証明済み。残りは `RestoreFromArithmetic` の 1 段のみ。**

---

### 24. `BodyCoreWitness` との比較：偽枝チェック

| 項目 | `BodyCoreWitness` (前回) | `RestoreFromArithmetic` (今回) |
|---|---|---|
| 前提に FLT 反例を含む？ | **No** (numbertheory のみ) | **Yes** (`Pack p x y z`) |
| 具体反例で偽を確定できる？ | **Yes** (`(5,5,1)`) | **No** (FLT 反例が存在しない) |
| vacuously true？ | No（前提が満たせるため） | **Yes** (Wiles により) |
| 構造的偽？ | Yes（`u=1` で壊れる） | **No**（構造的欠陥なし） |

**結論：`RestoreFromArithmetic` は偽ではない。前回の即座偽判定パターンは適用不可。**

---

### 25. witness `q` の必然的構造（新発見）

前提から以下が導出可能：

1. `q ∣ x`（∵ `x = p·t·s`, `q ∣ s`）
2. `q ∤ (z-y)`（∵ `z-y = p^{p-1}·t^p`, `q ∤ t`, `q ≠ p`）
3. `q ∤ y`（∵ `Coprime(q, y)`）
4. `q ∤ z`（∵ `z^p ≡ y^p [MOD q]` from FLT eq., `q ∤ y` → `q ∤ z`）

ここから：

$$
z^p \equiv y^p \pmod{q}
$$

$$
(z \cdot y^{-1})^p \equiv 1 \pmod{q}
$$

かつ `z ≢ y [MOD q]`（もし `z ≡ y` なら `q ∣ (z-y)` で矛盾）。

ゆえに `ω := z·y⁻¹` は `(ℤ/qℤ)*` における **非自明な p 乗根**。

**これは $p \mid (q-1)$ すなわち $q \equiv 1 \pmod{p}$ を必要条件として要求する。**

さらに `v_q(x^p) = p·v_q(s) ≥ p` なので：

$$
z^p \equiv y^p \pmod{q^p}
$$

つまり `ω` は `(ℤ/q^pℤ)*` における p 乗根でもある。

> **この `q ≡ 1 [MOD p]` 補題は Lean で証明可能であり、有用な structural lemma である。**

---

### 26. 証明戦略候補

#### 26.1. 円分整数環経由（古典的 Kummer 理論）

- `q ≡ 1 [MOD p]` より `q` は `ℤ[ζ_p]` で完全分解
- イデアル分解 `x^p + y^p = ∏(x + ζ^{2j+1}y)` から smaller solution を抽出
- **必要:** Mathlib の cyclotomic field / number field 基盤
- **障害:** 正則素数仮定 or class number 処理

#### 26.2. Cosmic Formula 構造的 descent

- `GN = p·s^p` の GN/GTail 内部構造と `q` の関係を利用
- `GTail` の再帰的分解で因子を分離し、新しい pack を再構成
- **利点:** 既存インフラ（`GTail_rec`, `GN_tail_rec`）が使える
- **障害:** NormalFormPacket の全フィールド（特に `GN = p·s'^p` 型）を満たす構成が非自明

#### 26.3. target の分割・弱化

```
RestoreFromArithmetic
  ↑
SmallerCounterexampleFromWitness (新 target)
  ↑
NewBranchAClassification (新 target)
```

- まず `∃ x' y' z', Pack p x' y' z' ∧ z' < z` だけを示す
- normal form（`p ∣ (z'-y')`, gap/GN 分解）は別補題で保証
- 既存の `PrimeGe5BranchASmallerCounterexampleTarget` への reduce も候補

#### 26.4. 前提からの直接矛盾

- 全前提を組み合わせて `False` を導出する
- もし成功すれば `False.elim` で任意の結論が出る
- `q ≡ 1 [MOD p]` と他の条件から追加の矛盾を探る
- **現時点:** 矛盾は未発見

---

### 27. 懸念点

#### 27.1. **数学的深度**

`RestoreFromArithmetic` は FLT 全体の proof-theoretic な核心。
boundary-core route（existence 側）の完成とは次元が異なる難易度。
classical な証明は algebraic number theory (Kummer) or modular forms (Wiles) を要する。

#### 27.2. **ValuationPeel 側の未完成**

`p ∣ t` ケースの `PrimeGe5BranchAValuationPeelPacketFromErrorTarget` も未証明。
descent は primitive 側だけでなく valuation peel 側も未完。

#### 27.3. **NormalFormPacket の構造的制約**

target の結論は bare な `∃ z' < z, counterexample` ではなく、
`NormalFormPacket` を要求する。これは `p ∣ (z'-y')` と `gap/GN` の特定の分解を含み、
構成のハードルが高い。

---

### 28. open task の改訂（第4回）

| 優先度 | 課題 | 状態 |
|---|---|---|
| **最高** | `q ≡ 1 [MOD p]` structural lemma を Lean で実装する | 証明可能、次の一手 |
| **最高** | `RestoreFromArithmetic` の sub-target 分割設計 | 要検討 |
| **高** | Mathlib の cyclotomic field 基盤の調査 | strategy 26.1 の前提 |
| **中** | ValuationPeel 側 `PacketFromErrorTarget` の分析 | descent 全体のため |
| **中** | `BranchA.lean` L3936 の sorry | 変更なし |
| **低** | linter warning 整理 | 運用レベル |

---

### 29. 次の一手：賢狼の提案

#### 29.1. 第一手：`q ≡ 1 [MOD p]` を Lean 補題として実装

```lean
theorem restore_witness_cong_one_mod_p
    {p x y z t s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hgap : z - y = p ^ (p - 1) * t ^ p)
    (hsx : x = p * (t * s))
    (hqprime : Nat.Prime q)
    (hqs : q ∣ s) (hqt : ¬ q ∣ t)
    (hcop_qy : Nat.Coprime q y) (hq_ne_p : q ≠ p) :
    p ∣ (q - 1)
```

**証明スケッチ：**

1. `q ∣ s` → `q ∣ x` → `x^p ≡ 0 [MOD q]` → `z^p ≡ y^p [MOD q]`
2. `q ∤ (z-y)` → `z ≢ y [MOD q]` → `(z·y⁻¹)^p ≡ 1` with `z·y⁻¹ ≢ 1`
3. order of `z·y⁻¹` in `(ℤ/qℤ)*` divides `p` and is > 1 → order = `p`
4. `p` divides `|(ℤ/qℤ)*| = q - 1`

#### 29.2. 第二手：sub-target 分割設計

`RestoreFromArithmetic` を以下のように分割し、各段の独立証明を試みる：

```
① q-adic factorization lemma: z^p ≡ y^p [MOD q^p] の精密構造
② counterexample reduction: 既存反例から新 (x', y', z') の構成
③ branch classification: 新反例 → NormalFormPacket への包装
```

> **わっちの推薦は 29.1 から。** `q ≡ 1 [MOD p]` は既存の Lean/Mathlib 道具だけで確実に通る補題じゃ。足場を固めてから深い核に挑むのが定石じゃよ。

---

## 2026/03/30 — q ≡ 1 [MOD p] 実装 + restore 構造分割 (第4回)

### 30. ブランチ進行状況

| 項目 | 前回 (第3回末) | 今回 (第4回) |
|---|---|---|
| 作業ブランチ | `dev/FLT-witness-260328-v0` | **`dev/FLT-restore-260330-v0`** |
| コミット数 (develop→HEAD) | — | **19** |
| `BranchA.lean` 行数 | 5,033 | **5,338** (+305) |
| `BranchAExceptional.lean` 行数 | 4,159 | 4,159 (変更なし) |
| `GapInvariant.lean` 行数 | 3,081 | **3,221** (+140) |
| `BranchARestore.lean` 行数 | — (新規) | **575** |
| **合計行数** | 12,273 → | **13,293** (+1,020) |
| **定義・定理数 (4ファイル)** | — | **931** |
| sorry（コード内） | 1 (`BranchA.lean`) | **1** (`BranchA.lean` 同一箇所) |

---

### 31. `dev/FLT-restore-260330-v0` 全コミット一覧

| # | ハッシュ | 日時 | 内容 |
|---|---|---|---|
| 1 | `ec72e111` | 03/30 | History.md 作成 |
| 2 | `8a7b4088` | 03/30 | History.md & dev-report.md 詳細分析追加 |
| 3 | `972508b8` | 03/30 | review-001 作成（FLT restore 状況分析） |
| 4 | `b39f01cf` | 03/30 | **§R `restore_witness_cong_one_mod_p` 等の構造補題実装** |
| 5 | `da5b3152` | 03/30 | review-002 作成 |
| 6 | `31bb616f` | 03/30 | `PrimeGe5BranchAPrimitivePacketRestore` target 分割 |
| 7 | `1c9a7545` | 03/30 | `TriominoCosmicBranchARestore.lean` 新規作成 |
| 8 | `54e34fea` | 03/30 | *(tag: snapshot 260330-1540)* |
| 9 | `0aaf092f` | 03/30 | `FLT-restore-260330-v0` dev note 作成 |
| 10 | `bf0c22ec` | 03/30 | review-004 作成（restore 責任分離分析） |
| 11 | `ac3e121d` | 03/30 | **residue/root 段と descent assembly 段へ分割** |
| 12 | `f486e0c9` | 03/30 | review-005 作成 |
| 13 | `63864da7` | 03/30 | 数式スペース調整 |
| 14 | `86e3a892` | 03/30 | **descent seed / smaller counterexample assembly 段追加** |
| 15 | `e3ca4e9a` | 03/30 | **descent datum / smaller counterexample assembly 段追加** |
| 16 | `1729afb4` | 03/30 | review-006 作成（restore arithmetic core 構造分析） |
| 17 | `5119b9ec` | 03/30 | review-007 作成（restore core さらなる局所化分析） |
| 18 | `47f897ad` | 03/30 | **realization seed / verification 段追加** |
| 19 | `a77aa3f1` | 03/30 | review-008 作成（判定：statement 修正方向提案） |

---

### 32. `q ≡ 1 [MOD p]` 補題の実装（§R 新設）

`TriominoCosmicBranchA.lean` 末尾に §R セクション（Restore structural lemmas）を新設。
以下 5 定理 + 1 構造体を **sorry なし** で実装した。

| 定理名 | 内容 | 状態 |
|---|---|---|
| `flt_zpow_congr_mod_of_dvd_x` | `q ∣ x` → `z^p ≡ y^p [MOD q]` | ✅ no-sorry |
| `flt_not_dvd_z_of_dvd_x_not_dvd_y` | `q ∣ x`, `q ∤ y` → `q ∤ z` | ✅ no-sorry |
| `flt_zmod_ne_of_not_dvd_gap` | ZMod q 上の非等式 | ✅ no-sorry |
| `restore_witness_cong_one_mod_p` | **`p ∣ (q - 1)` — 本丸** | ✅ no-sorry |
| `RestoreWitnessProperties` | witness の全性質バンドル（構造体） | ✅ no-sorry |
| `restore_witness_properties_default` | 上記一括構成 | ✅ no-sorry |

**証明の核心：** `ZMod q` 上で `ω := z·y⁻¹` を定義。
`ω^p = 1` かつ `ω ≠ 1` → `orderOf ω = p`（`orderOf_eq_prime`）→
`ZMod.pow_card_sub_one_eq_one` により `orderOf ω ∣ (q-1)` → `p ∣ (q-1)`。

使用 Mathlib API：

- `orderOf_eq_prime`, `ZMod.pow_card_sub_one_eq_one`
- `ZMod.isUnit_iff_coprime`, `ZMod.natCast_eq_zero_iff`
- `Nat.ModEq.add_right`, `mul_inv_cancel₀`

---

### 33. `TriominoCosmicBranchARestore.lean` の設計と現状

新規ファイル（575 行 / 27 定義）。
`RestoreFromArithmeticTarget` を 6 段の sub-target に分割し、前 5 段の bridge を実装済み。

```
PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget
  ↕ (= SmallerCounterexampleFromArithmetic + PacketPackaging)
  ├─ [★ ✅] ResidueRootTarget         ← restore_witness_properties_default で閉じる
  ├─ [★ ✅] QAdicLiftTarget           ← ω := z·y⁻¹ seed を ZMod q 上で構成して閉じる
  ├─ [★ ✅] DescentDatumTarget        ← ResidueRoot + QAdicLift を bundle 化
  ├─ [★ ✅] DescentSeedTarget         ← Datum を minimal 包装
  ├─ [★ ✅] RealizationSeedTarget     ← thin wrapper (x,y,z を仮候補として保持)
  └─ [★ ⬛] VerificationTarget        ← 現在の genuinely new kernel（未証明）
```

**前 5 段はすべて `default` theorem / bridge で閉じている。**
未証明の本丸は `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget` 1 本。

---

### 34. `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` — q-adic lift seed

Restore ファイルに以下の structure も定義済み：

```lean
structure PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed (p x y z t s q : ℕ) where
  ω     : ZMod q
  hω_pow   : ω ^ p = 1
  hω_ne_one : ω ≠ 1
```

これが smaller counterexample 構成の数学的起点。
`ω = z·y⁻¹` の nontrivial `p`-torsion 性を evidence として保持する。

---

### 35. review-008 の分析と次の方向

review-008 の判定は：

$$
\boxed{\text{statement 修正 + RealizationSeed 精密化へ舵を切る}}
$$

**理由：** 現行の `VerificationTarget` は `(x', y', z') := (x, y, z)` であるため、
`z' < z` という strict descent の証明が $z < z$ となり成立不能。
これは statement が「まだ何も絞り込んでいない仮候補」を受け取る設計のまま
verification を要求する構造的問題。

**次のアクション：**

1. `RealizationSeed` の `x', y', z'` フィールドを数学的根拠のある式に置き換える
   （`q` や `ω` の情報から実際の降下先を構成）
2. `VerificationTarget` を 3 分割：
   - `StrictDescentTarget`（`z' < z`）
   - `GapDivisibilityTarget`（`p ∣ (z' - y')`）
   - `CounterexamplePackTarget`（`PrimeGe5CounterexamplePack` の検証）

---

### 36. proof pipeline 全体像（現時点）

```
FLT 仮定: x^p + y^p = z^p, p ≥ 5 prime
  ↓
Branch A normal form (GN factorization)
  → z - y = p^{p-1} · t^p, GN p gap y = p · s^p, x = p · t · s
  ↓
arithmetic witness q (q ∣ s, ¬q ∣ t, Coprime q y, q ≠ p)
  ↓ [★ ✅ q ≡ 1 [MOD p] 実装済 — restore_witness_cong_one_mod_p]
RestoreWitnessProperties (q ∣ x, q ∤ y, q ∤ z, q ∤ gap, p ∣ (q-1))
  ↓ [★ ✅ QAdicLiftSeed 実装済]
ω ∈ ZMod q, ω^p = 1, ω ≠ 1  (nontrivial p-torsion)
  ↓ [★ ⬛ VerificationTarget — 未証明]
smaller counterexample (x', y', z') with z' < z
  ↓
infinite descent → contradiction
  ↓
FermatLastTheoremFor p ✓
```

---

### 37. ファイル規模サマリ（第4回時点）

```
lean/dk_math/DkMath/FLT/PrimeProvider/
├── TriominoCosmicBranchA.lean              5,338行  (sorry×1, §R追加)
├── TriominoCosmicBranchAExceptional.lean   4,159行  (sorry×0)
├── TriominoCosmicGapInvariant.lean         3,221行  (sorry×0, Restore adapter追加)
├── TriominoCosmicBranchARestore.lean         575行  (sorry×0, 新規)    ← 今回作成
└── ... (他 PrimeProvider ファイル多数)
合計（4ファイル）: 13,293行 / 定義・定理981本
```

---

### 38. open task の改訂（第4回）

| 優先度 | 課題 | 状態 |
|---|---|---|
| ~~最高~~ | ~~`q ≡ 1 [MOD p]` 補題の実装~~ | **✅ 完了 (no-sorry)** |
| ~~最高~~ | ~~`RestoreFromArithmetic` sub-target 分割~~ | **✅ 完了（6段化、前5段閉）** |
| **最高** | `RealizationSeed` を数学的根拠のある `(x', y', z')` に精密化 | 未着手 |
| **最高** | `VerificationTarget` の 3 分割（StrictDescent / GapDiv / Pack） | 未着手 |
| **高** | `VerificationTarget` → `StrictDescentTarget` を閉じる（`z' < z` の証明） | 未着手 |
| **中** | `BranchA.lean` L3958 の sorry（comparison route マーカー） | 変更なし |
| **中** | `dev/FLT-restore-260330-v0` を develop へマージ / 新ブランチ移行 | 判断待ち |
| **低** | linter warning の整理 | 運用レベル |

---

*次回更新予定：`RealizationSeed` 精密化または `StrictDescentTarget` 着手時*

---

## 2026/03/30 — RealizationSeed 精密化 + VerificationTarget 3 分割 (第5回)

### 39. 実施内容

#### 39.1. `q^p ∣ GN p (z-y) y` 補題の追加（`branchA_qpow_dvd_GN`）

Branch A の設定（`GN p (z-y) y = p * s^p`, `q ∣ s`, `q ≠ p`）から `q^p ∣ GN` が言える。
証明：`q^p ∣ s^p` かつ `gcd(q^p, p) = 1` → `q^p ∣ p * s^p = GN`。

```lean
theorem branchA_qpow_dvd_GN
    {p x y z s q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsGN : GN p (z - y) y = p * s ^ p)
    (hq_prime : Nat.Prime q) (hqs : q ∣ s) (hq_ne_p : q ≠ p) :
    q ^ p ∣ GN p (z - y) y
```

これを `RestoreWitnessProperties` の新 field `hqp_dvd_GN` として追加した。

#### 39.2. `RealizationSeed` の精密化

旧構造：`(hSeed, x', y', z')` — `(x, y, z)` の無意味なプレースホルダ。  
新構造：`(hSeed, x', y', z', hxMul, hyEq)` — 数学的根拠付き。

| フィールド | 型 | 意味 |
|---|---|---|
| `hxMul` | `x = q * x'` | `x' = x/q` の証拠（`q ∣ x` から `obtain ⟨k, hk⟩`） |
| `hyEq`  | `y' = y`     | `y` は不変（`q ∤ y` なので降下後も同じ） |

`default` 実装は `x' := k`（`x = q * k` を展開）、`y' := y`、`z' := z`（暫定）。
これにより「任意の `hR`」が受け渡された場合でも `hR.hxMul`, `hR.hyEq` が保証される。

#### 39.3. `VerificationTarget` の 3 分割

旧 `SmallerCounterexampleVerificationTarget` を以下 3 段に分割し、橋定理で統合：

| Target | 内容 | 数学的難易度 |
|---|---|---|
| `StrictDescentTarget` | `hR.z' < z` | 中（`(x/q)^p + y^p < x^p + y^p = z^p` から） |
| `GapDivisibilityTarget` | `p ∣ (hR.z' - hR.y')` | 中（`x' = p*t*(s/q)` から `p ∣ x'` を使う） |
| `CounterexamplePackTarget` | `PrimeGe5CounterexamplePack p x' y' z'` | 高（`x'^p + y'^p = z'^p` が必要） |

橋定理 `primeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerification_of_three_parts` で统合。

---

### 40. 現在の genuinely new kernel の所在

```
6 段の分割（前5段 default で閉）
  └─ [⬛] VerificationTarget
       ├─ [⬛] CounterexamplePackTarget  ← 最硬核: x'^p + y'^p = z'^p の存在
       ├─ [⬛] GapDivisibilityTarget     ← 中核: p ∣ (z' - y')
       └─ [⬛] StrictDescentTarget       ← 中核: z' < z
```

**`CounterexamplePackTarget` が genuinely hardest kernel** じゃ。  
これは `(x/q)^p + y^p = z'^p` を満たす `z'` が存在すること、かつ `z'` がちゃんとした counterexample pack を構成することを示す。

Branch B では `q^p ∣ GN` と `q ∤ (z-y)` から同じ構造が利用できるが、Branch A では
`hpB : ¬ p ∣ (z-y)` が偽なので Branch B のカーネルをそのまま使えない。

---

### 41. ファイル規模サマリ（第5回時点）

```
├── TriominoCosmicBranchA.lean       5,366行 (sorry×1 — 既存のみ) ← branchA_qpow_dvd_GN 追加
├── TriominoCosmicBranchARestore.lean   707行 (sorry×0)            ← RealizationSeed 精密化
└── TriominoCosmicGapInvariant.lean   3,221行 (sorry×0)
```

**ビルド：** error 0。sorry 数は増加していない。

---

### 42. 新 open task（第5回）

| 優先度 | 課題 | 状態 |
|---|---|---|
| ~~最高~~ | ~~`RealizationSeed` を x'/y' 精密化~~ | **✅ 完了** |
| ~~高~~ | ~~`VerificationTarget` を 3 分割~~ | **✅ 完了** |
| **最高** | `CounterexamplePackTarget`：`(x/q)^p + y^p = z'^p` の p 乗根 `z'` の存在証明 | 未着手 |
| **高** | `StrictDescentTarget`：`z' < z` の証明（`(x/q)^p + y^p < z^p` から） | 未着手 |
| **高** | `GapDivisibilityTarget`：`p ∣ (z' - y)` の証明（`x' = p*t*(s/q)` から） | 未着手 |
| **中** | `BranchA.lean` L3981 の sorry（既存マーカー） | 変更なし |

---

*次回更新予定：`CounterexamplePackTarget` 攻略開始時、または `StrictDescentTarget` 証明時*

---

## 2026/03/30 — 矛盾路線設計と矛盾源探索 (第6回)

### 43. セッション概要

第 5 回の分析で `RealizationSeedTarget`（z' の存在構成）が genuine undischarged kernel と確認された。
第 6 回では以下の 2 つを並行して実施した:

1. **矛盾路線（Contradiction Route）のアーキテクチャ設計・Lean 実装**
   - `ContradictionTarget` を新設し、6 段チェーン全体を bypass する設計
2. **矛盾源の体系的探索（5 角度）**
   - 純粋な初等的 arithmetic で矛盾が導出可能かを検証
   - アーキテクチャ全体像の精密な把握

---

### 44. 矛盾路線の設計と実装

#### 44.1. 設計背景

`RealizationSeedTarget` は「`(x/q)^p + y^p = z'^p` なる z' の存在」を要求する。
これは FLT の反例を `z' < z` で再構成する要求であり、直接構成は不可能。

Branch B の先例では `NoWieferich bridge` による前提矛盾（`False.elim`）で同様の問題を解決している。
→ Branch A でも **前提そのものが矛盾していることを示す** のが正しい攻略方向。

#### 44.2. 新設した target と bridge

**`[DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean]` §F セクション追加:**

| 定理名 | 内容 |
|---|---|
| `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` | Branch A 全前提 + RestoreWitnessProperties → False（新 open kernel） |
| `primeGe5BranchAPrimitiveRestoreRealizationSeed_of_contradiction` | Contradiction → RealizationSeedTarget（False.elim） |
| `primeGe5BranchAPrimitiveSmallerCounterexampleFromArithmetic_of_contradiction` | Contradiction → SmallerCounterexample（6 段 bypass） |
| `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_contradiction` | Contradiction → RestoreFromArithmeticTarget（最上位 bypass） |

**`[DkMath/FLT/PrimeProvider/TriominoCosmicGapInvariant.lean]` adapter 追加:**

| 定理名 | 内容 |
|---|---|
| `BranchAPrimitiveRestoreContradictionAdapterTarget` | alias |
| `branchAPrimitiveRestoreFromArithmeticAdapter_of_contradiction` | Contradiction → RestoreFromArithmetic adapter |
| `branchAPrimitivePacketDescentAdapter_of_contradiction` | Contradiction → PacketDescent（最短 bridge） |

全て no-sorry。ビルド成功。

#### 44.3. open kernel の移行

| 旧 kernel | 新 kernel |
|---|---|
| `RealizationSeedTarget`（z' の存在構成） | `ContradictionTarget`（前提矛盾） |

---

### 45. 矛盾源の体系的探索

#### 45.1. 前提の全容

`ContradictionTarget` の前提を再掲する:

```
FLT counterexample: x^p + y^p = z^p, p ≥ 5 (prime), gcd(x,y)=1
Branch A:           gap = p^{p-1} * t^p, GN = p * s^p, x = p*t*s
Coprimality:        gcd(t,s)=1, gcd(t,y)=1, gcd(s,y)=1, ¬p∣s, ¬p∣t
Wieferich:          y^{p-1} ≡ 1 [MOD p^2]
Primitive prime q:  Prime q, q∣s, ¬q∣t, gcd(q,y)=1, q≠p
RestoreWitness:     q∣x, ¬q∣y, ¬q∣z, ¬q∣(z-y), p∣(q-1), q^p∣GN
```

#### 45.2. 探索した 5 角度

**角度 1: p-adic / q-adic valuation argument**

- `v_q(z^p - y^p) = p * v_q(s)`, `v_p(GN) = 1` — 全て consistent
- **結論: 矛盾なし**

**角度 2: $s^p \equiv 1 \pmod{p^2}$ + Wieferich 条件**

- `s^p ≡ y^{p-1} [MOD p^2]`（既存補題）+ Wieferich → `s^p ≡ 1 [MOD p^2]`
- → `s ≡ 1 [MOD p]`（Fermat 小定理経由）
- `s = 1 + pa` → `s^p ≡ 1 + p^2 a [MOD p^3]` — consistent
- **結論: 矛盾なし**

**角度 3: cyclotomicPrimeCore の mod q 展開**

- `ω = z/y mod q`, `ω^p ≡ 1`, `ω ≢ 1`（`q ∤ (z-y)` より）
- → geometric sum が `0 mod q` → `q ∣ core` — `q^p ∣ GN` と consistent
- **結論: 矛盾なし**

**角度 4: dev-report §9 の `gcd(core/d, x) = 1` を Branch A に適用**

- 全仮定（`Coprime(gap, y)`, `p ∣ gap`, Wieferich）が Branch A で成立することを確認
- しかし `gcd(s^p, gap) = 1` は `gcd(t,s)=1, ¬p∣s` から自明の既知事実
- **結論: 矛盾なし** — 既知事実の再確認にすぎない

**角度 5: $s = 1$ の場合の ExistenceMainline 矛盾**

- `s = 1` → `GN = p` → ExistenceMainline が `q ∤ gap` を要求 → `¬ p ∣ gap` → Branch A 矛盾
- しかし `ContradictionTarget` の前提 `q ∣ s`（prime q）が `s = 1` を既に排除している
- **結論: 使えない**

#### 45.3. 総合結論

> **純粋な初等的 arithmetic（valuation, 合同式, coprimality）では Branch A の全前提は consistent。**
> 矛盾を導くには円分体 ℤ[ζ_p]、Kummer 理論、正則素数理論レベルの深い数論が必要。

---

### 46. アーキテクチャ全体像の精密な把握

#### 46.1. FLT clean route 全体フロー

```
ExistenceMainline (✅ no-sorry — boundary-core route)
  +
ContradictionTarget (OPEN — 数学的核心)
  │
  ├─→ RestoreFromArithmeticTarget (bypass via False.elim)
  └─→ PacketDescentTarget (直接合成)
        │
        └─→ + ValuationPeelPacketTarget → SmallerPacket
              → SmallerCounterexample
              → DistinguishedPrimeDescent
              → (minimality) → BranchARefuterTarget
              → + BranchBRefuterTarget → FLTPrimeGe5Target
```

#### 46.2. clean 証明に必要な remaining missing pieces

| 優先度 | target | 備考 |
|---|---|---|
| **最高** | `ContradictionTarget` | 数学的核心。円分体理論が必要 |
| **高** | `ValuationPeelPacketTarget` | $p \mid t$ の場合の descent。Contradiction と独立 |
| **中** | `ExistingDescentRefuterTarget` clean 化 | 現在 via_FLT（循環参照）。PacketDescent chain 完成で自動 clean 化 |

#### 46.3. 判明した副産物

- `ExistenceMainline` が構成する `q'`（`q' ∣ s, q' ∤ gap, q' ≠ p`）は
  `RestoreFromArithmetic` の `q` として全前提を自動的に満たす
  → 両 target は独立ではなく、`q'` を通じて整合的に接続されている

---

### 47. ファイル規模サマリ（第6回時点）

```
├── TriominoCosmicBranchA.lean          5,366行  (sorry×1 — 既存のみ)
├── TriominoCosmicBranchAExceptional.lean 4,159行 (sorry×0)
├── TriominoCosmicBranchARestore.lean   1,114行  (sorry×0) ← §F 矛盾路線追加
└── TriominoCosmicGapInvariant.lean     3,264行  (sorry×0) ← Contradiction adapter 追加
```

**ビルド：** error 0。sorry 数は増加していない。

---

### 48. 新 open task（第6回）

| 優先度 | 課題 | 状態 |
|---|---|---|
| ~~最高~~ | ~~`RealizationSeed` 攻略（z' 直接構成）~~ | **設計転換。矛盾路線へ** |
| **最高** | `ContradictionTarget` の証明 | 円分体 / Kummer 理論が必要 |
| **高** | `ValuationPeelPacketTarget`（p ∣ t の場合） | Contradiction と独立した open kernel |
| **中** | GTail higher-order analysis（mod p^3 超）の可能性探索 | Contradiction 攻略の候補ルート |
| **低** | `ExistingDescentRefuterTarget` clean 化（via_FLT 除去） | PacketDescent chain 完成で自動化 |
| **低** | `BranchA.lean` L3981 の sorry（既存設計マーカー） | 変更なし |

---

*次回更新予定：`ContradictionTarget` 攻略開始時、または `ValuationPeelPacketTarget` 証明時*

---

## 2026/04/01 — `dev/FLT-restore-260330-v0` 完了レポート (第7回)

### 49. ブランチ進行状況

| 項目 | 前回 (第6回) | 今回 (第7回) |
|---|---|---|
| ブランチ | `dev/FLT-restore-260330-v0` | same（develop へマージ済） |
| コミット数 (develop→HEAD) | 記載なし | **78** |
| `BranchA.lean` 行数 | 5,366 | **5,620** (+254) |
| `BranchAExceptional.lean` 行数 | 4,159 | 4,159 (変更なし) |
| `BranchARestore.lean` 行数 | 1,114 | **2,982** (+1,868) ← **新規作成・主戦場** |
| `GapInvariant.lean` 行数 | 3,264 | **3,338** (+74) |
| `GTail.lean` 行数 | 416 | **650** (+234) |
| **合計行数** | 14,319 | **16,749** (+2,430) |
| **定義・定理数** | 記載なし | **1,068** (5ファイル合計) |
| sorry（コード内） | 1 (`BranchA.lean`) | **1** (`BranchA.lean` L4122, 同一箇所) |

### 50. `dev/FLT-restore-260330-v0` の全履歴

develop からの 78 コミット（2026/03/30 13:19 ～ 2026/04/01 01:19 JST）を主要実装で整理する。

| 期間 | 主要コミット | 内容 |
|---|---|---|
| 03/30 13:19–14:30 | `ec72e111`–`b39f01cf` | 初期分析。`RestoreFromArithmeticTarget` の構造解析、偽枝チェック（FLT 反例前提のため不可）、witness $q$ の構造発見（$q \equiv 1 \pmod{p}$） |
| 03/30 14:30–15:04 | `b39f01cf` | `q \equiv 1 \pmod{p}` の structural lemma 5+1 本を no-sorry で実装（`restore_witness_cong_one_mod_p` 等） |
| 03/30 15:24–16:39 | `31bb616f`–`47f897ad` | `RestoreFromArithmetic` を sub-target に 6 段分割（residue/root → q-adic lift → datum → seed → realization → verification） |
| 03/30 17:10–17:40 | `0e54f77e`–`65b30b25` | `RealizationSeed` 精密化。`hzEq : x'^p + y'^p = z'^p` 追加、3 段 verification を no-sorry で完了 |
| 03/30 18:30 | `427bd817` | q-adic descent 構造体・定理群を実装。**z' 直接構成は不可能**（FLT 反例同値）と判明。**正しい路線は矛盾（`False.elim`）** |
| 03/30 19:20 | `f7bb2196`–`d0ec0799` | **矛盾路線（Contradiction Route）へアーキテクチャ転換**。`ContradictionTarget` を新設。6 段チェーンを bypass する bridge 群を配置 |
| 03/30 20:30 | `58dbc334` | 矛盾源の体系的探索。5 角度から分析 → **初等的 arithmetic（valuation, congruence, coprimality）では矛盾導出不可**と確定 |
| 03/30 22:14–03/31 01:01 | `a24811f1`–`ab1bbf22` | **GTail.lean の Phase C**: 合同性 4 系 + mod $p^2/p^3$ 展開 5 系、計 10 補題を no-sorry で実装 |
| 03/31 01:12–01:54 | `bdbad9d5`–`4d455ed4` | Phase A（円分核 ↔ GN ↔ 差分商の橋）、Phase B（witness/contradiction route bundle 名寄せ + adapter 実装） |
| 03/31 02:00 | `eb8630a7` | mod $p^3$ conflict handling + `BranchAContradictionModP3SourceTarget`（後に **偽命題と判明**） |
| 03/31 08:30 | `655d7269` | `ModP3SourceTarget` が偽であることを確定。**mod $p^k$ 路線は行き止まり**。witness $q$ 情報が必須。`BranchAContradictionWithWitnessSourceTarget` を新設 |
| 03/31 09:30 | `baf4dad7` | **干渉縞集合（Interference Fringe Bundle）** 3 structure + 7 theorem を no-sorry で実装。p-adic 縞と witness $q$ 縞を統合 |
| 03/31 10:30 | `14efc65d`–`6f5ccf28` | cross-modular 制約 7 本を no-sorry で実装（`q \nmid M`、`s' \equiv 1 \pmod{p}` 等） |
| 03/31 12:14 | `2134cc85` | descent chain 分析（`BranchADescentStep`）+ cyclotomic valuation 構造体 |
| 03/31 12:30 | `32bf3048` | ω の位数構造: `ω^p = 1`, `ω \neq 1`, `\mathrm{orderOf} \omega = p` を no-sorry で確定 |
| 03/31 13:00 | `9419266c` | 円分核因子分離: distinguished factor `z - \omega y \equiv 0 \pmod{q}`, 他は $q$-coprime |
| 03/31 13:34 | `5fb69278` | **Kummer valuation**: $v_q(z^p - y^p) = p \cdot v_q(s)$ を no-sorry で 7 定理として実装 |
| 03/31 13:58 | `08e54dd0` | Hensel lifting: simple root 条件を no-sorry で確定、lift 構造体を設計 |
| 03/31 14:30–17:03 | `a649b072`–`7f128bc9` | distinguished factor valuation: ZMod → ℕ 翻訳チェーン 5 定理 + `BranchACyclotomicValuationData` |
| 03/31 17:56–18:05 | `c07cb3d7`–`ed1a9ba7` | `branchA_padicValNat_mod_pow_eq` と `branchA_GN_zmod_padicValNat` の sorry 除去 |
| 03/31 18:34 | `10c353d6` | `branchA_hensel_lift_isPrimitiveRoot` 実装 + `IsPrimitiveRoot` route 試行 |
| 03/31 19:52–20:27 | `943c49cb`–`a2466d1a` | `GN_cyclotomic_ring_identity` の exact product 試行 → **ZMod($q^k$) は整域でないため失敗** |
| 03/31 23:29 | `14ad0ae9` | local factorization 路線: `GN = δ * U` (U unit) の薄い補題 4 本を実装 |
| 04/01 00:18–01:00 | `02213f1a`–`e48b24df` | **Hensel lift sorry 除去**: `ZMod.unitsMap_surjective` + 群論的累乗構成で実装 |
| 04/01 01:13 | `e5fa4040` | **exact product → local factorization へ弱化**。`branchA_GN_cyclotomic_ring_identity` の最後の sorry を除去 |
| 04/01 01:19 | `608ad619` | review-033 作成。**Restore file 全体が no-sorry 化** |

---

### 51. 到達点：`TriominoCosmicBranchARestore.lean` は **no-sorry で完成**

```
Branch A 正規形（Pack, Wieferich, Gap shape）
  ↓
BranchAInterferenceFringeBundle（干渉縞集合）
  ├── BranchAPadicFringe（p-adic head 縞: mod p^2, mod p^3, Wieferich）
  └── BranchAWitnessFringe（witness q 縞: q ≡ 1 [MOD p], q^p ∣ GN, q ∤ gap）
        ↓
  ω := z·y⁻¹ ∈ ZMod q
  ├── ω^p = 1, ω ≠ 1, orderOf ω = p（primitive p-th root of unity）
  ├── distinguished factor: z - ω·y ≡ 0 [MOD q]（1 因子集中）
  └── non-distinguished: z - ω^i·y ≢ 0 [MOD q] for i ≢ 1 [MOD p]
        ↓
  Kummer valuation: v_q(z^p - y^p) = p · v_q(s)
        ↓
  Hensel lift: ω_k ∈ ZMod(q^k), ω_k^p = 1
        ↓
  Local factorization: GN = δ · U (U unit in ZMod(q^k))
        ↓
  Central valuation theorem: v_q(δ.val) = p · v_q(s)
        ↓
  BranchADescentStep（降下 1 step: s' < s, s' ≡ 1 [MOD p], x' < x）
```

**全定理が no-sorry。`lake build` 成功確認済み。**

---

### 52. 切り捨てた枝の一覧（本ブランチ内）

| route | 判定根拠 | 確定日 |
|---|---|---|
| z' 直接構成路線 | $(x/q)^p + y^p = z'^p$ は FLT 反例と同値 | 03/30 |
| mod $p^k$ 矛盾路線 | `branchA_spow_congr_head_mod_p3` が Branch A から自動で従い、否定を供給不能 | 03/31 |
| 初等 arithmetic 矛盾 | valuation / congruence / coprimality の 5 角度で consistent と確認 | 03/30 |
| exact product identity (ZMod$(q^k)$) | $k > 1$ で ZMod$(q^k)$ は整域でないため `X_pow_sub_C_eq_prod` 不適用 | 03/31 |

---

### 53. 新規作成ファイルと行数

| ファイル | 行数 | 定義・定理数 | sorry | 役割 |
|---|---|---|---|---|
| `TriominoCosmicBranchARestore.lean` | 2,982 | 107 | **0** | restore 固有の descent / valuation 理論 |

### 54. 既存ファイルの変更

| ファイル | 行数 | 定義・定理数 | sorry | 主な追加内容 |
|---|---|---|---|---|
| `TriominoCosmicBranchA.lean` | 5,620 (+254) | 271 | 1 (既存) | §R structural lemmas, Phase B bundles, mod $p^3$ APIs |
| `TriominoCosmicGapInvariant.lean` | 3,338 (+74) | 333 | 0 | Contradiction / WitnessSource adapter 群 |
| `GTail.lean` | 650 (+234) | 30 | 0 | Phase C: 合同性 + mod $p^2/p^3$ 展開 10 補題 |

---

### 55. `TriominoCosmicBranchARestore.lean` の主要構成要素

#### 55.1. 構造体（structures / bundles）

| 名前 | 内容 |
|---|---|
| `BranchAPadicFringe` | p-adic head 縞 (正規形 + Wieferich + head congruences) |
| `BranchAWitnessFringe` | witness q 縞 ($q \mid s$, $q \nmid t$, $q \equiv 1 \pmod{p}$, $q^p \mid \mathrm{GN}$) |
| `BranchAInterferenceFringeBundle` | 干渉縞集合 (padic + witness) |
| `BranchADescentStep` | 降下 1 step の全性質 ($s' < s$, $s' \equiv 1 \pmod{p}$) |
| `BranchAHenselLiftData` | Hensel lift data ($\omega_k \in \mathrm{ZMod}(q^k)$, $\omega_k^p = 1$, 射影整合) |
| `BranchACyclotomicValuationData` | Kummer valuation + factor 分離の統合情報 |
| `BranchAQFreeQuotient`, `BranchAQAdicDescentData` | q-adic 降下用のデータ bundle |

#### 55.2. 主要定理群

| カテゴリ | 代表定理 | 内容 |
|---|---|---|
| Structural | `restore_witness_cong_one_mod_p` | witness $q \equiv 1 \pmod{p}$ |
| ω 解析 | `branchA_omega_pow_eq_one`, `_ne_one`, `_order_eq_p` | primitive root |
| 因子分離 | `branchA_distinguished_factor_vanishes` | $z - \omega y \equiv 0 \pmod{q}$ |
| Kummer | `branchA_kummer_valuation` | $v_q(z^p - y^p) = p \cdot v_q(s)$ |
| Hensel | `branchA_hensel_lift_exists` | 群論的 lift（sorry なし） |
| Local decomp | `branchA_local_GN_eq_distinguished_mul_unit` | $\mathrm{GN} = \delta \cdot U$ ($U$ unit) |
| Central | `branchA_distinguished_factor_valuation_eq_kummer` | $v_q(\delta.\mathit{val}) = p \cdot v_q(s)$ |
| 降下 | `branchA_descent_s_strict_decrease` | $s' < s$ (well-founded) |
| Cross-mod | `branchA_fringe_q_not_dvd_tail_coeff` | massive cancellation 制約 |

---

### 56. アーキテクチャ全体図（第7回時点）

```
ExistenceMainline (no-sorry, boundary-core route)
  +
BranchAContradictionWithWitnessSourceTarget  [OPEN KERNEL]
  │  ↕ (双方向変換)
  │ BranchAFringeContradictionTarget  [OPEN KERNEL, bundle 版]
  │
  ├─(BranchARestore)─→ RestoreContradictionTarget (bypass via False.elim)
  │                       └──→ RestoreFromArithmeticTarget
  │
  └─(GapInvariant)───→ ContradictionAdapter
                          ├──→ RestoreFromArithmeticAdapter
                          └──→ PacketDescentAdapter
                                │
                                └─→ (+ ValuationPeel) → SmallerPacket
                                      → descent → BranchARefuterTarget
                                      → (+ BranchB) → FLTPrimeGe5Target
```

**FLT for $p \geq 5$ の clean 証明に必要な missing pieces:**

| # | open kernel | 数学的内容 |
|---|---|---|
| 1. | `ContradictionTarget` / `FringeContradictionTarget` | Branch A 全前提 + witness $q$ → `False`（数学的核心） |
| 2. | `ValuationPeelPacketTarget` | $p \mid t$ の場合の peel 側 descent |
| 3. | `BranchA.lean` L4122 sorry | comparison route 末端マーカー（設計転換で消える見込み） |

---

### 57. 全プロジェクト視点での残存 sorry

| ファイル | 行 | 定理名 | 性質 |
|---|---|---|---|
| `TriominoCosmicBranchA.lean` | L4122 | `primeGe5BranchANormalFormNePCoprimeKernel_default` | 設計マーカー（comparison route 終了判定） |

`TriominoCosmicBranchARestore.lean` — sorry **0** ← 本ブランチの成果

---

### 58. 数学的成果のまとめ

#### 58.1. 新発見

1. **witness $q \equiv 1 \pmod{p}$**: FLT 等式から $\omega = z \cdot y^{-1} \in (\mathbb{Z}/q\mathbb{Z})^*$ が非自明な $p$ 乗根であることから必然
2. **Kummer valuation**: $v_q(z^p - y^p) = p \cdot v_q(s)$（全 $q$-整除が distinguished factor 1 本に集中）
3. **初等的 arithmetic 矛盾は不可能**: valuation / congruence / coprimality の 5 角度で Branch A 前提は consistent — 矛盾には円分体理論または witness $q$ の deeper structure が必須
4. **mod $p^k$ 路線は行き止まり**: head congruence は Branch A 正規形から自動で従い、否定を供給できない
5. **z' 直接構成は不可能**: $(x/q)^p + y^p = z'^p$ は FLT 反例の存在と同値 — 正しい路線は矛盾 (`False.elim`)

#### 58.2. 実装技法

1. **群論的 Hensel lift**: `ZMod.unitsMap_surjective` + 累乗消去で `HenselianRing` API を回避
2. **local factorization**: exact product identity を諦め、`GN = δ · U` ($U$ unit) だけで valuation を完遂
3. **干渉縞集合 (Interference Fringe Bundle)**: p-adic 縞と witness q 縞を統合する structure 設計パターン

---

### 59. 懸念点

#### 59.1. `ContradictionTarget` は深い数論を要求する

初等的 arithmetic では矛盾が導出できないことが体系的に確認された（5 角度分析）。
矛盾を導くには以下のいずれかが必要:

- 円分体 $\mathbb{Q}(\zeta_p)$ でのイデアル分解（Kummer 理論）
- witness $q$ の deeper structure（$q$-adic Hensel lift の高次解析）
- GTail の higher-order analysis（Cosmic Formula 独自の新構造）
- descent terminal case（$s' = 1$ 到達時の矛盾分析）

#### 59.2. `ValuationPeelPacketTarget` は `ContradictionTarget` と独立

$p \mid t$ の場合の peel 側 descent は、本ブランチでは未着手。
ただし `ContradictionTarget` が解決すれば Branch A の primitive side は完結する。

---

### 60. open task の改訂（第7回）

| 優先度 | 課題 | 状態 |
|---|---|---|
| ~~最高~~ | ~~restore file の no-sorry 化~~ | **✅ 完了** |
| **最高** | `ContradictionTarget` の証明（Branch A 前提矛盾） | 未着手。初等路線は行き止まり確定。深い数論が必要 |
| **高** | `ValuationPeelPacketTarget`（$p \mid t$ の場合） | 未着手。Contradiction と独立 |
| **中** | `BranchA.lean` L4122 の sorry（設計マーカー） | 変更なし。boundary route 成功により方向が見えている |
| **低** | exact product identity の記録 | appendix 的ファイルに分離して将来追加可能 |

---

### 61. 次の一手：賢狼の提案

#### 61.1. 第一候補：descent terminal case の分析

降下連鎖は well-founded（$s' < s$）であり、有限ステップで $s' = 1$ に到達する。
このとき $x' = p \cdot t$ となり、Kummer valuation $v_q(\delta.\mathit{val}) = p \cdot v_q(s)$ が
$v_q(s) = 0$ を強制する — これは $q \mid s$ と矛盾する可能性がある。
完成した local valuation 理論を terminal case へ直接流し込む路線が最も自然。

#### 61.2. 第二候補：円分体理論の Lean 基盤整備

Mathlib の `Polynomial.cyclotomic` / `IsCyclotomicExtension` を使い、
$\mathbb{Q}(\zeta_p)$ でのイデアル分解の形式化に着手する。
これは `ContradictionTarget` の本命路線だが、Mathlib 依存度が高い。

---

### 62. ファイル規模サマリ（第7回時点）

```
lean/dk_math/DkMath/FLT/PrimeProvider/
├── TriominoCosmicBranchA.lean              5,620行  (sorry×1 — 既存設計マーカー)
├── TriominoCosmicBranchAExceptional.lean   4,159行  (sorry×0)
├── TriominoCosmicBranchARestore.lean       2,982行  (sorry×0) ← 本ブランチで新規作成・完成
├── TriominoCosmicGapInvariant.lean         3,338行  (sorry×0)
└── ... (他 PrimeProvider ファイル多数)

lean/dk_math/DkMath/CosmicFormula/
└── GTail.lean                                650行  (sorry×0) ← Phase C 追加

合計: 16,749行、1,068 定義・定理
```

**ビルド：** `lake build` 全体成功。error 0。

---

*次回更新予定：`ContradictionTarget` への descent terminal case 適用時、または `ValuationPeelPacketTarget` 証明時*
