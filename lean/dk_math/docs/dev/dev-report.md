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

*次回更新予定: `BodyCoreWitnessExistenceConcreteTarget` の証明進捗があり次第*
