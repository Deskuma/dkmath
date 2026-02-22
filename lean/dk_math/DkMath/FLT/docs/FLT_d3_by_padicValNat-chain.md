# FLT\_d3\_by\_padicValNat：補題チェーン検証チェックリスト（\_\_dkmath-all.lean.txt.gz 内限定）

> 対象データベース：`__dkmath-all.lean.txt.gz`

---

## 0. 健全性（ファイル整合）

- **期待 SHA256**
  - `cef351d0e52cc87a2462b061fe7f2d31de08a72f6286ea12b129de1fc9897516`

- **チェック項目**
  - [x] `sha256sum __dkmath-all.lean.txt.gz` が期待値と一致（DB 健全）
  - [x] `zcat` / `zgrep` が動作（展開・検索OK）

---

## 1. ターゲット定理の所在と“表層”依存

### 1.1 所在

- 収録ファイル：`./DkMath/FLT/Main.lean`
- 定理開始行（DB内行番号）：**8751** 付近

### 1.2 ターゲット定理（そのまま）

```lean
theorem FLT_d3_by_padicValNat {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hS0_not_sq :
      ∀ {q : ℕ}, Nat.Prime q → q ∣ c ^ 3 - b ^ 3 → ¬ q ∣ c - b → ¬ q ^ 2 ∣ S0_nat c b) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
```

### 1.3 定理が**直接**呼ぶ補題（最短チェーン：DkMath 側のみ表示）

> 方針：Mathlib 側は列挙しない（対処不能＆情報過多）。ここでは **DkMath で書いた補題**だけを追う。

- ☑️`coprime_cb_of_eq`（DB 8407）
- ☑️`exists_prime_factor_cube_diff`（DB 8444）
- ☑️`cube_sub_eq_of_add_eq`（DB 8397）
- ☑️`padicValNat_lower_bound_of_dvd_d3`（DB 8631）
- ☑️`padicValNat_upper_bound_d3`（DB 8680）

### 1.4 補題別（DB版：個別監査セクション）

> 方針：この文書では **DkMath 自前の定理・補題**だけを追跡する（Mathlib 側の列挙はしない）。
>
> - ☑️ = no-sorry 確認済み（`#print axioms` で `sorryAx` なし、または明示的に確認済み）
> - [ ] = 監査待ち（`#print axioms` で確認する）

#### 1.4.1 `coprime_cb_of_eq`（DB 8407）

- 役割：`Nat.Coprime a b` と `a^3+b^3=c^3` から `Nat.Coprime c b` を導く

- 依存（DkMath）

  - ☑️`cube_sub_eq_of_add_eq`（DB 8397）

- 検査

  -

#### 1.4.2 `exists_prime_factor_cube_diff`（DB 8444）

- 役割：`b < c`, `0 < b`, `Nat.Coprime c b` から `∃ q, Nat.Prime q ∧ q ∣ c^3 - b^3 ∧ ¬ q ∣ (c - b)`

- 分岐：`by_cases h3 : 3 ∣ c - b`

- 依存（DkMath）

  - ☑️`S0_nat`（定義）
  - ☑️`exists_primitive_prime_factor_prime`（Zsigmondy/Cyclotomic 側への橋）
    - ☑️`exists_primitive_prime_factor_basic`
      - ☑️`exists_prime_divisor_not_dividing_diff_of_prime_exp`（DB 9818）

- 検査

  -

#### 1.4.3 `cube_sub_eq_of_add_eq`（DB 8397）

- 役割：`a^3+b^3=c^3` から `c^3-b^3=a^3` を導く

- 検査

  - ☑️ `omega` で閉じている（`sorryAx` なし）

#### 1.4.4 `padicValNat_lower_bound_of_dvd_d3`（DB 8631）

- 役割：`q ∣ c` なら `3 ≤ padicValNat q (c^3)`

- 依存（DkMath）

  - ☑️`DkMath.ABC.PadicValNat`（`padicValNat` 基盤）

- 検査

  -

#### 1.4.5 `padicValNat_upper_bound_d3`（DB 8680）

- 役割：`¬ q^2 ∣ S0_nat c b` を入力として `padicValNat q (c^3-b^3) ≤ 1`

- 依存（DkMath）

  - ☑️`padicValNat_le_one_of_not_sq_dvd`（DB 9178, PetalDetect）
  - ☑️`S0_nat`（定義）

- 検査

  -

---

#### 1.5 補題（Zsigmondy 軽量版の末端）

##### 1.5.1 `exists_prime_divisor_not_dividing_diff_of_prime_exp`（DB 9818）

- 役割：素数冪指数 `p`（prime, p ≥ 3）について、 `a^p - b^p` を割り、かつ `(a-b)` を割らない素因子 `q` を 1つ抽出する。

- 入力（要約）

  - `hp : Nat.Prime p`, `3 ≤ p`, `b < a`, `0 < b`, `Nat.Coprime a b`, 追加仮定 `hpnd : ¬ p ∣ a - b`

- 出力（要約）

  - `∃ q, Nat.Prime q ∧ q ∣ a^p - b^p ∧ ¬ q ∣ a - b`

- 証明スケルトン（要約）

  1. `G := quotientPrimePow a b p` を置き `1 < G` を示す（`quotientPrimePow_gt_one`）
  2. `q ∣ G` なる素数 `q` を取り、`q ∣ a^p - b^p` を得る
  3. もし `q ∣ (a-b)` なら gcd 経由で `q ∣ p` を得て `q = p`
  4. `hpnd : ¬ p ∣ (a-b)` と矛盾

- 依存（DkMath）

  - ☑️`quotientPrimePow_gt_one`
  - ☑️`pow_sub_pow_eq_diff_mul_quotient`
  - ☑️`DkMath.Algebra.DiffPow.pow_sub_pow_factor`
  - ☑️`DkMath.NumberTheory.GcdDiffPow.prime_dividing_gcd_divides_d`

- 検査

  - ☑️ `#print axioms DkMath.NumberTheory.GcdDiffPow.exists_prime_divisor_not_dividing_diff_of_prime_exp` は `[propext, Classical.choice, Quot.sound]` のみ（`sorryAx` なし）

## 2. “証明の流れ”を固定（監査用の骨格）

この定理は **下界（≥3）** と **上界（≤1）** の衝突で矛盾を出す。

1. 反例仮定：`h_eq : a^3 + b^3 = c^3`
2. `hcop_cb : Nat.Coprime c b` を得る（`coprime_cb_of_eq`）
3. `hbc : b < c` を示す（`by_contra` + `pow_le_pow_left` + `omega`）
4. `⟨q, prime, q ∣ c^3-b^3, ¬q ∣ c-b⟩` を得る（`exists_prime_factor_cube_diff`）
5. `c^3 - b^3 = a^3` を得る（`cube_sub_eq_of_add_eq`）
6. よって `q ∣ a^3`、`Nat.Prime.dvd_of_dvd_pow` で `q ∣ a`
7. **下界**：`3 ≤ padicValNat q (a^3)`（`padicValNat_lower_bound_of_dvd_d3`）
8. **上界**：`padicValNat q (c^3 - b^3) ≤ 1`（`padicValNat_upper_bound_d3`）
   - 上界の“入力”に、仮定 `hS0_not_sq` をそのまま供給
9. `3 ≤ 1` を得て `omega` で矛盾

---

## 3. 自前（DkMath）定理・補題ツリー（距離と隔離のため）

### 3.1 モジュール距離（Mathlib.FLT からの距離）

- `./DkMath/FLT/Main.lean` は次を import（DkMath 側のみ記載）：
  - `DkMath.FLT.PetalDetect`
  - `DkMath.FLT.GEisensteinBridge`
  - `DkMath.NumberTheory.GcdNext`
  - `DkMath.NumberTheory.ZsigmondyCyclotomic`
  - `DkMath.ABC.PadicValNat`
  - `DkMath.Algebra.DiffPow`

- ファイルコメントに「no-import `DkMath.FLT.Basic`（依存しないように外す）」が明記されている。

- 追加監査（距離の定量化）：
  - ☑️ DB 全体に `Mathlib.FLT` の import/参照が見当たらない（zgrep で 0 hit）

### 3.2 最短チェーン（DkMath 補題のみ）の木

`FLT_d3_by_padicValNat` は **仮定 `hS0_not_sq` を前提**にした「仮定構築テスト定理」。

```
FLT_d3_by_padicValNat  (test; assumes hS0_not_sq)
├─ coprime_cb_of_eq
│  └─ cube_sub_eq_of_add_eq   ☑️
├─ exists_prime_factor_cube_diff
│  ├─ (3 ∣ c-b) branch (elementary)
│  └─ (¬ 3 ∣ c-b) branch
│     └─ exists_primitive_prime_factor_prime
│        └─ exists_primitive_prime_factor_basic
│           └─ exists_prime_divisor_not_dividing_diff_of_prime_exp   ☑️
│              ├─ quotientPrimePow_gt_one
│              ├─ pow_sub_pow_eq_diff_mul_quotient
│              ├─ DiffPow.pow_sub_pow_factor
│              └─ prime_dividing_gcd_divides_d
├─ padicValNat_lower_bound_of_dvd_d3
└─ padicValNat_upper_bound_d3
   ├─ S0_nat (definition)
   └─ padicValNat_le_one_of_not_sq_dvd
```

### 3.3 sorry の隔離（最適化構成の指針）

- この定理系は「層A（存在）＋層B（valuation 上界）＋矛盾導出」だが、
  **このファイルで未解決なのは `hS0_not_sq` の構築だけ**。

- したがって構成最適化は次の 2 分離が効く：

1) **Test（仮定つき）を no-sorry のまま固定**
   - `FLT_d3_by_padicValNat` は “仮定が与えられたら落ちる” を保証する土台。

2) **仮定構築（`hS0_not_sq`）は別ファイルへ隔離**
   - `GEisensteinBridge.lean` に「旧主張の反例」があるため、無条件定理にはできない。
   - ここは「追加条件つき」「例外集合つき」「局所条件つき」で別途構築し、
     うまく行くところだけを Test 側へ接続する。

- Zsigmondy/Cyclotomic 側も同様に、
  「層A（存在）」と「層B（付値 1 等の精密評価）」を分離し、
  層B の sorry は層A の no-sorry を汚染しないようにする。

## 4. “機械的”チェック手順（Lean 側での監査コマンド案）

> 方針：`#print axioms` の結果に `sorryAx` が出ないことをもって「no-sorry の目安」とする。

### 4.1 `sorry` 混入チェック（DkMath 補題のみ）

- [x] `#print axioms FLT_d3_by_padicValNat`（`sorryAx` なし）
- [ ] `#print axioms coprime_cb_of_eq`
- [ ] `#print axioms exists_prime_factor_cube_diff`
- [x] `#print axioms cube_sub_eq_of_add_eq`（☑️omega で閉じる／`sorryAx` なし扱い）
- [ ] `#print axioms padicValNat_lower_bound_of_dvd_d3`
- [ ] `#print axioms padicValNat_upper_bound_d3`
- [ ] `#print axioms padicValNat_le_one_of_not_sq_dvd`
- [x] `#print axioms DkMath.NumberTheory.GcdDiffPow.exists_prime_divisor_not_dividing_diff_of_prime_exp`
  は `[propext, Classical.choice, Quot.sound]` のみ（`sorryAx` なし）

### 4.2 定理の“使ってる仮定”監査

- [ ] `hab : Nat.Coprime a b` は `coprime_cb_of_eq` のためだけに消費されている
- [ ] `hS0_not_sq` は `padicValNat_upper_bound_d3`（上界）の入力にだけ使われている
