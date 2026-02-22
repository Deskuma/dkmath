# FLT\_d3\_by\_padicValNat：補題チェーン検証チェックリスト（\_\_dkmath-all.lean.txt.gz 内限定）

> 対象データベース：`__dkmath-all.lean.txt.gz`

---

## 0. 健全性（ファイル整合）

- **期待 SHA256**

  - `cef351d0e52cc87a2462b061fe7f2d31de08a72f6286ea12b129de1fc9897516`

- **チェック項目**

  -

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

### 1.3 定理が**直接**呼ぶ補題（最短チェーン）

- `coprime_cb_of_eq`  （DB 8407）
- `exists_prime_factor_cube_diff`（DB 8444）
- `cube_sub_eq_of_add_eq`（DB 8397）
- `Nat.Prime.dvd_of_dvd_pow`（Mathlib）
- `padicValNat_lower_bound_of_dvd_d3`（DB 8631）
- `padicValNat_upper_bound_d3`（DB 8680）
- ほか：`Nat.pow_le_pow_left`, `Nat.sub_pos_of_lt`, `zify`, `ring_nf`, `omega`, `positivity` 等（主に Mathlib/tactic）

---

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

## 3. 依存ツリー（一次・二次）

### 3.1 `coprime_cb_of_eq`（DB 8407）

- 目的：`Nat.Coprime a b` と `a^3+b^3=c^3` から `Nat.Coprime c b`
- 主要依存：
  - `cube_sub_eq_of_add_eq`（DB 8397）
  - `Nat.exists_prime_and_dvd`（gcd≠1 → 素因子存在）
  - `Nat.dvd_sub`（`p|c^3` と `p|b^3` から `p|(c^3-b^3)`）
  - `Nat.Prime.dvd_of_dvd_pow`（`p|a^3 → p|a`）
  - `Nat.dvd_gcd` + `hab.gcd_eq_one`

**検査項目**

-

### 3.2 `exists_prime_factor_cube_diff`（DB 8444）

- 目的：`b < c` と `Nat.Coprime c b` から

  \(\exists q,\; \mathrm{Prime}\;q\;\land\; q\mid(c^3-b^3)\;\land\; \neg q\mid(c-b).\)

- **分岐**：`by_cases h3 : 3 ∣ c - b`

**(A) **``** ブランチ**

- `c = 3*k + b` とおいて、
  - `m := 3*k^2 + 3*k*b + b^2`
  - `S0_nat c b = 3*m` を明示（`ring`）
  - `m>1` から `q | m` なる素数 `q` を取る
  - `q ∤ (c-b)` を示す（`q|3k` から `q|3` or `q|k` を潰す）
  - 因数分解：`c^3 - b^3 = (c-b)*S0_nat c b`（`zify` + `ring_nf`）
  - よって `q | (c^3-b^3)`

**(B) **``** ブランチ**

- `exists_primitive_prime_factor_prime Nat.prime_three ...` に丸投げ
  - ここが Zsigmondy/Cyclotomic 側への接続点

**検査項目**

-

### 3.3 `padicValNat_lower_bound_of_dvd_d3`（DB 8631）

- 目的：`q|c` なら \(3 \le v_q(c^3)\)
- 主要依存：
  - `padicValNat.pow`（`v_q(c^3) = 3 * v_q(c)`）
  - `padicValNat.eq_zero_iff`（`v_q(c)=0` と `q∤c` の関係）

**検査項目**

-

### 3.4 `padicValNat_upper_bound_d3`（DB 8680）

- 目的：仮定 `¬ q^2 ∣ S0_nat a b` から \(v_q(a^3-b^3)\le 1\)
- 手順：
  1. 因数分解 `a^3-b^3 = (a-b)*S0_nat a b`
  2. `q ∤ (a-b)` かつ `q | (a^3-b^3)` から `q | S0`（`hq.dvd_mul.mp`）
  3. 上界：`padicValNat_le_one_of_not_sq_dvd`（PetalDetect内）
  4. `padicValNat.mul` と `padicValNat.eq_zero_of_not_dvd` を合わせる

**検査項目**

-

### 3.5 `padicValNat_le_one_of_not_sq_dvd`（DB 9178, PetalDetect）

- 目的：`¬ q^2 ∣ S0` ⇒ `padicValNat q S0 ≤ 1`
- 依存：`padicValNat_dvd_iff`（`2` での割り切りと valuation の同値）

**検査項目**

-

---

## 4. “機械的”チェック手順（Lean 側での監査コマンド案）

### 4.1 `sorry` 混入チェック（名前単位）

-

### 4.2 定理の“使ってる仮定”監査

-

---

## 5. 次の深掘りポイント（ここからが本番）

この定理の“独自性”は、**外部仮定** `hS0_not_sq` を「層Bの真相」として切り出している点。

- `hS0_not_sq` を **PetalDetect 側の定理**へ降ろして、仮定を消せるか？
  - つまり「q | diff かつ q ∤ diffFactor なら `¬ q^2 | S0`」を、どの追加条件で真にできるか。
  - 反例（a=18,b=1,q=7）の扱いが鍵。

（この“仮定の解消”ができれば、FLT d=3 の別解は完全自走になる。）
