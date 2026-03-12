# CFBRC 実装計画

## 1. 目的

DkMath の既存 `GN` を再利用しつつ、prime exponent case の「円分多項式側 core」を
**shifted homogeneous cyclotomic core**
として Lean で実装し、最終的に

\[
\operatorname{CyclotomicPrimeCore}(p,x,u) = GN(p,x,u)
\]

を **exact に証明** する。

ここでの狙いは、一般の斉次化 machinery 全体を先に建てることではない。
まずは **prime case の最小核** を完成させ、以後の

- Zsigmondy
- CFBRC
- PrimeProvider
- squarefree / valuation

の土台を共通化すること。

---

## 2. スコープ

今回の実装では **general \(d\) の斉次化 product 版はやらない**。

やることは次の 3 点だけ：

1. shifted homogeneous cyclotomic core を新規定義する
2. それが差の冪の商
   \[
   \frac{(x+u)^p-u^p}{x}
   \]

   に対応することを semiring-safe に示す
3. 既存の `GN` と一致することをまず `Nat` 上で exact に示す

---

## 3. 既存コードの前提

既存の `GN` は **再定義しない**。必ず既存のものを使うこと。

想定 import は少なくとも次：

```lean
import DkMath.CosmicFormula.CosmicFormulaBinom
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
```

必要なら追加で `omega` / `ring` / `nlinarith` 系 import を足してよいが、
**research / quarantine 系ファイルは import しない**。

---

## 4. 新規ファイル

新規ファイルを作る：

```text
lean/dk_math/DkMath/NumberTheory/CyclotomicPrimeCore.lean
```

namespace は次を推奨：

```lean
namespace DkMath.NumberTheory
open scoped BigOperators
open DkMath.CosmicFormulaBinom
```

---

## 5. 新規定義

まずは一般の 2 変数斉次多項式をいきなり作らず、
**shift 済み core**
をそのまま定義する。

```lean
@[simp] def cyclotomicPrimeCore {R : Type _} [CommSemiring R]
    (p : ℕ) (x u : R) : R :=
  ∑ k ∈ Finset.range p, (x + u) ^ k * u ^ (p - 1 - k)
```

数学的意味は

\[
\operatorname{CyclotomicPrimeCore}(p,x,u)
:=
\sum_{k=0}^{p-1}(x+u)^k u^{p-1-k}.
\]

これは prime \(p\) に対する円分多項式

\[
\Phi_p(T)=1+T+\cdots+T^{p-1}
\]

の **shifted homogeneous evaluation**
に相当する core である。

注意：

- この定義自体には `Nat.Prime p` を仮定しない
- prime 仮定は「円分多項式として意味づける」段階で使う
- 今回の patch では **algebraic core の exact bridge** を最優先する

---

## 6. 必須定理 5 本

以下の 5 本を **必須成果物** とする。

### 6.1. 定理 1

```lean
theorem add_pow_eq_mul_cyclotomicPrimeCore_add_gap
    {R : Type _} [CommSemiring R] (p : ℕ) (x u : R) :
    (x + u) ^ p = x * cyclotomicPrimeCore p x u + u ^ p := by
```

数学的には

\[
(x+u)^p=
x \cdot \sum_{k=0}^{p-1}(x+u)^k u^{p-1-k}
+u^p.
\]

これは semiring-safe 版の主恒等式。

**証明方針**
最初に mathlib に geometric-sum 系の補題があればそれを使う。
見つからなければ telescoping を手で組む。

狙う変形は

\[
x = (x+u)-u
\]

を使って

\[
x\,(x+u)^k u^{p-1-k}=
(x+u)^{k+1}u^{p-1-k}-(x+u)^k u^{p-k}
\]

の telescoping を作ること。
`CommSemiring` 上で subtraction を直接使わずに済むなら、その形を優先。

---

### 6.2. 定理 2

```lean
theorem mul_cyclotomicPrimeCore_eq_mul_GN
    {R : Type _} [CommSemiring R] (p : ℕ) (x u : R) :
    x * cyclotomicPrimeCore p x u = x * GN p x u := by
```

数学的には

\[
x \cdot \operatorname{CyclotomicPrimeCore}(p,x,u)=
x \cdot GN(p,x,u).
\]

**証明方針**
`DkMath.CosmicFormulaBinom.cosmic_id_csr'` を使い、

\[
(x+u)^p = x\cdot GN(p,x,u)+u^p
\]

と、定理 1 の

\[
(x+u)^p = x\cdot \operatorname{CyclotomicPrimeCore}(p,x,u)+u^p
\]

を比較して結論を得る。
ここは **比較して終わる** 形にすること。
GN を再展開して係数比較を始めないこと。沼る。

---

### 6.3. 定理 3

```lean
theorem cyclotomicPrimeCore_eq_GN_nat
    {p x u : ℕ} (hx : 0 < x) :
    cyclotomicPrimeCore p x u = GN p x u := by
```

数学的には

\[
x>0
\;\Longrightarrow\;
\operatorname{CyclotomicPrimeCore}(p,x,u)=GN(p,x,u).
\]

**証明方針**
定理 2 を `Nat` に specialized した後、`hx : 0 < x` から
左消去または右消去を使って結論を出す。
`Nat.succ_le_iff` や `Nat.eq_of_mul_eq_mul_left` 系を使ってよい。
必要なら `have hx0 : x ≠ 0 := Nat.ne_of_gt hx` を用意する。

---

### 6.4. 定理 4

```lean
theorem dvd_cyclotomicPrimeCore_iff_dvd_GN_nat
    {p x u q : ℕ} (hx : 0 < x) :
    q ∣ cyclotomicPrimeCore p x u ↔ q ∣ GN p x u := by
```

数学的には

\[
x>0
\;\Longrightarrow\;
q \mid \operatorname{CyclotomicPrimeCore}(p,x,u)
\iff
q \mid GN(p,x,u).
\]

**証明方針**
定理 3 をそのまま `simpa` で使う。
ここは「算術橋」の最小核として用意する。

---

### 6.5. 定理 5

```lean
theorem prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left
    {p x u q : ℕ}
    (hq : Nat.Prime q)
    (hq_dvd : q ∣ (x + u) ^ p - u ^ p)
    (hq_ndvd : ¬ q ∣ x) :
    q ∣ cyclotomicPrimeCore p x u := by
```

数学的には

\[
q \mid ((x+u)^p-u^p),\quad q \nmid x
\;\Longrightarrow\;
q \mid \operatorname{CyclotomicPrimeCore}(p,x,u).
\]

**証明方針**
定理 1 からまず Nat 版の補助補題

```lean
lemma sub_eq_mul_cyclotomicPrimeCore_nat (p x u : ℕ) :
    (x + u) ^ p - u ^ p = x * cyclotomicPrimeCore p x u := by
```

をローカルまたは別 lemma で出してよい。

あとは既存の `prime_dvd_GN_of_dvd_sub_not_dvd_left` と同じ形で

\[
q \mid x \cdot \operatorname{CyclotomicPrimeCore}(p,x,u)
\]

を得て、`hq.dvd_mul.mp` から `resolve_left hq_ndvd` で終える。

---

## 7. 補助補題は許可

上の 5 本を通すために、以下のような補助補題は追加してよい。

### 7.1

```lean
lemma sub_eq_mul_cyclotomicPrimeCore_nat (p x u : ℕ) :
    (x + u) ^ p - u ^ p = x * cyclotomicPrimeCore p x u := by
```

### 7.2

```lean
@[simp] lemma cyclotomicPrimeCore_zero_left
    {R : Type _} [CommSemiring R] (p : ℕ) (u : R) :
    cyclotomicPrimeCore p 0 u = ?something := by
```

ただし、**本体 5 本を隠すための過剰な補助補題乱立は禁止**。
必要最小限に留めること。

---

## 8. 実装上の制約

### 8.1

**`GN` は再定義しない。**
必ず既存の

```lean
DkMath.CosmicFormulaBinom.GN
```

を使うこと。

### 8.2

**general \(d\) の斉次 cyclotomic product 版には入らない。**
今回は prime case の shifted core だけ。

### 8.3

**`sorry` / `admit` 禁止。**
research file に逃がさない。

### 8.4

**FLT front line のファイルは触らない。**
まず `NumberTheory` 側だけで橋を完成させる。

---

## 9. stretch goal

必須ではないが、余力があれば次を試してよい。

### 9.1

prime \(p\) に対し、

\[
\Phi_p(T)=1+T+\cdots+T^{p-1}
\]

という mathlib の定理名を検索し、
`cyclotomicPrimeCore` が「prime cyclotomic polynomial の shifted homogeneous evaluation」であることを
コメントまたは補助定理で明記する。

ただし **exact theorem 名の探索で沼るなら、今回は見送ってよい**。
今回のパッチの本体は **GN との exact equality** である。

---

## 10. 完了条件

以下が通れば完了：

```bash
cd lean/dk_math
lake build DkMath.NumberTheory.CyclotomicPrimeCore
```

余裕があれば追加で：

```bash
lake build DkMath.NumberTheory.ZsigmondyCyclotomic
```

ただし後者は今回の patch では必須ではない。
まず新規ファイル単体で clean build を通すこと。

---

## 11. 最後に

この patch のボスは **定理 1** である。
そこが落ちれば、残り 4 本はかなり素直に連鎖する。
したがって、最初の作業時間の大半を

\[
(x+u)^p = x \cdot \operatorname{CyclotomicPrimeCore}(p,x,u)+u^p
\]

の証明に投入してよい。
GN の再展開・係数比較に突っ込むのは最後の手段とする。

---

## 12. 実行フェーズ計画（2026/03/12）

1. Phase A（完了）:
   `DkMath.CFBRC.Defs` に `cyclotomicPrimeCore` を定義し、
   `DkMath.CFBRC.Basic` で prime case の 5 本（+最小補助）を実装。
2. Phase B（次）:
   `Nat.Prime p` を仮定したときの
   「`cyclotomicPrimeCore` = prime cyclotomic の shifted homogeneous evaluation」
   を補題化する。
   - 2026/03/12 実装完了
     (`cyclotomicPrimeCore_eq_shiftedHomEval_cyclotomic_of_prime`)。
3. Phase C（次）:
   `DkMath.CFBRC.*` から Zsigmondy / valuation 層へ import 依存を追加し、
   除法同値補題を再利用 API として露出する。
   - 2026/03/12 実装完了（`DkMath.CFBRC.Bridge`）
     - `prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`
     - `padicValNat_sub_pow_eq_padicValNat_cyclotomicPrimeCore_of_not_dvd_boundary`
4. Phase D（次）:
   `CFBRC_Discussion.md` のロードマップに沿って、
   一般次数（general `d`）の product 版に進むかを評価して分岐判断する。
   - 2026/03/12 評価結果:
     - 進行条件は充足（Phase A/B/C 完了、`CFBRC` から valuation bridge まで接続済み）。
     - `CFBRC_Discussion.md` の最終判定とも整合し、次は general `d` product 版が妥当。
   - 分岐判断（Decision）: **GO**
     - Branch D-GO（採用）:
       general `d` の algebraic product bridge を Lean で実装する。
     - Branch D-HOLD（不採用）:
       valuation / squarefree 未完を理由に general `d` を保留する。
       （理由: 現段階では代数橋は独立に前進可能で、保留メリットが小さい）
   - D-GO の実装スコープ（次フェーズ）:
     1. `Homog(Φ_m)(X,Y)` の評価器を最小定義。
     2. `((X^d - Y^d)/(X-Y))` に対応する divisors product 版の橋渡し補題を実装。
     3. `X := x+w`, `Y := w` 代入で `GN(d,x,w)` 側へ接続する。
   - 非スコープ:
     - squarefree / valuation の一般次数強化
     - PrimeProvider 最終統合
