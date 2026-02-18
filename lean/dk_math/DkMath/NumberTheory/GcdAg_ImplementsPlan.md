# GCD-Ag 位相と (a+b) 検出器の実装計画

## 実装計画：Ag 位相・\((a+b)\) 検出器・反例回避へ

## Phase 0：土台の整理（ファイル配置と import）

- 既存：`SilverRatioUnit.lean`, `Sqrt2Lemmas.lean`, `NPUnit.lean`（アップ済）
- 追加する新ファイル案：
  - `DkMath/SilverRatio/GcdAg.lean`（Ag射影と gcd_Ag）
  - `DkMath/FLT/PetalDetect.lean`（\((a+b)\) 検出器と φビット補題）
  - 既存の FLT B層コードからは、まず補題を切り出して import する形へ

依存は最小で：

- `Mathlib.Algebra.Ring.GeomSum`（冪の差/和の一次因子割り）
- `Mathlib`（gcd、Nat 基本）

---

## Phase 1：Ag 射影 π と `gcd_Ag` を確定（整数100%）

### 1.1 定義

- `π_Ag (n : ℕ) : ℕ := n / 2`
- `gcd_Ag (a b : ℕ) : ℕ := Nat.gcd (π_Ag a) (π_Ag b)`

### 1.2 基本補題（まずここだけでビルドOKにする）

- `π_Ag (2*k) = k`
- `π_Ag (2*k+1) = k`
- `gcd_Ag a (2*k) = gcd_Ag a (2*k+1)`（位相を見ない）
- メイン観測：
  \[
  N=2n \Rightarrow \gcd(N,N+2)=2,\quad \gcd_{\rm Ag}(N,N+2)=1
  \]

  を Lean で補題化：
  - `gcd_even_add_two_eq_two : Nat.gcd (2*n) (2*n+2) = 2`
  - `gcdAg_even_add_two_eq_one : gcd_Ag (2*n) (2*n+2) = 1`

> ここまでで「偶数は半位相落とす」を Lean の関数として固定。

---

## Phase 2：φビット構造 \(S_\phi\) を定義して“差分核”を補題化

### 2.1 定義（Ring/CommSemiring 版でも Nat 版でもOK）

- `S0 a b := a^2 + a*b + b^2`
- `S1 a b := (a+b)^2`
- `Sφ a b (φ : Bool)` を
  - `φ=false → S0`
  - `φ=true  → S1`
  としてもよいし、整数なら
  \[
  S_\phi = S_0 + \phi\cdot ab,\quad \phi\in\{0,1\}
  \]

  を `φ : ℕ` with `φ=0/1` でやってもよい。

### 2.2 差分核

- `S1 - S0 = a*b`（CommRingなら）
- Nat の場合は等式でなく `=`
  - `S1 = S0 + a*b` を証明（展開して `ring`）

> ここまでで「半位相⇔完成」のビットが固定。

---

## Phase 3：本丸の検出器「(a+b) が割るか？」を Mathlib 補題で組む

### 3.1 既製品の利用（Mathlib）

- `Odd.add_dvd_pow_add_pow`（奇数冪で \(a+b\mid a^n+b^n\)）
- `sub_dvd_pow_sub_pow`（常に \(a-b\mid a^n-b^n\)）
（どちらも `Mathlib/Algebra/Ring/GeomSum`）

### 3.2 φ検出に使う補題

- `S1` 側は自明：
  \[
  (a+b)\mid (a+b)^2
  \]

- `S0` 側は合同で見るのが最短：
  \[
  a\equiv -b\pmod{a+b} \Rightarrow S0 = a^2+ab+b^2 \equiv b^2 \pmod{a+b}
  \]

  したがって
  \[
  (a+b)\mid S0 \iff (a+b)\mid b^2
  \]

- さらに（反例世界でよく置く）\(\gcd(a,b)=1\) を入れると
  \[
  \gcd(a+b,b)=1 \Rightarrow (a+b)\mid b^2 \Rightarrow a+b=1
  \]

  のように「ほぼ不可能」へ落とせる。

> ここで “φ=0 側は核が吸い込まれない” を定理化できる。

---

## Phase 4：Ag 正規化込みの「互いに素環境」を B層へ挿入

### 4.1 2ノイズ除去の宣言

- B層の冒頭で
  - “以降、2進位相は `π_Ag` で正規化して扱う”
  - “互いに素は `gcd_Ag = 1` を基準にする”
  を明示

### 4.2 `padicValNat = 1` の置き換え戦略

目標を「=1」から

\[
\exists q,\ v_q(\text{Body})\not\equiv 0\pmod n
\]

へ変更し、特に \(q=2\) 由来の邪魔は Ag 正規化で先に消す。

- 2進は `gcd_Ag` / `π_Ag` で処理
- 残りの奇素数 \(q\neq 2\) について
  - “(a+b) が割る/割らない” で新因子の入口を作り
  - 必要なら Zsigmondy/LTE へ繋ぐ

---

## 進め方（最短の作業順）

1. **Phase 1だけ**を先に新ファイルで完成（ビルドOK✅️）
2. 次に **Phase 2**（φと差分核）を追加（ringで終わる）
3. **Phase 3**：`GeomSum` の既製補題を import して `(a+b)` 検出器を固める
4. 最後に **Phase 4**：FLT B層の既存コードへ差し込んで “強すぎる `padicValNat=1`” を撤去

---

## 期待できる成果（B層の目的に対して）

- 「2 のせいで互いに素が言えない」状況を `gcd_Ag` で解消
- 「半位相（φ=0）では核 \((a+b)\) が吸い込まれない」を定理として固定
- それにより “外部から連れてくる素数 \(q\)” の候補が作りやすくなり、付値合同で反例を潰す土台ができる

---
