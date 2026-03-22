# 差の因数分解原理からみた \( x\,GN_d(x,u) \) と素因数分解の一意性

cid: 69becbd2-3f3c-83ab-97af-666a8f8f4fb3

## 1. 目的

本ノートの目的は、差の因数分解

\[
(x+u)^d - x^d = u\,GN_d(x,u)
\]

を起点として、  
**\( x\,GN_d(x,u) \) 多項式が素因子をどのように分離して保持するか** を整理し、  
そこから **素因数分解の一意性へ向かう原理核** を取り出すことである。

ここでの主眼は、標準的な Euclid の補題

\[
p \mid ab \;\Rightarrow\; p \mid a \ \text{or}\ p \mid b
\]

を、そのまま使うのではなく、  
**差分構造の中で素因子の所属先が曖昧にならない** という形で再解釈する点にある。

---

## 2. 基本定義

\( d \ge 1 \) とし、差の冪を割る多項式 \( GN_d(x,u) \) を

\[
GN_d(x,u)
:=
\frac{(x+u)^d - x^d}{u}
\]

で定める。二項展開により

\[
GN_d(x,u) =
\sum_{k=1}^{d} \binom{d}{k} x^{d-k} u^{k-1}
\]

である。

したがって基本恒等式

\[
(x+u)^d - x^d = u\,GN_d(x,u)
\]

が成り立つ。

さらに \( x \) を掛けると

\[
x\bigl((x+u)^d - x^d\bigr)=xu\,GN_d(x,u)
\]

すなわち

\[
x(x+u)^d - x^{d+1} = xu\,GN_d(x,u)
\]

を得る。

---

## 3. 宇宙式的な読み替え

この式を宇宙式の語彙で見ると、

- \( x^{d+1} \) は旧世界
- \( x(x+u)^d \) は拡張世界
- \( xu\,GN_d(x,u) \) は両者の差分 Body

である。

特に \( xu\,GN_d(x,u) \) は、

- \( x \) 由来の因子
- \( u \) 由来の因子
- 差分 kernel \( GN_d(x,u) \) 由来の因子

を同時に含むため、  
**素因子の所属先を観測する器** として働く。

---

## 4. 最重要の合同式

### 4.1. \( x \) に関する合同

\[
GN_d(x,u) =
\sum_{k=1}^{d} \binom{d}{k} x^{d-k} u^{k-1}
\]

を \( \bmod x \) で見ると、\( x \) を含む項はすべて消え、最後の項だけが残る。  
したがって

\[
GN_d(x,u)\equiv d\,u^{d-1}\pmod{x}
\]

を得る。

### 4.2. \( u \) に関する合同

同様に \( \bmod u \) で見れば、\( u \) を含む項は消え、最初の項だけが残るから

\[
GN_d(x,u)\equiv d\,x^{d-1}\pmod{u}
\]

を得る。

この 2本が、差の因数分解における素因子分離の原理核である。

---

## 5. 共通因子制御

上の合同式から、もし \( g \mid x \) かつ \( g \mid GN_d(x,u) \) なら

\[
g \mid d\,u^{d-1}
\]

が従う。  
ゆえに \( \gcd(x,u)=1 \) なら

\[
\gcd(x,GN_d(x,u)) \mid d
\]

となる。

同様に、もし \( g \mid u \) かつ \( g \mid GN_d(x,u) \) なら

\[
g \mid d\,x^{d-1}
\]

であり、\( \gcd(x,u)=1 \) のもとでは

\[
\gcd(u,GN_d(x,u)) \mid d
\]

を得る。

これをまとめると、次が成り立つ。

### 補題

\[
\gcd(x,u)=1
\quad\Rightarrow\quad
\gcd(x,GN_d(x,u)) \mid d,
\qquad
\gcd(u,GN_d(x,u)) \mid d
\]

---

## 6. 非例外素数の分離

上の補題から、\( p \nmid d \) なる素数 \( p \) に対して、\( \gcd(x,u)=1 \) なら次が言える。

### 命題

\[
p \mid x \Rightarrow p \nmid GN_d(x,u)
\]

\[
p \mid u \Rightarrow p \nmid GN_d(x,u)
\]

### 証明

たとえば \( p \mid x \) かつ \( p \mid GN_d(x,u) \) と仮定すると、前節より

\[
p \mid d
\]

が必要になる。これは \( p \nmid d \) に反する。  
同様に \( p \mid u \) の場合も同じである。 \( \square \)

この結果の意味は大きい。  
**次数 \( d \) に由来する例外素数を除けば、\( x \) や \( u \) の素因子は \( GN_d(x,u) \) に勝手に紛れ込まない** のである。

---

## 7. \( x\,u\,GN_d(x,u) \) における素因子の所属先

以上より、\( \gcd(x,u)=1 \) かつ \( p \nmid d \) のもとでは、  
素数 \( p \) が

\[
x\,u\,GN_d(x,u)
\]

を割るとき、その所属先は

- \( p \mid x \)
- \( p \mid u \)
- \( p \mid GN_d(x,u) \)

のいずれかであり、しかも **複数層へ同時にまたがらない** 。

すなわち、非例外素数は

\[
x \;\sqcup\; u \;\sqcup\; GN_d(x,u)
\]

という 3層のどこに属するかが一意に定まる。

これが差の因数分解における **素因子所属の一意性** である。

---

## 8. これと素因数分解の一意性との関係

通常の素因数分解の一意性は、Euclid の補題

\[
p \mid ab \Rightarrow p \mid a \ \text{or}\ p \mid b
\]

を繰り返し使って証明される。

差分 kernel \( GN_d \) を使う見方では、この補題を次のように読み替える。

> 素因子は、差分 Body の中で曖昧に混ざらず、必ずどこかの層に属する。

すなわち、

\[
xu\,GN_d(x,u)
\]

に現れる素因子は、  
\( x \), \( u \), \( GN_d(x,u) \) のどこから来たかが追跡可能である。  
この **所属先の曖昧さの無さ** が、標準整数論における Euclid 型消去の差分版に対応する。

---

## 9. 差の因数分解から見た Euclid 型原理

ここで得られる原理を整理すると次のようになる。

### 原理 A. 差分分離原理

\[
(x+u)^d - x^d = u\,GN_d(x,u)
\]

において、\( \gcd(x,u)=1 \) なら、非例外素数 \( p \nmid d \) は  
\( u \) 側と \( GN_d \) 側の両方に同時には現れない。

### 原理 B. 拡張分離原理

\[
x(x+u)^d - x^{d+1} = xu\,GN_d(x,u)
\]

において、非例外素数 \( p \nmid d \) は  
\( x \), \( u \), \( GN_d(x,u) \) の複数層へ同時には現れない。

### 原理 C. 素因子剥離原理

したがって、ある素因子 \( p \) を 1枚剥がす操作を行うとき、  
その剥離先は曖昧でなく、一意に定まる。

この原理 C が、標準証明における「素数を 1個つかまえて消去する」操作に対応する。

---

## 10. なぜこれが「差の因数分解の原理」なのか

差の因数分解の本質は

\[
A^d - B^d = (A-B)\cdot(\text{中間 kernel})
\]

という形にある。  
差 \( A-B \) が外層をなし、残りが kernel をなす。

本ノートでは \( A=x+u \), \( B=x \) と置き、

\[
(x+u)^d - x^d = u\,GN_d(x,u)
\]

をその最も基本的な形として使った。  
ここで大事なのは、**差 \( u \) と kernel \( GN_d(x,u) \) が素因子を混線させずに保持する** ことじゃ。

ゆえに差の因数分解は、単なる式変形ではなく、

**素因子の出現場所を分離して観測するための構造的分解**

として理解できる。

---

## 11. 一意分解へ向かう設計図

差の因数分解から素因数分解の一意性へ進むには、次の段階を踏むと見通しがよい。

### 11.1. 局所分離

\[
GN_d(x,u)\equiv d\,u^{d-1}\pmod{x},
\qquad
GN_d(x,u)\equiv d\,x^{d-1}\pmod{u}
\]

から、局所的な素因子分離を得る。

### 11.2. 例外素数の隔離

\( p \mid d \) なる例外素数だけを別管理する。

### 11.3. 剥離の反復

非例外素数について、どの層から現れたかが一意に分かることを使い、  
素因子を 1枚ずつ剥がす。

### 11.4. 停止性

自然数の良順序性により、この剥離操作は有限回で止まる。

### 11.5. 一意性

剥離先が毎回曖昧でないため、得られる素因子列は順序を除いて一致する。

---

## 12. 注意点

ここは正確さのために明記しておく。

**\( x\,GN_d(x,u) \) だけで直ちに算術の基本定理の完全証明になるわけではない。**

まだ必要なのは、

- 任意整数に対する反復剥離の一般定式化
- 例外素数 \( p \mid d \) の処理
- 剥離操作の停止性と整合性

である。

したがって、ここで得たものは

**素因数分解の一意性そのものの完成証明** というよりは、  
**差の因数分解から Euclid 型消去原理を再構成するための骨格**

と理解するのが最もよい。

---

## 13. まとめ

本ノートの核心は次の一行に尽きる。

\[
GN_d(x,u)\equiv d\,u^{d-1}\pmod{x}
\]

および対称的に

\[
GN_d(x,u)\equiv d\,x^{d-1}\pmod{u}
\]

である。

これにより、非例外素数は

- \( x \) 層
- \( u \) 層
- \( GN_d(x,u) \) 層

のどこに属するかが曖昧にならない。

ゆえに、差の因数分解

\[
(x+u)^d - x^d = u\,GN_d(x,u)
\]

は、単なる展開公式ではなく、  
**素因子の所属先を分離して観測する構造原理** である。

この意味で、素因数分解の一意性とは、

> 素因子が差分 Body の内部で混線せず、反復剥離の過程で常に一意の所属層を持つこと

として再解釈できる。

---

## 14. 定理案

最後に、上の内容を定理風にまとめておく。

```text
定理（差分 kernel の素因子分離原理）

\[
\gcd(x,u)=1,\quad
(x+u)^d-x^d=u\,GN_d(x,u)
\]

とする。このとき任意の素数 \( p \nmid d \) について

\[
p\mid x \Rightarrow p\nmid GN_d(x,u),\qquad
p\mid u \Rightarrow p\nmid GN_d(x,u)
\]

が成り立つ。したがって \( xu\,GN_d(x,u) \) に現れる非例外素数は、
その所属層 \( x,u,GN_d(x,u) \) が一意に定まる。
この原理を反復剥離に適用することで、素因数分解の一意性へ向かう
Euclid 型消去原理の差分版が得られる。
```

---

## 15. 補足メモ

この視点の美点は、加法的差分

\[
(x+u)^d - x^d
\]

と乗法的因数分解

\[
u\,GN_d(x,u)
\]

の橋が、そのまま **素因子の追跡理論** になっている点にある。  
すなわち、差の因数分解は

- 差を作る
- 差を kernel に分ける
- kernel の中で素因子の所属を観測する

という 3段階の構造を持つ。

この橋を一般の \( ab \) 型の積へどう延長するかが、今後の定式化上の主課題となる。

---

## 16. Lean 実装計画（事前調査）

### 16.1 調査スコープ

本フェーズでは「自然数の素因数分解の一意性」を、
既存の `GN`/差分系補題と `Nat.factorization` 系 API を使って実装可能かを確認した。

### 16.2 既存補題の所在（ワークスペース内）

1. `DkMath/Basic/Nat.lean`

- `mem_support_factorization_iff`
  - `p ∈ n.factorization.support ↔ (n ≠ 0 ∧ Nat.Prime p ∧ p ∣ n)`
- `disjoint_support_of_coprime`
  - `Nat.Coprime a b → Disjoint a.factorization.support b.factorization.support`
- `support_mul_coprime`
  - 互いに素条件下で support が和集合になる補題
- `rad_mul_coprime`
  - support 分離を使う積の既存実装例として有用

1. `DkMath/CFBRC/Basic.lean`

- `sub_eq_mul_cyclotomicPrimeCore_nat`
- `prime_dvd_cyclotomicPrimeCore_of_dvd_sub_not_dvd_left`
  - 差分式から core 側への素数除法移送

1. `DkMath/CFBRC/Bridge.lean`

- `prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`
  - `q ∤ x` 下で差分式と core の除法同値
- primitive prime existence 系 wrapper
  - `exists_primitive_prime_factor_*`

1. `DkMath/NumberTheory/Gcd/GN.lean`

- `gcd_gap_GN_dvd_exp_int`
- `coprime_gap_GN_of_not_dvd_exp_prime`
- `padicValNat_sub_pow_eq_padicValNat_GN_of_not_dvd_gap`
  - 例外素数（指数を割る素数）を切り分けるための補強材料

### 16.3 利用可能定理（主に Mathlib API）

既存コードで実際に使用されており、本実装でも再利用可能であることを確認:

- `Nat.factorization_mul`
- `Nat.mem_primeFactors`
- `Nat.Prime.dvd_mul`
- `Nat.dvd_gcd`, `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`
- `Nat.exists_prime_and_dvd`
- `Nat.coprime_iff_gcd_eq_one`

### 16.4 実装方針（分割）

1. Phase A: 純粋な自然数版の一意性骨格

- 目標: `factorization.support` の同一性から、素因子集合の一意性を先に確立。
- 依存: `mem_support_factorization_iff`, `support_mul_coprime`。

1. Phase B: Euclid 型消去を差分（`GN`）へ接続

- 目標: `p ∤ d` の非例外素数で、`x / u / GN` の所属先が競合しないことを Lean 補題化。
- 依存: `prime_dvd_sub_pow_iff_dvd_cyclotomicPrimeCore_nat`, `coprime_gap_GN_of_not_dvd_exp_prime`。

1. Phase C: 一意性定理として統合

- 目標: 「分解が 2 通り与えられたとき、素数ごとの指数が一致する」主定理へ集約。
- 実装形: `Nat.factorization` の pointwise equality (`ext p`) を基本に構成。

### 16.5 直近の実装対象（提案）

- 新規ファイル候補: `DkMath/NumberTheory/UniqueFactorizationGN.lean`
- 最初に置く補題候補:
  1. `prime_mem_support_iff_dvd`
  2. `support_eq_of_primewise_dvd_iff`
  3. `factorization_ext_of_primewise`
  4. `unique_factorization_nat_via_support`

この順で進めると、既存補題の再利用率が高く、`sorry` を最小化しやすい。

### 16.6 プロトタイプ実装（Mathlib 依存）進捗

初手の骨格として、以下を実装済み:

- 新規 Lean ファイル:
  - `DkMath/NumberTheory/UniqueFactorizationGN.lean`
- 追加した主要定理:
  - `prime_mem_support_iff_dvd`
  - `support_eq_of_primewise_dvd_iff`
  - `factorization_eq_of_prime_pow_dvd_iff`
  - `unique_factorization_nat_via_prime_powers`

ビルド確認:

- `lake build DkMath.NumberTheory.UniqueFactorizationGN` 成功。

備考:

- この実装は「プロトタイプ優先」のため Mathlib API を積極利用している。
- 将来の `DkMathlib` 独立化フェーズでは、ここを wrapper/bridge 境界として分離する。

### 16.7 `GN` 側「層所属一意性」補題の接続

`UniqueFactorizationGN` へ、`Gcd.GN` 層を利用した以下の接続補題を追加:

- `prime_dvd_left_not_dvd_GN_of_coprime_of_not_dvd_exp`
  - 前提: `1 ≤ d`, `0 < x`, `Nat.Coprime x u`, `Nat.Prime q`, `¬ q ∣ d`, `q ∣ x`
  - 結論: `¬ q ∣ GN d x u`
- `prime_dvd_right_not_dvd_GN_swap_of_coprime_of_not_dvd_exp`
  - 前提: `1 ≤ d`, `0 < u`, `Nat.Coprime x u`, `Nat.Prime q`, `¬ q ∣ d`, `q ∣ u`
  - 結論: `¬ q ∣ GN d u x`（左境界対称版）

実装ポイント:

- `DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp_int` を中核に再利用。
- `z := x+u, y := u` 代入（対称版は変数 swap）で gap 側と `GN` 側を接続。

### 16.8 まだ残っていること（明示）

今回の補題で得たのは **prime divisibility の非競合** であり、まだ

\[
q^k \mid x \Rightarrow q^k \nmid GN_d(x,u)
\]

のような **prime-power レベルの完全分離** ではない。  
したがって、前段の

\[
\forall p, k,\; p^k \mid m \iff p^k \mid n
\]

へは直結していない。  
ただし方向は妥当であり、現段階は

\[
k = 1 \text{ の層所属一意性}
\]

を先に固定した段と位置づける。

また、左右対称版が `GN d u x` に対する形で出ているため、将来的には API の見え方を揃える目的で、

\[
\text{boundaryLeft},\ \text{boundaryRight},\ \text{kernel}
\]

のような naming に寄せると、証明の意味がより明確になる。

### 16.9 次に狙うべき順序

#### 16.9.1 prime から prime-power へ

今回の補題を足場に、非例外素数（`q ∤ d`）について

\[
v_q(\gcd(x, GN_d(x,u))) = 0
\]

または少なくとも

\[
q^k \mid x \Rightarrow q \nmid GN_d(x,u)
\]

型の valuation 補題へ伸ばす。  
ここで一気に `k` まで言うか、先に `v_q` 記法を整えるかが分岐点。

#### 16.9.2 二層圧縮 wrapper

現在の三層構造

\[
x,\ u,\ GN_d(x,u)
\]

を、一意性モジュール入口として

\[
A := x,\qquad B := GN_d(x,u)
\]

または

\[
A := xu,\qquad B := GN_d(x,u)
\]

に圧縮し、

\[
q \mid A \Rightarrow q \nmid B
\]

型 API にまとめる。これにより `factorization_eq_of_prime_pow_dvd_iff` 側へ接続しやすくなる。

#### 16.9.3 例外素数（`q ∣ d`）の隔離

現行補題は条件 `q ∤ d` を持つ。これは妥当かつ必要なので、  
例外側は明示的に別レイヤとして扱う方針を維持する。

### 16.10 `v_q` ベース補題の実装（prime-power 接続点）

`DkMath/NumberTheory/UniqueFactorizationGN.lean` に、`q ∤ d` 下の `v_q` 補題を追加した。

- `prime_not_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp`
  - `¬ q ∣ gcd(x, GN d x u)` を直接与える。
- `padicValNat_gcd_left_GN_eq_zero_of_coprime_of_not_dvd_exp`
  - `v_q(gcd(x, GN d x u)) = 0`。
- `padicValNat_gcd_right_GN_swap_eq_zero_of_coprime_of_not_dvd_exp`
  - 左境界対称版（`gcd(u, GN d u x)`）。
- `not_primePow_dvd_gcd_left_GN_of_coprime_of_not_dvd_exp`
  - `k>0` なら `q^k ∤ gcd(x, GN d x u)`。

これで、`k=1` の層分離から `v_q`・`q^k` 側への最初の橋が通った。

### 16.11 product レベル valuation と二層 wrapper の追加

次段として、`UniqueFactorizationGN` に以下を実装:

- wrapper 定義:
  - `boundaryRight`, `boundaryLeft`
  - `kernelRight`, `kernelLeft`
  - `boundaryProd`
- product valuation:
  - `padicValNat_mul_boundaryRight_kernelRight_eq_add`
    - `v_q(x * GN d x u) = v_q(x) + v_q(GN d x u)`
  - `padicValNat_mul_boundaryProd_kernelRight_eq_add`
    - `v_q(x*u*GN d x u) = v_q(x) + v_q(u) + v_q(GN d x u)`
- wrapper 上の層分離:
  - `prime_dvd_boundaryRight_not_dvd_kernelRight_of_coprime_of_not_dvd_exp`
  - `prime_dvd_boundaryLeft_not_dvd_kernelLeft_of_coprime_of_not_dvd_exp`

これで「gcd レベル → product レベル」への最初の移送と、`boundary/kernel` 命名での API 入口が揃った。

### 16.12 `boundaryProd` の prime-power 読み出しと比較 wrapper

精密化ポイント（設計上の切り分け）:

- valuation 加法そのものは `padicValNat.mul` の一般公式。
- GN 側の固有貢献は、
  - 何を `boundary/kernel` 積として見るか
  - 非競合条件をどう API に持ち上げるか
  - naming をどう固定するか
  にある。

追加実装:

- `primePow_dvd_boundaryProd_iff_exists_split`
  - `q^k ∣ boundaryProd x u` と
    `∃ i j, i+j=k ∧ q^i∣x ∧ q^j∣u` の同値（`q` prime, `x,u>0`）。
- `padicValNat_mul_boundaryProd_kernelRight_eq_add_wrapper`
  - wrapper 形で
    `v_q(boundaryProd * kernelRight) = v_q(boundaryProd)+v_q(kernelRight)`。

これで `boundaryProd` 側の prime-power API と `kernelRight` 比較 API の入口が揃った。

### 16.13 `boundaryProd` の prime-power 判定を不等式 wrapper へ拡張

存在分割版

- `primePow_dvd_boundaryProd_iff_exists_split`

に加えて、不等式版 wrapper を追加した。

- `primePow_dvd_boundaryProd_iff_le_padicVal_sum`
  - `q^k ∣ boundaryProd x u ↔ k ≤ v_q(x) + v_q(u)`（`q` prime, `x,u>0`）。

これにより、将来の factorization 一致・support 比較で使いやすい
`k ≤ ...` 形式の入口が明示化された。

### 16.14 `boundaryProd` と `kernelRight` の prime-power 非重複（`q ∤ d` 層）

`q^k ∣ boundaryProd x u`（`k>0`）から `kernelRight` 側の非重複を引く補題を追加した。

- `primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp`
  - `q^k ∣ boundaryProd x u` なら `¬ q ∣ kernelRight d x u`。
- `primePow_dvd_boundaryProd_not_primePow_dvd_kernelRight_of_coprime_of_not_dvd_exp`
  - 任意の `l>0` で `¬ q^l ∣ kernelRight d x u`。

証明の分岐は
`q ∣ x*u` から `q ∣ x` または `q ∣ u` を取り、
前者は既存の `q ∤ d` 非競合補題、後者は新規補題
`prime_dvd_right_not_dvd_GN_of_coprime`（`q ∣ u → ¬ q ∣ GN d x u`）で処理している。

### 16.15 非重複を `v_q` / support 比較 API（`k ≤ ...` 形）へ統合

`boundaryProd` vs `kernelRight` の非重複を、比較しやすい API に持ち上げた。

- `padicValNat_kernelRight_eq_zero_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp`
  - `0<k` かつ `k ≤ v_q(boundaryProd)` なら `v_q(kernelRight)=0`。
- `not_le_padicValNat_kernelRight_of_pos_le_padicVal_boundaryProd_of_coprime_of_not_dvd_exp`
  - 同じ前提で `¬ k ≤ v_q(kernelRight)`（`k ≤ ...` 形の直接比較）。
- `support_boundaryProd_disjoint_kernelRight_of_coprime_of_not_dvd_exp`
  - `q ∈ support(boundaryProd)` なら `q ∉ support(kernelRight)`（`q ∤ d` 層）。

これで、prime-power 非重複が
`dvd` 表現だけでなく `valuation` / `support` 比較 API として再利用可能になった。

### 16.16 例外素数（`q ∣ d`）レイヤ分離 API と最終比較定理への接続

例外素数を明示分離するため、prime-power 比較 API を 2 層に分割した。

- `PrimePowComparisonExceptionalLayer d m n`
  - `q ∣ d` 側だけで `q^k ∣ m ↔ q^k ∣ n` を要求。
- `PrimePowComparisonNonExceptionalLayer d m n`
  - `q ∤ d` 側だけで `q^k ∣ m ↔ q^k ∣ n` を要求。

この 2 層 API から、既存の最終比較系へ直接接続する橋を追加:

- `factorization_eq_of_prime_pow_dvd_iff_split_layers`
  - 2 層仮定から `m.factorization = n.factorization`。
- `unique_factorization_nat_via_split_prime_layers`
  - 2 層仮定から `m = n`。

これで、例外素数レイヤを別管理したまま
最終の factorization 比較定理へ入れる導線が明示化された。

### 16.17 `hExc` の具体供給と end-to-end 比較定理

`boundaryProd/kernelRight` の具体補題群から `hExc` を供給する接続層を追加した。

- 例外層の具体補題:
  - `prime_dvd_boundaryRight_dvd_kernelRight_of_dvd_exp`
    - `q ∣ d` かつ `q ∣ boundaryRight` なら `q ∣ kernelRight`。
  - `prime_dvd_boundaryProd_dvd_kernelRight_of_dvd_exp_of_not_dvd_boundaryLeft`
    - `q ∣ d`, `q ∣ boundaryProd`, `q ∤ boundaryLeft` から `q ∣ kernelRight`。
- 層供給 API:
  - `exceptionalLayer_of_boundaryProd_kernelRight`
  - `nonExceptionalLayer_of_boundaryProd_kernelRight`
  - それぞれ `boundaryProd/kernelRight` 由来の比較補題群を
    `PrimePowComparisonExceptionalLayer` / `PrimePowComparisonNonExceptionalLayer`
    に束ねる。
- end-to-end:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e`
    - 上記 2 層 API を受けて、最終的に `m = n` を返す。

これで、`hExc` を抽象引数のまま置かずに
`boundaryProd/kernelRight` 補題群から注入して
最終比較定理まで一気通しで接続できる形になった。
