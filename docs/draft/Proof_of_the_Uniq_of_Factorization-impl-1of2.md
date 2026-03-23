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

### 16.18 `hExcBK/hNonExcBK` の自動供給縮約（valuation 等式ベース）

`hExcBK` / `hNonExcBK` を直接仮定せず、`v_q` 等式から自動供給する補題群を追加した。

- `exceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight`
  - 例外層（`q ∣ d`）で
    `v_q(boundaryProd)=v_q(kernelRight)` から
    `q^k ∣ boundaryProd ↔ q^k ∣ kernelRight` を自動生成。
- `nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight`
  - 非例外層（`q ∤ d`）の同型。
- `exceptionalLayer_of_boundaryProd_kernelRight_autoBK`
- `nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK`
  - それぞれ `hExcBK` / `hNonExcBK` を内部生成して層 API を構成。
- `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK`
  - `hExcBK/hNonExcBK` を要求しない end-to-end 版。

これにより、比較仮定は
「prime-power 同値そのもの」から
「層別 valuation 等式」へ縮約され、実データ供給が軽くなった。

### 16.19 `hExcBK/hNonExcBK` の追加縮約（`<=` / 0 化ベース）

`hExcBK` / `hNonExcBK` をさらに軽い形で供給できるよう、次の縮約を追加した。

- 例外層（`q ∣ d`）:
  - `exceptionalBK_fwd_of_padicValNat_le_boundaryProd_kernelRight`
    - `v_q(boundaryProd) ≤ v_q(kernelRight)` から
      `q^k ∣ boundaryProd -> q^k ∣ kernelRight`。
  - `exceptionalBK_rev_of_padicValNat_le_kernelRight_boundaryProd`
    - 逆向き不等式から逆向き含意。
  - `exceptionalBK_of_padicValNat_le_le_boundaryProd_kernelRight`
    - 両向き `≤` から `q^k` 同値を生成。
- 非例外層（`q ∤ d`）:
  - `nonExceptionalBK_of_padicValNat_eq_zero_boundaryProd_kernelRight`
    - `v_q(boundaryProd)=0 ∧ v_q(kernelRight)=0` から
      `q^k` 同値を生成。
- 層 API への注入:
  - `exceptionalLayer_of_boundaryProd_kernelRight_autoBK_le`
  - `nonExceptionalLayer_of_boundaryProd_kernelRight_autoBK_zero`
- end-to-end:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoBK_le_zero`
    - 例外層は `≤`（両向き）、非例外層は 0 化で与えれば `m = n` へ到達。

これで `hExcBK/hNonExcBK` の供給窓は
1) valuation 等式版 と 2) `<=`/0 化版 の 2 系統になり、
実データ側の前提整備に応じて選べるようになった。

### 16.20 `hExcLe/hExcLeRev/hNonExcZero` の自動導出（GN concrete chain）

`hExcLe` / `hExcLeRev` / `hNonExcZero` を直接仮定せず、
GN 側の具体補題から自動構成する導線を追加した。

- 例外層の導出:
  - `exceptionalLe_of_padicValNat_eq_boundaryProd_kernelRight`
  - `exceptionalLeRev_of_padicValNat_eq_boundaryProd_kernelRight`
  - `hExcVal`（valuation 等式）から `hExcLe` / `hExcLeRev` を自動生成。
- 非例外層の導出:
  - `nonExceptionalNotDvd_boundaryProd_of_not_dvd_boundarySides`
    - `boundaryRight`/`boundaryLeft` の `¬dvd` から `boundaryProd` の `¬dvd` を構成。
  - `nonExceptionalZero_of_not_dvd_boundaryProd_and_kernelRight`
    - `boundaryProd`/`kernelRight` の具体 `¬dvd` から `hNonExcZero` を生成。
- end-to-end 追加:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal`
    - 上記自動導出を内部で使って `m = n` へ接続。

この追加で、呼び出し側は `hExcLe/hExcLeRev/hNonExcZero` を手で組み立てず、
より concrete な GN 側補題（valuation 等式・prime `¬dvd`）を与えればよくなった。

### 16.21 非例外層 `kernelRight` 側 `¬dvd` / 0化の弱化 chain 拡張

非例外層で `kernelRight` 側 `¬dvd` を直接要求していた部分を、
より弱い仮定から供給できる chain を追加した。

- 追加補題:
  - `nonExceptionalNotDvd_kernelRight_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd`
    - 仮定:
      - `v_q(kernelRight) ≤ v_q(boundaryProd)`
      - `¬ q ∣ boundaryProd`
    - 結論:
      - `¬ q ∣ kernelRight`
  - `nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundaryProd`
    - 上の条件から `v_q(boundaryProd)=0 ∧ v_q(kernelRight)=0` を生成。
  - `nonExceptionalZero_of_padicValNat_le_boundaryProd_and_not_dvd_boundarySides`
    - `boundaryRight/Left` 側 `¬dvd` から `¬ q ∣ boundaryProd` を自動生成して接続。
- end-to-end 弱化 wrapper:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_split_layers_e2e_autoGNVal_weakKernel`
    - `hNonExcNotDvdKernelRight` 直接仮定を除去し、
      `hNonExcLeRev + hNonExcNotDvdBoundaryProd` に置換。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundarySides`
    - さらに `hNonExcNotDvdBoundaryProd` も除去し、
      `boundaryRight/Left` 側 `¬dvd` 入力から自動供給。

これで非例外層の `kernelRight` 側は、
「直接 `¬dvd` を与える」から
「valuation 比較 + 境界側 `¬dvd` で導出する」へ弱化できた。

### 16.22 `hNonExcLeRev` の自動供給（prime-power chain 入力）

次段として、`hNonExcLeRev` 自体を直接与えず、
非例外層の kernel→boundary prime-power 連鎖（`k>0`）から導出する補題を追加した。

- 追加補題:
  - `nonExceptionalLeRev_of_primePow_kernelRight_to_boundaryProd`
    - 仮定:
      - `∀ q k, q` prime, `q ∤ d`, `0<k`,
        `q^k ∣ kernelRight -> q^k ∣ boundaryProd`
    - 結論:
      - `hNonExcLeRev`（`v_q(kernelRight) ≤ v_q(boundaryProd)`）
- end-to-end wrapper:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_boundarySides`
    - 上記 prime-power chain から `hNonExcLeRev` を内部生成し、
      既存の weakKernel/boundarySides ルートへ接続して `m = n` を返す。

これで非例外層は、
`prime-power` chain -> `hNonExcLeRev` -> `hNonExcZero` -> end-to-end
の接続が可能になった。

### 16.23 `hNonExcPowRev` の concrete wrapper 追加（GN 既存比較補題から生成）

`hNonExcPowRev` を手で与えず、既存の非例外層比較補題から抽出する wrapper を追加した。

- 追加補題:
  - `nonExceptionalPowRev_of_nonExceptionalBK`
    - 非例外層の `hNonExcBK`（`boundaryProd ↔ kernelRight`）から
      kernel→boundary の `q^k` 連鎖を抽出。
  - `nonExceptionalPowRev_of_padicValNat_eq_boundaryProd_kernelRight`
    - `hNonExcVal`（valuation 等式）を
      `nonExceptionalBK_of_padicValNat_eq_boundaryProd_kernelRight`
      で `hNonExcBK` 化し、上記抽出へ接続。
- end-to-end wrapper:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_powChain_from_nonExcVal`
    - `hNonExcVal` から `hNonExcPowRev` を内部生成し、
      既存の `...powChain_boundarySides` ルートに接続。

これで `hNonExcPowRev` は、
GN 側既存比較補題（`hNonExcBK` / `hNonExcVal` 系）から
具体的に供給できるようになった。

### 16.24 `hNonExcNotDvdRight/Left` の boundary-side 自動供給 wrapper 強化

`hNonExcNotDvdRight/Left` を手で与えず、GN 側既存補題から供給する導線を追加した。

- 追加補題:
  - `nonExceptionalNotDvd_boundaryProd_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
    - `hNonExcBK`（`boundaryProd ↔ kernelRight`）と
      `primePow_dvd_boundaryProd_not_dvd_kernelRight_of_coprime_of_not_dvd_exp`
      を組み合わせて、非例外層の `¬ q ∣ boundaryProd` を導出。
  - `nonExceptionalNotDvd_boundarySides_of_not_dvd_boundaryProd`
    - `¬ q ∣ boundaryProd` から `¬ q ∣ boundaryRight/Left` を抽出。
  - `nonExceptionalNotDvd_boundarySides_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
    - 上の 2 段を合成して `hNonExcNotDvdRight/Left` を供給。
  - `nonExceptionalNotDvd_boundarySides_from_nonExcVal`
    - `hNonExcVal` を `hNonExcBK` 化して同じ chain に接続。
- end-to-end wrapper:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundarySides`
    - `hNonExcVal` と `Nat.Coprime x u` から `hNonExcNotDvdRight/Left` を内部生成し、
      既存の `...powChain_from_nonExcVal` へ接続して `m = n` を返す。

これで boundary-side 入力は、
GN 側比較補題と非重複補題から自動供給できるようになった。

### 16.25 `hNonExcNotDvdBoundaryProd` の入力形整理（`hNonExcVal` / `hNonExcBK` 直結）

`hNonExcNotDvdBoundaryProd` 側も、`hNonExcVal` / `hNonExcBK` から
直接使える形へ整理した。

- 追加補題:
  - `nonExceptionalNotDvd_boundaryProd_from_nonExcBK`
    - 既存の
      `nonExceptionalNotDvd_boundaryProd_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
      への短名 wrapper。
  - `nonExceptionalNotDvd_boundaryProd_from_nonExcVal`
    - `hNonExcVal` を `hNonExcBK` 化して
      `hNonExcNotDvdBoundaryProd` を直接供給。
- end-to-end wrapper:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryProd`
    - `hNonExcBK` から `hNonExcPowRev -> hNonExcLeRev` と
      `hNonExcNotDvdBoundaryProd` を内部生成し、
      `...split_layers_e2e_autoGNVal_weakKernel` へ接続。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryProd`
    - `hNonExcVal` から
      `hNonExcLeRev`（等式から）と
      `hNonExcNotDvdBoundaryProd`（上記 wrapper）を生成し、
      同じ weakKernel 入口へ接続。

これで非例外層の `boundaryProd` 側非除法は、
`hNonExcVal` / `hNonExcBK` から直接供給できる API になった。

### 16.26 `boundaryProd / boundarySides` 入口の統一 facade

最終 e2e で、非例外層の境界入口を
`boundaryProd` / `boundarySides` の二系統から一つに統一した。

- 追加定義:
  - `NonExceptionalBoundaryEntrance d x u`
    - `hNonExcNotDvdBoundaryProd` 直入力
      または
      `hNonExcNotDvdRight/Left` 入力
      のどちらかを受ける facade 型。
- 追加補題:
  - `nonExceptionalNotDvd_boundaryProd_of_boundaryEntrance`
    - facade 入力を常に `hNonExcNotDvdBoundaryProd` へ正規化。
- 追加 e2e:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_weakKernel_boundaryFacade`
    - weakKernel 入口で facade を直接受ける統一版。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryFacade`
    - `hNonExcVal` から `hNonExcLeRev` を作って上記へ接続。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryFacade`
    - `hNonExcBK` から `hNonExcLeRev` を作って上記へ接続。

これで呼び出し側は、非例外層境界の入力形を
`boundaryProd` / `boundarySides` のどちらで持っていても、
同じ facade API に渡せるようになった。

### 16.27 facade 基準での旧 wrapper 群の thin 化（段階 1）

既存公開名を維持したまま、内部実装を facade 委譲に寄せた。

- 追加補助:
  - `nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd`
  - `nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides`
  - 入口値を作るだけの薄い constructor を用意。
- 置換（thin wrapper 化）:
  - `nonExceptionalNotDvd_boundarySides_of_nonExceptionalBK_of_coprime_of_not_dvd_exp`
    - 直接導出から `nonExceptionalNotDvd_boundaryProd_from_nonExcBK` 経由へ整理。
  - `nonExceptionalNotDvd_boundarySides_from_nonExcVal`
    - `hNonExcVal` から一旦 `hNonExcNotDvdBoundaryProd` を作って
      `boundarySides` を再構成する形に整理。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundarySides`
    - 旧ルート（`...powChain_from_nonExcVal`）呼び出しから
      `...nonExcVal_boundaryFacade` 呼び出しへ置換。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcBK_boundaryProd`
    - `...nonExcBK_boundaryFacade` への委譲へ置換。
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcVal_boundaryProd`
    - `...nonExcVal_boundaryFacade` への委譲へ置換。

これで旧 wrapper 群は、段階的に facade 入口を中心にした薄い互換層へ移行し始めた。

### 16.28 `weakKernel_boundarySides` / `powChain_boundarySides` の facade 中心化（再配置）

`boundarySides` 系の旧入口も facade 中心へ揃えるため、
依存順を保ちながらコア定理を前段へ置く再配置を行った。

- 追加:
  - `unique_factorization_nat_e2e_autoGNVal_weakKernel_boundaryFacade_core`
    - `NonExceptionalBoundaryEntrance` を直接受ける共通コア。
- 薄化:
  - `..._weakKernel_boundarySides`
    - `boundaryRight/Left` 入力から facade constructor
      `nonExceptionalBoundaryEntrance_of_not_dvd_boundarySides`
      で入口値を作り、上記コアへ委譲。
  - `..._weakKernel_boundaryFacade`
    - 本体を上記コアへの委譲に統一。
  - `..._powChain_boundarySides`
    - `hNonExcLeRev` 生成後に `boundarySides` を facade 化し、
      同じコアへ接続。

これで `boundarySides` 入口の実装本体も、facade 中心の一本化ルートへ揃った。

### 16.29 現在地の整理（完全自動 e2e に対する進捗）

ここで本来目的に対する現在地を明示する。

- 完了済み:
  - `∀ p k` 型（prime-power 判定）から `m = n` を導く核定理。
  - 例外層/非例外層の 2 層 API から核定理へ接続する橋。
  - 非例外層境界入力（`boundaryProd` / `boundarySides`）の facade 統一と thin 化。
- 未完（完全自動 e2e の残差）:
  - `hExcM / hExcK` の自動供給を GN 実データから閉じる導線。
  - `hNonExcM / hNonExcK` の自動供給を GN 実データから閉じる導線。
  - 最終的に `d, x, u, m, n`（+最小限の整合前提）のみで `m = n` へ到達する一本化 API。
- 実装の詰め方（次段）:
  - 段 A: 例外層の `m/n` 側比較入力（`hExcM/hExcK`）の concrete wrapper 化。
  - 段 B: 非例外層の `m/n` 側比較入力（`hNonExcM/hNonExcK`）の concrete wrapper 化。
  - 段 C: A/B を facade 最終入口へ束ね、旧 e2e を互換 thin wrapper に寄せる。

要点として、理論コアは完成しており、残りは「入力供給層の閉じ込み」である。

### 16.30 段 A: 例外層 `hExcM/hExcK` の concrete 自動供給 wrapper を追加

段 A の最初として、例外層の `m/n` 側入力を valuation 等式から自動供給する
wrapper 群を実装した。

- 追加（汎用）:
  - `exceptionalPowComparison_of_padicValNat_eq`
    - `q ∣ d` 上の `v_q(a)=v_q(b)` を
      `q^k ∣ a ↔ q^k ∣ b`（全 `k`）へ持ち上げる共通補題。
- 追加（concrete 供給）:
  - `exceptionalM_of_padicValNat_eq_m_boundaryProd`
    - `hExcMVal : v_q(m)=v_q(boundaryProd x u)` から
      `hExcM` を自動供給。
  - `exceptionalK_of_padicValNat_eq_n_kernelRight`
    - `hExcKVal : v_q(n)=v_q(kernelRight d x u)` から
      `hExcK` を自動供給。
- 追加（e2e 接続）:
  - `unique_factorization_nat_e2e_autoGNVal_nonExcVal_boundaryFacade_autoExcMK`
  - `unique_factorization_nat_e2e_autoGNVal_nonExcBK_boundaryFacade_autoExcMK`
  - いずれも `hExcM/hExcK` を内部生成し、既存 facade e2e へ委譲。

これで段 A は「設計開始」から一歩進み、例外層入力の concrete 自動供給ルートが
実装として成立した。次は段 B（非例外層 `hNonExcM/hNonExcK` の同型自動供給）を詰める。

### 16.31 段 B: 非例外層 `hNonExcM/hNonExcK` の concrete 自動供給 wrapper を追加

段 B として、非例外層の `m/n` 側入力も valuation 等式から自動供給できるようにした。

- 追加（汎用）:
  - `nonExceptionalPowComparison_of_padicValNat_eq`
    - `q ∤ d` 上の `v_q(a)=v_q(b)` を
      `q^k ∣ a ↔ q^k ∣ b`（全 `k`）へ持ち上げる共通補題。
- 追加（concrete 供給）:
  - `nonExceptionalM_of_padicValNat_eq_m_boundaryProd`
    - `hNonExcMVal : v_q(m)=v_q(boundaryProd x u)` から
      `hNonExcM` を自動供給。
  - `nonExceptionalK_of_padicValNat_eq_n_kernelRight`
    - `hNonExcKVal : v_q(n)=v_q(kernelRight d x u)` から
      `hNonExcK` を自動供給。
- 追加（e2e 接続）:
  - `unique_factorization_nat_e2e_autoGNVal_nonExcVal_boundaryFacade_autoExcNonExcMK`
  - `unique_factorization_nat_e2e_autoGNVal_nonExcBK_boundaryFacade_autoExcNonExcMK`
  - いずれも段 A の `autoExcMK` 入口を再利用しつつ、
    `hNonExcM/hNonExcK` を内部生成して接続。

これで A/B の両方で `m/n` 側比較入力の concrete 自動供給が揃った。
次段（段 C）は、A/B を束ねた最終 facade 入口の一本化と旧 wrapper 群の更なる thin 化。

### 16.32 段 C: A/B を束ねた最終 facade 入口を追加

段 C として、段 A/B の分岐（`hNonExcVal` 入口か `hNonExcBK` 入口か）を
単一 facade に吸収する最終入口を追加した。

- 追加（facade 型）:
  - `NonExceptionalBridgeEntrance`
    - `hNonExcVal` または `hNonExcBK` を `Or` で統一。
  - constructor:
    - `nonExceptionalBridgeEntrance_of_nonExcVal`
    - `nonExceptionalBridgeEntrance_of_nonExcBK`
- 追加（最終 e2e 入口）:
  - `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`
  - 入力:
    - 段 A/B の valuation concrete 入力（`hExcMVal/hExcKVal/hNonExcMVal/hNonExcKVal`）
    - `hNonExcBridge : NonExceptionalBridgeEntrance d x u`
    - `hNonExcBoundary : NonExceptionalBoundaryEntrance d x u`
  - 内部:
    - `hNonExcBridge` を分解し、段 B の
      `...nonExcVal...autoExcNonExcMK` / `...nonExcBK...autoExcNonExcMK`
      へ委譲。

これで最終 API は、非例外層 bridge 入力と boundary 入力の両方で facade 統一され、
段 A/B の実装を 1 つの入口から呼べる形になった。

### 16.33 段 C-2: 旧 wrapper 群の thin 化（`nonExcFacade_boundaryFacade` 中心）

段 C の次段として、旧 wrapper の本体ロジックを新入口へ段階的に寄せた。

- 追加（中間統一入口）:
  - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcFacade_boundaryFacade`
  - 役割:
    - `hNonExcVal` / `hNonExcBK` の分岐を
      `NonExceptionalBridgeEntrance` で一本化。
    - 既存 `...nonExcVal_boundaryFacade` / `...nonExcBK_boundaryFacade` へ委譲。
- 置換（thin wrapper 化）:
  - `...nonExcVal_boundarySides`
  - `...nonExcBK_boundaryProd`
  - `...nonExcVal_boundaryProd`
  - 上記 3 本は、`hNonExcBoundary` 生成後に
    `hNonExcBridge`（Val/BK facade）を作って
    `...nonExcFacade_boundaryFacade` へ委譲する形に整理。

これで旧 wrapper 群の一部は、公開シグネチャを維持したまま
新 facade 入口中心の薄い互換層へ移行した。

### 16.34 段 C-3: A/B 旧 wrapper の委譲化（第2段）

残る A/B 系 wrapper も、同じ facade 入口へ段階的に寄せた。

- 追加（共通入口）:
  - `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcMK`
  - 役割:
    - 例外層 `hExcM/hExcK` を valuation から自動生成。
    - 非例外層は `hNonExcBridge : NonExceptionalBridgeEntrance` で統一受理。
    - 下位の
      `...via_boundaryProd_kernelRight...nonExcFacade_boundaryFacade`
      へ委譲。
- 置換（thin wrapper 化）:
  - `unique_factorization_nat_e2e_autoGNVal_nonExcVal_boundaryFacade_autoExcMK`
  - `unique_factorization_nat_e2e_autoGNVal_nonExcBK_boundaryFacade_autoExcMK`
  - `unique_factorization_nat_e2e_autoGNVal_nonExcVal_boundaryFacade_autoExcNonExcMK`
  - `unique_factorization_nat_e2e_autoGNVal_nonExcBK_boundaryFacade_autoExcNonExcMK`
  - 上記 4 本は branch-specific 本体を縮退し、
    `hNonExcBridge` を構築して共通入口へ委譲する形に整理。

これで A/B 系の旧 wrapper も、段階的に
`...nonExcFacade_boundaryFacade...` 中心の薄い互換層へ揃った。

### 16.35 `compat/thin` ラベル付けと最終推奨入口の導線整理

互換維持のため残す wrapper 群に `compat/thin` を明示し、
「新規実装でどこを呼ぶべきか」を固定した。

- コード内ラベル方針:
  - 旧公開名で残す wrapper の docstring 先頭に
    ``[compat/thin]`` を付与。
  - 併せて「新規コードではどの facade 入口を使うべきか」を追記。
  - 最終入口には ``[recommended]`` を付与。
- 最終推奨入口（完全 concrete 版）:
  - `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`
  - これを「A/B/C を束ねた最終推奨入口」とする。
- 準推奨入口（入力が一部高レベルの場合）:
  - 例外層だけ concrete の場合:
    - `unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcMK`
  - `m/n` 側 prime-power 比較を既に持つ場合:
    - `unique_factorization_nat_via_boundaryProd_kernelRight_e2e_autoGNVal_nonExcFacade_boundaryFacade`

これで「互換 API は残すが新規呼び出しは推奨入口へ」という導線が
コードと文書の両方で一致した。
