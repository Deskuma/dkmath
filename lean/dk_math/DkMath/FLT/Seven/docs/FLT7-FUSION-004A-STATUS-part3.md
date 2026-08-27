# FLT7-FUSION 状況レポート — Part 3

## PR 分割・レビュー境界の分析

現在の PR #73 は、当初の「FUSION reconstruction を開始する PR」という役割から大きく成長しています。

現状は Draft / open / mergeable、19 commits、62 changed files、約2万行追加です。PR 本文は依然として FUSION-001 の開始地点を中心に書かれていますが、実装はすでに FUSION-003F と FUSION-004A まで進んでいます。

したがって、この PR は現在、単なる「大きな PR」ではなく、

> **異なる数学的責務を持つ複数 checkpoint が、一つの依存鎖として積層された PR**

になっています。

---

## 1. 現在の PR に含まれる三つの数学的世界

変更内容は、自然に三つの大区分へ分かれます。

```text
A. Integer / Real-cubic fusion
B. Scalar load exact allocation
C. Degree-six orientation
```

それぞれが異なる問いに答えています。

---

### 区分 A — FUSION-001 から 003E

#### 問い

```text
RAMIFIED で得た real-cubic descent seed を、
どこまで整数・signed-root・real-pair data に戻せるか
```

#### 到達点

* signed roots
* exact gap depth
* exact quotient root
* real-pair carrier 三体
* pairwise-coprime core
* Galois orbit
* exact core norm
* 二セル routing gate

最終形は、

$$
\operatorname{Norm}(C_i)=-e
$$

および、

$$
e\text{ が符号付き七乗}
\iff
c_{21},c_{22}\text{ が自然数七乗}
$$

です。

#### この区分の論理的性格

これは **FUSION の基礎座標系の確立**です。

この層ではまだ `c21,c22` は unresolved load ですが、

```text
敵が何であるか
```

を完全に定義しています。

この区分だけでも一つの完成した研究 checkpoint です。

---

### 区分 B — FUSION-003F

#### 問い

```text
c21,c22 を七乗と証明せずに、
それらを三つの real-pair core へ正確に配れるか
```

#### 到達点

* canonical gcd load allocation
* load product の scalar cell 回収
* stripped core の無条件七乗抽出
* Galois coherence
* exact absolute norm
* quotient-prime の canonical $μ_7$ address
* maximal real-cubic kernel
* exact kernel multiplicity
* rational $q$-adic valuation との一致
* finite support 全体の exact ideal factorization
* direct signed chart の正式排除

003F の代表形は、

$$
C_i\sim L_{21,i}L_{22,i}R_i^7
$$

です。

さらに、

$$
v_{\mathfrak P_q}(L_i)=v_q(c)
$$

が成立し、load ideal 全体が有限 prime support 上の kernel power 積として再構成されています。

#### この区分の論理的性格

これは **二セル問題の完全解決層**です。

003E と 003F の境界は非常に明確です。

```text
003E:
  c21,c22 が七乗なら core 全体を七乗抽出できる

003F:
  c21,c22 が何であっても load と residual seventh power に分解できる
```

条件付きから無条件へ移る地点なので、独立 checkpoint として非常に強い境界です。

---

### 区分 C — FUSION-004A

#### 問い

```text
real-pair の unordered factor を、
degree-six 世界で oriented linear factor に分けられるか
```

#### 到達点

* concrete quadratic algebra
* 整数 rank 6
* explicit $\zeta,\zeta^{-1}$
* $\zeta^7=1$
* oriented carrier
* conjugate carrier
* exact carrier product
* canonical local evaluation
* oriented maximal ideal
* conjugate maximal ideal
* distinctness
* comaximality
* common real-cubic contraction
* rational contraction $(q)$
* residue cardinality $q$

現在の停止点は、

$$
\operatorname{map}(\mathfrak p)=\mathfrak P\overline{\mathfrak P}
$$

の逆包含だけです。

#### この区分の論理的性格

これは **新しい代数世界の導入**です。

003F までは実三次整数環が主役でした。

004A からは、

$$
\mathcal O^+\subset \mathcal O^+[\zeta]
$$

という二次拡大へ移ります。

したがってファイル数やコード量だけでなく、型・環・イデアル・共役作用の世界そのものが変わります。

これは明確に別のレビュー単位です。

---

## 2. 最も自然な三分割

数学的な checkpoint として最も自然なのは、次の三分割です。

| レビュー単位           | 数学的内容       | 終端 theorem                     |
| ---------------------- | ---------------- | -------------------------------- |
| FUSION Core            | FUSION-001〜003E | exact norm / two-cell gate       |
| Prime-Load Lift        | FUSION-003F      | unconditional loaded power split |
| Degree-Six Orientation | FUSION-004A      | conjugate prime-pair packet      |

---

### PR-A 相当 — FUSION Core

概念的終端は、

```text
three pairwise-coprime real-pair cores
exact Galois orbit
Norm(Cᵢ) = -quotientRoot
two-cell iff gate
```

です。

主要なレビュー観点は、

* signed-root provenance
* theta-depth
* Galois unit orientation
* norm の符号
* pairwise coprimality
* routing cell の意味

です。

これは「実三次 core を正しく作れたか」というレビューになります。

---

## PR-B 相当 — Prime-Load Lift

概念的終端は、

```text
RealPairLoadedPowerSplit
exact load norms
exact q-adic kernel multiplicities
global load ideal factorization
```

です。

主要なレビュー観点は、

* gcd projection の妥当性
* Associated の向き
* integral quotient
* load cancellation
* pairwise coprime residual
* PID seventh-power extraction
* ideal divisibility
* ideal norm
* prime-power multiplicity

です。

これは「二セル scalar information を損失なく algebraic load に変換できたか」というレビューになります。

---

## PR-C 相当 — Degree-Six Orientation

概念的終端は、

```text
concrete rank-six carrier
oriented and conjugate factors
two distinct conjugate maximal ideals
common contraction
explicit remaining fibre obligation
```

です。

主要なレビュー観点は、

* quadratic algebra の定義
* $\zeta$ の関係式
* primitive seventh root
* rank 6 coordinates
* evaluation hom
* star conjugation
* maximality
* comaximality
* contraction
* residue cardinality
* fibre-product inclusion

です。

これは「実三次 pair を degree-six oriented factor へ正しく分離できたか」というレビューになります。

---

## 3. なぜ 003E と 003F は分けやすいのか

003E の最後には明確な theorem boundary があります。

$$
e\text{ が七乗}
\iff
c_{21},c_{22}\text{ が七乗}
$$

003F はこの theorem を壊したり書き換えたりせず、その上に新しい一般化を置いています。

$$
C_i\sim L_{21,i}L_{22,i}R_i^7
$$

旧 Branch A も、003F の loaded split から特殊場合として再回収されています。

したがって依存関係は、

```text
003E theorem
  ↓
003F general loaded theorem
  ↓
003E Branch A recovery
```

です。

これは非常に健全な層構造です。

003F は003Eを置換しているのではなく、003Eを一般化し、旧結果を corollary にしています。

---

## 4. なぜ exact valuation は 003F 側なのか

exact valuation と global factorization は、004A の degree-six carrier より前に成立しています。

対象は実三次整数環上の、

```text
evalKernel
realPairLoad
scalar routing cell
```

です。

三つの real-cubic Galois kernel が $(q)$ を完全分解し、

$$
\mathrm{evalKernelMultiplicity}
===============================

\mathrm{padicValNat}(q,\mathrm{cell})
$$

を得ています。

degree-six orientation を使わなくても成立するため、これは003Fの完結部です。

数学的には、

```text
real cubic prime routing の完成
```

であり、

```text
degree-six oriented splitting
```

ではありません。

---

## 5. なぜ 004A は独立性が高いのか

004A では新しい型、

```lean
SevenCyclotomicDegreeSixInt.Ring
```

が登場します。

これは、

```lean
QuadraticAlgebra SevenRealCubicInt (-1) (alpha - 1)
```

として構成され、実三次環上 rank 2、整数上 rank 6 を持ちます。

この時点でレビュー対象は、

* 実三次整数環の theorem
* quadratic algebra の演算
* star conjugation
* extension / contraction of ideals

へ変わります。

つまりレビューに必要な数学的文脈が異なります。

003F の PID gcd proof と、004A の quadratic fibre proof を同時に読むことは可能ですが、同じ誤りモデルでは監査できません。

---

## 6. 現 PR のレビュー上の危険

現在の PR は数学的には整然としています。

しかしレビュー視点では、三つの危険があります。

## 危険1 — 重要 theorem がコード量に埋もれる

今回の差分には、たとえば、

```lean
associated_gcd_three_of_dvd_product
nonempty_realPairLoadedPowerSplit
evalKernelMultiplicity_eq_padicValNat_addressedCell
globalLoadFactorIdeal_eq_span_load
cyclotomicDegreeSixCarrier_mul_conj
```

という、それぞれ一つの checkpoint を代表できる theorem が並んでいます。

これらを一つの PR で同時に見ると、各 theorem の重要度が差分量の中で均質化されます。

本来はそれぞれ、

```text
新しい数学的段階を開いた theorem
```

です。

---

## 危険2 — 一つの問題が別層の問題に見える

たとえば現在残っている reverse fibre containment は004A固有の obligation です。

しかし巨大 PR 全体を見れば、

```text
FLT7 全体が未完成だから残っている
```

ように見えます。

実際には、

```text
003F は完成
004A は局所的に一包含だけ未完成
primitive chart は次段階
```

と分ける必要があります。

層を分けないと、完成した部分まで「進行中」に見えてしまいます。

---

## 危険3 — rollback boundary が曖昧になる

仮に degree-six quadratic algebra の設計を後で変更しても、

* 003F load allocation
* exact valuation
* global real-cubic factorization

は独立に保存できます。

しかし一つの PR に積層されると、degree-six 設計変更が FUSION 全体の巻き戻しに見えます。

数学的依存は、

```text
003E
  ↓
003F
  ↓
004A
```

ですが、設計変更可能性は、

```text
003E stable
003F stable
004A experimental frontier
```

です。

---

## 7. 文書も三つの役割に分かれている

現在の文書は実際に、

* 003E 指示書
* 003F report
* 004A report
* README
* STATUS
* ROADMAP

という形に分かれています。

003F report は Events 1–10 の完了と exact boundary を明記しています。

004A report は degree-six orientation と一つの remaining obligation を明記しています。

つまりドキュメント構造は、既に PR 分割可能な checkpoint を自然に示しています。

コードだけが一つの PR に連続して積まれている状態です。

---

## 8. 現 PR の数学的完成度

PR #73 全体を一つとして判定すると、

```text
completed foundational phases
  +
completed load phase
  +
nearly completed orientation phase
  +
unstarted primitive reconstruction phase
```

が混在しています。

そのため「PR完成度」を単一数字で表すのは難しいです。

| 部分                                   |    完成度 |
| -------------------------------------- | --------: |
| FUSION-001〜003E                       |      100% |
| FUSION-003F core/load                  |      100% |
| exact valuation / global factorization |      100% |
| FUSION-004A carrier                    |       95% |
| FUSION-004A fibre equality             | 約70〜80% |
| primitive chart                        |    未完成 |
| strict decrease                        |    未完成 |

PR全体を当初のロードマップ終端である descent closure まで含むものとして見ると未完成です。

しかし checkpoint PR の集合として見ると、**既に二つの完成 PRと、一つのほぼ完成 PRが中に存在しています。**

---

## 9. 最も安定した境界

現在最も安定している境界は、次です。

```text
Stable boundary 1:
  FUSION-003E completed

Stable boundary 2:
  FUSION-003F + exact real-cubic load factorization completed

Active frontier:
  FUSION-004A reverse fibre containment
```

`ConjugatePrimeFiberProductEqualityObligation` が explicit Prop として残されているため、004A の未完成部分も隠れていません。

これは非常に良い状態です。

未完成 theorem が既存 packet の内部仮定として混入しておらず、明示された frontier obligation として外側にあります。

---

## 10. PR分割によって何が変わるか

分割はコード品質を上げるためだけではありません。

数学的には、次の読み方が可能になります。

### 第一冊

```text
From ramified algebra to exact real-pair cores
```

### 第二冊

```text
From scalar routing cells to exact algebraic prime loads
```

### 第三冊

```text
From real conjugate pairs to oriented degree-six factors
```

これらは、それぞれ独立した論文節に近い内容です。

一つの PR に置くと「一つの巨大証明途中」に見えますが、分けると、

```text
三つの完成した構造定理
```

として認識できます。

---

## 11. 現時点でのレビュー順序

状況分析として、自然な論理順は明白です。

```text
1. 003E real-pair core foundation
2. 003F load allocation and exact valuation
3. 004A degree-six orientation
```

この順序以外で読むと、004A の oriented prime が何を orient しているのか分からなくなります。

特に004A の二つの maximal ideal は、003F で得た canonical quotient-prime ratio address を延長しています。

したがって004Aは003Fの局所 address layerに意味的に依存しています。

---

## 12. 現在の PR は失敗しているか

いいえ。

巨大化は「設計失敗」ではありません。

今回の PR は、研究が予測以上に連続して成功したために肥大化しています。

```text
FUSION-003E の gate
```

を調べていたところ、

```text
003F loaded split
exact valuation
global ideal factorization
degree-six carrier
conjugate primes
```

まで自然に一本道で進みました。

つまり肥大化の原因は、

```text
責務を考えずに機能を追加した
```

ことではなく、

```text
一つの数学的発見が次の発見を連続的に解放した
```

ことです。

研究 PR としては自然な成長です。

---

## 13. 現在の最重要認識

PR #73 を、

```text
まだ FLT7 が証明できていない巨大な未完成 PR
```

と見るのは不正確です。

正しくは、

```text
FUSION基礎：完成
Prime-load lift：完成
Degree-six orientation：ほぼ完成
Primitive reconstruction：次フェーズ
```

です。

PR の UI 上は一つでも、数学的 checkpoint はすでに複数完了しています。

---

## Part 3 結論

現在の PR #73 の内部には、次の三つの明確な研究成果があります。

```text
I. Real-pair core theorem layer
II. Exact prime-load allocation theorem layer
III. Concrete degree-six orientation theorem layer
```

そのうち、

* I は完成
* II は完成
* III は局所 fibre equality 一件を除き完成域

です。

したがって、現在の状態を最も正確に表現すると、

> **一つの未完成巨大PRではなく、二つの完成 checkpoint と、一つの active frontier checkpoint が連結された研究系列である。**

となります。

次の Part 4 は、PR構造ではなく、**現在完成した定理群が数学的に何を新しく証明しているのかを、既知数学用語へ翻訳する分析**になります。
