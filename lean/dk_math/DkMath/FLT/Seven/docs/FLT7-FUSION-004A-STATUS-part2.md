# FLT7-FUSION 状況レポート — Part 2

## 概要

前回は **Part 1＝全体戦況と進捗率** でした。

ここからの **Part 2** は、実装量ではなく、

> **最新成果が、FLT7 の矛盾論理をどこまで変形・圧縮したか**

を解析します。

## 矛盾経路の論理構造分析

---

### 1. 以前の矛盾経路

FUSION-003E 直後の構造は、概念的には次でした。

```text
仮想 FLT7 反例
  ↓
real-pair cores C₀,C₁,C₂
  ↓
Norm(Cᵢ) = -quotientRoot
  ↓
quotientRoot が七乗であれば
  ↓
Cᵢ は七乗 up to unit
  ↓
整数 chart を再構築できるか？
```

しかし `quotientRoot` が七乗であるためには、

$$
c_{21},c_{22}\text{ が七乗}
$$

を証明する必要がありました。

つまり以前は、

```text
core の七乗抽出
```

へ入る前に、

```text
二つの scalar cell の七乗性
```

が門番として立っていました。

---

### 2. 003F が行った論理変換

003F は、その門番を倒したのではありません。

**門そのものを撤去しました。**

以前は、

$$
C_i\sim X_i^7
$$

を直接得ようとしていました。

現在は、

$$
C_i\sim L_{21,i}L_{22,i}R_i^7
$$

です。

ここで、

* $L_{21,i}$ は `c21` 由来の正確な load
* $L_{22,i}$ は `c22` 由来の正確な load
* $R_i^7$ は load を除いた residual seventh power

です。

つまり、

```text
core は七乗ではないかもしれない
```

という問題を、

```text
core の非七乗部分を完全に名指しする
```

問題へ変換しました。

そして名指しされた非七乗部分が、

```text
未知の unit
未知の scalar
未知の prime support
```

ではなく、canonical gcd load として完全に固定されています。

---

### 3. 「七乗抽出」の意味が変わった

以前の Branch A は、

$$
c_{21}=a^7,\qquad c_{22}=b^7
$$

を仮定して、load 全体を七乗へ吸収する方式でした。

現在の無条件 Branch B は、

$$
C_i=L_iD_i
$$

と分け、

$$
D_i\sim R_i^7
$$

を証明しています。

したがって、七乗抽出の対象が、

```text
core 全体
```

から、

```text
load-free residual core
```

へ変わりました。

これは単なる定理の弱化ではありません。

むしろ情報量は増えています。

旧 Branch A：

```text
Cᵢ は unit × 七乗
```

新 loaded form：

```text
Cᵢ は
  exact c21-prime load
  × exact c22-prime load
  × unit
  × 七乗
```

後者のほうが core の素因数構造を詳しく保存しています。

---

### 4. load は「誤差」ではなく orientation 情報

ここが今回の最重要解釈です。

`c21,c22` の load は、最初は七乗抽出を邪魔する余計な scalar mass に見えました。

しかし exact valuation と Galois splitting によって、実際には各 prime $q$ が、

```text
どの real-pair core に属するか
どの maximal ideal に属するか
何回その ideal が現れるか
```

を記録していることが判明しました。

つまり load は削除すべきノイズではなく、

$$
\boxed{\text{global orientation を復元するための住所情報}}
$$

です。

特に、

$$
v_{\mathfrak P_q}(L_i)=v_q(c)
$$

が証明されたことで、整数世界の prime-power depth が代数世界で完全に保存されています。

これは primitive chart 再構築に必要な prime ownership の基礎です。

---

### 5. 実三次世界で不足していた情報

実三次体では、七乗根 $\zeta$ と $\zeta^{-1}$ は、

$$
\zeta+\zeta^{-1}
$$

という同じ実元へ潰れます。

したがって real-pair carrier は、

$$
(R-\zeta L)(R-\zeta^{-1}L)
$$

という共役積しか見ません。

この世界では、

```text
ζ 側
ζ⁻¹ 側
```

の区別が失われています。

FUSION-003C で見えていた、

```text
binary sign × ternary phase
```

のうち、実三次 Galois は ternary phase だけを持っていました。

binary orientation が欠落していたわけです。

---

### 6. 004A が binary orientation を復元した

degree-six carrier では、

$$
F=R-\zeta L
$$

$$
\overline F=R-\zeta^{-1}L
$$

を別々の元として保持できます。

さらに、

$$
F\overline F=P_0
$$

です。

そして局所評価では、

$$
F\mapsto0
$$

$$
\overline F\mapsto\neq0
$$

となります。

共役評価では逆に、

$$
F\mapsto\neq0
$$

$$
\overline F\mapsto0
$$

です。

したがって、同じ real prime の上に、

$$
\mathfrak P,\qquad\overline{\mathfrak P}
$$

という二つの oriented prime が現れました。

これで、

```text
real-pair の unordered factor
```

が、

```text
oriented linear factor
conjugate linear factor
```

へ分裂しました。

これは primitive chart を作るために必要だった orientation 情報そのものです。

---

### 7. 3×2＝6 の実体化

現在の構造は非常に美しいです。

実三次 Galois 回転が、

$$
C_0\to C_1\to C_2\to C_0
$$

という3周期を与えます。

一方、quadratic conjugation が、

$$
\zeta\leftrightarrow\zeta^{-1}
$$

という2周期を与えます。

したがって degree-six 世界では、

$$
\boxed{3\times2=6}
$$

の六つの oriented address が自然に現れます。

これは以前の `μ₂ × μ₃` sector 分解が、単なる `ZMod 7` の分類ではなく、

```text
real cubic Galois orbit × quadratic conjugation
```

という代数的構造だったことを示しています。

魔法陣で見えていた六 sector が、ここで本物の環構造になった、と読めます。

---

### 8. 現在の矛盾鎖

現在の証明済み論理鎖は、概ね次です。

```text
仮想 FLT7 反例
  ↓
seven-primary terminal packet
  ↓
signed roots r,l
  ↓
real-pair carriers P₀,P₁,P₂
  ↓
pair cores C₀,C₁,C₂
  ↓
pairwise coprime
  ↓
Norm(Cᵢ) = -quotientRoot
  ↓
scalar cells c21,c22 の canonical gcd allocation
  ↓
Cᵢ ~ load21ᵢ · load22ᵢ · residualᵢ^7
  ↓
各 load の exact prime-ideal factorization
  ↓
degree-six carrier
  ↓
oriented factor F と conjugate factor F̄
  ↓
二つの oriented maximal ideals
```

ここまでは Lean 内で存在しています。

未完成なのは、その先です。

```text
oriented prime/factor data
  ↓
global additive factorization
  ↓
primitive integer/quadratic FLT7 chart
  ↓
strictly smaller counterexample
  ↓
minimality contradiction
```

---

### 9. 現在の reverse containment の位置付け

現在の直近停止点は、

$$
\mathfrak P\overline{\mathfrak P}
\subseteq
\mathrm{map}(\mathfrak p)
$$

です。

既に逆向き、

$$
\mathrm{map}(\mathfrak p)
\subseteq
\mathfrak P\overline{\mathfrak P}
$$

はあります。

この equality が閉じると、

$$
\mathrm{map}(\mathfrak p)=\mathfrak P\overline{\mathfrak P}
$$

となり、real prime が degree-six 世界で二つの共役 prime に正確に分裂することが固定されます。

#### 重要な判定

この obligation は、現在の最終ラスボスではありません。

これは、

```text
degree-six orientation layer の局所完成条件
```

です。

閉じれば 004A が完全完成しますが、その後も global chart reconstruction が残ります。

したがって戦況上は、

```text
局所 orientation の最後の一枚
```

であり、

```text
FLT7 矛盾の最後の一枚
```

ではありません。

---

### 10. 本当の主戦場は global additive reconstruction

現在、乗法構造は非常によく分かっています。

$$
F\overline F=P_0
$$

$$
C_i\sim L_iR_i^7
$$

$$
(L_i)=\prod_q\mathfrak P_q^{v_q(c)}
$$

という乗法的データは揃いました。

しかし Fermat 方程式は加法方程式です。

$$
x^7+y^7=z^7
$$

したがって必要なのは、

```text
prime ideal factorization
```

だけではなく、

```text
三つの oriented seventh-power factors が
どのような加法関係を満たすか
```

です。

これが `AdditiveChartFrontier` の名前の意味です。

現在は additive frontier に到達していますが、まだ additive chart は完成していません。

---

### 11. 何を再構築しなければならないか

最終的に必要なのは、概念的には次の形です。

degree-six 側の oriented data から、

$$
X',Y',Z'
$$

を作り、

$$
X'^7+Y'^7=Z'^7
$$

を得る。

さらに、

$$
\gcd(X',Y')=1
$$

$$
X'Y'Z'\neq0
$$

$$
X',Y',Z'>0
$$

を示す。

そして元の反例より小さい measure、

$$
\mu(X',Y',Z')<\mu(X,Y,Z)
$$

を証明する。

ここで初めて descent が成立します。

---

### 12. primitive chart の難しさ

primitive chart reconstruction には少なくとも三つの整合性が必要です。

#### 加法整合性

oriented factors から得た候補が、実際に Fermat 型加法式を満たすこと。

#### 整数整合性

degree-six ring の元が、必要な整数または既存 quadratic coordinate に降りること。

#### primitive 整合性

load factor を含む各成分が、互いに素な新しい triple を生成すること。

現在の exact prime ownership は、第三の primitive 整合性を支える大きな材料です。

以前は load がどこに属するか不明だったため、primitive 性を追跡できませんでした。

今回、その障害は大幅に減りました。

---

### 13. strict decrease は依然として独立の問題

仮に新しい triple が作れても、同じ大きさや大きい triple なら矛盾になりません。

必要なのは strict drop です。

現在までに構築されたものの多くは、

```text
exact identity
exact depth
exact factorization
exact valuation
```

です。

一方 strict decrease は、

```text
大小関係
正値性
well-founded measure
```

の世界です。

したがって、代数的 reconstruction が完成しても、自動的に descent が完成するわけではありません。

ここは依然として第二の大魔核です。

---

### 14. terminal branch の特殊性

既存 terminal route は $7$-primary exponent が1の枝です。

この branch では、通常型の descent seed が存在すれば valuation contradiction が生じることが、既に示唆・固定されています。

したがって最終構造はおそらく、

```text
terminal exponent = 1
  → reconstructed object の存在自体が矛盾

higher exponent
  → strict smaller counterexample を生成
```

の二分岐になります。

つまり terminal branch では「小さい反例を作る」前に、primitive reconstruction が既存 depth-one data と衝突する可能性があります。

ここは今後の重要な分岐点ですが、現時点ではまだ theorem chain になっていません。

---

### 15. 現在のリスク分布

#### 低〜中リスク

##### 共役 fibre equality

既存の maximality、comaximality、rank 2、residue cardinality から見て、有限指数または quotient cardinality の比較で閉じる可能性があります。

数学的未知度は低めです。

#### 中〜高リスク

##### additive chart reconstruction

現在の乗法 factor data を Fermat 型加法式へ戻せるか。

ここが現在もっとも重要な数学的リスクです。

### 高リスク

#### strict decrease

再構築された chart に自然な減少 measure があるか。

ここはまだ具体的な候補が十分固定されていません。

---

### 16. 大躍進をどう評価するか

今回の進歩を単に、

```text
大量の Lean ファイルが増えた
```

と見るのは不正確です。

実際には次の三つの質的転換があります。

#### 転換1

```text
unresolved scalar cells
```

から、

```text
fully allocated algebraic loads
```

へ。

#### 転換2

```text
conditional core seventh powers
```

から、

```text
unconditional loaded seventh powers
```

へ。

#### 転換3

```text
unordered real conjugate pair
```

から、

```text
concrete oriented degree-six factors
```

へ。

この三つはすべて、最終 chart reconstruction に必要な情報を増やしています。

単なる補題追加ではなく、証明モデルが更新されています。

---

### 17. 現在の達成度を二種類に分ける

一つの数字だけでは誤解を生みます。

#### 代数的分解達成度

$$
\boxed{90％\text{ 以上}}
$$

real cubic、Galois、load、valuation、degree-six orientation の局所構造は、ほぼ揃いました。

#### FLT7 矛盾達成度

$$
\boxed{約70％}
$$

primitive chart と strict decrease が未完成なので、こちらはまだ明確な距離があります。

---

## Part 2 結論

現在の DkMath FLT7 は、

> **反例の乗法的・局所的・素イデアル的構造をほぼ完全に解剖し、その情報を失わないまま degree-six oriented world へ持ち上げるところまで到達した。**

という状況です。

以前は、

```text
反例をどう分解するか
```

が問題でした。

現在は、

```text
完全に分解された oriented data を
どのように再び一つの primitive additive chart へ組み上げるか
```

が問題です。

つまり研究段階は、

```text
分解・分類フェーズ
```

から、

```text
再構築・降下フェーズ
```

へ正式に移りました。

次の Part 3 は、今回の変更を数学的 checkpoint 単位で切り分けた **PR 分割・レビュー境界の状況分析** になります。
