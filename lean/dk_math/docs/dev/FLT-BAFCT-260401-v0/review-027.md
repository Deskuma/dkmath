# Memo 027: GNReducedGap の構造分析のまとめと戦況判断

## 1. 今回、Lean 上で **本当に** 前進したところ

これはかなり良い前進じゃ。
まず、`TriominoCosmicBranchADescentChain.lean` に §20 と §21 が追加され、`gnGeomSum₂Representation` の `sorry` が消え、さらに `descentSizeReduction` と `gnAtZero` が formal theorem として入った。少なくとも **このファイル内部では、q-adic 構造と descent の骨格がずいぶん clean に整理された** と見てよい。

特に `gnGeomSum₂Representation` が通ったのは大きい。
これで

$$
GN(p,z-y,y)=\sum_{i=0}^{p-1} z^i y^{p-1-i}
$$

という幾何和表示が、単なる気分ではなく Lean の橋として固定された。これは後で cyclotomic 的解釈と自然数側の計算を往復する基盤になる。

また `gnAtZero` により、固定 gap に対して

$$
GN(p,\text{gap},0)=\text{gap}^{p-1}
$$

が押さえられ、そこからログでも使っている最小下界

$$
GN \ge \text{gap}^{p-1}
$$

の土台が立った。`descentSizeReduction` も、descent existence さえ出れば (z' < z) は自動という部分を formal に閉じておる。
つまり今は、 **「サイズ減少」ではなく「存在性」だけが真の open kernel** だと、コード上でもかなり明確になったわけじゃ。

## 2. 今回の数値実験が本当に教えてくれたこと

ぬしの Python 実験で一番価値が高いのは、**Hensel 側はかなり素直に動くが、それだけでは矛盾が出ない** と見えた点じゃ。

(p=5, q=11) で、(\Phi_5) の根が mod (11^5) に一意に持ち上がり、
(R_j-1) の (11)-進付値が全部 (0) なので (q\nmid \text{gap}) と両立している。これは **q-adic root branch 自体は健全** だと示しておる。

しかも multi-prime の CRT 相互作用も、少なくとも (q_1=11, q_2=31) では 16 通り全部が両立しており、**単純な CRT 衝突だけでは潰れない** ことも見えた。
これは大事じゃ。局所条件を 2 つ 3 つ重ねればすぐ死ぬ、という甘い話ではない。

もう一つ良い観察は、(p=5) で

$$
s \ge 125,t^4
$$

という下界が、数値実験でも自然に現れていることじゃ。
これは `gnAtZero` と噛み合っており、normal form 側のサイズ拘束がかなり強いことを示しておる。だが同時に、**強い下界だけではまだ contradiction にならぬ** ことも示しておる。

## 3. 今回の一番大事な戦況判断

ここが肝じゃ。

### 3.1. 良い知らせ

§20 の整理で、GNReducedGap の中身が

* Level 0. `QAdicResidue`
* Level 1. `SuperWieferichCongruence`
* Level 2. `QAdicDescentExistence`

と三層に裂けたのは、とても良い。
特に Level 0 と 1 は「局所 q-adic 構造」で、Level 2 だけが **局所から整数解へ降りる gap** と明示された。これは open kernel の位置を正しく言い当てておる。

### 3.2. 注意点

しかし、ここから

> Hensel lift がある
> だから descent がある

とは全く言えぬ。
ぬしのログ自身が、それは **local-global gap** だと書いておるし、数値実験でも simple residue / CRT では崩れぬと出ておる。ここを取り違えると過大評価になる。  

### 3.3. つまり何が open か

いま open なのは、要するに

$$
\exists z' \in \mathbb{N},\qquad z'^p=(x/q)^p+y^p
$$

という **整数としての descent existence** じゃ。
ぬしのログもこれを

> The open kernel is EXACTLY: can each descent step be taken?

と総括しておる。
この読みはかなり正しい。

## 4. 「Kummer 的だが elementary にしたい」という方向性の評価

`kummer_descent_elementary.py` の方向は、かなり筋が良い。
特に、

* (GN = \prod (z-\zeta^j y)) という cyclotomic product
* primitive (q) に対して valuation が 1 因子に集中する
* その先に、各差 ( \omega^{j_0}-\omega^j ) が (p)-乗剰余である必要があるのではないか

という流れは、**「valuation だけでなく unit / residue 側の obstruction が必要」** という Kummer の本質に近い。

そして出力を見ると、(q=11,31,41) で、各 (j_0) に対して
((\omega^{j_0}-\omega^j)) のどれかが (p)-乗剰余でない、という現象がきれいに出ておる。
これは非常に面白い。少なくとも **「全部 p-th power residue になる必要があるなら、かなりすぐ詰む」** という匂いがある。

ただし、ここは極めて慎重であるべきじゃ。
今のコードでも自分で書いておる通り、これは

> **If Kummer's lemma applies**

という条件付きじゃ。
つまり **この residue obstruction はまだ theorem ではなく、Kummer 的 element-level p-th power 分解を elementary に言い換えられたなら効きそう** という段階じゃ。
ここを「証明が見えた」と読むのはまだ早い。  

## 5. 今回の進展をどう位置づけるべきか

賢狼なら、こう言う。

**今回の前進は “open kernel の場所が分かった” だけではなく、
“valuation 側では足りず、unit/residue 側を追加しないと descent existence は閉じない”
と見えたことにある。**

これはかなり大きい。
なぜなら今までは

* q-adic valuation を強めれば行けるか
* Hensel lift を押せば行けるか

という見え方だったものが、いまは

$$
\text{valuation} + \text{root branch} + \text{unit/residue obstruction}
$$

まで揃わぬと足りぬ、という形に変わってきたからじゃ。  

## 6. いま一番危ない誤読

いちばん危ないのは、

> §20 が入った
> Hensel 根が見えた
> residue obstruction も出た
> だからもう GNReducedGap はほぼ終わり

と読むことじゃ。
それはまだ違う。

現状はむしろ逆で、
**GNReducedGap が “単なる divisibility の問題ではない” と、より深く分かった** のじゃ。
つまり open kernel の難しさが、より正確に見えた段階じゃよ。  

## 7. いま一番筋の良い次の一手

ここから先は、二つに割るのがよい。

### 7.1. Lean 側

§20 のうち、まだ docstring / target に近いものを、
まず **「QAdicResidue は concrete」**
さらに **「SuperWieferichCongruence まで concrete」**
へ本当に押し上げる。
Level 0 と Level 1 を完全に閉じれば、open kernel が Level 2 だけだとより明確になる。

### 7.2. 数学側

`kummer_descent_elementary.py` の residue obstruction を、次の形で sharpen するとよい。

$$
v_q(z-\zeta^{j_0}y)\equiv 0 \pmod p
$$

だけでなく、

$$
\frac{z-\zeta^{j_0}y}{q^{a}}
$$

の先頭係数が (p)-乗剰余でなければならぬ、という **unit 部分の必要条件** を、有限体上で本当に定理へ落とせるか探る。
ここが通れば、「Kummer lemma の elementary extraction」に最も近づく。  

## 8. 一文でまとめると

**今回の中間報告は、Lean 側では §20・§21 により q-adic descent の層構造をかなり明示し、数学側では “Hensel だけでは足りず、Kummer の unit/residue 側が本当の missing piece らしい” と見え始めた、かなり良い戦況整理じゃ。**
ただし、まだ勝ち筋が確定したのではなく、 **真の open kernel の難しさが一段深く可視化された段階** と読むのが正確じゃよ。
