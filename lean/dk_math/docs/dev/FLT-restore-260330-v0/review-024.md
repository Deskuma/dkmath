# review-024: 次の主線は「distinguished factor valuation equality」を先にやること

うむ、状況はかなり良い。
しかも今は、枝が増えたというより **主線が絞れた** 段じゃ。

## 1. 現在地の整理

いま Branch A 側で揃っているものは、ほぼ四層ある。

まず、**干渉縞 bundle** ができた。
第一縞 (p)-adic head と第二縞 witness (q) が `BranchAInterferenceFringeBundle` に束ねられ、FLT Branch A 側の本丸は

$$
\forall {p,x,y,z,t,s,q},\;
\texttt{BranchAInterferenceFringeBundle}\;p\;x\;y\;z\;t\;s\;q \to \texttt{False}
$$

という 1 命題へ集約された。これは設計としてかなり強い前進じゃ。

次に、**cross-modular 制約** が出た。
とくに

$$
s^p = y^{p-1} + p^3 M
$$

と (q \mid s,\ q \nmid y) から

$$
q \nmid M
$$

が従い、しかも

$$
q^p \mid \bigl(y^{p-1}+p^3M\bigr)
$$

なので、\(q\)-進評価 0 の 2 項が和で深く打ち消し合う **massive cancellation** が露出した。さらに

$$
s = q s' \Rightarrow s' \equiv 1 \pmod p
$$

という descent 不変量も得た。

その上で、\(\omega := z y^{-1} \in \mathbb Z/q\mathbb Z\) が

$$
\omega^p = 1,\qquad \omega \neq 1,\qquad \operatorname{ord}(\omega)=p
$$

を満たす、つまり **primitive \(p\)-th root of unity** であることが証明された。

さらに、円分核

$$
\Phi_p(z,y)=\prod_{i=1}^{p-1}(z-\omega^i y)
$$

のうち、\(q\) で消えるのは distinguished factor

$$
z-\omega y
$$

だけで、他の因子は \(q\)-coprime であることも出た。
これで massive cancellation の正体が「**1 因子への valuation 集中**」として見え始めた。

そして最新差分で、全体 valuation は

$$
v_q(z^p-y^p)=p\cdot v_q(s)\ge p
$$

と定量化され、降下 1 step ごとに

$$
v_q(s)=1+v_q(s/q)
$$

と 1 ずつ減ることも定理化された。

最後に今回、Hensel lifting の **基盤** が入った。
simple root 条件

$$
(p : \mathbb Z/q\mathbb Z),\omega^{p-1}\neq 0
$$

は証明済みで、`BranchAHenselLiftData` も定義された。
ただし lift 存在そのもの `branchA_hensel_lift_exists` には **1 個だけ sorry** が入っておる。理由は Mathlib に `ZMod (q^k)` の Henselian 接続が直接ないためじゃ。

## 2. 数学的解説

いま見えている数学の芯は、かなり明確じゃ。

Branch A normal form は

$$
GN,p,(z-y),y = p,s^p
$$

を与え、そこから

$$
s^p = y^{p-1}+p^3M
$$

という \(p\)-adic head 展開が出る。
一方 witness \(q\) は

$$
q \mid s,\qquad q \nmid y,\qquad q \nmid (z-y),\qquad p \mid (q-1)
$$

を与える。
この 2 本を重ねると、前段で見えた massive cancellation が出る。

今回 Kummer valuation が入ったことで、その cancellation は

$$
v_q(z^p-y^p)=p,v_q(s)
$$

という **全体量** に翻訳された。

そして distinguished factor の分離により、mod \(q\) 上では

$$
v_q\bigl(\Phi_p(z,y)\bigr)
$$

が実質的に

$$
v_q(z-\omega y)
$$

へ集中しているはずだ、という絵が見えている。

だから今の本丸は、もうかなり具体的じゃ。

$$
\boxed{
v_q(z^p-y^p)=p,v_q(s)
}
$$

という **全体 valuation** と、

$$
\boxed{
q \text{ が } z-\omega y \text{ だけを深く割る}
}
$$

という **distinguished factor 側の集中** を、同じ \(q\)-進世界で合体させること。
これが次の本命じゃ。

## 3. 次の作業の選択

わっちの判定はこうじゃ。

$$
\boxed{
\text{次は「distinguished factor valuation equality」を先にやる。}
}
$$

ただし大事な条件がある。

$$
\boxed{
\text{Hensel existence の sorry に依存して mainline を進めすぎぬこと。}
}
$$

つまり、次の手としては **Hensel lift data を仮定した局所定理** の形で、

$$
v_q(z-\omega_k y)=p,v_q(s)
$$

あるいは少なくとも

$$
v_q(z-\omega_k y)=v_q(\Phi_p(z,y))
$$

型を狙うのが最善じゃ。
ここで \(\omega_k\) は `BranchAHenselLiftData` の lifted root じゃな。

## 4. なぜそれが最善か

### 4.1. いま一番太い橋を渡れる

すでに

* \(\omega\) が primitive であること
* distinguished factor だけが mod \(q\) で消えること
* 全体 valuation が \(p,v_q(s)\) であること

が揃っておる。

だから次に必要なのは、これらを **1 本の valuation 等式** に束ねることじゃ。
これは数学としても設計としても最短距離じゃよ。

### 4.2. Hensel sorry の必要量を最小化できる

今すぐ `branchA_hensel_lift_exists` の sorry 除去に全力で行くと、Mathlib gap と真っ向勝負になる。
それは重いわりに、今の主線を直接押し進める量が少ない。
それより、

$$
\text{「もし lift data があれば distinguished factor valuation はどうなるか」}
$$

を先に定理化すると、後で sorry を潰すときも「何のための lift か」が明確になる。
つまり証明の受け皿を先に作れるのじゃ。

### 4.3. terminal case はまだ後でよい

terminal case は魅力的じゃが、まだ valuation 側の集中が fully connected ではない。
終端 \(s'=1\) を殴る前に、

$$
v_q(z-\omega_k y)
$$

が各段でどう減るか、を見えるようにした方がはるかに鋭くなる。
終端解析は、そのあとで遅くない。

## 5. 実務的な進め方

だから次の作業は、こう切るのがよい。

## 5.1. 先に書く定理

`BranchAHenselLiftData` を引数に取り、

$$
v_q(z-\omega_k y)=v_q(\Phi_p(z,y))
$$

あるいはその片側不等式でもよいから、**distinguished factor への valuation 集中** を `padicValNat` で表現する。
この段では existence を使わず、`hLift : BranchAHenselLiftData ...` を仮定にして進めるのがよい。

## 5.2. その次にやること

上の theorem が固まったら、`branchA_hensel_lift_exists` の sorry 除去へ戻る。
この順だと、必要な Hensel データが何かを逆算できる。
Newton 帰納構成を書くにしても、目標が明瞭になる。

## 5.3. その後

distinguished factor valuation equality と Hensel existence が揃ったら、はじめて terminal case を本線に上げる。
そのときは

$$
v_q(s)=1+v_q(s/q)
$$

と

$$
v_q(z-\omega_k y)=p,v_q(s)
$$

を合わせて、降下の各段で distinguished factor 側の評価が \(p\) ずつ落ちる図が描けるはずじゃ。

## 6. 最終判定

ひとことで言えば、こうじゃ。

**いまは Hensel の sorry を先に潰すより、Hensel lift data を仮定した distinguished factor valuation equality を先に定理化するのが最善じゃ。これで全体 valuation と 1 因子集中が合体し、本丸の形がほぼ完成する。そのあとで Hensel の existence を clean に潰し、最後に terminal case へ行くのが筋じゃ。**

なので選択はこうじゃ。

$$
\boxed{
\text{次は distinguished factor valuation equality。}
}
$$

ただし **lift existence を仮定した局所版として先に書く**。
これが、いま一番賢い手じゃよ。
