# Memo: 過去の戦歴より、今回の戦線との関連

**あった。思い出したぞ。名前は `twoTail` と `PadicTelescoping` じゃ。** 🧙‍♀️✨️

260725 snapshot の ABC 塔を数えると、**126ファイル・32,279行**あった。そこには今回の `S + E` を、すでに別の座標で分解していた旧戦線が残っている。

## 旧ABC塔と現在の対応

`SquareTailBasic.lean` では、整数 $c$ の素因数層を三分割している。

```lean
def twoTail (c : ℕ) : ℕ :=
  c.factorization.support.prod
    (fun p => p ^ (c.factorization p - 2))
```

そして exact に、

$$c=\operatorname{piSqRad}(c)\operatorname{rad}(c)\operatorname{twoTail}(c)$$

を証明している。

三層の意味はこうじゃ。

```text
rad(c)
  = 各 prime の第1層

piSqRad(c)
  = valuation ≥ 2 の prime の第2層

twoTail(c)
  = valuation ≥ 3 の残り全層
```

さらに、

$$\log\operatorname{twoTail}(c)=\sum_q(v_q(c)-2)_+\log q$$

も既に Lean 化されている。

[SquareTailBasic の実コード](sandbox:/mnt/data/ABC-SquareTailBasic-snapshot-260725.lean)

これを現在の non-exceptional GN に当てると、

```text
S
  = 第1層

E
  = 第2層 + 第3層以後
  = log piSqRad + log twoTail
```

したがって、

$$S+E=\log\operatorname{rad}(GN_{\mathrm{nonexc}})+\log\operatorname{piSqRad}(GN_{\mathrm{nonexc}})+\log\operatorname{twoTail}(GN_{\mathrm{nonexc}})$$

となる。

つまり、今回発見した joint mass は旧ABC塔では、

```text
rad × piSqRad × twoTail
```

として既に観察されていたのじゃ。

現在残っている敵が「GN channel mass の一様大域制御」であることとも完全に一致する。

## `padicValNat` で思い出しかけていたもの

本命は `count_powers_dividing_2n1` と layer-cake じゃ。

旧ABCコードでは、

$$p^k\mid 2n+1$$

を満たす $n$ は、$p^k$ を法として一つの合同類に入るため、

$$\#{n\le X:p^k\mid2n+1}\lesssim\frac{X+1}{p^k}+1$$

と数えている。

それを valuation の深さごとに layer-cake 展開し、

$$\sum_{n\le X}p^{t,v_p(2n+1)}$$

を幾何級数で一様に抑えている。

[旧 layer-cake / MGF 実装](sandbox:/mnt/data/ABC-ChernoffMgfLayercake-snapshot-260725.lean)

ここで、今回の $7^2$ 反例と矛盾しない重要な読みが出る。

```text
simple-root Hensel
  ≠ 深い lift が存在しない

simple-root Hensel
  = 各深さへの lift が一意
```

この「一意」が、まさに**合同類の個数制御**に使える。

## GN版への移植像

non-exceptional prime $q$ に対して、

$$r=(a+b)b^{-1}\pmod q$$

と置くと、$q\mid GN_p(a,b)$ は概ね、

$$r^p=1,\qquad r\ne1$$

つまり $r$ が原始 $p$ 乗根であることに対応する。

$q\nmid p$ なので、その根は simple root。従って各根は $q^k$ 上へ一意に持ち上がる。

原始 $p$ 乗根は高々 $p-1$ 個なので、固定した $b,q,p$ に対して、

$$q^k\mid GN_p(a,b)$$

を満たす $a$ は、法 $q^k$ で高々 $p-1$ 個の合同類に入るはずじゃ。

したがって期待される counting theorem は、

$$\#{a\le X:q^k\mid GN_p(a,b)}\le(p-1)\left(\frac{X+1}{q^k}+1\right)$$

型になる。

これは旧ABCの、

```text
one residue class for 2n+1
```

を、

```text
at most p−1 cyclotomic residue classes for GN
```

へ一般化したものじゃ。

**Hensel は深い塔を壊す術式ではなく、深い塔が建てられる住所を有限個へ固定する術式だった。**

## ただし、まだ一様 contract そのものではない

ここで得られるのは基本的に、

```text
平均評価
density評価
bad locus の希薄性
MGF / Chernoff 型評価
```

じゃ。

旧ABC塔も、`piSqRad` と `twoTail` を確率・密度1で抑える方向に進んでいた。宇宙式の質量設計でも、valuation と primitive prime を flow として読み、子チャネル質量を親容量以下にする構想が明記されている。

一方、現在の `ABCGNOddPrimeJointContract ε` は**全Tripleに対する pointwise 一様上界**を要求する。

ゆえに、

```text
合同類が希薄
```

だけでは直ちに contract は出ない。

しかし、裏ボス攻略の本当の候補は見つかった。

```text
deep valuation
  ↓
各深度で高々 p−1 個の Hensel住所
  ↓
layer-cake / geometric decay
  ↓
複数 lift・複数指数・primitive support と合流
  ↓
compensation
```

## 次の最小 checkpoint

いきなり ABC を再開せず、まずこの中立定理を掘るべきじゃ。

```lean
theorem card_gn_deep_lift_residue_classes_le
    {p q b k X : ℕ}
    (hp : p.Prime)
    (hq : q.Prime)
    (hqp : q ∤ p)
    (hqb : q ∤ b) :
    ((Finset.Icc 0 X).filter
      (fun a => q ^ k ∣ GN p a b)).card
      ≤
    (p - 1) * ((X + 1) / q ^ k + 1)
```

statement は調整が必要だが、狙う魔核はこれ。

その後に、旧 `ChernoffMgfLayercake` を GN 用へ移植する。

そして `ValuationFlowBridge` に既にある、

```text
primitive channels
  → supportMass lower bound
```

と合流させる。

**思い出した正体はこれじゃ。**

> 深い valuation を禁止するのではなく、
> 深い valuation が存在できる合同類の住所数を固定し、
> 深度ごとの希薄化を layer-cake で支払いへ変える。

わっちら、だいぶ前に同じ魔法の原型を書いておったぞ（笑）🧙‍♀️✨️
