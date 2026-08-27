# Note: Review: Ultra-001-K

## 総合判定

**全面採用。Ultra-001K、有限 Hensel 一意性を完全討伐じゃ。** ⚔️🧙‍♀️✨️

重大問題 0。主要問題 0。修正必須事項 0。

PR #69 は head `3624499d389985aad24ff1f6109739080f8f3346`、11 commits、22 files、5487 additions、現在も mergeable じゃ。

## 証明の心臓部

今回の証明は、Hensel lift を深度ごとに反復していない。

任意の可換環上で、

$$P(x+y)=P(x)+P'(x)y+cy^2$$

という一次 Taylor 展開を `Polynomial.taylor` と `X_pow_dvd_iff` から構成した。

深度 $k$ の二つの GN root $a,r$ に対し、`ZMod (q^k)` 上で、

$$d=a-r$$

と置くと、

$$d\bigl(P'(r)+cd\bigr)=0$$

を得る。

さらに $a\equiv r\pmod q$ なので $d$ の mod $q$ 像はゼロ。したがって第二因子の mod $q$ 像は、

$$P'(r)$$

そのものになる。

既に閉じた simple-root theorem により、

$$P'(r)\ne0\pmod q$$

なので、第二因子は `ZMod (q^k)` の unit。よって、

$$d=0\pmod {q^k}$$

すなわち、

$$a\equiv r\pmod {q^k}$$

となる。

これは実に美しい。

```text
同じ mod-q 根から
深さ k に伸びる枝は高々一本
```

を、反復なしの一撃で証明した。

## `ZMod (q^k)` の unit 判定

```lean
isUnit_zmod_primePow_of_castHom_ne_zero
```

も正しい位置にある。

mod $q$ へ落として非零なら、その元の標準代表は $q$ で割れない。したがって $q^k$ と互いに素であり、`ZMod (q^k)` では unit になる。

これにより整数の符号・減算・valuation cancellation を外へ出さず、有限環の内部だけで Taylor の第二因子を消去できた。

## 二つの Hensel API が本当に同値になった

前 checkpoint で残っていた、

```lean
GNDeepLiftReductionInjective
GNDeepLiftCongruenceUnique
```

の逆方向も追加された。

したがって現在は、

```text
canonical residue 集合上の reduction injectivity
        ↕
任意の自然数 root に対する合同一意性
```

が kernel 上で完全に同値じゃ。

この整理により、有限集合 counting 側と数論側が互いに独立して利用できる。

## Deep root 数が全深度で固定された

今回の結果を一行で書けば、

$$#{r\bmod q^k:q^k\mid GN_p(r,b)}\le p-1$$

じゃ。

発動条件は、

```text
p prime
q prime
q ∤ p
q ∤ b
0 < k
```

であり、まさに現行 GN の non-exceptional channel から得られる条件じゃ。

構造は、

$$#\operatorname{Roots}(q^k)\le#\operatorname{Roots}(q)\le p-1$$

となった。

```text
mod q の住所数       ≤ p−1
各住所の地下枝数     ≤ 1
深度 k の総住所数    ≤ p−1
```

深さが増えても、住所数は増殖しない。

## 区間 counting まで無条件化された

最終 endpoint、

```lean
card_gn_deep_lift_residue_classes_le_of_simpleRoot
```

により、

$$#{a\in[0,X]:q^k\mid GN_p(a,b)}\le(p-1)\left(\frac{X+1}{q^k}+1\right)$$

が、non-exceptional 条件下で追加 contract なしに成立した。

したがって旧 ABC 塔から続く lane は、

```text
canonical residue cover          complete
mod-q root count                 complete
simple-root derivative           complete
finite Hensel uniqueness         complete
deep-lift residue count          complete
divisibility → padic depth       complete
finite layer-cake input          complete
```

となった。

## $7^2$ 反例との整合

$GN_3(2,3)=7^2$ は、この theorem に反していない。

この theorem は、

```text
深い root は存在しない
```

とは言わない。

言っているのは、

```text
mod 7 のある simple root から
mod 7^k へ伸びる root は高々一つ
```

じゃ。

$7^2$ は、その唯一の枝が深度2まで伸びた例。

つまり反例を排除するのではなく、反例を含む正しい構造を証明できている。

## 残る敵

局所 Hensel 戦線はこれで閉じた。

残るのは本当に、

```text
希薄な住所へ、
一つの ABC triple が
複数 prime・複数深度・複数観測を通して
入り続けられるか
```

という大域問題じゃ。

現在得たものは density estimate。

必要なのは pointwise compensation。

```text
各 q^k の bad address は希薄
        ↓
しかし特定 triple は bad address に入れる
        ↓
複数の bad address へ同時・反復的に入る代償を示す
        ↓
S + E の pointwise uniform bound
```

## 次 checkpoint

次は単一 $q,k$ の counting を再び証明する必要はない。

旧 layer-cake と今回の counting を実際に合成し、固定 $p,q,b,X$ に対する明示的な平均 valuation bound を作るべきじゃ。

候補は、

```lean
theorem sum_padicValNat_GN_le_of_simpleRoot
    {p q b X : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    ∑ a ∈ Finset.Icc 0 X, padicValNat q (GN p a b)
      ≤ ...
```

または weighted 版、

```lean
theorem sum_GN_depthMass_over_interval_le
```

じゃ。

これにより、

```text
一深度の住所数
  ↓
全深度の平均 multiplicity
  ↓
全 prime の平均 E
```

へ進める。

その次に初めて、

```text
平均ではなく、なぜ各 Triple を抑えられるのか
```

という deterministic compensation の裏ボスへ戻る。

## 最終戦況

```text
U-001A  exact normal form                         complete
U-001B  joint contract / direct bridge            complete
U-001C  exact radical identity                    complete
U-001D  finite layer-cake                         complete
U-001E  pincer / deep witness                     complete
U-001F  exact order                               complete
U-001H  raw endpoint                              complete
U-001I  legacy tail/counting reconnection         complete
U-001J  canonical roots / base count              complete
U-001K  finite Hensel uniqueness                  complete

U-001G  pointwise uniform compensation            open
```

**これは明確な進軍成功じゃ。**

🧙‍♀️✨️ 以前は「深い valuation が何者か分からない」状態だった。いまは、**深い valuation は高々 $p-1$ 本の一意な地下道に閉じ込められた。残る戦いは、その地下道を何本同時に占有できるかという大域資源戦**じゃ。
