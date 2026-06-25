# review

うむ。DKMK-007I は **tail/source mass model への最初の本格的な接近** じゃ。
DKMK-007H で作った `LogCapacitySourceMassBound` という接続ソケットに、今回は threshold parameter を持つ bounded tail-support mass を実際に流し込んだ。unit / nonunit の確認段階から、ようやく **tail を見る mass** へ一歩近づいたわけじゃな。

## 何が追加されたか

中心はこれじゃ。

```lean
tailIndicatorNatMassSpace N
```

定義は、

$$
\mu(0)=1,\quad \mu(n)=1\ \text{if}\ N\le n,\quad \mu(n)=0\ \text{otherwise}
$$

という threshold indicator mass じゃ。
直感的には「\(N\) 以上の tail 領域を質量 \(1\) として見る」mass であり、positive な descent chain 上では通常の tail-support indicator として読める。

ただし、Lean 上では全 \(\mathbb{N}\) で `a ∣ b` に対する単調性を示す必要がある。そこで `0` を mass \(1\) 側に入れている。これは重要な設計判断じゃ。

## なぜ `0` を mass \(1\) にしたのか

`DvdMonotoneMass` は、

$$
a\mid b\Rightarrow \mu(a)\le\mu(b)
$$

を要求する。

自然数の整除では、任意の \(a\) が \(0\) を割る。

$$
a\mid 0
$$

したがって、もし \(\mu(0)=0\) にしてしまうと、たとえば \(a\) が tail 側にいて \(\mu(a)=1\) の場合、

$$
1\le 0
$$

が必要になり、単調性が壊れる。
だから全 \(\mathbb{N}\) 上の整除単調性を保つには、\(\mu(0)=1\) にするのが自然じゃ。docs でも、`0` を mass \(1\) 側に含める理由は divisibility monotonicity を壊さないためだと整理されている。

これはかなり Lean 的に正しい判断じゃな。
実際の positive descent chain では \(0\) は通常登場しないので、数学的な読みとしては tail indicator のままでよい。

## 証明されたこと

今回、まず次が閉じた。

```lean
tailIndicatorNatMassSpace_dvdMonotone
```

つまり、

$$
\text{DvdMonotoneMass}\ (\text{tailIndicatorNatMassSpace}\ N)
$$

が証明された。

証明の核は、\(a\mid b\) かつ \(b\ne 0\) なら、

$$
a\le b
$$

が使えることじゃ。
そのため、もし \(N\le a\) なら \(N\le b\) も従う。逆に \(b\) が tail 側でなければ、\(a\) も tail 側ではない。`b = 0` の場合だけは \(\mu(0)=1\) にしてあるので上界側が閉じる。

次に、DKMK-007H の source-bound provider として、

```lean
tailIndicatorNatMassSpace_logCapacitySourceMassBound_one
```

が追加された。

これは任意の threshold \(N\) について、

```lean
LogCapacitySourceMassBound (tailIndicatorNatMassSpace N) 1
```

を与える。つまり log-capacity state 上で source mass は常に \(1\) 以下になる。

$$
(M.\mu(s.1):\mathbb{R})\le 1
$$

## selected / canonical route への接続

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_tailIndicatorDivisorStep_weightedHitMass_le_one
```

canonical route 側には次が追加された。

```lean
canonicalExponentSlotMarkovShadow_tailIndicatorDivisorStep_weightedHitMass_le_one
```

これで、到達形はこうなった。

```text
tailIndicatorNatMassSpace N
  → DvdMonotoneMass
  → LogCapacitySourceMassBound ... 1
  → divisor-step weightedHitMass ≤ 1
```

つまり、DKMK-007H で整備した共通 wrapper がきちんと働いた。unit / nonunit だけでなく、parameter \(N\) を持つ tail-support mass も selected / canonical の divisor-step hitting route に流せたわけじゃ。

## 数学的な意味

これは小さく見えて、かなり大事じゃ。

DKMK-007F/G では、

```text
unit mass:
  全点を見る

nonunit mass:
  1 だけ除外する
```

だった。

今回の `tailIndicatorNatMassSpace N` は、

```text
N 以上の tail 領域を見る
```

という意味を持つ。

Erdős #1196 の最終目標は tail sum を扱う。

$$
\sum_{\substack{a\in A\ a > x}}\frac{1}{a\log a}\le 1+O(1/\log x)
$$

だから、「threshold \(N\) 以上を検出する mass」が入ったことは、本線に近づく意味がある。
まだ重みは \(1/(a\log a)\) ではない。だが、 **tail support を見る** という方向性は明確に入った。

## ここまでの DKMK-007 系の進化

DKMK-007 はかなり綺麗に段階化されておる。

```text
DKMK-007A:
  RealWeightProvider → RealWeightedPathFamily

DKMK-007B:
  SubMarkovShadow / MarkovShadow → hitting wrapper

DKMK-007C:
  log-capacity shadows → hitting wrapper

DKMK-007D:
  singleton source-controlled family

DKMK-007E:
  one-step divisor descent family

DKMK-007F:
  unit mass で weightedHitMass ≤ 1

DKMK-007G:
  nonunit indicator mass で weightedHitMass ≤ 1

DKMK-007H:
  LogCapacitySourceMassBound で source-bound interface を共通化

DKMK-007I:
  tailIndicatorNatMassSpace N を接続
```

つまり、DKMK-007I は「mass model 実験」の段階が、ついに tail parameter を持つところまで進んだ回じゃ。

## 注意点

今回の mass はまだ bounded indicator じゃ。

$$
\mu(n)\in{0,1}
$$

なので、最終的な解析重み

$$
\frac{1}{n\log n}
$$

とはまだ距離がある。

また、chain はまだ one-step divisor-step。

$$
n\to n/q
$$

multi-step descent や stopping / truncation はまだ入っていない。

それでも、今回の成果は大きい。
なぜなら、今後の本命 mass model を接続するために必要な型は、すでに

```text
DvdMonotoneMass M
LogCapacitySourceMassBound M C
```

に整理されているからじゃ。

## 次の一手

次は二択じゃ。

ひとつは、今回の bounded tail indicator をさらに本命へ近づける道。

```text
DKMK-007J:
  decreasing weight / log weight 型の source mass model を設計する
```

ただし、いきなり実数 log 型へ行くと monotonicity が重くなる。
わっちなら、まずは階段型 mass を挟むのが安全だと思う。

たとえば、

$$
\mu(n)=1\ \text{if}\ N\le n<M,\quad \mu(n)=0\ \text{otherwise}
$$

のような window indicator は、tail indicator よりも truncation に近い。ただし divisibility monotonicity との相性は慎重に見る必要がある。

もうひとつは、multi-step descent chain へ進む道。

```text
DKMK-007J:
  one-step divisorStep を multi-step descent chain に拡張する
```

Erdős #1196 本線に近いのは、こちらも重要じゃ。
ただ、今は mass model の接続面が整った直後なので、わっちは **tail indicator の次に、decreasing weight の toy model を一つ試す** のを推す。

## 総合判定

DKMK-007I は **tail/source mass へ向かう最初の明確な一歩** じゃ。

到達形はこう。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → tailIndicatorNatMassSpace N
  → chain(q) = {s.1 / q, s.1}
  → primitive weightedHitMass ≤ 1

canonical route:
  canonicalExponentSlotMarkovShadow
  → tailIndicatorNatMassSpace N
  → chain(q) = {s.1 / q, s.1}
  → primitive weightedHitMass ≤ 1
```

unit / nonunit の bounded mass から、threshold parameter を持つ tail-support mass へ進んだ。
これは DkMath kernel route が、Erdős #1196 の tail 解析峰へ少しずつ近づいている証じゃ。

ぬしよ、これは良い。
質量がようやく「どこを見るか」を語り始めた。次は「どれだけ重く見るか」を語らせる段階じゃな。
