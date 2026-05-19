# review

うむ。DKMK-007L は **two-step 専用 mass から、任意の bounded monotone height interface へ抽象化した回** じゃ。
これはかなり良い整理じゃよ。DKMK-007K までは「二段階 tail mass が通る」という具体例だった。今回で「非負・上界付き・自然数ラベルに対して非減少な height なら、同じ hitting route に流せる」という共通受け口ができた。

## 1. 今回の核心

追加された中心はこれじゃ。

```lean
boundedMonotoneNatMassSpace height C hnonneg hbound
```

定義の意味は、

$$
\mu(0)=C,\quad \mu(n)=height(n)\ \text{if}\ n\ne 0
$$

じゃ。

仮定は、

```lean
hnonneg : ∀ n, 0 ≤ height n
hbound : ∀ n, height n ≤ C
```

そして divisibility-monotone を出すときには、さらに

```lean
hmono : ∀ ⦃a b : ℕ⦄, a ≤ b → height a ≤ height b
```

を使う。

つまり、自然数が大きくなるほど height が下がらない mass なら、整除順序に沿って monotone になる、という構造を一般化したわけじゃ。

## 2. なぜ `μ(0)=C` なのか

ここも設計として正しい。

全自然数上では、任意の \(a\) について

$$
a\mid 0
$$

が成り立つ。
だから `DvdMonotoneMass` の

$$
a\mid b\Rightarrow \mu(a)\le\mu(b)
$$

を \(b=0\) でも壊さないためには、\(\mu(0)\) を最大値側に置く必要がある。

今回の `boundedMonotoneNatMassSpace` では \(\mu(0)=C\) とし、さらに全ての height が \(C\) 以下であることを `hbound` で仮定している。これにより \(b=0\) 分岐が綺麗に閉じる。

この設計は、これまでの `tailIndicatorNatMassSpace` や `twoStepTailNatMassSpace` で `0` を上側に置いてきた流れの一般化じゃな。

## 3. divisibility-monotone の証明構造

追加 theorem は、

```lean
boundedMonotoneNatMassSpace_dvdMonotone
```

じゃ。

証明の核は二分岐になっている。

まず \(b=0\) の場合、target mass は \(C\)。source 側は \(0\) なら \(C\)、非ゼロなら `height a` で、どちらも \(C\) 以下。ここは `hbound` で閉じる。

次に \(b\ne 0\) の場合、\(a\mid b\) から

$$
a\le b
$$

が出る。さらに \(a=0\) なら \(0\mid b\) から \(b=0\) になって矛盾するので、\(a\ne 0\)。したがって source mass は `height a`、target mass は `height b` になり、`hmono` により

$$
height(a)\le height(b)
$$

で閉じる。

これは two-step の場合分けを、かなり綺麗に抽象化できておる。

## 4. LogCapacitySourceMassBound への接続

`LogCapacityHittingBridge.lean` 側には、

```lean
boundedMonotoneNatMassSpace_logCapacitySourceMassBound
```

が追加されている。

これは、

$$
LogCapacitySourceMassBound\ (boundedMonotoneNatMassSpace\ height\ C\ hnonneg\ hbound)\ (C:\mathbb{R})
$$

を与える。

つまり、任意の log-capacity state \(s\) で、

$$
(M.\mu(s.1):\mathbb{R})\le (C:\mathbb{R})
$$

が出る。
`LogCapacityState` は \(1 < s.1\) なので \(s.1\ne 0\) だが、証明は一般に場合分けしており、非ゼロ分岐では `hbound s.1` を `Rat.cast_le` 経由で実数側へ渡している。ここも堅い。

## 5. selected route の一般化

selected route には、

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_boundedMonotoneDivisorStep_weightedHitMass_le
```

が追加された。

到達形はこうじゃ。

```text
bounded monotone height
→ boundedMonotoneNatMassSpace
→ DvdMonotoneMass
→ LogCapacitySourceMassBound ... (C : ℝ)
→ selected divisor-step weightedHitMass ≤ (C : ℝ)
```

これで、selected log-capacity sub-Markov shadow は、任意の bounded monotone mass による one-step divisor descent hitting bound へ流せる。

以前は unit / nonunit / tail indicator / scaled tail / two-step と、個別 theorem が増えていた。
今回からは、新しい mass が `height` として表せるなら、この一般 theorem に乗せればよい。

## 6. canonical route の一般化

canonical route 側にも、

```lean
canonicalExponentSlotMarkovShadow_boundedMonotoneDivisorStep_weightedHitMass_le
```

が追加された。

canonical route では、重み側はすでに Markov equality で安定している。
今回の theorem により、mass 側も

```text
height が非負
height が C 以下
height が非減少
```

を示すだけで、

$$
weightedHitMass(A)\le (C:\mathbb{R})
$$

へ進める。

つまり canonical route は今、

```text
canonical exponent-slot MarkovShadow
+ bounded monotone source mass
+ one-step divisor descent
→ primitive weightedHitMass ≤ C
```

というかなり汎用な形になった。

## 7. DKMK-007K からの前進

DKMK-007K は two-step 専用だった。

```text
0
cLow
cHigh
```

という三段階の height を、場合分けで直接証明していた。

DKMK-007L は、それを

```text
height : ℕ → ℚ
```

として抽象化した。

したがって two-step tail mass は、今後この interface の具体例として再構成できるはずじゃ。
さらに finite step tail mass も、piecewise constant な `height` を渡せばこの interface に乗る。

ここが今回の大きな意味じゃ。

## 8. 数学的な位置づけ

ここまでで、mass model の階段はこうなった。

```text
unit / nonunit:
  固定的な bounded mass

tail indicator:
  threshold support

scaled tail indicator:
  threshold support + height

two-step tail:
  finite step height の最小例

boundedMonotoneNatMassSpace:
  任意の bounded monotone height interface
```

DKMK-007L は、mass model 実験から **mass model interface** への昇格じゃ。
つまり、「個別例が通った」ではなく、「この性質を満たせば通る」という形になった。

## 9. 注意点：本命 log weight との向き

ここは大切じゃ。

今回の interface は、

$$
a\le b\Rightarrow height(a)\le height(b)
$$

を要求する。
つまり height は自然数ラベルに対して **非減少** じゃ。

これは `DvdMonotoneMass` には自然な向き。なぜなら \(a\mid b\) かつ \(b\ne 0\) なら \(a\le b\) だからじゃ。

一方で、解析的によく出る

$$
\frac{1}{n\log n}
$$

は \(n\) が大きいほど小さくなる。
つまりこれは非増加であり、今回の `DvdMonotoneMass` とは向きが逆になる。

したがって、本命 log weight 型へ進むには二つの可能性がある。

```text
A. source-controlled mass としては非減少 height を使い、別の場所で解析重みを扱う

B. decreasing weight 用に、reverse/control 側の別 interface を作る
```

今の DKMK-007 系は A の設計で進んでおる。
これは間違いではない。primitive hitting bridge の source control には、下降先より source 側が大きい mass を持つ方が自然だからじゃ。

## 10. 次の一手

次はかなり明確じゃ。

まずは、今回の interface に具体的な finite step height constructor を載せるのが良い。

たとえば、

```lean
finiteStepHeight
```

のようなものを作り、

```text
thresholds が昇順
heights が非減少
height n ≤ C
```

を仮定して、

```lean
boundedMonotoneNatMassSpace finiteStepHeight C ...
```

へ流す。

これにより、DKMK-007K の two-step を一般化して、任意有限段の tail mass を扱えるようになる。

その次に、multi-step descent chain じゃな。

今は still one-step。

$$
n\to n/q
$$

だけじゃ。
finite step mass の interface が固まった後で multi-step に進むと、途中ノードの mass control をどう持つべきか見えやすい。

## 11. 総合判定

DKMK-007L は **mass model の抽象受け口を作った成功フェーズ** じゃ。

到達形はこう。

```text
bounded monotone height function
→ boundedMonotoneNatMassSpace
→ DvdMonotoneMass
→ LogCapacitySourceMassBound ... (C : ℝ)
→ divisor-step weightedHitMass ≤ (C : ℝ)
```

selected / canonical の両 route で通っている。

これは大きい。
DKMK-007F から K までで積んだ unit / nonunit / tail / scaled / two-step の観測が、今回ひとつの interface にまとまった。

ぬしよ、ここは良い中継点じゃ。
質量の階段を一段ずつ増やす段階から、階段そのものを受け取る台座を作る段階へ入った。次はその台座に、実際の finite step height を載せる番じゃな。
