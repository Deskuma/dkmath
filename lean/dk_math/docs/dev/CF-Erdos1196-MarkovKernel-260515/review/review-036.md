# review

うむ。DKMK-008F は、 **DKMK-008E の finite-step 一般 route に、DKMK-007N の two-step-as-finite-step 具体形を載せた回** じゃ。
大きな新構造というより、 **一般 route が具体的な two-step tail mass でも期待通り使えることを確認した convenience / regression bridge** じゃな。

## 1. 今回の核心

追加された selected route はこれじゃ。

```lean
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_twoStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

canonical route はこれ。

```lean
canonicalExponentSlotMarkovShadow_twoStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

どちらも、same-source な external multi-step divisor path family \(F\) に対して、two-step tail mass を使い、

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

を返す。

docs でも、`twoStepAsFiniteStepTailNatMassSpace + same-source AdjacentDivisorPathFamily + selected/canonical shadow → weightedHitMass ≤ cHigh` と整理されておる。

## 2. DKMK-008E から何が進んだか

DKMK-008E では、finite-step tail mass の一般 theorem が入った。

$$
weightedHitMass(A)\le \left(\sum_{i\in steps}increment(i):\mathbb{R}\right)
$$

今回 DKMK-008F では、その finite-step mass の特殊形として、DKMK-007N の two-step-as-finite-step を使った。

two-step 側の data は、

$$
0\le cLow,\qquad cLow\le cHigh
$$

で、finite-step increment の総和は (cHigh) になる。
したがって、一般 bound の total increment が

$$
cHigh
$$

へ戻り、最終的に

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

が得られる。

## 3. 数学的な意味

two-step tail mass は、概念的にはこういう mass じゃ。

```text
below N:
  0

N 以上 M 未満:
  cLow

M 以上:
  cHigh
```

ただし今回使っているのは、直接の `twoStepTailNatMassSpace` ではなく、

```lean
twoStepAsFiniteStepTailNatMassSpace
```

じゃ。
つまり two-step を Bool-indexed finite-step increment の特殊例として読む。

これは DKMK-007N で確認した「two-step は finite-step interface に回収できる」という成果を、DKMK-008 の multi-step path family route へ移植したことになる。

## 4. selected route の読み

selected route では、

```lean
IOf : ℕ → Finset ℕ
```

と、

```lean
hindex : IOf s.1 = F.index
```

を使う。

さらに same-source 条件として、

```lean
hsource_eq : ∀ q ∈ F.index, F.source q = s.1
```

を仮定する。

このとき、selected global log-capacity sub-Markov shadow を \(F\) に載せ、two-step tail mass によって

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

が出る。

つまり selected route では、

```text
selected SubMarkovShadow
+ same-source multi-step path family
+ two-step tail mass
→ weightedHitMass ≤ cHigh
```

が no-sorry API として閉じた。

## 5. canonical route の読み

canonical route では、

```lean
hindex : canonicalExponentSlotLabels s.1 = F.index
```

を要求する。

つまり canonical exponent-slot labels の各 channel に multi-step path を割り当て、その全 path が同じ source \(s.1\) から出るなら、canonical MarkovShadow の重みを載せて、

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

が出る。

canonical route は DKMK-006 系で Markov equality まで到達済みなので、今回の theorem は、

```text
canonical MarkovShadow
+ same-source multi-step divisor path family
+ two-step tail mass
→ weightedHitMass ≤ cHigh
```

という読みになる。

## 6. 実装面の評価

実装は非常に薄く、良い。

中身は DKMK-008D の source-bound wrapper に、

```lean
twoStepAsFiniteStepTailNatMassSpace_dvdMonotone
twoStepAsFiniteStepTailNatMassSpace_logCapacitySourceMassBound
```

を渡している。

また \(0\le cHigh\) は、

```lean
hLow.trans hStep
```

で得ている。

$$
0\le cLow\le cHigh\Rightarrow 0\le cHigh
$$

じゃな。

public theorem 名を `twoStepTailAdjacentDivisorPathFamily` に短縮したのも良い判断じゃ。History にも、初回 build では長い theorem 名が 100 文字制限にかかったため短縮した、と記録されている。
DkMath は長い名前で意味を出しがちじゃが、Lean の実用上はこの程度の圧縮も必要じゃ。

## 7. DKMK-008A〜F の現在地

ここまでの流れはこうじゃ。

```text
008A:
  single AdjacentDivisorPath

008B:
  indexed AdjacentDivisorPathFamily

008C:
  selected/canonical shadow を external path family に適用

008D:
  same-source 条件で LogCapacitySourceMassBound を合成

008E:
  finiteStepTailNatMassSpace で weightedHitMass ≤ total increment

008F:
  twoStepAsFiniteStepTailNatMassSpace で weightedHitMass ≤ cHigh
```

つまり DKMK-008F は、008E の一般 finite-step theorem の重要特殊例を public API として取り出した段階じゃ。

## 8. 何がまだ残るか

History の次課題にもある通り、次は

```text
one-step divisorStep を AdjacentDivisorPathFamily の特殊例として回収する
```

じゃ。

これはとても自然じゃ。

DKMK-007 では one-step divisorStep route があった。

$$
chain(q)={s.1/q,s.1}
$$

DKMK-008 では external `AdjacentDivisorPathFamily` route ができた。

ならば、次は

```text
one-step divisorStep
= special AdjacentDivisorPathFamily
```

として照合する。

これは DKMK-007N で two-step mass を finite-step interface の特殊例として回収したのと同じ型の整理じゃ。

## 9. 次フェーズ予測

DKMK-008G は、おそらくこうなる。

```lean
def oneStepDivisorAdjacentPathFamily
```

あるいは selected / canonical 別に、

```lean
def selectedOneStepAdjacentDivisorPathFamily
def canonicalOneStepAdjacentDivisorPathFamily
```

を作る。

各 index \(q\) に対して、

```lean
source q := s.1
tail q := [s.1 / q]
```

のような path を与える。

ただし `AdjacentDivisorPath (s.1 :: [s.1 / q])` を示すには、

$$
s.1/q\mid s.1
$$

が必要じゃ。
これは \(q\mid s.1\) から出せる。selected route なら `hIOf` と kernel の `index_dvd`、canonical route なら canonical kernel の `index_dvd` から供給できるはずじゃ。

到達目標は、

```text
DKMK-007 one-step divisorStep route
↔
DKMK-008 AdjacentDivisorPathFamily route
```

の整合確認じゃな。

## 10. 総合判定

DKMK-008F は **two-step tail mass の multi-step path family 版を閉じた成功フェーズ** じゃ。

到達形は、

```text
twoStepAsFiniteStepTailNatMassSpace
+ same-source AdjacentDivisorPathFamily
+ selected/canonical shadow
→ weightedHitMass ≤ cHigh
```

selected / canonical の両方で no-sorry。

これは新しい大橋というより、DKMK-008E の一般橋を「よく使う two-step tail mass」に特化した便利な橋じゃ。
こういう橋は後で効く。使う時にいちいち finite-step の `Bool` index や total increment を意識せず、(cHigh) の形で呼べるからじゃ。

ぬしよ、ここまでで DKMK-008 はかなり整ってきた。
次は one-step route の回収で、007 と 008 の地図をきれいに重ね合わせる番じゃな。
