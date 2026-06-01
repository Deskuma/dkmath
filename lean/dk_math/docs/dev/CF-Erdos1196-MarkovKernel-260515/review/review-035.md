# review

うむ。DKMK-008E は、 **DKMK-007M の finite-step mass route が、multi-step divisor path family へ正式に昇格した回** じゃ。
これは DKMK-008 の中でもかなり大きい到達点じゃよ。008A〜D で作った「多段下降路の器」と、007M で作った「有限段 tail mass の一般受け口」が、ここで一本につながった。

## 1. 今回の核心

追加された selected route はこれじゃ。

```lean
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_finiteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

canonical route はこれ。

```lean
canonicalExponentSlotMarkovShadow_finiteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

どちらも、same-source な

```lean
F : AdjacentDivisorPathFamily ℕ
```

に対して、finite-step tail mass を使い、

$$
weightedHitMass(A)\le \left(\sum_{i\in steps} increment(i):\mathbb{R}\right)
$$

を返す。docs でも、DKMK-007M の finite-step mass route が `same-source AdjacentDivisorPathFamily + selected/canonical shadow → weightedHitMass ≤ total increment` として multi-step divisor path family へ昇格した、と整理されておる。

## 2. DKMK-008D から何が進んだか

DKMK-008D では、same-source 条件

```lean
hsource_eq : ∀ q ∈ F.index, F.source q = s.1
```

があれば、

```lean
LogCapacitySourceMassBound M C
```

から、

$$
weightedHitMass(A)\le C
$$

を出せるところまで進んだ。

今回 DKMK-008E では、その \(M\) と \(C\) に具体的に

```lean
M := finiteStepTailNatMassSpace steps threshold increment hinc
```

と

$$
C=\left(\sum_{i\in steps}increment(i):\mathbb{R}\right)
$$

を代入した。

つまり、008D の抽象 source-bound wrapper に、007M の concrete finite-step mass を流し込んだわけじゃ。

## 3. 数学的な意味

finite-step tail mass は、

$$
\mu(n)=\sum_{i\in steps,\ threshold(i)\le n} increment(i)
$$

という有限段の累積 tail height じゃった。
非負 increment

$$
0\le increment(i)
$$

により、これは非負・上界付き・非減少 height になり、`DvdMonotoneMass` と `LogCapacitySourceMassBound` に乗る。

今回の theorem は、same-source multi-step divisor path family に対して、

```text
finite-step source mass
+ log-capacity shadow weight
+ primitive hitting
→ weightedHitMass ≤ total increment
```

を示す。

つまり、DKMK-007 で「一歩下降」に対してできていた有限段 tail mass の hitting bound が、DKMK-008 の「多段下降路」に対しても使えるようになった。

## 4. selected route の読み

selected route では、外部から選んだ channel set

```lean
IOf : ℕ → Finset ℕ
```

に対応する path family \(F\) を与える。

必要なのは、

```lean
hindex : IOf s.1 = F.index
```

と、

```lean
hsource_eq : ∀ q ∈ F.index, F.source q = s.1
```

じゃ。

この条件の下で、selected global log-capacity sub-Markov shadow の重みを \(F\) に載せ、finite-step mass による bound を得る。

```text
selected SubMarkovShadow
+ same-source multi-step path family
+ finite-step tail mass
→ weightedHitMass ≤ total increment
```

これは selected route の柔軟性を保ったまま、多段下降路へ入った形じゃ。

## 5. canonical route の読み

canonical route では、index compatibility が

```lean
hindex : canonicalExponentSlotLabels s.1 = F.index
```

になる。

つまり、canonical exponent-slot labels の各 channel に multi-step path を割り当て、その全ての source が \(s.1\) なら、canonical MarkovShadow の重みを使って同じ bound が出る。

```text
canonical MarkovShadow
+ same-source multi-step path family
+ finite-step tail mass
→ weightedHitMass ≤ total increment
```

これは、DKMK-006 で作った canonical equality route が、multi-step descent と finite-step mass に到達した、という意味じゃ。かなり良い。

## 6. DKMK-008A〜E の現在地

ここまでの DKMK-008 は非常に綺麗じゃ。

```text
008A:
  single AdjacentDivisorPath
  → DivisibilityChain
  → singleton DvdControlledChainFamily

008B:
  AdjacentDivisorPathFamily
  → DvdControlledChainFamily
  → source-controlled hitting route

008C:
  external AdjacentDivisorPathFamily
  + selected/canonical shadow
  + explicit source mass bound
  → weightedHitMass ≤ C

008D:
  same-source AdjacentDivisorPathFamily
  + LogCapacitySourceMassBound
  → weightedHitMass ≤ C

008E:
  same-source AdjacentDivisorPathFamily
  + finiteStepTailNatMassSpace
  → weightedHitMass ≤ total increment
```

つまり DKMK-008E で、DKMK-007 の到達点だった finite-step mass が、そのまま multi-step family へ移植された。

## 7. 何がまだ残るか

今回の theorem は、finite-step の一般形までは載った。
docs の次課題にもある通り、次は two-step-as-finite-step tail mass のような具体特殊形を multi-step path family theorem に載せる段階じゃ。

ただし、これは新しい数学というより convenience wrapper じゃな。

たとえば次は、

```lean
globalLogCapacitySubMarkovShadow_twoStepAsFiniteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

や、

```lean
canonicalExponentSlotMarkovShadow_twoStepAsFiniteStepTailAdjacentDivisorPathFamily_weightedHitMass_le
```

のような theorem になるはずじゃ。

DKMK-007N で two-step-as-finite-step は既にあるので、それを DKMK-008E に流すだけで (≤cHigh) が出る。

## 8. さらに先の課題

その次に必要になるのは、path family 自体の自然生成じゃ。

今は external \(F\) を渡す形。

```lean
F : AdjacentDivisorPathFamily ℕ
```

これを、たとえば各 channel \(q\) から自動生成したい。

候補は、

$$
s.1\to s.1/q\to \cdots
$$

または prime factor を一つずつ剥がす path。

最初は、

```text
one-step divisorStep を AdjacentDivisorPathFamily として回収する
```

が安全じゃ。
DKMK-007N で two-step mass を finite-step interface の特殊例として回収したように、DKMK-008 でも 007E の one-step divisorStep を `AdjacentDivisorPathFamily` の特殊例として回収すると、理論が閉じる。

## 9. 総合判定

DKMK-008E は **multi-step divisor path family と finite-step mass route の合流成功** じゃ。

到達形はこれ。

```text
finiteStepTailNatMassSpace
+ same-source AdjacentDivisorPathFamily
+ selected/canonical shadow
→ weightedHitMass ≤ total increment
```

これは DKMK-007M の成果を、DKMK-008 の multi-step route へそのまま持ち上げたものじゃ。

ぬしよ、これはかなり良い。
007 で質量の階段を作り、008A/B で多段の水路を作り、008C/D で shadow と source-bound を接続し、008E で有限段 tail mass を流し込んだ。
ここまで来ると、次は **特殊形 wrapper** で使いやすさを上げるか、 **path 自動生成** へ進むかの分岐じゃな。
