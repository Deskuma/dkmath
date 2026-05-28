# review

うむ。DKMK-008L は、 **DKMK-008K で作った witness-derived quotient path family を、selected / canonical の weightedHitMass bound へ直結した回** じゃ。
これで DKMK-008 は、「path を外から受け取る」段階だけでなく、 **selected / canonical labels から witness 由来の multi-step path を自動生成し、そのまま finite-step / two-step mass bound へ流す theorem-facing API** を持つようになった。

## 1. 今回の核心

追加された入口は 4 本じゃ。

selected route:

```lean
PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_finiteStepTailPrimePowerQuotientPathFamily_weightedHitMass_le

PrimePowerWitnessProvider
  .globalLogCapacitySubMarkovShadow_twoStepTailPrimePowerQuotientPathFamily_weightedHitMass_le
```

canonical route:

```lean
canonicalExponentSlotMarkovShadow_finiteStepTailPrimePowerQuotientPathFamily_weightedHitMass_le

canonicalExponentSlotMarkovShadow_twoStepTailPrimePowerQuotientPathFamily_weightedHitMass_le
```

意味は、それぞれ次の流れじゃ。

```text
selected / canonical labels
→ witness-derived quotient path family
→ finite-step / two-step source mass
→ weightedHitMass bound
```

docs でも、この段階で DKMK-008 は `witness-derived quotient path family → finite-step / two-step source mass → selected / canonical weightedHitMass bound` まで theorem-facing API として到達した、と整理されている。

## 2. DKMK-008K から何が進んだか

DKMK-008K では、

```lean
W.primePowerQuotientPathFamily n I hI
```

が作られた。
これは各 (q\in I) に対して witness provider から

$$
p(q)=W.basePrimeOf(n,I,hI,q),\qquad k(q)=W.baseExponentOf(n,I,hI,q)
$$

を読み、

$$
n\to n/p(q)\to n/p(q)^2\to\cdots\to n/p(q)^{k(q)}
$$

という path を `AdjacentDivisorPathFamily` に載せるものじゃった。

今回 DKMK-008L では、この family を DKMK-008E/F の same-source theorem に直接渡した。
つまり、K は **path family の自動構成** 、L は **その path family を hitting bound に接続** した回じゃ。

## 3. selected route の読み

selected finite-step 版では、state (s) に対して

```lean
W.primePowerQuotientPathFamily s.1 (IOf s.1)
  (fun q hq => hIOf s.1 q hq)
```

を作る。

ここで (IOf(s.1)) が selected labels であり、`hIOf` により各 (q) が transition kernel の index に属することを保証する。

この family の source は常に (s.1)。
したがって same-source 条件は、

```lean
W.primePowerQuotientPathFamily_source_eq ...
```

で供給できる。

そして finite-step mass なら、

$$
weightedHitMass(A)\le \left(\sum_{i\in steps} increment(i):\mathbb{R}\right)
$$

two-step mass なら、

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

が出る。

つまり selected route は、外部 path family を手で組まずとも、

```text
IOf(s.1)
→ witness-derived quotient path family
→ weightedHitMass bound
```

まで一発で行けるようになった。

## 4. canonical route の読み

canonical 版では index が固定されている。

```lean
canonicalExponentSlotLabels s.1
```

そして path family は、

```lean
canonicalExponentSlotWitnessProvider.primePowerQuotientPathFamily
  s.1 (canonicalExponentSlotLabels s.1) (fun _ hq => hq)
```

で作られる。

canonical route では index が canonical labels に固定されているため、compatibility は `rfl` で閉じる、と docs にも整理されておる。

これはとても良い。
canonical 側は DKMK-006 から続く「標準 full route」なので、ここで witness-derived multi-step path family と直結した意義は大きい。

## 5. 数学的な意味

今回の到達形は、次のように読める。

各 selected / canonical label (q) は、prime-power witness により

$$
q=p(q)^{k(q)}
$$

と読まれる。

その (q) を一発で

$$
n\to n/q
$$

と落とすのではなく、

$$
n\to n/p(q)\to n/p(q)^2\to\cdots\to n/p(q)^{k(q)}
$$

という **指数スロットをなぞる下降路** に展開する。

その path family に log-capacity shadow の重みを載せ、finite-step / two-step source mass で primitive hitting を抑える。

つまり、

$$
\text{prime-power witness}
$$

が、

```text
log weight の供給源
```

であるだけでなく、

```text
multi-step descent path の生成源
```

にもなった。

ここが DkMath kernel route として実に美しいところじゃ。
R-log route で読んだ (p,k) が、質量重みと下降 path の両方に使われておる。

## 6. DKMK-008A〜L の現在地

ここまでの DKMK-008 は、かなり整った。

```text
008A:
  single AdjacentDivisorPath

008B:
  AdjacentDivisorPathFamily

008C:
  external path family を selected / canonical shadow に接続

008D:
  same-source 条件で LogCapacitySourceMassBound を合成

008E:
  finite-step mass bound

008F:
  two-step mass bound

008G:
  one-step divisorStep を path-family 特殊例として回収

008H:
  one-step selected / canonical wrappers

008I:
  docs report

008J:
  p^k ∣ n から primePowerQuotientPath を生成

008K:
  witness provider 由来の quotient path family を構成

008L:
  witness-derived quotient path family を selected / canonical mass bound へ直結
```

流れとしては、008 はもう **外部 path 受け口の章** から **witness-derived path 自動生成の章** へ移行した、と見てよい。

## 7. 今回の実装の良い点

今回の wrapper は薄い。
DKMK-008E/F の既存 theorem に、

```lean
W.primePowerQuotientPathFamily ...
```

を渡しているだけじゃ。

これは良い設計じゃ。
新しい数学を重複証明していない。008A〜K で作った部品が、今回自然に合成されている。

また canonical wrapper で `fun q hq => hq` の unused variable warning を避けるため `fun _ hq => hq` にしたという記録も、実装品質として堅い。

## 8. まだ残る課題

History の次課題では、

```text
quotient path family wrapper を examples / theorem comparison 表に載せ、
one-step route と multi-step witness route の使い分けを整理する。
```

とされている。

これは妥当じゃ。
ここまで theorem が増えてきたので、次はドキュメント上で使い分けを明確にした方がよい。

特に整理すべき比較はこれじゃ。

```text
DKMK-007:
  one-step divisorStep route

DKMK-008H:
  one-step path-family route

DKMK-008L:
  witness-derived prime-power quotient path route
```

数学的には、

```text
one-step:
  q を一発で剥がす

prime-power quotient path:
  q = p^k を p, p^2, ..., p^k の段階に展開して剥がす
```

この違いを docs/report の対応表に載せると、次の利用時に迷わぬ。

## 9. 次の一手

わっちなら DKMK-008M は docs / examples 寄りを推す。

候補は三つ。

第一に、`report-DKMK-008.md` に comparison table を追加する。

```text
007 divisorStep
008 oneStepPath
008 primePowerQuotientPathFamily
```

第二に、小さな concrete example を追加する。
たとえば (72,3,2) の path は既にあるので、これを witness-derived family 側で見える例にするか、docs に図示する。

第三に、theorem naming の導線を整理する。
`PrimePowerQuotientPathFamily` 系 theorem は名前が長いので、推奨入口を report に明示しておくのがよい。

## 10. 総合判定

DKMK-008L は **witness-derived multi-step path route が weightedHitMass bound まで到達した成功フェーズ** じゃ。

到達形はこう。

```text
selected / canonical labels
→ witness-derived (p(q), k(q))
→ n → n/p(q) → ... → n/p(q)^k(q)
→ finite-step / two-step mass
→ weightedHitMass bound
```

これで DKMK-008 は、DKMK-007 の one-step route を含みつつ、さらに prime-power witness を内部展開した multi-step route まで持つようになった。

ぬしよ、これは良い。
今までは「道を外から渡す」か「一歩だけ下る」だった。
いまや (q=p^k) というラベルを見ただけで、賢狼の足元に (p)-段の下降路が自動で敷かれる。山道が、ついに地形から自生し始めたのじゃ。
