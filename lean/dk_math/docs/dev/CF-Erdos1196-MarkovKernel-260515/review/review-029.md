# review

うむ。DKMK-007N は **DKMK-007M の finite-step interface が本当に既存 two-step tail mass を吸収できることを確認した回** じゃ。
DKMK-007K で作った two-step 専用 mass を捨てるのではなく、DKMK-007M の一般 finite-step route からも同じ (≤cHigh) bound を得られるようにした。つまり、 **個別実装から一般 interface への回収橋** が入ったわけじゃな。

## 1. 今回の核心

追加された中心は、この Bool-indexed 表現じゃ。

```lean
twoStepTailFiniteThreshold
twoStepTailFiniteIncrement
```

`twoStepTailFiniteThreshold N M` は、Bool の `false` 側を lower step (N)、`true` 側を upper step (M) として読む。

`twoStepTailFiniteIncrement cLow cHigh` は、

```text
false ↦ cLow
true  ↦ cHigh - cLow
```

という増分を与える。

つまり two-step mass の高さ

```text
0 → cLow → cHigh
```

を、finite-step の累積 increment として表現しておる。

$$
cHigh=cLow+(cHigh-cLow)
$$

この形にしたことで、DKMK-007M の `finiteStepTailHeight` にそのまま載せられる。

## 2. 非負性と total increment

今回、まず重要なのはこの二つ。

```lean
twoStepTailFiniteIncrement_nonneg
twoStepTailFiniteIncrement_sum
```

仮定は、

```lean
hLow : 0 ≤ cLow
hStep : cLow ≤ cHigh
```

じゃ。

これにより lower increment (cLow) は非負であり、upper increment (cHigh-cLow) も非負になる。

$$
0\le cLow,\quad 0\le cHigh-cLow
$$

さらに total increment は (cHigh) に戻る。

$$
\sum_{i\in Finset.univ:Finset\ Bool} twoStepTailFiniteIncrement(cLow,cHigh)(i)=cHigh
$$

ここが今回の要じゃ。
finite-step route の一般 theorem は上界として total increment を返す。だから two-step の上界を (cHigh) として復元するには、この補題が必要だった。

## 3. `twoStepAsFiniteStepTailNatMassSpace` の意味

今回追加された mass wrapper がこれじゃ。

```lean
twoStepAsFiniteStepTailNatMassSpace
```

これは既存の `twoStepTailNatMassSpace` を定義上置き換えるものではない。
むしろ、

```text
two-step data
→ Bool-indexed finite-step increments
→ finiteStepTailNatMassSpace
```

という経路を明示する wrapper じゃ。

docs にも、既存 `twoStepTailNatMassSpace` は維持しつつ、finite-step route から同じ bound を得る橋として追加したとある。

これは良い判断じゃ。
既存の直接 two-step model は読みやすい。
一方で、finite-step interface の特殊例としても使えることを示すと、今後の一般化の信頼性が上がる。

## 4. selected route への接続

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le
```

意味は、

```text
selected global log-capacity SubMarkovShadow
+ two-step data represented via finite-step interface
+ one-step divisorStep
+ PrimitiveOn A
→ weightedHitMass A ≤ cHigh
```

じゃ。

DKMK-007M の finite-step route では、上界が total increment になる。
今回 `twoStepTailFiniteIncrement_sum` により total increment が (cHigh) へ戻るので、two-step bound と同じ形が得られる。

## 5. canonical route への接続

canonical route 側にも対応する theorem が追加された。

```lean
canonicalExponentSlotMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le
```

こちらも到達形は同じ。

```text
canonical exponent-slot MarkovShadow
+ two-step-as-finite-step mass
+ one-step divisorStep
+ PrimitiveOn A
→ weightedHitMass A ≤ cHigh
```

canonical route は DKMK-006 系で Markov equality まで到達済みなので、mass 側の finite-step total bound がそのまま hitting bound の上界になる。

## 6. なぜ今回が重要か

DKMK-007M で finite-step interface ができた時点では、

```text
任意の finite-step height が通る
```

という一般論はあった。

今回 DKMK-007N では、過去に個別実装した two-step tail mass が、その一般論の中にきちんと入ることを確認した。

これはライブラリ設計として大事じゃ。

```text
DKMK-007K:
  two-step 専用 model

DKMK-007M:
  finite-step 一般 model

DKMK-007N:
  two-step を finite-step の特殊例として回収
```

この流れにより、今後は three-step / many-step を個別に増やすのではなく、finite-step constructor を使えばよい、という方針が確定しやすくなった。

## 7. 実装上の評価

Bool-indexed にしたのは良い選択じゃ。

```text
false:
  lower step

true:
  upper step
```

という二点 index により、two-step 構造を最小の finite-step として表現できる。

また、`Finset.univ : Finset Bool` の sum の表示順が expected type と合わない問題に対して、`twoStepTailFiniteIncrement_sum` を実数 cast した等式で明示的に上界を書き換えた、と記録されておる。
これは Lean 的に堅い。sum の正規形に依存せず、名前付き補題で制御している。

## 8. 現在の mass model route

ここまでで、DKMK-007 の mass route はかなり整理された。

```text
unit / nonunit
  ↓
tailIndicator
  ↓
scaledTailIndicator
  ↓
twoStepTailNatMassSpace
  ↓
boundedMonotoneNatMassSpace
  ↓
finiteStepTailHeight / finiteStepTailNatMassSpace
  ↓
twoStepAsFiniteStepTailNatMassSpace
```

最後の DKMK-007N により、過去の two-step が finite-step の中へ戻ってきた。
つまり、個別実装と一般実装が分裂せず、合流した。

## 9. 次の分岐

docs の次課題にもあるように、ここで DKMK-007A から DKMK-007N までの mass model route を短く総括するのが良い。

その後は、いよいよ DKMK-008 として、

```text
one-step divisor-step route
→ multi-step descent chain
```

へ進むのが自然じゃ。

ここまでで one-step 側は十分整った。

```text
log-capacity shadow
+ one-step divisorStep
+ finite-step mass
→ primitive weightedHitMass bound
```

次は chain 側を伸ばす番じゃな。

## 10. 総合判定

DKMK-007N は **一般 finite-step interface の健全性確認として成功** じゃ。

到達形はこう。

```text
two-step data cLow ≤ cHigh
  → Bool-indexed finite-step increments
  → finiteStepTailNatMassSpace
  → total increment = cHigh
  → divisor-step weightedHitMass ≤ cHigh
```

selected / canonical の両 route で通っている。
これで two-step は個別定理としても、finite-step interface の特殊例としても使える。

ぬしよ、これはよい締めじゃ。
質量側の階段は、もう「任意有限段」を受け止める台座まで来た。そろそろ DKMK-007 を一度総括し、次の DKMK-008 で multi-step descent chain へ山道を伸ばす頃合いじゃな。
