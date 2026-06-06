# review

うむ、DKMK-019C は **façade 章としての山頂に届いた** と見てよい。
DKMK-019B では source / envelope / mass-space までは短名化されたが、結論側にまだ `globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily ...` という長い quotient-path application が残っておった。今回 019C で、それを `logCapacitySourcePathFamily` として包み、最終 theorem の主語を path-family にできた。

## 1. 何が改善されたか

今回追加された surface は二つ。

```lean
PrimePowerWitnessProvider.logCapacitySourcePathFamily
PrimePowerWitnessProvider.logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
```

これにより、最終 theorem は次のように読める。

```lean
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A ≤
  1 + error
```

これはかなり大きい。
019B の時点では source 側は短くなったが、weighted-hit の対象がまだ raw construction だった。019C では **path family 自体が主語** になったので、定理文の意味がそのまま読めるようになった。

## 2. façade stack が完成した

DKMK-019 の façade stack は、これで揃った。

```text
logCapacitySourceRatIncrement
  -> logCapacitySourceTruncationEnvelope
  -> logCapacitySourceFiniteStepMass
  -> logCapacitySourcePathFamily
  -> weightedHitMass bound
```

この stack は、DKMK-018 の長い構成列をそのまま短名化したものじゃ。数学的に新しい評価を足すのではなく、既に閉じた route を読みやすい API として再提示している。
これは DKMK-019A の章目標「LogCapacity Source Facade」にぴったり合っておる。

## 3. 何が隠れたか

今回の成果は、次の二つを表面から隠したことじゃ。

```text
positiveRatIncrementBelow (...)
globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily ...
```

前者は 019B で `logCapacitySourceRatIncrement` に包まれた。
後者は 019C で `logCapacitySourcePathFamily` に包まれた。

これにより、利用者は

```text
LogCapacity source が作る path family
```

という単位で theorem を読める。

これは大事じゃ。なぜなら、次に別 source を追加するときにも、

```text
〇〇SourceRatIncrement
〇〇SourceTruncationEnvelope
〇〇SourceFiniteStepMass
〇〇SourcePathFamily
〇〇SourcePathFamily_weightedHitMass_le_one_add_error
```

という façade pattern を再利用できるからじゃ。

## 4. DKMK-019 は閉じてよいか

わっちの判断では、 **閉じてよい** 。

DKMK-019 の目的は、新しい source を増やすことではなかった。
目的は、DKMK-018F の caller friction を減らし、LogCapacity source route を安定した public surface に包むことじゃった。

019B で source / envelope / mass を包み、019C で path-family / bound を包んだ。
これ以上 wrapper を増やすと、むしろ冗長になる可能性がある。

したがって、次は

```text
DKMK-019D: completion report
```

として総括するのが自然じゃ。

## 5. 次章候補

DKMK-020 は二方向ある。

### 5.1. Analytic source expansion

LogCapacityKernel 以外の source を、この façade pattern に流す。たとえば、

```text
RealLog source
Dyadic-band provider
geometric majorant の一般化
```

を検討する。

今回の façade stack ができたので、別 source でも同じ型に寄せられる。

### 5.2. Threshold / support policy

現在の theorem は `threshold : ℕ -> ℕ` を外部から受けている。
次は `threshold` の自然な選び方、あるいは `IOf` と threshold の整合を固定する章にしてもよい。

ただし、わっちはまず 020 では **source expansion** よりも **threshold policy** を一段見た方がよいと思う。理由は、source を増やす前に「どの step をどの tail へ割り当てるか」の規格を固めると、後続 source が同じ座標系に乗るからじゃ。

## 6. 総合判定

DKMK-019C は成功じゃ。

現在の最終形は、

```lean
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A ≤
  1 + error
```

という、かなり読める theorem になった。
DKMK-018 の raw construction route は、DKMK-019 によって caller-facing façade へ変換された。

この賢狼の見立てでは、ここで DKMK-019 は **completed façade chapter** として締めるのがよい。次は DKMK-020 の設計に入れるぞい。
