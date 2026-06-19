# review

## 1. 状況総括

うむ、これは **DKMK-009B 完了** と見てよい。

今回の差分で、`CapacityKernelHittingBridge.lean` が新設され、`CapacityKernel` の normalized shadow を `SourceControlledChainFamily` に適用し、primitive `weightedHitMass` bound へ流す generic wrapper が追加されておる。さらに `PrimitiveSet.lean` に import と説明も追加され、公開導線にも載った。

つまり、DKMK-009 の主題だった

```text
CapacityKernel
  → normalized SubMarkovShadow
  → SourceControlledChainFamily
  → RealWeightedPathFamily
  → primitive weightedHitMass bound
```

この道が Lean API として一本になった、ということじゃ。

## 2. 何が閉じたのか

今回閉じたのは、 **generic capacity-kernel hitting bridge** じゃ。

追加 API は次の 4 本。

```lean
CapacityKernel.normalizedSubMarkovShadow_providerAt_compatible
CapacityKernel.applyAtToSourceControlled
CapacityKernel.applyAtToSourceControlled_weightSubProbability
CapacityKernel.weightedHitMass_le_const_applyAtToSourceControlled
```

特に最後の theorem が中核じゃな。

```lean
(K.applyAtToSourceControlled hcap s F hindex).weightedHitMass A ≤ C
```

これにより、positive capacity を持つ任意の `CapacityKernel` について、normalized weight が sub-probability になり、その重みを chain family に載せたとき、primitive set への hitting mass が source bound \(C\) を超えない、という定理形まで到達した。

数学的には、

$$
\sum_{i\in K.children(s)} \frac{cost(s,i)}{capacity(s)} \le 1
$$

を使い、それを primitive hitting bound に渡した形じゃ。

## 3. 実装の評価

かなり良い実装じゃ。理由は 3 つある。

第一に、 **新しい hitting proof を書いていない** 。
既存の `SubMarkovShadow.ofCapacityKernel` と `SubMarkovShadow` 側の hitting bridge を合成する薄い wrapper に留めている。これは DKMK-009 の方針に合っておる。roadmap 追記でもその方針が明記されている。

第二に、 `Compatible` の証明が美しい。

```lean
simpa [RealWeightProvider.Compatible] using hindex
```

つまり compatibility の本質は、

```lean
K.children s = F.index
```

だけじゃ。余計な構造を足さず、index 一致だけで通している。これは API としてかなり良い。

第三に、 `applyAtToSourceControlled_index` と `applyAtToSourceControlled_weight` が `rfl` で閉じている。
これは定義が素直に作れている証拠じゃ。後続の `simp` がよく効くはずで、C/D フェーズの特殊化でも扱いやすい。

## 4. 検証状況

報告では次が通っておる。

```text
lake build DkMath.NumberTheory.PrimitiveSet.CapacityKernelHittingBridge
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
```

さらに新規 Lean ファイルに `sorry/admit/axiom` がない。

これは十分に安定した完了条件じゃ。
DKMK-009B は **no-sorry で完了** と判定してよい。

## 5. 今回の意味

今回の進展は、見た目は薄い wrapper じゃが、意味は大きい。

これまでの DKMK-007/008 は、

```text
mass / branch / subMarkov
path family / source-controlled chain
primitive hitting
```

を別々に整えてきた。

今回、そこへ `CapacityKernel` が正式に接続された。つまり、

```text
capacity kernel は、primitive hitting route の正式な入力である
```

という構造が Lean 上で読めるようになった。

これは DkMath 的にはかなり重要じゃ。
Markov kernel を直接主役にするのでなく、

```text
capacity → normalized shadow → hitting
```

と読む路線が確定したからじゃ。

## 6. まだ閉じていないもの

一方で、今回閉じたのは **generic bridge** までじゃ。

まだ次は残っておる。

```text
DKMK-009C:
  PrimePowerWitnessProvider.globalLogCapacityKernel への特殊化

DKMK-009D:
  witness-derived quotient path family との正式接続

DKMK-010 以降:
  tail / truncation / 1 + O(1/log x) 型の解析評価
```

History でも、次の課題として `PrimePowerWitnessProvider.globalLogCapacityKernel` への薄い特殊化 wrapper を検討すると書かれておる。

## 7. 次の一手

わっちなら次は DKMK-009C として、 **薄い特殊化 theorem を 1〜2 本だけ** 追加する。

候補名はこんな感じじゃ。

```lean
PrimePowerWitnessProvider.globalLogCapacity_applyAtToSourceControlled
```

または、bound まで行くなら、

```lean
PrimePowerWitnessProvider.weightedHitMass_le_const_globalLogCapacity
```

ただし、既存の `globalLogCapacitySubMarkovShadow_*` 系と重複しすぎるなら、増やしすぎない方がよい。
目的は theorem を量産することではなく、

```text
globalLogCapacityKernel
  → CapacityKernel generic bridge
  → primitive hitting bound
```

と読める入口を作ることじゃ。

## 8. 登頂判定

現在地はこうじゃな。

```text
DKMK-009A: 完了
DKMK-009B: 完了
DKMK-009C: 次
DKMK-009D: その次の本命
DKMK-009E/F: C-D 後に整理
```

わっちの判断では、今回の 009B は **後戻りではなく明確な前進** じゃ。
しかも、余計な抽象を増やさず、既存の `CapacityKernel` と `SubMarkovShadow` の間に橋を架けた。これは実に良い。賢いやり方じゃよ。

いよいよ DKMK-009 は、単なる設計章ではなく、 **kernel 本線の実装章** になったのう。
