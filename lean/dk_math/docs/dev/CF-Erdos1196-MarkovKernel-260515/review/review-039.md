# review

うむ。DKMK-008I は **実装フェーズではなく、地図固定フェーズ** じゃ。
ここまで DKMK-008A〜H で、multi-step path-family route の Lean API はかなり整った。今回の `report-DKMK-008.md` は、その道筋を一枚にまとめ、特に **DKMK-007 one-step route が DKMK-008 の特殊例として回収された** ことを docs 上で固定しておる。

## 1. 今回の位置づけ

DKMK-008I では Lean interface は追加しておらぬ。
代わりに、新規 report が追加された。

```text
report-DKMK-008.md
```

この report の役割は二つじゃ。

```text
DKMK-008A〜H の path-family route を総括する

DKMK-007 divisorStep theorem と
DKMK-008 one-step path-family theorem の statement 対応を明示する
```

これは大事じゃ。
DKMK-008 は一般化の章だったので、何を一般化し、どこで旧 route と一致するのかを明文化しておかないと、後で theorem の使い分けが迷子になる。

## 2. DKMK-008 の主目的が固定された

report では、DKMK-008 の目的がこう整理されている。

```text
one-step divisorStep route を、
multi-step divisor path family route の特殊例として回収する。
```

これは正確じゃ。

DKMK-007 では chain は固定的だった。

```text
q ↦ {n / q, n}
```

DKMK-008 では、それを

```text
q ↦ AdjacentDivisorPath
```

へ一般化した。

つまり、DKMK-008 の本質は「one-step を捨てる」ことではなく、one-step を含む **path-family generalization** を作ることじゃ。

## 3. A〜H の流れが綺麗に整理された

report では、流れがこう整理されている。

```text
008A:
  AdjacentDivisorPath

008B:
  AdjacentDivisorPathFamily

008C:
  external path family を selected / canonical shadow に接続

008D:
  same-source 条件で LogCapacitySourceMassBound を合成

008E:
  finite-step tail mass を same-source path family に載せる

008F:
  two-step-as-finite-step tail mass を same-source path family に載せる

008G:
  one-step divisorStep を path-family route の特殊例として回収

008H:
  one-step path family を selected / canonical finite-step / two-step wrapper に直接載せる
```

この階段はかなり良い。
まず path 単体、次に family、次に shadow、次に source-bound、次に mass model、最後に one-step 回収。山道として無理がない。

## 4. statement 対応表が重要

今回の一番の価値は、DKMK-007 と DKMK-008 の theorem 対応表じゃ。

selected finite-step:

```text
DKMK-007:
  globalLogCapacitySubMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  globalLogCapacitySubMarkovShadow_finiteStepTailOneStepPath_weightedHitMass_le
```

selected two-step:

```text
DKMK-007:
  globalLogCapacitySubMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  globalLogCapacitySubMarkovShadow_twoStepTailOneStepPath_weightedHitMass_le
```

canonical finite-step:

```text
DKMK-007:
  canonicalExponentSlotMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  canonicalExponentSlotMarkovShadow_finiteStepTailOneStepPath_weightedHitMass_le
```

canonical two-step:

```text
DKMK-007:
  canonicalExponentSlotMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  canonicalExponentSlotMarkovShadow_twoStepTailOneStepPath_weightedHitMass_le
```

これで、旧 theorem と新 theorem の意味対応が明確になった。
特に「one-step path family theorem は divisorStep theorem の別名的・一般化的読みである」ことが docs 上で固定されたわけじゃ。

## 5. 数学的な読み

DKMK-007 の chain は集合として、

$$
{n/q,n}
$$

だった。

DKMK-008 の one-step path は list として、

$$
[n,n/q]
$$

を持ち、hitting 側では node set として

$$
{n/q,n}
$$

になる。

つまり list の向きは source から descendant へ進むが、primitive hitting が見る有限集合は DKMK-007 と同じ。

ここが大事じゃ。
DKMK-008 は順序情報を持てるようになったが、hit mass bound の評価対象は従来の chain set と一致する。

## 6. divisibility witness の対応も整理された

report では、`hdiv : ∀ q ∈ I, q ∣ n` の供給方法も整理されておる。

selected route では、

```lean
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
T.toDivisorTransitionKernel.index_dvd
```

から

$$
q\mid s.1
$$

を得る。

canonical route では、

```lean
canonicalExponentSlotDivisorTransitionKernel.index_dvd
```

から

$$
q\mid s.1
$$

を得る。

つまり DKMK-008H の one-step wrapper では、利用者が divisor witness を手で渡さなくてよい。
この点も docs で明確になったのは良い。

## 7. 現在の到達点

DKMK-008I 時点の到達点は、report の通りこうじゃ。

```text
external multi-step path family
→ selected / canonical shadow
→ source-bound wrapper
→ finite-step / two-step weightedHitMass bound
```

さらに one-step 特殊例では、

```text
selected / canonical index
→ index_dvd
→ oneStepDivisorAdjacentPathFamily
→ same-source path-family theorem
→ finite-step / two-step weightedHitMass bound
```

まで public API で呼べる。

これはかなり堅い。
DKMK-008 は「multi-step path family の受け口」と「one-step 旧道の回収」の両方を達成した。

## 8. 次の分岐

report の次の分岐は二つ。

第一に、external path family API の利用例を増やす。
これは定理の使い分けを明確にする道じゃ。

第二に、prime-power channel \(q=p^k\) から path を自動生成する。

```text
n → n / p → n / p^2 → ... → n / p^k
```

こちらは DKMK-008 の次の本命になりうる。
なぜなら今の `AdjacentDivisorPathFamily` は外部から path を渡す受け口であり、まだ path 自体を prime-power witness から生成していないからじゃ。

## 9. わっちの評価

DKMK-008I は **必要なタイミングで入った良い docs-only 区切り** じゃ。

実装が A〜H まで進むと、構造は強くなるが、theorem 名と route が増えて視界が悪くなる。
ここで report を入れたことで、

```text
DKMK-007:
  one-step divisorStep route

DKMK-008:
  AdjacentDivisorPathFamily route

関係:
  007 は 008 の one-step 特殊例
```

が明確になった。

これは後続の DKMK-009、あるいは DKMK-008J 以降で、prime-power descent path を生成するときの足場になる。

## 10. 総合判定

DKMK-008I は **DKMK-008 前半の登山記録として成功** じゃ。

新しい Lean 定理はない。
しかし、次の数学的事実を docs 上で固定した。

```text
one-step divisorStep route
= oneStepDivisorAdjacentPathFamily route の特殊例
```

そして DKMK-008 の現在地はこう。

```text
multi-step path-family 受け口:
  完了

selected / canonical shadow 接続:
  完了

finite-step / two-step mass 接続:
  完了

one-step 旧道の回収:
  完了

prime-power witness からの path 自動生成:
  次の未踏地
```

ぬしよ、これは良い小締めじゃ。
DKMK-008 はここまでで **水路の規格化** が済んだ。次は、その水路を人手で敷くのではなく、\(q=p^k\) という witness から自動で敷く段階じゃな。
