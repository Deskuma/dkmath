# review

うむ、DKMK-018F は **章末 theorem として正しい着地** じゃ。
DKMK-018 はここで **completed analytic source replacement milestone** と見てよい。

## 1. 何が閉じたか

今回追加されたのは、

```lean
PrimePowerWitnessProvider.logCapacityKernel_finiteStepTail_weightedHitMass_le_one_add_error
```

じゃな。これは 018E で得た

```text
LogCapacityKernel Real provider
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
```

を、DKMK-017 の終端側である

```lean
TruncationEnvelopeEstimate.finiteStepTail_weightedHitMass_le_one_add_error
```

へ直接流し、

$$
\mathrm{weightedHitMass}(A)\le 1+\mathrm{error}
$$

まで到達させておる。添付 diff でも、この theorem は 018E の envelope を DKMK-017 finite-step weighted-hit bound に直結した章末接続と整理されている。

## 2. DKMK-018 全体の意味

DKMK-018 の流れは、かなり綺麗に閉じた。

```text
018A: source candidate survey
018B: Real majorant -> Rat envelope bridge
018C: LogCapacityKernel Real provider attachment
018D: positive rational under-approximation
018E: log-capacity provider の strict positivity
018F: weighted-hit bound への end-to-end 接続
```

つまり、最初に問題だった

```text
Real-valued analytic source は既存 Rat route に流せるのか？
```

への答えは、

**流せる。しかも LogCapacityKernel 由来の concrete source で weightedHitMass bound まで到達できる。**

になったわけじゃ。

これは DKMK-017 の `geometricIncrement` を、少なくとも最初の本命候補である `LogCapacityKernel` 由来 source に置き換える道が開通した、ということじゃな。

## 3. 重要な評価点

今回の theorem は、添付 roadmap にある通り **新しい解析を足した theorem ではなく wrapper** じゃ。だが、これは弱点ではない。むしろ章末 theorem としては正しい。

なぜなら DKMK-018 の目的は、新解析ではなく、

```text
LogCapacityKernel source が DKMK-017 route を end-to-end で走れること
```

を Lean 上に記録することだったからじゃ。

したがって、今回の成果は「強い新補題」ではなく、 **既存の強い部品が正しく合流したことの証明** じゃ。

この種の theorem は、後で読み返した時に非常に効く。
証明本文が長くても、名前ひとつで登山路全体を呼べるからの。

## 4. 現在の到達点を一文で言うと

DKMK-018F により、

```text
LogCapacityKernel Real provider
  -> strict positive Real weights
  -> positive Rat under-approximation
  -> TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> quotient-path weightedHitMass bound
```

が一本の Lean theorem として接続された。

これは **analytic source replacement route の完成** と言ってよい。

## 5. 次にすべきこと

わっちの推奨は、ここで一度 **DKMK-018 総括** を入れることじゃ。

次章に進む前に、最低限これを整理した方がよい。

```text
1. DKMK-017 で何が閉じていたか
2. DKMK-018 で何を置き換えたか
3. toy geometric source と LogCapacityKernel source の違い
4. end-to-end theorem の推奨入口
5. 次章で攻める未解決点
```

その上で、次章候補は二つ。

第一候補は **API 整理章**。
今回の theorem は強いが、型が長い。`s.1`, `IOf s.1`, `positiveRatIncrementBelow ...` が全面に出るので、次は短い façade theorem を置くと使いやすくなる。

第二候補は **解析 source 拡張章**。
LogCapacityKernel 以外の RealLog / dyadic-band source を同じ bridge に流せるかを試す。こちらは新ルート探索じゃ。

## 6. わっちの判断

今は次へ急ぎすぎず、まず **DKMK-018 完了報告** がよい。

DKMK-018 は、A から F まで無駄が少ない。
「型の谷」を見つけ、「橋」を架け、「本命 source」を通し、「正の Rat source」に落とし、「weightedHitMass bound」まで運んだ。

これは良い章じゃ。
この賢狼が見ても、今回の登山はかなり締まっておるぞい。
