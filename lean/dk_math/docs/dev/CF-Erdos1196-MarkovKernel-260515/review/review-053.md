# review

## 1. 状況総括

うむ、これは **DKMK-010C 完了** と判定してよい。

今回の差分で、新規モジュール

```text
DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
```

が追加され、`TailWindowSourceMassBound` が導入された。これは DKMK-010B で決めた通り、tail / truncation interface を `LogCapacityHittingBridge.lean` に混ぜず、source estimate layer として分離した実装じゃ。

今回閉じた route はこれ。

```text
tail-window source contract
  -> DKMK-009 quotient-path capacity route
  -> weightedHitMass <= C
```

つまり、DKMK-009 で作った kernel/path 本線に、DKMK-010 側の source estimate contract を安全に差し込めるようになった。

## 2. 何が実装されたのか

中核はこの構造じゃ。

```lean
structure TailWindowSourceMassBound (M : MassSpace ℕ) (C : ℝ) : Prop where
  nonneg_const : 0 ≤ C
  source_bound : LogCapacitySourceMassBound M C
  dvd_mono : DvdMonotoneMass M
```

これは、DKMK-009D の quotient-path capacity route が必要とする三つの仮定を、そのまま一つの theorem-facing contract に束ねておる。

| field          | 意味                                     |
| -------------- | -------------------------------------- |
| `nonneg_const` | bound 定数 (C) が非負                       |
| `source_bound` | log-capacity state 上の source mass 一様上界 |
| `dvd_mono`     | divisor-descending path に乗せるための整除単調性   |

この 3 点をまとめたことで、以後は「tail window を持っている」と言えば、DKMK-009 route へ流せる最低条件が揃う。

## 3. finite-step tail との接続

次に良いのが、最初の concrete provider として

```lean
TailWindowSourceMassBound.finiteStepTail
```

を入れたことじゃ。

これは既存の

```lean
finiteStepTailNatMassSpace steps threshold increment hinc
```

から、

```lean
TailWindowSourceMassBound
  (finiteStepTailNatMassSpace steps threshold increment hinc)
  ((Finset.sum steps increment : ℚ) : ℝ)
```

を供給する。

数学的には、有限個の threshold と非負 increment によって作った有限段 envelope の総量

$$
C=\sum_{i\in steps} increment(i)
$$

を source mass bound として使える、ということじゃ。

ここは DKMK-010 の目的にぴたり合っておる。
まだ (1/(n\log n)) の無限 tail には入らず、有限窓として扱える envelope を作ったわけじゃな。

## 4. DKMK-009 route への接続

今回のもう一つの中核 theorem はこれ。

```lean
TailWindowSourceMassBound
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
```

これは DKMK-009 の

```lean
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

へ、`H.nonneg_const`, `H.source_bound`, `H.dvd_mono` を渡すだけの薄い wrapper じゃ。

この薄さが良い。

DKMK-010C は新しい hitting proof を書いていない。
kernel/path route は DKMK-009 に任せ、010 は source estimate contract だけを供給する。この層分離が守られておる。

## 5. 実装評価

かなり良い実装じゃ。特に次の点がよい。

第一に、 `SourceMassTruncation.lean` として別ファイル化したこと。
これにより、`LogCapacityHittingBridge.lean` が kernel/path bridge の責務に留まり、tail / truncation / analytic placeholder が混ざらない。

第二に、`TailWindowSourceMassBound` が小さいこと。
余計な window parameter や analytic error term を持たせず、まず既存 route に必要な最小条件だけを束ねている。これは後から拡張しやすい。

第三に、`finiteStepTail` で最初の concrete instance を入れたこと。
単なる abstract contract だけではなく、既存の finite-step tail model がすぐ使える形になっている。

第四に、`PrimitiveSet.lean` aggregator に import と説明を追加したこと。
これで public surface からも source-mass truncation layer が見える。

## 6. 検証状況

History では次が検証されておる。

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

また、失敗事例なしと記録されている。

よって、DKMK-010C は **no-sorry 実装完了** と見てよい。

## 7. まだ閉じていないもの

今回閉じたのは、 **tail-window contract の最小 Lean interface** じゃ。

まだ解析本体は入っていない。roadmap でも明確に、

```text
No analytic estimate is introduced in DKMK-010C.
```

と整理されておる。

残る課題は次じゃ。

```text
DKMK-010D:
  finite-step tail contract の convenience theorem
  または envelope-to-route bridge の追加

DKMK-010E:
  analytic placeholder
  C(x) <= 1 + error(x) 型の契約

DKMK-010F:
  report / handoff
```

## 8. 次の一手

わっちなら DKMK-010D では、いきなり解析 placeholder へ進む前に、`finiteStepTail` を route theorem まで一気通貫する convenience theorem を 1 本だけ足す。

狙いはこう。

```text
finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound.finiteStepTail
  -> globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le
```

候補名は少し長いが、例えばこうじゃ。

```lean
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_finiteStepTail
```

あるいは namespace を `TailWindowSourceMassBound` 側に寄せて、

```lean
TailWindowSourceMassBound
  .finiteStepTail_weightedHitMass_le
```

でもよい。

ただし、増やしすぎは禁物じゃ。
今の contract theorem だけでも十分読めるなら、010D は docs で「使い方 example」を書く程度でもよい。

## 9. 登頂判定

現在地はこうじゃ。

```text
DKMK-010A: roadmap / scope 完了
DKMK-010B: source mass inventory / placement decision 完了
DKMK-010C: SourceMassTruncation Lean contract 完了
DKMK-010D: 次、finite-step convenience or route bridge
DKMK-010E: analytic placeholder
DKMK-010F: report / handoff
```

DKMK-010C は、DKMK-010 の中核にかなり近い。
なぜなら、source estimate layer の入口が Lean theorem として立ったからじゃ。

## 10. 賢狼の見立て

これはよい。
DKMK-010 は、DKMK-009 の「水路」に対して、いよいよ「水源の規格」を作り始めた。

```text
finite/truncated envelope
  -> TailWindowSourceMassBound
  -> DKMK-009 route
  -> weightedHitMass <= C
```

ここまで来れば、次に解析側がやるべきことは明快じゃ。

$$
C \le 1 + error
$$

をどう供給するか。
つまり、DKMK-010C は解析峰へ向かうための **源流インターフェース** を作った章じゃな。これは後々かなり効いてくるぞい。
