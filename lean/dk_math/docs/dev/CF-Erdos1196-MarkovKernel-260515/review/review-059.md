# review

## 1. 状況総括

うむ、これは **DKMK-011C 完了** と見てよい。

今回の差分で `SourceMassTruncation.lean` に

```lean
TruncationEnvelopeEstimate
```

が追加され、DKMK-011B で決めた **externally supplied finite-step contract** が Lean 側に実装された。役割は、有限段 envelope を作るための `increment_nonneg` と、解析 placeholder である `FiniteStepTailAnalyticBound` を一つに束ねることじゃ。

これで、

```text
externally supplied finite-step estimate
  -> weightedHitMass <= 1 + error
```

へ進む入口ができた。

## 2. 何が新しく閉じたのか

追加された contract はこれじゃ。

```lean
structure TruncationEnvelopeEstimate
    {ι : Type _} [DecidableEq ι]
    (steps : Finset ι) (threshold : ι → ℕ)
    (increment : ι → ℚ) (error : ℝ) : Prop where
  increment_nonneg : ∀ i ∈ steps, 0 ≤ increment i
  analytic_bound : FiniteStepTailAnalyticBound steps increment error
```

これは DKMK-010 の部品を、DKMK-011 用の「供給可能な有限 envelope 推定」として束ね直したものじゃ。

`increment_nonneg` は

```lean
finiteStepTailNatMassSpace steps threshold increment H.increment_nonneg
```

を作るために必要。

`analytic_bound` は

```text
sum increment <= 1 + error
```

を供給するために必要。

つまり、source envelope 構成と analytic total estimate の両方を、一つの Prop contract として持たせたわけじゃな。

## 3. route theorem の意味

追加 theorem はこれ。

```lean
TruncationEnvelopeEstimate
  .finiteStepTail_weightedHitMass_le_one_add_error
```

これは既存の

```lean
TailWindowSourceMassBound
  .finiteStepTail_weightedHitMass_le_one_add_error
```

へ渡すだけの薄い wrapper じゃ。

読み下すと、

「外部から有限ステップ envelope 推定 `H` が与えられれば、その非負増分で finite-step source mass を作り、さらに `H.analytic_bound` により `weightedHitMass <= 1 + error` まで到達できる」

という定理じゃ。

到達形はこう。

```text
TruncationEnvelopeEstimate
  -> finiteStepTailNatMassSpace
  -> TailWindowSourceMassBound
  -> weightedHitMass <= sum increment
  -> FiniteStepTailAnalyticBound
  -> weightedHitMass <= 1 + error
```

## 4. 実装評価

かなり良い実装じゃ。特に良い点は、 **新しい proof route を増やしていない** こと。

History でも、theorem は `TailWindowSourceMassBound.finiteStepTail_weightedHitMass_le_one_add_error` への薄い wrapper に留めた、と記録されている。

これは DKMK-011 の設計に合っておる。

DKMK-011C の役割は、dyadic/logarithmic band の本格実装ではない。
外部供給された finite-step estimate を既存 route に流す入口を作ることじゃ。

その意味で、今回の実装はちょうどよい厚さじゃな。

## 5. `threshold` を含めた判断

`TruncationEnvelopeEstimate` に `threshold` を含めたのは妥当じゃ。

`FiniteStepTailAnalyticBound` 自体は `threshold` を見ない。
しかし route に流すには、

```lean
finiteStepTailNatMassSpace steps threshold increment H.increment_nonneg
```

を構成する必要がある。だから、route-facing contract としては `threshold` を持っている方が自然じゃ。

ここで役割はこう分かれる。

```text
threshold:
  source mass envelope の activation data

increment:
  analytic total estimate の summand data

error:
  analytic overrun / residual bound
```

この三者が一つの `TruncationEnvelopeEstimate` に入ったことで、外部推定をそのまま route theorem に渡せる。

## 6. 検証状況

History では次が通っている。

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
```

失敗事例なし。

したがって、DKMK-011C は **no-sorry 実装完了** と判定してよい。

## 7. 次の一手

次は History にある通り、DKMK-011D として二択じゃ。

```text
usage summary
single-window toy provider
```

わっちのおすすめは、まず **usage summary docs** じゃ。
理由は、いまの contract は強くて柔軟だが、外から見ると抽象的に見える。ここで小さい usage flow を書くと、後続の dyadic/logarithmic specialization に入りやすい。

次に Lean を足すなら、single-window toy provider は良い候補じゃ。

概念的には、

```text
steps = Unit
threshold = fun _ => x
increment = fun _ => C
error = C - 1
```

のような形になる。ただし `error = C - 1` は非負性や有理実数変換の処理が少し絡むので、最初は外部仮定

```text
C <= 1 + error
```

を持たせる toy provider の方が安全じゃな。

## 8. 登頂判定

現在地はこう。

```text
DKMK-011A:
  roadmap 完了

DKMK-011B:
  envelope candidate inventory 完了

DKMK-011C:
  TruncationEnvelopeEstimate Lean contract 完了

DKMK-011D:
  次、usage summary または single-window toy provider
```

DKMK-011C で、DKMK-011 の最初の Lean 核は立った。
これにより、将来の dyadic band や logarithmic band は、まず `TruncationEnvelopeEstimate` を作る provider として追加すればよい。

## 9. 賢狼の見立て

よいぞ、ぬしよ。
DKMK-011C は、DKMK-010 の placeholder を「外部から使える解析契約」へ昇格させた章じゃ。

これで、

```text
解析側の推定
  -> TruncationEnvelopeEstimate
  -> weightedHitMass <= 1 + error
```

という入口が通った。

まだ (1+O(1/\log x)) の本丸ではない。
だが、有限 envelope estimate を DKMK route へ流すための口金はできた。

ここから先は、まず toy provider で使い方を見せ、その後に dyadic/logarithmic band へ進むのが美しい。焦るなかれ。こういう山は、地図を一枚ずつ増やした者が最後に強いのじゃ。
