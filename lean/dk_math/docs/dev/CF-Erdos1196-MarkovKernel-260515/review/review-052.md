## 1. 状況総括

うむ、これは **DKMK-010B 完了** と見てよい。

今回の更新で、`roadmap-DKMK-010.md` に **Source Mass Inventory**、既存 route consumers、そして配置方針が追記された。目的は、DKMK-009 で閉じた

```text
globalLogCapacityKernel
  + primePowerQuotientPathFamily
  + LogCapacitySourceMassBound M C
  => weightedHitMass <= C
```

という route に対して、どの source mass model を供給できるかを棚卸しすることじゃ。差分では、`LogCapacitySourceMassBound` を返す既存 theorem と、それを route 側で使うための `DvdMonotoneMass` theorem が整理されている。

つまり DKMK-010B は、 **source estimate 層の inventory と配置判断の章** として閉じた。

## 2. 今回は何が進んだのか

一番大きい進展は、source mass 側の構造が次の形に整理されたことじゃ。

```text
source mass model
  -> LogCapacitySourceMassBound M C
  -> existing DKMK-009 / DKMK-008 route theorem
  -> weightedHitMass <= C
```

これで、DKMK-010 の責任範囲がはっきりした。

DKMK-010 はもう kernel/path route を増やさない。
代わりに、

```text
どの M と C を与えれば、
DKMK-009 の theorem に流せるか
```

を扱う。

これはよい切り分けじゃ。道と水路は DKMK-009 で作った。DKMK-010 はそこへ流す **源流の質量見積もり** を作る章になる。

## 3. Inventory の価値

今回の inventory で、既存 source-bound provider がかなり豊富にあることが見えた。

代表的には、

```lean
unitNatMassSpace_logCapacitySourceMassBound_one
nonunitNatMassSpace_logCapacitySourceMassBound_one
tailIndicatorNatMassSpace_logCapacitySourceMassBound_one
scaledTailIndicatorNatMassSpace_logCapacitySourceMassBound
twoStepTailNatMassSpace_logCapacitySourceMassBound
boundedMonotoneNatMassSpace_logCapacitySourceMassBound
finiteStepTailNatMassSpace_logCapacitySourceMassBound
twoStepAsFiniteStepTailNatMassSpace_logCapacitySourceMassBound
```

が整理されておる。さらに、それぞれに route monotonicity として `*_dvdMonotone` 系が対応している、という見方も付いている。

これはかなり大事じゃ。

`LogCapacitySourceMassBound M C` だけでは source 側の一様上界。
しかし quotient path family は divisor-descending family として動くため、route 側では `DvdMonotoneMass M` が必要になりやすい。今回の inventory は、その **source bound と route monotonicity の二点セット** を明示したことに意味がある。

## 4. finite-step tail を主候補にした判断

今回の判断で特に良いのは、 **finite-step tail mass を DKMK-010 の主候補に置いたこと** じゃ。

roadmap では、

```lean
finiteStepTailNatMassSpace steps threshold increment hinc
```

が、有限個の threshold と nonnegative increment を bounded monotone height として package し、

```lean
LogCapacitySourceMassBound
  (finiteStepTailNatMassSpace steps threshold increment hinc)
  ((Finset.sum steps increment : ℚ) : ℝ)
```

を供給すると整理されておる。

これは、まさに **finite window / truncated envelope** に近い。

解析的な (1/(n\log n)) をいきなり入れるのではなく、まず有限段の envelope を作る。
そして後で、その envelope の総量 (C) が

$$
C(x) \le 1 + error(x)
$$

になるように解析側で評価する。

この分離は Lean 形式化としてかなり強い。焦って実解析を入れず、まず theorem shape を固定している。

## 5. 配置判断も正しい

今回、tail/truncation interface を `LogCapacityHittingBridge.lean` に混ぜず、

```text
DkMath/NumberTheory/PrimitiveSet/SourceMassTruncation.lean
```

へ分離する方針にしたのは正解じゃ。

理由は明快。

`LogCapacityHittingBridge.lean` は kernel/path route の橋。
`SourceMassTruncation.lean` は source estimate layer の橋。

ここを混ぜると、009 で綺麗に分けた層構造が崩れる。

```text
kernel/path layer
source estimate layer
analytic estimate layer
```

この三つは分けた方がよい。
特に今後 DKMK-010E 以降で analytic placeholder や Mertens 的評価に近づくなら、別ファイルにしておく方が安全じゃ。

## 6. 今回の注意点

docs-only なので Lean build は不要、これは問題ない。
ただし次の DKMK-010C で Lean ファイルを追加するなら、最初はかなり小さくすべきじゃ。

候補名として、

```lean
TailWindowSourceMassBound
```

が挙がっておる。

わっちもこの名前がよいと思う。

`TruncatedTailSourceMassBound` より、`TailWindowSourceMassBound` の方が軽い。
「解析的 tail そのもの」ではなく、「有限窓として切った source mass contract」という意味が出る。

## 7. DKMK-010C の推奨形

次に Lean interface を足すなら、いきなり解析 estimate を入れず、次のような薄い contract がよい。

```lean
structure TailWindowSourceMassBound (M : MassSpace ℕ) (C : ℝ) : Prop where
  source_bound : LogCapacitySourceMassBound M C
  dvd_mono : DvdMonotoneMass M
```

ただし、これは少し強い。
`LogCapacitySourceMassBound` だけを包む案もあるが、DKMK-009D の quotient path route へ流すには `DvdMonotoneMass M` が必要になりやすいので、最初から両方を持つ package にしておくのが実用的じゃ。

もう少し DkMath らしくするなら、

```lean
structure TailWindowEnvelope (M : MassSpace ℕ) (C : ℝ) : Prop where
  source_bound : LogCapacitySourceMassBound M C
  dvd_mono : DvdMonotoneMass M
  nonneg_const : 0 ≤ C
```

でもよい。

ただし、既存 theorem が `hC : 0 ≤ C` を別引数で取っているなら、`nonneg_const` を構造に含めるかどうかは実装感触で決めるのがよい。

## 8. 次の実装で狙う theorem

DKMK-010C/D では、最終的に次の薄い theorem があると美しい。

```lean
theorem TailWindowSourceMassBound.weightedHitMass_le
    ...
    (H : TailWindowSourceMassBound M C)
    (hA : PrimitiveOn A) :
    weightedHitMass A ≤ C
```

中身は新しい証明ではなく、DKMK-009D の

```lean
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

へ `H.source_bound` と `H.dvd_mono` を渡すだけでよい。

つまり DKMK-010C/D の役割は、

```text
TailWindowSourceMassBound
  -> LogCapacitySourceMassBound M C + DvdMonotoneMass M
  -> DKMK-009 endpoint
```

を theorem-facing にすることじゃ。

## 9. 登頂判定

現在地はこう。

```text
DKMK-010A: roadmap / scope 完了
DKMK-010B: source mass inventory / placement decision 完了
DKMK-010C: 次、SourceMassTruncation.lean に小さい Lean contract
DKMK-010D: envelope-to-route bridge
DKMK-010E: analytic placeholder
DKMK-010F: report / handoff
```

DKMK-010B は良い整理じゃ。
特に、source-bound provider と route monotonicity を並べたことで、次の Lean 追加が「何を包めばよいか」見えてきた。

## 10. 賢狼の見立て

DKMK-010B は、派手ではないが重要な **棚卸し勝利** じゃ。

これで、

```text
finite-step or bounded monotone source envelope
  -> LogCapacitySourceMassBound M C
  -> DKMK-009 quotient-path capacity route
  -> weightedHitMass <= C
```

という筋がはっきりした。

次は `SourceMassTruncation.lean` を小さく作る。
大きな解析定理はまだ要らぬ。まずは tail window を theorem-facing contract にする。

ぬしよ、これはよい。DKMK-010 は焦らず行く山じゃ。
いきなり雲の上の (1+O(1/\log x)) を掴みに行かず、まず足場の板を一枚ずつ打っておる。こういう登り方は、長い山では強いぞい。
