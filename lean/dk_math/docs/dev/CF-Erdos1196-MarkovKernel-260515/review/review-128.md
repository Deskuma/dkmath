# review

うむ、DKMK-018 開始じゃ。
わっちの見立てでは、今回の章名はかなりはっきりしておる。

## 1. DKMK-018 の現在地

DKMK-017 は、 **toy source でも経路が通る** ことを確認した章じゃ。具体的には `geometricIncrement base ratio : Nat -> Rat` が、

$$
\texttt{TruncationEnvelopeEstimate}
\to
\texttt{finiteStepTailNatMassSpace}
\to
\texttt{quotient-path weightedHitMass bound}
$$

へ流れることを示した。だが、この `geometricIncrement` は最終 source ではなく、route-validation 用の試験流体として受理された、という位置づけじゃ。

DKMK-018 の目的は、その試験流体を **本命の解析 source** に差し替えること。候補としては `RealLog.lean`, `ValuationBudget.lean`, `LogCapacityKernel.lean`, `SourceMassTruncation.lean` 周辺がすでに調査され、Real log-ratio / valuation budget / capacity-derived / dyadic route に分類されておる。

結論として、最初に狙うべき本命は **Real log-ratio / capacity-derived source** じゃ。理由は明快で、既に Real 側には nonnegativity と sub-probability があり、しかも prime-power witness と log-capacity kernel に接続済みだからじゃ。

## 2. 真の障害は数学ではなく型

今回の主問題は、解析評価そのものではない。
型じゃ。

既存の意味ある解析 source は Real-valued：

$$
\frac{\log p}{\log n},\quad
\texttt{RealWeightProvider},\quad
\texttt{CapacityKernel.normalizedWeight}
$$

一方、DKMK-017 の route は rational-valued：

```lean
increment : Nat -> Rat
```

を消費する。したがって、今ぶつかっている壁は

$$
\text{Real analytic weight}
\to
\text{Rat finite-step increment}
$$

の橋じゃ。これは DKMK-018-A でも、いきなり Real-mass 全体へ refactor せず、まず Real-valued analytic majorant が既存 Rat route を certify できるか試すべき、と整理されておる。

ここはよい判断じゃ。大改築の前に、橋だけ架ける。狼の山歩きでも、橋を見ずに谷へ飛び込むたわけは長生きせぬからの。

## 3. 018B の最短実装方針

次の一手、DKMK-018B はこれでよい。

```lean
RealAnalyticIncrementEnvelope
```

相当の小さな bridge を作る。

想定する構造は、資料案どおり次の形じゃ。

```lean
realIncrement : Nat -> Real
ratIncrement  : Nat -> Rat
compare       : ∀ k, (ratIncrement k : Real) ≤ realIncrement k
rat_nonneg    : ∀ k, 0 ≤ ratIncrement k
real_budget   : finite real sum ≤ bound
```

ただし、Lean 実装ではここに一つ注意がある。
既存 `TruncationEnvelopeEstimate` が Rat の bound を要求するなら、`real_budget` の右辺はなるべく

```lean
(bound : Rat)
```

を Real に cast したものにするべきじゃ。

つまり、

```lean
(∑ k in S, realIncrement k) ≤ (bound : Real)
```

を持ち、

```lean
(∑ k in S, (ratIncrement k : Real)) ≤ (bound : Real)
```

を経由し、`Rat.cast_le` / `exact_mod_cast` 系で

```lean
(∑ k in S, ratIncrement k) ≤ bound
```

へ戻す。

ここが通れば、既存の `finiteStepTailNatMassSpace` は Rat のまま残せる。
ここが DKMK-018 の最重要 checkpoint じゃ。

## 4. ２手先計画

### 4.1. DKMK-018B: Real-majorant bridge

目的は、実解析 source をまだ具体化せず、

$$
(r_k : \mathbb{Q}) \le R_k
$$

と Real 側の有限和評価から、Rat route 用の有限和評価を回収すること。

候補 theorem 名はこんなところじゃ。

```lean
rat_sum_le_of_cast_sum_le
rat_sum_le_of_real_majorant
truncationEnvelopeEstimate_of_realMajorant
dyadicBandAnalyticEstimate_of_realMajorant
```

ここでは `LogCapacityKernel` をまだ直接つながなくてよい。
まず **Real majorant が Rat route を certify できる** という構文だけを閉じる。

### 4.2. DKMK-018C: LogCapacityKernel を source として接続

018B が通ったら、次に `LogCapacityKernel.lean` 側の

```lean
PrimePowerWitnessProvider.logCapacityKernel
logCapacityKernel_normalized_subProbability
logCapacityKernelRealWeightProvider
```

を、`realIncrement : Nat -> Real` の具体例として流す。

ここでの本質は、

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

を、単なる theorem としてではなく、DKMK-017 の finite-step source へ供給できる形にすることじゃ。これは、以前の実装計画で「exact Markov kernel や (\Lambda(q)/\log n) へいきなり入らず、まず構造的 spine を作る」とした方針とも合っておる。

### 4.3. DKMK-018D: 失敗時だけ Real route 分岐

018B で Rat への反射が苦しい場合だけ、

```lean
finiteStepTailRealMassSpace
RealTruncationEnvelopeEstimate
```

のような Real-native route を作る。

ただし、これは **第１手ではない** 。
先にやると DKMK-017 の蓄積を捨てることになる。賢くない。

## 5. 今回の作業モード

DKMK-017 のペースが良かった理由は、たぶん「薄い provider → build → docs → 次の薄い provider」という束ね方が効いたからじゃ。今回も同じでよいが、もう少し速めるなら、各 bundle はこう切る。

```text
DKMK-018B:
  Real-majorant bridge only
  no concrete analytic source yet

DKMK-018C:
  LogCapacityKernel / RealLog source attachment
  reuse 018B bridge

DKMK-018D:
  either polish Rat bridge
  or decide Real-native finite-step route
```

つまり、毎回「定義だけ」「補題だけ」と細切れにせず、

$$
\text{設計判断}
\to
\text{Lean 実装}
\to
\text{自己診断}
\to
\text{検証}
\to
\text{短い報告}
$$

で一束にするのがよい。これはお主の言う 2 手先計画に合っておる。

## 6. わっちの開始判定

DKMK-018 は **かなり良い入り** じゃ。

理由は三つ。

第一に、DKMK-017 の成果が無駄になっておらぬ。Rat route はそのまま保持し、Real source を上から certify する方針だからじゃ。

第二に、候補選定が正しい。`geometricIncrement` の wrapper を増やすより、Real log-ratio / capacity-derived source へ向かう方が Erdős #1196 の本筋に近い。

第三に、失敗時の分岐も明確じゃ。小 bridge が通れば大 refactor 回避、通らなければ Real finite-step route へ進む。この判断点が明示されておるのは強い。

わっちの結論はこうじゃ。

**DKMK-018B は、`Real -> Rat` の bridge を最小定理として閉じる。018C で `LogCapacityKernel` を流す。018D で方針確定。**

ここまで見えていれば、かなり速く進められるぞい。賢狼の鼻でも、これはよい獲物の匂いがする。
