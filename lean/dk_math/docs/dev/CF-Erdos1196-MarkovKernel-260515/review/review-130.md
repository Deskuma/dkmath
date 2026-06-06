# review

うむ、DKMK-018C は **本命 source 接続の第一関門を突破** じゃ。
018B までは「Real source を Rat route に載せられるか」という抽象橋だったが、018C では実際に `PrimePowerWitnessProvider.logCapacityKernelRealWeightProvider` が `TruncationEnvelopeEstimate` まで届いた。これはもう配管試験ではなく、 **LogCapacityKernel が DKMK-017 の truncation-envelope 入口に接続された** ということじゃ。

## 1. 何が閉じたか

追加された theorem は二つ。

```lean
PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_of_ratMajorizedIncrement
PrimePowerWitnessProvider.logCapacityKernel_truncationEnvelope_zeroIncrement
```

前者は本命の **assumed-rationalization route** で、

```lean
increment : Nat -> Rat
∀ q ∈ I, 0 ≤ increment q
∀ q ∈ I,
  (increment q : Real) ≤
    (logCapacityKernelRealWeightProvider n I hI hn).weight q
0 ≤ error
```

から、

```lean
TruncationEnvelopeEstimate I threshold increment error
```

を作る。後者は `increment := 0` による smoke test で、provider/API の噛み合わせ確認じゃ。

つまり 018C で閉じたのは、

$$
\text{LogCapacityKernel Real provider}
\to
\text{RealWeightProvider bridge}
\to
\text{Rat TruncationEnvelopeEstimate}
$$

という実接続じゃ。

## 2. 数学的な意味

これは DKMK の R/log route の本筋にかなり近い。過去の R/log 登山では、prime-power witness (q=p^k) から base prime (p) を読み、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

を有限集合 (I) で示すことが目標だった。重複する base prime は valuation slot で管理し、最終的に finite log `SubProbability` へ接続した、という流れじゃ。

今回の 018C は、その Real log-capacity 側の成果を、DKMK-017 の finite-step mass / truncation route に接続した。
つまり、

$$
\text{finite R/log sub-probability}
$$

が、ただの独立 theorem ではなく、

$$
\text{finite-step tail mass route}
$$

へ流れ込めるようになった。

これは良い。わっち、少し尻尾を振ってしまうのう。

## 3. ただし、まだ最終 source replacement ではない

ここで注意点じゃ。

018C は **非自明な Rat increment の構成** までは閉じておらぬ。
現在は、

$$
(\mathrm{increment}(q):\mathbb{R})\le \mathrm{provider.weight}(q)
$$

を外部仮定として受ける theorem surface ができた段階じゃ。roadmap 側でも、残課題は非自明な rational increment がまだ外部にあり、次は rationalization policy の判断だと明記されておる。

つまり、現在の位置はこう。

```text
済み:
  Real log-capacity provider は Rat envelope を certify できる。

未完:
  provider.weight q の下にある非ゼロ Rat increment をどう作るか。
```

## 4. DKMK-018D の判断点

次は三択じゃが、わっちの推奨は明確じゃ。

### 4.A. assumed-rationalization surface を main にする

まずはこれを採用すべきじゃ。

```lean
∀ q ∈ I,
  (increment q : ℝ) ≤ provider.weight q
```

を仮定に残す形は、柔軟で強い。
後から rationalization policy を差し替えられるし、現時点で DKMK-017 route と LogCapacityKernel route の合流点として十分に価値がある。

### 4.B. finite index 上の rational lower approximation を別補題化する

これは 018D か 018E でよい。

理想形は例えば、

```lean
exists_ratIncrement_majorizedBy_realWeightProvider
```

のような補題で、

```lean
∀ q ∈ P.index, 0 < P.weight q
```

から、

```lean
∃ increment : ℕ → ℚ,
  (∀ q ∈ P.index, 0 < increment q) ∧
  (∀ q ∈ P.index, (increment q : ℝ) ≤ P.weight q)
```

を作る形じゃ。

ただしこれは、Real/Rat の稠密性、有限集合上の choice、index 外の値の処理などが絡む。数学的には当然でも、Lean では意外に小石が多い。急がぬ方がよい。

### 4.C. Real-native finite-step route はまだ不要

これは最後の逃げ道じゃ。

018B と 018C で、Real provider は Rat route を certify できることが確認済み。したがって現段階で `finiteStepTailRealMassSpace` のような大改築へ進む必要はない。

## 5. 次の実装提案

DKMK-018D は、次の薄い bundle がよい。

```lean
theorem logCapacityKernel_truncationEnvelope_of_assumedRatIncrement
```

これは既に 018C の theorem とほぼ同じなので、次にやるなら整理・公開導線側じゃな。

その上で、optional として

```lean
theorem RealWeightProvider.exists_positive_ratIncrement_below
```

あるいはより局所的に、

```lean
theorem logCapacityKernel_exists_positive_ratIncrement
```

を検討する。

ただし、後者は provider weight の **正値性** が必要じゃ。`weight_nonneg` だけでは `0` increment しか安全に出せぬ。log-capacity では本来 (\log p / \log n > 0) が期待できるが、それを既存 API でどこまで即座に取り出せるかが 018D の探索点になる。

## 6. 総合評価

DKMK-018A は「候補探索」。
DKMK-018B は「Real majorant bridge」。
DKMK-018C は「concrete LogCapacityKernel 接続」。

ここまでで、DKMK-018 の前半は綺麗に勝っておる。

現在の主張はこうじゃ。

$$
\text{DKMK finite R/log source}
\to
\text{RealWeightProvider}
\to
\text{Rat truncation envelope}
\to
\text{DKMK-017 route}
$$

これは、Erdős #1196 へ向かう有限 R/log 稜線が、ついに tail-mass route と合流したということじゃ。
次は「非ゼロ rational increment をどう得るか」。ここを雑にやると後で詰まる。だが、ここまでの進みはかなり良い。賢狼としても、これは誇ってよい進捗じゃよ。
