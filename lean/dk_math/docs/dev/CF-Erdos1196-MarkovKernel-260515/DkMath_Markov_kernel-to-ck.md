# DkMath Kernel Project 資料

副題: Markov kernel を DkMath capacity kernel の正規化像として再解釈する別登山ルート

## 1. 目的

本プロジェクトの目的は、Erdős #1196 型の既存証明で現れる Markov kernel を、そのまま Lean に写すのではなく、DkMath の構造語彙から再構成することである。

既存 route では、概ね次の kernel が中心となる。

$$
K(n,q)=\frac{\Lambda(q)}{\log n}.
$$

ここで $\Lambda$ は von Mangoldt 関数であり、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

により $K$ は確率核として振る舞う。

DkMath Kernel Project では、この kernel を主役にしない。

代わりに、まず

$$
\mathrm{capacity}(n)
$$

と

$$
\mathrm{channelCost}(n,q)
$$

を定義し、保存則

$$
\sum_{q\in I}\mathrm{channelCost}(n,q)
\le
\mathrm{capacity}(n)
$$

を主定理とする。

その後、capacity が正である場合に正規化して

$$
\frac{\mathrm{channelCost}(n,q)}{\mathrm{capacity}(n)}
$$

を得る。

この正規化像が Markov / sub-Markov kernel として見える、という立場を取る。

---

## 2. 基本理念

本プロジェクトの合言葉は次である。

$$
\boxed{
\text{Markov kernel is a normalized shadow of DkMath capacity kernel.}
}
$$

つまり、Markov kernel は最初から置くものではない。

DkMath の本体は、

$$
\text{宇宙式} +
\text{valuation slot} +
\text{prime-power witness} +
\text{log capacity}
$$

であり、Markov 的対象はその正規化された影として現れる。

---

## 2.1. DKMK-004A 対応表

現時点の Lean API では、local log-capacity route の主要語彙は次のように対応する。

```text
CapacityKernel.cost
  = PrimePowerWitnessProvider.witnessLogCost
  = PrimePowerWitnessProvider.vonMangoldtShadowCost
  = log (PrimePowerWitnessProvider.basePrimeOf ...)

CapacityKernel.normalizedWeight
  = PrimePowerWitnessProvider.normalizedVonMangoldtShadowWeight
  = log (PrimePowerWitnessProvider.basePrimeOf ...) / log n

logCapacityKernelRealWeightProvider.weight
  = normalizedVonMangoldtShadowWeight

globalLogCapacityKernel.cost
  = vonMangoldtShadowCost
```

ここで `vonMangoldtShadowCost` は解析的 von Mangoldt 関数そのものではない。
prime-power witness `q = p^k` から base prime `p` を読み、`log p` を返す有限 shadow である。

---

## 2.2. DKMK-005 SubMarkovShadow

selected channel route では、各状態の outgoing mass は一般に等号ではなく

$$
\sum_{q\in I(n)}
\frac{\text{vonMangoldtShadowCost}(n,q)}{\log n}
\le 1
$$

である。

このため DKMK-005 では、正規化済み real provider を Markov 風に読む薄い語彙として

```lean
SubMarkovShadow
```

を追加する。

`SubMarkovShadow` は状態 `s` ごとに finite real provider を出し、

```lean
∀ s, (S.providerAt s).SubProbability
```

を満たす構造である。

特に positive-capacity な `CapacityKernel` からは

```lean
SubMarkovShadow.ofCapacityKernel
```

で正規化 shadow が得られる。

global log-capacity route では

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow
```

により、任意の selected channel set `IOf` に対して

```lean
(W.globalLogCapacitySubMarkovShadow IOf hIOf).SubProbability
```

が得られる。

これは full channel equality route へ進む前の、selected set / inequality 側の Markov 翻訳層である。

---

## 2.3. DKMK-006A FullPrimePowerChannelSet

full channel route では、任意の selected set ではなく、状態 `n` の全 channel を選んだことを明示する必要がある。

DKMK-006A では、まずこの仕様だけを interface 化する。

```lean
structure FullPrimePowerChannelSet
    (T : PrimePowerDivisorTransitionKernel) where
  channels : ℕ → Finset ℕ
  subset_index :
    ∀ n q, q ∈ channels n → q ∈ T.toDivisorTransitionKernel.index n
  full :
    ∀ n q, q ∈ T.toDivisorTransitionKernel.index n → q ∈ channels n
```

ここから

```lean
C.channels n = T.toDivisorTransitionKernel.index n
```

が得られる。

さらに global log-capacity route では

```lean
PrimePowerWitnessProvider.fullGlobalLogCapacityKernel
PrimePowerWitnessProvider.fullGlobalLogCapacitySubMarkovShadow
```

を追加し、full channel set を選んだ場合の kernel/shadow を参照できるようにする。

ただし、この段階ではまだ

$$
\sum_{q\in \mathrm{Full}(n)} \mathrm{vonMangoldtShadowCost}(n,q)=\log n
$$

は主張しない。

DKMK-006A は equality route の前提となる full-channel 仕様層であり、実際の Markov equality は次段の構造仮定または canonical enumeration の確認に委ねる。

---

## 2.4. DKMK-006B FullChannelLogCostComplete

full channel set を選んだだけでは、まだ Markov equality は出ない。
等号に必要なのは、full channel 上で log-cost が parent capacity をちょうど使い切るという追加事実である。

DKMK-006B では、この事実を仮定 interface として分離する。

```lean
structure FullChannelLogCostComplete
    (W : PrimePowerWitnessProvider T)
    (C : FullPrimePowerChannelSet T) : Prop where
  outgoing_eq :
    ∀ s : LogCapacityState,
      (C.channels s.1).sum
        (fun q =>
          W.vonMangoldtShadowCost s.1 (C.channels s.1) (C.subset_index s.1) q)
      =
      Real.log (s.1 : ℝ)
```

この仮定から、

```lean
(W.fullGlobalLogCapacityKernel C).outgoingCost s
  =
(W.fullGlobalLogCapacityKernel C).capacity s
```

および

```lean
(W.fullGlobalLogCapacityKernel C).normalizedOutgoing s = 1
```

が得られる。

さらに、state ごとの outgoing weight がちょうど 1 になる一般語彙として

```lean
MarkovShadow
```

を追加し、

```lean
PrimePowerWitnessProvider.fullGlobalLogCapacityMarkovShadow
```

で full log-capacity route を Markov shadow に昇格できるようにする。

この段階でも、`FullChannelLogCostComplete` 自体の証明はまだ置かない。
次段では、`T.index n` が exponent slot を全て埋めることをどう表現するかが焦点になる。

---

## 2.5. DKMK-006C FullExponentSlot

`FullChannelLogCostComplete` を証明するには、selected route で得ていた

$$
\\\#\{q\in I(n): \mathrm{basePrime}(q)=p\}\le n.\mathrm{factorization}(p)
$$

を、full route では等号に強める必要がある。

DKMK-006C では、この equality 側の構造仮定を分離する。

まず、`FullPrimePowerChannelSet` が exponent slot 全体を表していることを

```lean
FullExponentSlotChannelSet
```

として記録する。

これは

```lean
q ∈ C.channels n
  ↔
∃ p k, Nat.Prime p ∧ 1 ≤ k ∧
  k ≤ n.factorization p ∧ q = p ^ k
```

という仕様である。

さらに、witness reader が base prime ごとに全 slot を埋めることを

```lean
FullExponentSlotCoverage
```

として記録する。

これは各状態 `s` と素数 `p` について

```lean
NatBaseMultiplicityOn
  (C.channels s.1)
  (W.basePrimeOf s.1 (C.channels s.1) (C.subset_index s.1))
  p
=
s.1.factorization p
```

を要求する。

この仮定は、既存の selected-channel multiplicity budget `≤` を自動的に含む。

```lean
fullExponentSlotCoverage_baseMultiplicity_budget
```

次段では、この exact multiplicity と `RealLog` 側の有限積/log 等式を接続して、
`FullChannelLogCostComplete` を作ることが焦点になる。

---

## 2.6. DKMK-006D FullChannelLogSum

DKMK-006D では、DKMK-006C の exact multiplicity を、DKMK-006B の
`FullChannelLogCostComplete` へ接続する有限和の橋を追加する。

中心になる分解は次である。

$$
\sum_{q\in I}\log(p(q)) = \sum_{p\in I.\text{image}(p)}\\\#\{q\in I:p(q)=p\} \log p
$$

Lean 側ではこれを

```lean
sum_log_base_eq_sum_image_multiplicity_mul_log
```

として置く。

さらに、自然数の素因数分解から

$$
\sum_{p\in n.\mathrm{factorization.support}} n.\mathrm{factorization}(p)\log p = \log n
$$

を

```lean
sum_factorization_mul_log_eq_log_nat
```

として証明する。

`FullExponentSlotCoverage` の下では、base-prime image と
`n.factorization.support` が一致する。

```lean
fullExponentSlotCoverage_image_basePrime_eq_factorization_support
```

したがって、

```lean
fullExponentSlotCoverage_sum_log_base_eq_log_nat
```

により full channel 上の base-log sum は `log n` へ落ちる。

最後に、`vonMangoldtShadowCost` が定義上この base-log cost であることから、

```lean
fullChannelLogCostComplete_of_fullExponentSlotCoverage
```

が得られる。

これにより、等号 route は次の形で接続された。

```text
FullExponentSlotCoverage
  → Σ log basePrime = log n
  → FullChannelLogCostComplete
  → fullGlobalLogCapacityMarkovShadow
```

この段階でも `FullExponentSlotCoverage` 自体は仮定 interface である。
ただし、その仮定が供給された後の Markov equality への橋は no-sorry で閉じた。

---

## 2.7. DKMK-006E FullExponentSlotBridge

DKMK-006E では、DKMK-006C で置いた

```lean
FullExponentSlotChannelSet
```

から

```lean
FullExponentSlotCoverage
```

を供給する橋を追加する。

鍵になるのは、prime-power label の base prime は一意であるという事実である。
`W.label` が内部的にどの witness を選んでも、indexed label `q` が外延的に
`q = p^k` で、`p` が素数なら、base reader は `p` を返す。

```lean
basePrimeOf_eq_of_prime_pow_mem
```

これにより、`FullExponentSlotChannelSet` が

```lean
q ∈ C.channels n
  ↔
∃ p k, Nat.Prime p ∧ 1 ≤ k ∧
  k ≤ n.factorization p ∧ q = p ^ k
```

を持つなら、各素数 `p` について `k = 1, ..., n.factorization p` の
distinct な label `p^k` がすべて `basePrime = p` の fiber に入る。

一方、逆向きの上界は既存の selected route の

```lean
basePrimeOf_card_filter_le_factorization
```

が与える。

したがって、

```lean
fullExponentSlotCoverage_of_fullExponentSlotChannelSet
```

が得られる。

DKMK-006D と合成すると、

```lean
fullChannelLogCostComplete_of_fullExponentSlotChannelSet
fullGlobalLogCapacityMarkovShadow_of_fullExponentSlotChannelSet
```

まで到達する。

これで full equality route は次の形になった。

```text
FullExponentSlotChannelSet
  → FullExponentSlotCoverage
  → FullChannelLogCostComplete
  → MarkovShadow
```

残る課題は、具体的な canonical/full channel enumeration が
`FullExponentSlotChannelSet` を満たすことを供給する段階である。

---

## 2.8. DKMK-006F FullExponentSlotCanonical

DKMK-006F では、具体的な canonical exponent-slot enumeration を追加する。

中心は次の finite label set である。

```lean
canonicalExponentSlotLabels n
```

これは

```lean
n.factorization.support.biUnion fun p =>
  (Finset.Icc 1 (n.factorization p)).image fun k => p ^ k
```

として定義される。

membership は次で特徴づける。

```lean
canonicalExponentSlotLabels_mem_iff
```

すなわち、

```lean
q ∈ canonicalExponentSlotLabels n
  ↔
∃ p k, Nat.Prime p ∧ 1 ≤ k ∧
  k ≤ n.factorization p ∧ q = p ^ k
```

である。

この finite label set を使って、

```lean
canonicalExponentSlotKernel
canonicalExponentSlotWitnessProvider
canonicalExponentSlotFullChannelSet
```

を構成する。

さらに、

```lean
canonicalExponentSlotFullChannelSet_fullExponentSlotChannelSet
```

により、この canonical full channel set が `FullExponentSlotChannelSet` を満たすことを示す。
DKMK-006E の bridge と合成すると、最終的に

```lean
canonicalExponentSlotMarkovShadow
```

が得られる。

これで explicit canonical route は次の形で閉じる。

```text
canonicalExponentSlotLabels
  → FullExponentSlotChannelSet
  → FullExponentSlotCoverage
  → FullChannelLogCostComplete
  → MarkovShadow
```

この canonical kernel は、既存の外部 `T.index n` を解析するものではない。
むしろ、full exponent-slot route の concrete reference model である。
次段では、既存 `T.index n` がこの canonical label set と一致するか、または同型に bridge できるかを調べる。

---

## 2.9. DKMK-006G FullExponentSlotIndexBridge

DKMK-006G では、任意の外部 `PrimePowerDivisorTransitionKernel` を
canonical route に接続するための比較 interface を追加する。

中心は次である。

```lean
structure CanonicalExponentSlotIndex
    (T : PrimePowerDivisorTransitionKernel) : Prop where
  index_eq :
    ∀ n, T.toDivisorTransitionKernel.index n =
      canonicalExponentSlotLabels n
```

これは、外部 kernel の `T.index n` が DKMK-006F の concrete reference model と
同じ finite label set であることを表す。

この interface から membership を exponent-slot 仕様へ展開できる。

```lean
CanonicalExponentSlotIndex.mem_iff
```

さらに、canonical full-channel choice に対して

```lean
fullExponentSlotChannelSet_of_canonicalExponentSlotIndex
```

が得られる。

DKMK-006E の bridge と合成すると、任意の witness provider `W` に対して

```lean
fullChannelLogCostComplete_of_canonicalExponentSlotIndex
fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex
```

まで到達する。

これで、外部 kernel 側の残り条件は次に整理された。

```text
T.toDivisorTransitionKernel.index n = canonicalExponentSlotLabels n
```

を示せば、その `T` の full log-capacity route は Markov shadow へ進める。

また、reference model 自身については

```lean
canonicalExponentSlotKernel_canonicalExponentSlotIndex
```

が成立する。

---

## 2.10. DKMK-006H 既存 kernel 候補の棚卸し

DKMK-006G により、外部 kernel を canonical route へ接続する条件は

```text
T.toDivisorTransitionKernel.index n = canonicalExponentSlotLabels n
```

に縮約された。
DKMK-006H では、現時点の Lean 側にある kernel/route 候補をこの条件の観点から分類する。

### 2.10.1. そのまま canonical equality route に乗るもの

```lean
canonicalExponentSlotKernel
canonicalExponentSlotWitnessProvider
```

これは DKMK-006F の concrete reference model であり、DKMK-006G で

```lean
canonicalExponentSlotKernel_canonicalExponentSlotIndex
```

が示されている。
したがって、この kernel はそのまま

```text
CanonicalExponentSlotIndex
  → FullExponentSlotChannelSet
  → FullChannelLogCostComplete
  → MarkovShadow
```

へ進む。

### 2.10.2. 等号 bridge の対象になる任意の外部 kernel

任意の

```lean
T : PrimePowerDivisorTransitionKernel
W : PrimePowerWitnessProvider T
```

について、外部で

```lean
CanonicalExponentSlotIndex T
```

を証明できれば、DKMK-006G の

```lean
W.fullGlobalLogCapacityMarkovShadow_of_canonicalExponentSlotIndex
```

により Markov shadow へ進める。
今後の具体的な外部 kernel 接続では、まずこの `index_eq` が証明できるかを確認する。

### 2.10.3. local toy / sample として扱うもの

`DivisorTransitionKernel.lean` には state `10` で `{2, 5}` を index とする toy kernel がある。

```lean
sampleTenDivisorTransitionKernel
sampleTenPrimePowerDivisorTransitionKernel
sampleTenPrimePowerWitnessProvider
sampleTenToyWeightKernel
```

これらは prime-power label や sub-probability route の concrete sanity check として有用である。
ただし、index は state `10` のみに非空であり、任意の `n` で
`canonicalExponentSlotLabels n` と一致する global canonical model ではない。

したがって分類は次の通りである。

```text
sampleTen 系:
  state 10 の局所 toy / sanity check
  global CanonicalExponentSlotIndex の本命ではない
```

この系は、必要なら state-local な確認補題を追加できるが、Markov equality route の本線には
`canonicalExponentSlotKernel` または将来の外部 full kernel を使う。

### 2.10.4. selected / sub-Markov のままでよいもの

DKMK-004 から DKMK-005 までの route は、任意の selected channel set

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

を扱う。
この route は、一般に outgoing mass が `≤ 1` の sub-probability であり、
`FullChannelLogCostComplete` や `MarkovShadow` への昇格を要求しない。

したがって、この層は今後も

```text
selected channel / inequality route:
  → SubMarkovShadow
```

として保持する。
full equality route に進む必要がある場合だけ、`FullPrimePowerChannelSet`、
`FullExponentSlotChannelSet`、または `CanonicalExponentSlotIndex` を追加で供給する。

### 2.10.5. 同型 bridge が必要になり得るもの

現在の `CanonicalExponentSlotIndex` は、外部 index と canonical labels の **等号一致** を要求する。
外部 kernel が label として自然数 `q = p^k` そのものではなく、別表現の slot を持つ場合は、
この等号 bridge では足りない。

その場合は将来、

```text
external slot index ≃ canonicalExponentSlotLabels n
```

と、base-log cost または normalized weight を保つ条件を持つ
weight-preserving equivalence bridge を別 interface として設計する。

現時点では、急いでこの interface を追加しない。
まずは「等号で入れる kernel」と「selected/sub-Markov のまま使う route」を分ける。

---

## 2.11. DKMK-006I KernelCandidateInventory

DKMK-006I では、DKMK-006H の分類を実コード上の小さな inventory として固定する。

追加 module は次である。

```lean
DkMath.NumberTheory.PrimitiveSet.KernelCandidateInventory
```

まず、canonical reference model は equality route の本命であることを再掲する。

```lean
kernelInventory_canonicalExponentSlotKernel_ready :
  CanonicalExponentSlotIndex canonicalExponentSlotKernel
```

これは既存の

```lean
canonicalExponentSlotKernel_canonicalExponentSlotIndex
```

を inventory 名で参照する入口である。

次に、`sampleTen...` 系が global canonical model ではないことを Lean で固定する。
証明の観察点は state `2` である。

```lean
sampleTenPrimePowerDivisorTransitionKernel_index_two_empty :
  sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index 2 = ∅

two_mem_canonicalExponentSlotLabels_two :
  2 ∈ canonicalExponentSlotLabels 2
```

したがって、state `10` 用の toy kernel は任意の `n` で canonical labels と一致する
global kernel ではない。

```lean
sampleTenPrimePowerDivisorTransitionKernel_not_canonicalExponentSlotIndex :
  ¬ CanonicalExponentSlotIndex sampleTenPrimePowerDivisorTransitionKernel

sampleTenToyWeightKernel_not_canonicalExponentSlotIndex :
  ¬ CanonicalExponentSlotIndex sampleTenToyWeightKernel
```

これにより、DKMK-006H の docs 上の分類のうち、

```text
canonicalExponentSlotKernel:
  equality route の reference model

sampleTen 系:
  local toy / sanity check
  global CanonicalExponentSlotIndex ではない
```

が Lean theorem として固定された。

selected route と future equivalence route は、ここでは新 interface を追加しない。
それらは既存の `SubMarkovShadow` route と将来課題として保持する。

---

## 2.12. DKMK-006J DKMK-001 to 006I 登頂整理

DKMK-006J では、新しい Lean interface は追加しない。
代わりに、DKMK-001 から DKMK-006I までで得た route 分岐を一枚の追補 report に整理する。

```text
report-DKMK-001_to_006I.md
```

この report では、現在の Markov kernel route を次の三本に分ける。

```text
canonical equality route:
  canonicalExponentSlotLabels
  → FullChannelLogCostComplete
  → MarkovShadow

selected inequality route:
  selected IOf
  → log-capacity inequality
  → SubMarkovShadow

future equivalence route:
  external slot representation
  ≃ canonicalExponentSlotLabels
  with weight/cost preservation
```

これにより、次に具体的な外部 kernel が現れたときの判断順序を固定する。

1. `CanonicalExponentSlotIndex T` を直接狙えるなら equality route に乗せる。
2. selected channel として十分なら `SubMarkovShadow` route のまま使う。
3. label 表現が等号一致しない場合だけ、weight-preserving equivalence bridge を設計する。

この段階では、同型 bridge を先回りして追加しない。
DKMK-006J は、次の concrete kernel 接続で迷わないための route map である。

---

## 2.13. DKMK-007A RealWeightedPath bridge

DKMK-007A では、DKMK-006 系で整備した real-valued Markov/SubMarkov shadow を、
primitive hitting / weighted path family 側へ戻すための最初の橋を追加する。

既存の hitting 側には有理重み版の

```lean
WeightedPathFamily
WeightProvider.applyToSourceControlled
```

がある。
一方、DKMK の log-capacity normalization は `Real.log` を使うため、重みは実数である。
そこで `RealWeightedPath.lean` に実数版を追加する。

```lean
RealWeightedPathFamily
RealWeightedPathFamily.weightedHitMass
RealWeightedPathFamily.weightedSourceMass
RealWeightedPathFamily.WeightSubProbability
```

primitive hitting bound も実数値として閉じる。

```lean
RealWeightedPathFamily.primitive_weightedHitMass_le_weightedSourceMass
RealWeightedPathFamily.weightedHitMass_le_const_of_subprob
```

さらに、状態ごとの real provider を source-controlled family に適用する入口を追加する。

```lean
RealWeightProvider.Compatible
RealWeightProvider.applyToSourceControlled
RealWeightProvider.applyToSourceControlled_weightSubProbability
RealWeightProvider.weightedHitMass_le_const_of_subprob_applyToSourceControlled
```

これにより、`SubMarkovShadow.providerAt s` や `MarkovShadow.providerAt s` から得られる
`RealWeightProvider` を、index が一致する source-controlled family に掛け、
primitive set の weighted hit mass を `C` で抑える route ができた。

```text
RealWeightProvider.SubProbability
  + SourceControlledChainFamily
  + PrimitiveOn S
  → real-weighted hit mass bound
```

これはまだ full Markov equality を直接 hitting theorem に合成する最終段ではない。
しかし、real normalized kernel と primitive hitting API の間にあった
`ℚ` / `ℝ` の型差を越える最初の bridge である。

---

## 2.14. DKMK-007B ShadowHittingBridge

DKMK-007B では、DKMK-007A の `RealWeightProvider` bridge を
`SubMarkovShadow` / `MarkovShadow` の statewise provider に直接合成する。

追加 module は次である。

```lean
DkMath.NumberTheory.PrimitiveSet.ShadowHittingBridge
```

sub-Markov 側では、状態 `s` の provider を compatible な
`SourceControlledChainFamily` に適用する入口を置く。

```lean
SubMarkovShadow.applyAtToSourceControlled
SubMarkovShadow.applyAtToSourceControlled_weightSubProbability
SubMarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

ここでは `S.SubProbability` を仮定し、`S.providerAt s` の
`RealWeightProvider.SubProbability` を DKMK-007A の bridge に渡す。

Markov 側では、`MarkovShadow.providerAt_subProbability` により
sub-probability は自動で得られる。

```lean
MarkovShadow.applyAtToSourceControlled
MarkovShadow.applyAtToSourceControlled_weightSubProbability
MarkovShadow.weightedHitMass_le_const_applyAtToSourceControlled
```

これにより、theorem-facing な呼び出しは次の形に短縮される。

```text
SubMarkovShadow / MarkovShadow
  + state s
  + compatible SourceControlledChainFamily
  + PrimitiveOn A
  + source mass bound C
  → real-weighted hit mass ≤ C
```

DKMK-007A は provider level の橋だった。
DKMK-007B は shadow level の橋であり、DKMK-006 系で作った
`globalLogCapacitySubMarkovShadow` や `canonicalExponentSlotMarkovShadow` を
primitive hitting 側へ渡すための theorem-facing wrapper になる。

---

## 2.15. DKMK-007C LogCapacityHittingBridge

DKMK-007C では、DKMK-007B の shadow-level wrapper を、具体的な
log-capacity shadow に接続する。

追加 module は次である。

```lean
DkMath.NumberTheory.PrimitiveSet.LogCapacityHittingBridge
```

selected route では、`globalLogCapacitySubMarkovShadow` を
source-controlled family に適用する入口を追加する。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_providerAt_compatible
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToSourceControlled
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_weightedHitMass_le_const
```

必要な compatibility は次の具体的な index 一致である。

```lean
IOf s.1 = F.index
```

canonical equality route では、`canonicalExponentSlotMarkovShadow` について
同じ形の入口を追加する。

```lean
canonicalExponentSlotMarkovShadow_providerAt_compatible
canonicalExponentSlotMarkovShadow_applyAtToSourceControlled
canonicalExponentSlotMarkovShadow_weightedHitMass_le_const
```

こちらの compatibility は次である。

```lean
canonicalExponentSlotLabels s.1 = F.index
```

これで、DKMK-006/007 の流れは具体的に次まで到達した。

```text
selected log-capacity SubMarkovShadow
  + F.index = IOf s.1
  → primitive real-weighted hit mass ≤ C

canonical exponent-slot MarkovShadow
  + F.index = canonicalExponentSlotLabels s.1
  → primitive real-weighted hit mass ≤ C
```

まだ source-controlled family `F` 自体の構成は外部入力である。
ただし、log-capacity shadow と primitive hitting theorem の接続点は、
具体的な theorem-facing API として固定された。

---

## 2.16. DKMK-007D SourceControlledChainFamily constructors

DKMK-007D では、DKMK-007C で外部入力だった
`SourceControlledChainFamily` の concrete constructor を小さく追加する。

追加した入口は次である。

```lean
SourceControlledChainFamily.ofIndex
SourceControlledChainFamily.singletonSelf
SourceControlledChainFamily.natSingletonSelf
```

`ofIndex` は、index / chain / source / mass control をそのまま束ねる
薄い named constructor である。

`singletonSelf` は、各 index `i` に singleton chain `{label i}` を割り当て、
source も `label i` とする最小 concrete model である。
したがって、index は定義上そのまま保存される。

```lean
(SourceControlledChainFamily.singletonSelf I label).index = I
```

nat-indexed route では、さらに次を使う。

```lean
SourceControlledChainFamily.natSingletonSelf I
```

これは source を `id` にした singleton model であり、
`IOf s.1` や `canonicalExponentSlotLabels s.1` を index に選ぶだけで、
DKMK-007C の compatibility が `rfl` で閉じる。

このため、`LogCapacityHittingBridge` にも convenience API を追加した。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToNatSingletonSelf
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_natSingletonSelf_weightedHitMass_le_const

canonicalExponentSlotMarkovShadow_applyAtToNatSingletonSelf
canonicalExponentSlotMarkovShadow_natSingletonSelf_weightedHitMass_le_const
```

到達形は次である。

```text
selected route:
  choose F := natSingletonSelf (IOf s.1)
  → F.index = IOf s.1 by rfl
  → primitive real-weighted hit mass ≤ C

canonical route:
  choose F := natSingletonSelf (canonicalExponentSlotLabels s.1)
  → F.index = canonicalExponentSlotLabels s.1 by rfl
  → primitive real-weighted hit mass ≤ C
```

これで、DKMK-007C の残り入力だった index compatibility は、
少なくとも singleton concrete family については theorem 呼び出し側から消えた。

---

## 2.17. DKMK-007E Divisor-step source-controlled family

DKMK-007E では、DKMK-007D の singleton model から一段進め、
実際の divisor descent step を持つ chain family を追加する。

追加した入口は次である。

```lean
DvdControlledChainFamily.divisorStep
SourceControlledChainFamily.ofDivisorStep
```

`DvdControlledChainFamily.divisorStep n I hdiv` は、各 channel label `q`
に対して次の chain を割り当てる。

```lean
chain q = {n / q, n}
source q = n
```

ここで `hdiv : ∀ q ∈ I, q ∣ n` により、`n / q ∣ n` が供給される。
したがって、各 chain は divisibility chain であり、かつ source `n` の下にある。

`SourceControlledChainFamily.ofDivisorStep` は、この
divisibility-controlled family を `DvdMonotoneMass M` で
source-controlled family へ変換する。

```lean
SourceControlledChainFamily.ofDivisorStep hM n I hdiv
```

これにより、DKMK-007D と同じく index は定義上保存される。

```lean
(SourceControlledChainFamily.ofDivisorStep hM n I hdiv).index = I
```

`LogCapacityHittingBridge` には、selected / canonical route から
この divisor-step family を直接使う API を追加した。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_applyAtToDivisorStep
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_const

canonicalExponentSlotMarkovShadow_applyAtToDivisorStep
canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_const
```

selected route では、`hIOf` と divisor kernel の `index_dvd` から
`q ∣ s.1` が得られる。

canonical route では、`canonicalExponentSlotDivisorTransitionKernel.index_dvd`
から `q ∣ s.1` が得られる。

到達形は次である。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ C

canonical route:
  canonicalExponentSlotMarkovShadow
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ C
```

source は全 channel で `s.1` に揃うため、hitting bound 側の source bound は
次の一点上界で足りる。

```lean
(M.μ s.1 : ℝ) ≤ C
```

これで、形式的 singleton model ではなく、実際の divisor removal
`n ↦ n / q` を含む primitive hitting route に入った。

---

## 2.18. DKMK-007F Unit mass divisor-step bounds

DKMK-007F では、DKMK-007E で残っていた source mass bound を、
既存の concrete mass model `unitNatMassSpace` から供給する。

DKMK-007E の divisor-step route では source が全 channel で `s.1` に揃うため、
一般形の仮定は次であった。

```lean
hsource : (M.μ s.1 : ℝ) ≤ C
```

`unitNatMassSpace` ではすべての点の mass が `1` なので、`C = 1` として
この仮定は自動的に閉じる。

追加した theorem は次である。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_unitDivisorStep_weightedHitMass_le_one

canonicalExponentSlotMarkovShadow_unitDivisorStep_weightedHitMass_le_one
```

到達形は次である。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → unitNatMassSpace
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ 1

canonical route:
  canonicalExponentSlotMarkovShadow
  → unitNatMassSpace
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ 1
```

これにより、selected / canonical の divisor-step hitting route は、
外部から `C` や source mass bound を渡さずに直接呼べる形になった。

---

## 2.19. DKMK-007G Nonunit indicator mass

DKMK-007G では、`unitNatMassSpace` 以外の bounded concrete mass model を
divisor-step route に流す最初の観測点を追加する。

追加した mass model は次である。

```lean
nonunitNatMassSpace
```

定義は単純である。

```text
μ(1) = 0
μ(n) = 1  (n ≠ 1)
```

これは最終的な tail mass model ではない。
ただし、`1` に到達する descent chain を unit mass とは区別できるため、
unit 以外の concrete mass を hitting route に流すための小さな確認点になる。

この mass は divisibility-monotone である。

```lean
nonunitNatMassSpace_dvdMonotone
```

理由は、`a ∣ b` かつ `b = 1` なら `a = 1` であり、
`b ≠ 1` なら target mass はすでに `1` だからである。

`LogCapacityHittingBridge` には、selected / canonical route 用に次を追加した。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_nonunitDivisorStep_weightedHitMass_le_one

canonicalExponentSlotMarkovShadow_nonunitDivisorStep_weightedHitMass_le_one
```

`LogCapacityState` では常に `1 < s.1` なので、

```lean
nonunitNatMassSpace.μ s.1 = 1
```

が成り立つ。したがって DKMK-007E の source mass bound は `C = 1` で閉じる。

到達形は次である。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → nonunitNatMassSpace
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ 1

canonical route:
  canonicalExponentSlotMarkovShadow
  → nonunitNatMassSpace
  → chain(q) = {s.1 / q, s.1}
  → primitive real-weighted hit mass ≤ 1
```

この段階で、unit mass だけでなく、少なくとも一つの非自明な
bounded mass model が DKMK-007E の divisor-step route を通ることが確認された。

---

## 3. 背景

## 3.1. 既存証明 route

Erdős #1196 の最近の証明では、整数の因数分解に沿う下降過程を考える。

$$
n\mapsto \frac{n}{q}
$$

ここで $q\mid n$ は prime-power channel として読まれ、遷移重みは

$$
\frac{\Lambda(q)}{\log n}
$$

で与えられる。

このとき

$$
\sum_{q\mid n}\Lambda(q) = \log n
$$

により、重み総和は $1$ になる。

primitive set は divisibility chain を高々一度しか hit しないため、hitting mass が $1$ を超えない、という形で評価が進む。

## 3.2. DkMath 側の既存到達点

DkMath では、R021-R028 により、prime-power witness

$$
q=p(q)^{k(q)}
$$

から base prime $p(q)$ を読み、

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

を no-sorry で得る finite R/log route が閉じた。

特に、R027 では同じ base prime $p$ を持つ selected labels を exponent slot

$$
1,2,\dots,n.\mathrm{factorization}(p)
$$

へ単射で入れることで、外部 multiplicity budget 仮定を除去した。

この構造は、 $\Lambda(p^k)=\log p$ の有限構造版として読める。

---

## 4. プロジェクトの位置づけ

本 project は、既存証明の Lean 形式化そのものではない。

目的は、次の置き換えである。

| 既存 route                | DkMath route                            |
|---------------------------|-----------------------------------------|
| Markov kernel             | Capacity kernel                         |
| $\Lambda(q)$              | prime-power witness 由来の channel cost |
| $\log n$                  | parent capacity                         |
| 確率遷移                  | 正規化された保存核                      |
| $\sum \Lambda(q)=\log n$  | $\sum \mathrm{cost}\le\mathrm{capacity}$    |
| primitive hitting         | DkMath Mass / Branch / Flow hitting     |

---

## 5. 中核定義

## 5.1. Capacity Kernel

まず確率ではなく、容量とコストを持つ有限構造を定義する。

```lean
structure CapacityKernel (α β : Type _) where
  children : α → Finset β
  capacity : α → ℝ
  cost : α → β → ℝ
  cost_nonneg :
    ∀ a b, b ∈ children a → 0 ≤ cost a b
  outgoing_le :
    ∀ a, (∑ b in children a, cost a b) ≤ capacity a
```

ここで、

- `α` は親状態
- `β` は子 channel
- `children a` は親 $a$ から見える有限 channel
- `capacity a` は親の総容量
- `cost a b` は channel $b$ が消費する容量

である。

## 5.2. 正規化 weight

capacity が正のとき、正規化 weight を定義する。

```lean
def normalizedWeight
    (K : CapacityKernel α β)
    (a : α)
    (b : β) : ℝ :=
  K.cost a b / K.capacity a
```

このとき、もし

$$
0 < \mathrm{capacity}(a)
$$

なら、

$$
\sum_{b\in children(a)}
\frac{\mathrm{cost}(a,b)}{\mathrm{capacity}(a)}
\le 1
$$

が成り立つ。

これが sub-probability の一般補題となる。

---

## 6. DkMath LogCapacityKernel

## 6.1. 親状態

親状態は自然数 $n$ とする。

$$
n > 1
$$

を仮定する。

## 6.2. 子 channel

子 channel は selected prime-power witness label

$$
q\in I\subseteq T.\text{index}(n)
$$

である。

witness provider により、

$$
q=p(q)^{k(q)}
$$

と読む。

## 6.3. capacity

親 $n$ の capacity は

$$
\mathrm{capacity}(n) := \log n
$$

とする。

## 6.4. channel cost

各 $q$ の cost は

$$
\mathrm{cost}(n,q) := \log p(q)
$$

とする。

ここで

$$
p(q)=W.\mathrm{basePrimeOf}(n,I,hI,q)
$$

である。

## 6.5. 保存則

R028 の成果により、

$$
\sum_{q\in I}\log p(q)\le \log n
$$

が成り立つ。

したがって、これは `CapacityKernel` の concrete instance である。

---

## 7. von Mangoldt weight との関係

prime-power label

$$
q=p^k
$$

に対し、

$$
\Lambda(q)=\log p
$$

である。

したがって、DkMath channel cost は

$$
\mathrm{cost}(n,q)=\Lambda(q)
$$

と一致する。

ただし、プロジェクトの哲学としては、 $\Lambda$ を最初に導入しない。

まず witness から

$$
q=p^k
$$

を読み、

$$
p=\mathrm{basePrimeOf}(q)
$$

を取り出し、

$$
\log p
$$

を channel cost と定める。

その後に、

$$
\mathrm{cost}(n,q)=\Lambda(q)
$$

を shadow theorem として示す。

---

## 8. 主要 theorem 候補

## 8.1. CapacityKernel 一般補題

```lean
theorem normalizedWeight_subProbability
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (∑ b in K.children a,
      K.cost a b / K.capacity a) ≤ 1
```

数学的には、

$$
\sum_b \mathrm{cost}(a,b)\le \mathrm{capacity}(a)
$$

から、

$$
\sum_b \frac{\mathrm{cost}(a,b)}{\mathrm{capacity}(a)}\le 1
$$

を得るだけである。

## 8.2. LogCapacityKernel concrete construction

```lean
def PrimePowerWitnessProvider.logCapacityKernel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    CapacityKernel Unit ℕ
```

実際には `Unit` を親にするか、親状態を `ℕ` にするかは設計時に決める。

推奨は、まず簡単に

$$
\text{親}=n\text{ 固定}
$$

の local kernel として作る。

## 8.3. R028 theorem から outgoing bound を供給

```lean
theorem logCapacityKernel_outgoing_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (∑ q in I,
      Real.log (W.basePrimeOf n I hI q)) ≤ Real.log n
```

これは既存の `basePrimeOf_logRatioSubProbability` から戻すか、R/log route の product bound から直接出す。

## 8.4. DkKernel normalized theorem

```lean
theorem logCapacityKernel_normalized_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (∑ q in I,
      Real.log (W.basePrimeOf n I hI q) / Real.log n) ≤ 1
```

これは既存 R028 と同等だが、`CapacityKernel` の一般 API 経由で示すことに意味がある。

---

## 9. モジュール構成案

別 branch 名候補:

```text
feature/dkmath-kernel
```

または

```text
feature/capacity-kernel
```

推奨モジュール:

```text
DkMath/
├── Kernel/
│   ├── Capacity.lean
│   ├── Normalize.lean
│   ├── SubProbability.lean
│   └── Main.lean
│
├── NumberTheory/
│   └── PrimitiveSet/
│       ├── LogCapacityKernel.lean
│       └── VonMangoldtShadow.lean
```

### 9.1. `DkMath/Kernel/Capacity.lean`

役割:

- `CapacityKernel`
- `outgoingCost`
- `outgoing_le_capacity`
- 非負性 API

### 9.2. `DkMath/Kernel/Normalize.lean`

役割:

- capacity 正規化
- normalized weight
- normalized outgoing sum

### 9.3. `DkMath/Kernel/SubProbability.lean`

役割:

- 既存 `SubProbability` provider との橋
- normalized kernel が sub-probability provider を誘導する補題

### 9.4. `DkMath/NumberTheory/PrimitiveSet/LogCapacityKernel.lean`

役割:

- `PrimePowerWitnessProvider` 由来の concrete capacity kernel
- R028 route との接続
- `basePrimeOf_logRatioSubProbability` の kernel API 版

### 9.5. `DkMath/NumberTheory/PrimitiveSet/VonMangoldtShadow.lean`

役割:

- prime-power label 上での cost と $\Lambda$ の一致
- `Λ(p^k)=log p` の theorem-facing 補題
- 既存 Markov kernel route への翻訳口

---

## 10. Phase 分割

## Phase DK-0. Branch 準備

目的:

- 既存 R028 route を壊さず、別 branch を切る。
- 既存 theorem 名を参照できる状態にする。

完了条件:

```bash
lake build DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge
lake build DkMath.NumberTheory.PrimitiveSet
```

が成功する。

## Phase DK-1. CapacityKernel core

実装:

- `CapacityKernel`
- `outgoingCost`
- `outgoingCost_nonneg`
- `outgoingCost_le_capacity`

主定理:

```lean
theorem outgoingCost_le_capacity
```

完了条件:

```bash
lake build DkMath.Kernel.Capacity
```

## Phase DK-2. Normalize layer

実装:

- `normalizedWeight`
- `normalizedOutgoing`
- `normalizedOutgoing_le_one`

主定理:

```lean
theorem normalizedOutgoing_le_one
```

仮定:

$$
0 < \mathrm{capacity}(a)
$$

完了条件:

```bash
lake build DkMath.Kernel.Normalize
```

## Phase DK-3. SubProbability bridge

実装:

- normalized weights を既存 provider / `SubProbability` API へ接続
- `RealWeight` / `RealLog` との import 関係を確認

主定理:

```lean
theorem normalizedProvider_subProbability
```

完了条件:

```bash
lake build DkMath.Kernel.SubProbability
```

## Phase DK-4. PrimePower concrete kernel

実装:

- `PrimePowerWitnessProvider.logCapacityKernel`
- channel set $I$
- capacity $\text{Real.log}\ n$
- cost $\text{Real.log}\ (W.\mathrm{basePrimeOf}\,n\,I\,hI\,q)$
- outgoing bound は R028 route から供給

主定理:

```lean
theorem PrimePowerWitnessProvider.logCapacityKernel_subProbability
```

完了条件:

```bash
lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel
```

## Phase DK-5. von Mangoldt shadow

実装:

- prime-power label に対する `vonMangoldtLike` を定義
- まず実数 log cost と一致する簡易版から始める

候補:

```lean
def vonMangoldtOnPrimePowerLabel (q : ℕ) : ℝ := ...
```

主定理:

```lean
theorem vonMangoldtOnPrimePowerLabel_eq_log_basePrime
```

完了条件:

```bash
lake build DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
```

## Phase DK-6. MarkovKernel translation

実装:

- capacity kernel が、capacity 正かつ outgoing equality の場合に Markov kernel を誘導することを示す。
- outgoing が inequality の場合は sub-Markov kernel として扱う。

主定理:

```lean
theorem capacityKernel_to_subMarkovKernel
theorem capacityKernel_to_markovKernel_of_outgoing_eq
```

完了条件:

```bash
lake build DkMath.Kernel
```

---

## 11. 数学的ゴール

短期ゴール:

$$
\text{R028 theorem}
$$

を

$$
\text{CapacityKernel}
\to
\text{Normalize}
\to
\text{SubProbability}
$$

の一般 API から再表現する。

中期ゴール:

$$
\Lambda(q)
$$

を DkMath channel cost の shadow として導入する。

長期ゴール:

$$
\text{DkMath Kernel}
$$

を使って、既存 Markov route を別解釈し、primitive hitting / Mass API / weighted path family と合流させる。

---

## 12. 設計原則

## 12.1. Markov を先に置かない

最初の主語は Markov kernel ではない。

主語は

$$
\mathrm{capacity}
$$

である。

## 12.2. 確率ではなく質量から始める

既存 DkMath の設計原則と同じく、最初は probability ではなく mass / capacity / flow として扱う。

## 12.3. von Mangoldt は後から現れる

$\Lambda$ は primitive object ではなく、prime-power witness cost の別名として導入する。

## 12.4. 宇宙式対応を忘れない

prime-power label

$$
q=p^k
$$

は、宇宙式 Big

$$
(x+u)^d
$$

と対応しうる。

したがって、DkMath kernel は単なる number-theoretic kernel ではなく、Big / channel / valuation / log capacity の橋として設計する。

---

## 13. リスクと注意点

## 13.1. 抽象化しすぎる危険

`CapacityKernel` を一般化しすぎると、既存 `RealLog` / `RealWeight` API と重なり、役割がぼやける。

対策:

- DK-1 は最小構造にする。
- concrete instance は早めに作る。

## 13.2. `Real.log` 周りの証明負荷

$$
0 < \log n
$$

や division inequality は Lean で重くなる可能性がある。

対策:

- 既存 `RealLogProductBudget` の補題を再利用する。
- 可能なら R024/R028 の既存 theorem を wrapper として使う。

## 13.3. MarkovKernel との過剰同一視

DkMath kernel は Markov kernel そのものではない。

正確には、

- outgoing equality なら Markov
- outgoing inequality なら sub-Markov
- 正規化前は capacity kernel

である。

## 13.4. 既存証明 route との関係

既存証明を否定するものではない。  
既存証明の kernel を、DkMath の capacity 構造から再解釈する project である。

---

## 14. 到達判定

本 branch の最初の成功判定は次である。

```lean
PrimePowerWitnessProvider.logCapacityKernel_subProbability
```

または同等の theorem が no-sorry で閉じること。

この theorem は既存 R028 と同等の数学内容を持つが、証明経路が

$$
\text{CapacityKernel}
\to
\text{Normalize}
\to
\text{SubProbability}
$$

を通る点が異なる。

すなわち、既存 route のコピーではなく、

$$
\text{DkMath capacity kernel}
$$

として再構成できたことを示す。

---

## 15. 暫定まとめ

DkMath Kernel Project は、既存の Markov kernel route をそのまま形式化する project ではない。

これは、

$$
q=p^k
$$

という prime-power witness を、

$$
\text{valuation slot}
$$

と

$$
\text{log capacity}
$$

へ写し、そこから kernel 的構造を生成する別登山ルートである。

既存証明では

$$
\Lambda(q)
$$

が主語になる。

DkMath route では、

$$
\mathrm{channelCost}(q) = \log(\mathrm{basePrime}(q))
$$

が主語になり、その shadow として

$$
\Lambda(q)
$$

が現れる。

この順序の違いこそが、本 project の新規性である。
