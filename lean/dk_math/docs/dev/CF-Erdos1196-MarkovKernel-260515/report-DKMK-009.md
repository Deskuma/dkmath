# DKMK-009: report

DKMK-009 は、DKMK-007/008 で整えた hitting route と descent path route を、
既存の `CapacityKernel` 層へ戻す章である。

DKMK-007 は、log-capacity shadow を primitive hitting bound へ載せる
mass / hitting route を整えた。
DKMK-008 は、その chain 側を one-step divisor descent から
multi-step path family、さらに witness-derived quotient path family へ拡張した。

DKMK-009 では、新しい path を増やさず、

```text
CapacityKernel
  → normalized shadow
  → SourceControlledChainFamily
  → RealWeightedPathFamily
  → primitive weightedHitMass bound
```

という kernel-facing route を Lean API として固定した。

## 1. 主目的

DKMK-009 の主目的は次である。

```text
capacity kernel の normalized shadow が、
primitive hitting route の正式な入力であることを固定する。
```

これは、DkMath Kernel Project の基本理念

```text
Markov kernel is a normalized shadow of DkMath capacity kernel.
```

を primitive hitting route 上で theorem-facing にしたものと言える。

## 2. 009B: generic capacity-kernel hitting bridge

DKMK-009B では、新規ファイルとして次を追加した。

```text
DkMath/NumberTheory/PrimitiveSet/CapacityKernelHittingBridge.lean
```

主な API は次。

```lean
CapacityKernel.normalizedSubMarkovShadow_providerAt_compatible
CapacityKernel.applyAtToSourceControlled
CapacityKernel.applyAtToSourceControlled_weightSubProbability
CapacityKernel.weightedHitMass_le_const_applyAtToSourceControlled
```

この段階で、任意の positive capacity kernel について、

```text
K : CapacityKernel σ ι
hcap : ∀ s, 0 < K.capacity s
F : SourceControlledChainFamily M ι
hindex : K.children s = F.index
```

から `F` に normalized weight を載せられるようになった。
さらに、primitive set `A` と source mass bound があれば、

```text
weightedHitMass A ≤ C
```

が得られる。

証明は新しい hitting proof を作らず、
`SubMarkovShadow.ofCapacityKernel` と既存の `ShadowHittingBridge` を合成する
薄い wrapper に留めた。

## 3. 009C: global log-capacity kernel への特殊化

DKMK-009C では、009B の generic bridge を
`PrimePowerWitnessProvider.globalLogCapacityKernel` へ特殊化した。

追加 API は次。

```lean
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToSourceControlled
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToSourceControlled_index
PrimePowerWitnessProvider.globalLogCapacityKernel_weightedHitMass_le_const
```

これにより、次の読み方ができる。

```text
PrimePowerWitnessProvider.globalLogCapacityKernel
  → CapacityKernel.applyAtToSourceControlled
  → RealWeightedPathFamily
  → weightedHitMass bound
```

既存の `globalLogCapacitySubMarkovShadow_*` route は維持したまま、
capacity kernel から generic bridge を経由する入口を明示した。

## 4. 009D: quotient path family への接続

DKMK-009D では、009C の route を witness-derived quotient path family へ接続した。

追加 API は次。

```lean
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily
PrimePowerWitnessProvider.globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily_index
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

この段階で、DKMK-009 の本命 route は次の形になった。

```text
PrimePowerWitnessProvider
  → globalLogCapacityKernel
  → CapacityKernel generic bridge
  → primePowerQuotientPathFamily
  → weightedHitMass bound
```

`primePowerQuotientPathFamily` は、label `q` の witness

```text
q = p(q)^k(q)
```

を読み、

```text
n → n / p(q) → ... → n / p(q)^k(q)
```

という multi-step quotient path を作る。

DKMK-009D では、この concrete path family に global log-capacity kernel の
normalized weight を載せた。
上界は `LogCapacitySourceMassBound M C` から供給する。
これは quotient path family の source が常に現在の state `s.1` であるためである。

## 5. route 図

DKMK-009 の抽象 route は次である。

```text
CapacityKernel
  ↓ normalized shadow
SubMarkovShadow
  ↓ applyAtToSourceControlled
RealWeightedPathFamily
  ↓ primitive hitting bridge
weightedHitMass bound
```

Erdős #1196 向けの selected log-capacity route では、次のように特殊化される。

```text
PrimePowerWitnessProvider
  ↓ globalLogCapacityKernel
global log-capacity CapacityKernel
  ↓ CapacityKernel.applyAtToSourceControlled
primePowerQuotientPathFamily
  ↓ primitive hitting bridge
weightedHitMass bound
```

つまり、finite R/log route の normalized mass は、
単なる sub-probability statement に留まらず、
witness-derived divisor descent path 上の hitting mass bound へ流れる。

## 6. API 対応表

| phase | role | main API group |
| --- | --- | --- |
| 009B | generic bridge | `CapacityKernel` |
| 009C | selected log-capacity specialization | `globalLogCapacityKernel` |
| 009D | quotient path family route | `primePowerQuotientPathFamily` |

Main theorem names:

```lean
CapacityKernel.weightedHitMass_le_const_applyAtToSourceControlled
PrimePowerWitnessProvider.globalLogCapacityKernel_weightedHitMass_le_const
PrimePowerWitnessProvider
  .globalLogCapacityKernel_primePowerQuotientPathFamily_weightedHitMass_le_of_sourceBound
```

DKMK-009B は任意の capacity kernel に対する入口である。
DKMK-009C は selected global log-capacity kernel への特殊化である。
DKMK-009D は witness-derived quotient path family まで含めた本線である。

## 7. DKMK-008 との接続

DKMK-008 の到達点は、

```text
manual path
one-step divisor path
witness-derived multi-step quotient path
```

の三入口を持つ path route だった。

DKMK-009 は、そのうち witness-derived multi-step quotient path を、
capacity kernel の normalized shadow へ明示的に接続した。

このため、DKMK-008 と DKMK-009 の関係は次のように読める。

```text
DKMK-008:
  path を作る章

DKMK-009:
  capacity kernel の normalized weight を path に流す章
```

## 8. 到達点

DKMK-009 の中核は、DKMK-009D で閉じた。

到達形は次。

```text
PrimePowerWitnessProvider
→ globalLogCapacityKernel
→ normalized capacity-kernel bridge
→ witness-derived quotient path family
→ primitive weightedHitMass bound
```

これは有限 kernel-hitting spine として、次の解析層へ進むための構造である。

## 9. 次の分岐

次は二方向が自然である。

第一は、DKMK-009E/F として public/docs をさらに整理することである。
この report と `DkMath_Markov_kernel-to-ck.md` の DKMK-009 節は、その第一段である。

第二は、必要が明確になった場合に finite-step / two-step convenience wrapper を
追加することである。
ただし DKMK-009 の中核 route はすでに通っているため、API を増やす場合は
用途を明確にしてからにする。

その先の DKMK-010 では、tail / truncation / analytic estimate へ進む。
