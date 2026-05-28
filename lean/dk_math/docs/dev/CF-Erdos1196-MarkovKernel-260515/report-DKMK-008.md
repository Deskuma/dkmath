# DKMK-008: report

DKMK-008 は、DKMK-007 で整えた one-step divisor descent route を、
`AdjacentDivisorPathFamily` による path-family route へ持ち上げる章である。

DKMK-007 の中心は、log-capacity shadow を one-step divisorStep family に
載せ、source mass bound から primitive hitting bound を得ることだった。
DKMK-008 では、同じ mass / hitting machinery を、外部から与えた
multi-step divisor path family にも使える形へ拡張した。

最終的に DKMK-008H で、DKMK-007 の one-step theorem と DKMK-008 の
path-family theorem が theorem-facing API として重なった。

## 1. 主目的

DKMK-008 の目的は次の一文にまとめられる。

```text
one-step divisorStep route を、
multi-step divisor path family route の特殊例として回収する。
```

DKMK-007 では chain 側が

```text
q ↦ {n / q, n}
```

に固定されていた。

DKMK-008 では、これを

```text
q ↦ AdjacentDivisorPath
```

へ一般化し、各 index に任意の adjacent divisor path を割り当てられる
ようにした。

## 2. DKMK-008A-H の流れ

DKMK-008A では、list-shaped な single divisor path を入れた。

```lean
AdjacentDivisorPath
```

これは head から tail へ隣接 divisibility step で進む path であり、
`toDvdControlledChain` により既存の chain API に戻せる。

DKMK-008B では、single path を finite indexed family に拡張した。

```lean
AdjacentDivisorPathFamily
```

この family は、各 index ごとに source / tail / path / nodeSet を持ち、
`toDvdControlledChainFamily` で既存の `DvdControlledChainFamily` に
接続できる。

DKMK-008C では、この external path family を selected / canonical shadow に
直接載せる wrapper を追加した。

DKMK-008D では、same-source 条件

```lean
∀ q ∈ F.index, F.source q = s.1
```

のもとで `LogCapacitySourceMassBound` を合成できる wrapper を追加した。

DKMK-008E では、finite-step tail mass を same-source path family に載せた。

DKMK-008F では、two-step-as-finite-step tail mass を same-source path family に
載せた。

DKMK-008G では、one-step divisorStep を path-family route の特殊例として
回収した。

```lean
oneStepDivisorAdjacentPathFamily
```

DKMK-008H では、この one-step path family を selected / canonical の
finite-step / two-step shadow wrapper に直接載せた。

## 3. DKMK-007 と DKMK-008 の対応

DKMK-007 route の chain は、概念的には次である。

```text
divisorStep:
  q ↦ {n / q, n}
```

DKMK-008 route の one-step path family は、次である。

```text
oneStepDivisorAdjacentPathFamily:
  q ↦ [n, n / q]
  nodeSet q = {n / q, n}
```

list の向きは source から descendant へ進むが、hitting 側で見る node set は
DKMK-007 の divisorStep chain と同じである。

したがって、DKMK-007 の one-step theorem は、DKMK-008 では
`oneStepDivisorAdjacentPathFamily` を渡した same-source
`AdjacentDivisorPathFamily` theorem として読める。

## 4. Statement 対応表

selected route の finite-step 対応は次である。

```text
DKMK-007:
  PrimePowerWitnessProvider
    .globalLogCapacitySubMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  PrimePowerWitnessProvider
    .globalLogCapacitySubMarkovShadow_finiteStepTailOneStepPath_weightedHitMass_le
```

selected route の two-step-as-finite-step 対応は次である。

```text
DKMK-007:
  PrimePowerWitnessProvider
    .globalLogCapacitySubMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  PrimePowerWitnessProvider
    .globalLogCapacitySubMarkovShadow_twoStepTailOneStepPath_weightedHitMass_le
```

canonical route の finite-step 対応は次である。

```text
DKMK-007:
  canonicalExponentSlotMarkovShadow_finiteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  canonicalExponentSlotMarkovShadow_finiteStepTailOneStepPath_weightedHitMass_le
```

canonical route の two-step-as-finite-step 対応は次である。

```text
DKMK-007:
  canonicalExponentSlotMarkovShadow_twoStepAsFiniteStepTailDivisorStep_weightedHitMass_le

DKMK-008:
  canonicalExponentSlotMarkovShadow_twoStepTailOneStepPath_weightedHitMass_le
```

両 route の上界は同じである。

finite-step では、

```lean
((Finset.sum steps increment : ℚ) : ℝ)
```

two-step では、

```lean
(cHigh : ℝ)
```

を返す。

## 5. Divisibility witness の対応

DKMK-007 の divisorStep route では、one-step chain を作るために

```lean
hdiv : ∀ q ∈ I, q ∣ n
```

が必要だった。

DKMK-008G の `oneStepDivisorAdjacentPathFamily` も同じ witness を要求する。
しかし DKMK-008H の selected / canonical wrapper では、この witness は
利用者が手で渡さなくてよい。

selected route では、

```lean
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
T.toDivisorTransitionKernel.index_dvd
```

から `q ∣ s.1` を作る。

canonical route では、

```lean
canonicalExponentSlotDivisorTransitionKernel.index_dvd
```

から `q ∣ s.1` を作る。

このため、one-step path family は shadow wrapper の内部で構成される。

## 6. 008 の到達点

DKMK-008 の現在の到達点は次である。

```text
external multi-step path family
  → selected / canonical shadow
  → source-bound wrapper
  → finite-step / two-step weightedHitMass bound
```

さらに one-step の特殊例として、

```text
selected / canonical index
  → index_dvd
  → oneStepDivisorAdjacentPathFamily
  → same-source path-family theorem
  → finite-step / two-step weightedHitMass bound
```

も public API で呼べる。

これにより DKMK-007 は、DKMK-008 の特殊例として回収された。

## 7. 次の分岐

ここから先は二方向が自然である。

第一は、現在の external path family API を使う側の examples / reports を
増やすことである。これは theorem-facing API の使い分けを明確にする。

第二は、path を自動生成することである。例えば prime-power channel
`q = p^k` から

```text
n → n / p → n / p^2 → ... → n / p^k
```

のような multi-step path を作る route である。

DKMK-008A-H は、後者へ進むための path-family 受け口を整えた段階と
位置づけられる。

## 8. 追補: DKMK-008J

DKMK-008J では、prime-power channel

```text
q = p^k
```

から multi-step divisor path を作るための path-level constructor が入った。

```lean
primePowerQuotientPath
primePowerQuotientPath_isPath
```

`primePowerQuotientPath n p k` は、

```text
[n / p^0, n / p^1, ..., n / p^k]
```

を返す。

`primePowerQuotientPath_isPath` は、`p^k ∣ n` のもとでこの list が
`AdjacentDivisorPath` であることを示す。

これにより、DKMK-008I で次の未踏地として整理した

```text
n → n / p → n / p^2 → ... → n / p^k
```

の最小 Lean 核が入った。

ただし、DKMK-008J はまだ pure path-level である。
`PrimePowerWitnessProvider` から `(p,k)` を読み、selected / canonical の
`AdjacentDivisorPathFamily` へ自動で載せる wrapper は次段の課題として残る。

## 9. 追補: DKMK-008K

DKMK-008K では、DKMK-008J の path-level constructor を
`PrimePowerWitnessProvider` に接続した。

追加した constructor は次である。

```lean
PrimePowerWitnessProvider.primePowerQuotientPathFamily
```

これは、state `n` と finite index set `I` について、各 `q ∈ I` から
witness-derived な `(p(q), k(q))` を読み、

```text
n → n / p(q) → n / p(q)^2 → ... → n / p(q)^k(q)
```

を `AdjacentDivisorPathFamily` として構成する。

path の divisibility 仮定は、新しい仮定ではなく既存 theorem

```lean
W.basePrimeOf_pow_baseExponentOf_dvd_source_on n I hI q hq
```

から供給する。

これで DKMK-008 は、

```text
selected labels
  → witness-derived prime-power data
  → quotient path family
  → same-source multi-step path-family route
```

へ進む入口を持つ。
