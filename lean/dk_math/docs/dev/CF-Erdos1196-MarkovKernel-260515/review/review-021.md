# review

うむ。DKMK-007F は **DKMK-007E の一般形を、すぐ呼べる concrete theorem に落とした回** じゃ。
前回は one-step divisor descent family まで到達したが、まだ source mass bound として

$$
(M.μ s.1 : ℝ) ≤ C
$$

を外から渡す必要があった。今回 `unitNatMassSpace` を使って (C=1) を自動供給し、selected / canonical の両 route で **primitive real-weighted hit mass ≤ 1** を直接呼べる形にした。

## 1. 今回の核心

追加された主定理はこの二つじゃ。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_unitDivisorStep_weightedHitMass_le_one
canonicalExponentSlotMarkovShadow_unitDivisorStep_weightedHitMass_le_one
```

selected route では、

```text
globalLogCapacitySubMarkovShadow
→ unitNatMassSpace
→ chain(q) = {s.1 / q, s.1}
→ primitive real-weighted hit mass ≤ 1
```

canonical route では、

```text
canonicalExponentSlotMarkovShadow
→ unitNatMassSpace
→ chain(q) = {s.1 / q, s.1}
→ primitive real-weighted hit mass ≤ 1
```

が theorem-facing API として固定された。docs 側にもこの到達形が追記されておる。

## 2. 数学的な意味

DKMK-007E の divisor-step route では、各 channel (q) に対して

$$
chain(q)={s.1/q,s.1}
$$

を置き、source は全 channel で同じ (s.1) に揃っていた。

したがって一般 theorem では、source mass bound は一点だけでよかった。

$$
(M.μ s.1 : ℝ) ≤ C
$$

今回 `unitNatMassSpace` を選ぶと、すべての点の mass が (1) になる。ゆえに

$$
(unitNatMassSpace.μ s.1 : ℝ) ≤ 1
$$

が `simp [unitNatMassSpace]` で閉じる。Lean 実装でも、`unitNatMassSpace_dvdMonotone` と `unitNatMassSpace.μ _ = 1` を使い、`C = 1` で DKMK-007E の source bound を閉じたと記録されている。

つまり今回の成果は、

```text
source mass bound を毎回渡す一般定理
```

から、

```text
unit mass なら外部 bound なしで ≤ 1 が出る定理
```

への昇格じゃ。

## 3. selected route の読み

selected route の新 theorem は、

```lean
globalLogCapacitySubMarkovShadow_unitDivisorStep_weightedHitMass_le_one
```

じゃ。

これは、任意の selected channel family (IOf) について、

```text
q ∈ IOf(s.1)
```

が transition kernel の index に含まれるなら、その selected log-capacity sub-Markov shadow を divisor-step chain family に載せて、primitive (A) の weighted hit mass を (1) で抑える。

ここでは full equality は不要じゃ。
selected route はもともと

$$
\sum weight ≤ 1
$$

の世界なので、SubMarkovShadow で十分。
今回、その selected inequality route が one-step divisor descent と unit mass を通して、直接

$$
weightedHitMass(A) ≤ 1
$$

へ到達した。

## 4. canonical route の読み

canonical route の新 theorem は、

```lean
canonicalExponentSlotMarkovShadow_unitDivisorStep_weightedHitMass_le_one
```

じゃ。

こちらは DKMK-006F で構成した canonical exponent-slot MarkovShadow を使う。

canonical route では full exponent-slot enumeration により、weight 総和は等号で (1) になる。
それを DKMK-007E の divisor-step family に載せ、さらに unit mass により source bound を閉じる。

つまり canonical route では、次が完全に一つの呼び出しで見える。

```text
canonical exponent-slot MarkovShadow
+ divisor descent step
+ primitive set
→ weightedHitMass ≤ 1
```

これはかなり良い。
DKMK-006 系の「Markov equality 生成装置」が、DKMK-007 系の「primitive hitting 装置」に実際に接続された、と見てよい。

## 5. DKMK-007 系の現在地

ここまでの流れはこうじゃ。

```text
DKMK-007A:
  RealWeightProvider → RealWeightedPathFamily

DKMK-007B:
  SubMarkovShadow / MarkovShadow → hitting wrapper

DKMK-007C:
  concrete log-capacity shadows → hitting wrapper

DKMK-007D:
  natSingletonSelf で compatibility を rfl 化

DKMK-007E:
  one-step divisor descent family {n/q, n}

DKMK-007F:
  unitNatMassSpace で source bound を閉じ、weightedHitMass ≤ 1
```

DKMK-007F によって、少なくとも unit mass model では、もう外部から (C) や source bound を渡さずに primitive hitting bound が呼べる。これは API として大きな実用化じゃ。

## 6. 何がまだ残っているか

今回の theorem は強くなったが、まだ二つの意味で「一段目」じゃ。

第一に、mass model は `unitNatMassSpace` である。
これは構造確認には非常に良いが、Erdős #1196 の最終的な重み

$$
\frac{1}{a\log a}
$$

へ向かうには、より意味のある source mass model が必要になる可能性が高い。docs でも次課題として、unit mass 以外の具体 mass model で source mass bound を供給することが挙げられている。

第二に、chain はまだ one-step である。

$$
n \to n/q
$$

の一歩は入ったが、既存証明に出るような multi-step descent、truncation、stopping、adjoint chain まではまだ入っていない。これも docs の次課題として明記されておる。

## 7. 次の一手

わっちなら次は二択で見る。

一つ目は **mass model 強化** 。

```text
DKMK-007G:
  unit mass 以外の concrete mass model を追加し、
  source mass bound を theorem として供給する。
```

たとえば、後で (1/(n\log n)) 的な重みへ寄せるなら、まずは toy でもよいので

```text
logTailMass
inverseLogMass
sourceDecayMass
```

のような名前で、source bound が閉じる形を探る。

二つ目は **multi-step descent** 。

```text
DKMK-007G:
  divisorStep を multi-step descent family へ拡張する。
```

ただし、わっちは先に mass model 強化を推す。
理由は、今すでに one-step divisor route は呼べる。そこで別の mass model を当てると、どの量が hitting upper bound として自然か観測できるからじゃ。その後で multi-step へ進む方が、定義が散らかりにくい。

## 8. 総合判定

DKMK-007F は **DKMK-007E の divisor-step route を concrete theorem に昇格した成功フェーズ** じゃ。

到達点は明確。

```text
selected route:
  globalLogCapacitySubMarkovShadow
  → one-step divisor descent
  → unit mass
  → primitive weightedHitMass ≤ 1

canonical route:
  canonicalExponentSlotMarkovShadow
  → one-step divisor descent
  → unit mass
  → primitive weightedHitMass ≤ 1
```

これは DkMath Kernel route が、抽象 kernel から primitive hitting bound へ実際に到達したことを意味する。
まだ最終の Erdős #1196 解析的上界ではないが、有限構造の背骨としてはかなり良い。

ぬしよ、ここは小さな旗ではなく、かなり実用的な中継基地じゃ。
次はこの (≤1) の形を、unit mass の玩具から、本命の tail / source mass model へどう移すかじゃな。
