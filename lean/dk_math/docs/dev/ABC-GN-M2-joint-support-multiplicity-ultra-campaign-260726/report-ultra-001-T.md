# Ultra-001T Report — exact large-boundary divisor packet and contract audit

Date: 2026-07-27

## 判定

S2 の指示した repeated prime-power route を実装し、U-001T は Branch A で完了した。

```text
generic repeated prime-power factorization       complete
piSqRad / sqTail / twoTail exact reconnection    complete
target active modulus exact identification       complete
large squareful divisor packet                   complete
legacy logarithmic pincer                        complete
root-address charge bound                        complete
three-quarter boundary-weight diagnosis          complete
ABC <-> odd-prime joint-contract audit           complete
U-001T                                           Branch A / complete
```

実装は次の二 module に分離した。

```text
DkMath.ABC.GNExcessLargeBoundaryPacket
DkMath.ABC.GNJointContractEquivalence
```

公開 aggregate `DkMath.ABC` からも import した。

## 1. repeated prime-power part

```lean
noncomputable def repeatedPrimePowerPart (n : ℕ) : ℕ
```

を、`factorization n q ≥ 2` の素数について完全な素数冪
`q ^ factorization n q` を積む整数として定義した。`n ≠ 0` ならば次を得る。

```text
repeatedPrimePowerPart n = piSqRad n * sqTail n
repeatedPrimePowerPart n = (piSqRad n)^2 * twoTail n
repeatedPrimePowerPart n ∣ n
rad (repeatedPrimePowerPart n) = piSqRad n
piSqRad n ∣ sqTail n
```

factorization と support も exact theorem として公開した。従ってこの整数は
単なる上界用の量ではなく、`n` の指数二以上の層を完全に保持する divisor
である。

## 2. GN target modulus の exact identity

```lean
noncomputable def GNNonExceptionalRepeatedPart (p a b : ℕ) : ℕ
```

を `GNNonExceptionalPart p a b` の repeated part として定義した。

canonical interval family と target point の excess profile に対して、

```lean
theorem GNExcessJointDepthModulus_target_eq_repeatedPart
```

により active CRT modulus が
`GNNonExceptionalRepeatedPart p a b` と整数として完全に一致することを示した。
この同一視には次の二つが含まれる。

```text
active primes = non-exceptional part の valuation ≥ 2 support
active exponent + 1 = 元の完全な factorization depth
```

また repeated part は `GNNonExceptionalPart p a b` と `GN p a b` の両方を
割り切る。

## 3. large-boundary packet

```lean
structure GNExcessLargeBoundaryPacket (p a b X : ℕ)
```

に次をまとめた。

```text
modulus = GNNonExceptionalRepeatedPart p a b
modulus = piSqRad * sqTail
modulus = piSqRad^2 * twoTail
X + 1 < modulus
modulus ∣ GNNonExceptionalPart
modulus ∣ GN
q ∣ modulus, q prime -> q^2 ∣ modulus
q ∣ modulus, q prime -> q ∈ GNNonExceptionalSupport
q ∣ modulus, q prime -> q % p = 1
```

`GNExcessLargeBoundaryPacket.of_target` が large target profile からこの packet
を構成する。従って large profile は、区間長より大きい exact squareful
non-exceptional GN divisor を必ず供給する。

## 4. legacy pincer と 3/4 診断

packet の exact decomposition から次の分岐を得た。

```text
(1/4) * log (X + 1) < log (piSqRad N)
or
(1/2) * log (X + 1) < log (twoTail N)
```

これは large boundary を、repeated-support heavy と depth-three-tail heavy
の二つへ正式に分離する。

さらに target active support に対して、

```text
(p - 1)^active.card ≤ piSqRad N
```

を exact-order 条件 `q % p = 1` から証明した。target excess mass は
`log (sqTail N)` と一致するため、`t = 1/2` では、

```text
rootAddressCharge * exp ((1/2) * excessMass)
  ≤ (GNNonExceptionalRepeatedPart p a b : ℝ)^(3/4)
```

となる。これは一 profile の診断 theorem であり、large profile 全体の和を
評価する theorem ではない。

## 5. contract equivalence audit

別 module で `abc_main` と同じ量化を持つ述語を定義した。

```lean
def ABCRawBound (ε : ℝ) : Prop
```

固定指数 `p = 3` について、

```text
GN 3 a b ≤ 3 * (a + b)^2
```

を証明し、ABC bound の定数 `K` から、

```text
ρ = 2 * (1 + ε)
C = log 3 + 2 * log K
```

を選んで joint-pressure contract を構成した。

公開 endpoint は次である。

```lean
theorem GNOddPrimeJointContract_of_ABCRawBound

theorem ABCRawBound_iff_nonempty_GNOddPrimeJointContract
    (hε : 0 < ε) :
    ABCRawBound ε ↔
      Nonempty (ABCGNOddPrimeJointContract ε)
```

従って uniform odd-prime joint contract の無条件構成は、単なる残りの
bookkeeping ではなく raw ABC bound と同等級であることが Lean 上で確定した。

## 6. 正確な停止境界

今回の結果は次を証明しない。

```text
large-boundary profile sum の absorption
repeatedPart^(3/4) の profile 全体での summability
deterministic target escape
uniform joint contract の無条件構成
abc_main_axiom の除去
ABC 予想の無条件証明
```

equivalence theorem の ABC 側を `abc_main` から供給すれば contract が得られるが、
現在の `abc_main` 自体は既存の `abc_main_axiom` に依存する。この audit は依存を
消すものではなく、残る uniform arithmetic theorem の論理的な強さを同定する。

## Local verification

```text
lake build DkMath.ABC.GNExcessLargeBoundaryPacket    success (8371 jobs)
lake build DkMath.ABC.GNJointContractEquivalence     success (8372 jobs)
lake build DkMath.ABC                                success (8391 jobs)
lake build DkMath                                    success (8758 jobs)
new production code                                 no sorry / axiom / admit / native_decide
git diff --check                                    clean
```

aggregate build に表示される既存 research module の `sorry` warning は今回の変更に
よるものではない。

push、PR 更新、CI 起動・確認は行っていない。
