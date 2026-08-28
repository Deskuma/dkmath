# PRIM-L040 report — parity-safe support excess / quotient co-support transport

## 判定

**Outcome A — EXACT SUPPORT-EXCESS / QUOTIENT CO-SUPPORT TRANSPORT**

PRIM-L036 の candidate-side `paritySafeSupportExcess` を、covered candidate
ごとの canonical quotient co-support incidenceへ exact に transportした。
これは有限 support と quotient factorization の checkpointであり、
universal estimate、descent、または Legendre 予想の証明ではない。

## 実装

追加した module は
`DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient` で、
`DkMath.NumberTheory.Legendre` facadeから importできる。

主要な theorem surface は次のとおり。

- `paritySafeCanonicalSupportPrime_mem_activeSupport`

  covered candidate の active supportから least memberを canonical primeとして
  選び、その membershipを証明する。

- `paritySafeCanonicalSupportPrime_packet`

  canonical memberが candidate-side active support、old nondivisor support、
  parity-safe active prime worldのすべてに属することを回収する。

- `paritySafeSupportExcess_seat_eq_quotientCoSupport_card`

  `card activeSupport - 1` と、canonical primeを eraseした
  `squareQuotientAnchorNondivisorSupport` の cardinalityを exact に一致させる。
  証明は既存の `erase_squareQuotientSupport_eq_erase_offsetSupport` を再利用し、
  support definitionを複製していない。

- `paritySafeSupportExcess_eq_covered_quotientCoSupport_sum`

  uncovered candidateの空 support termを有限 `Nat` bookkeepingで消去し、
  L036 の全 support excessを covered candidatesだけの quotient co-support sumへ
  書き換える。

- `paritySafeCanonicalQuotientCoSupportIncidences`

  `(r,q)` の有限 incidence setを、covered candidateと parity-safe active prime
  の product-filterとして定義する。

- `paritySafeCanonicalQuotientCoSupportIncidences_card_eq_supportExcess`

  上記 incidence setの cardinalityが `paritySafeSupportExcess` と exact に等しい
  ことを証明する。

- `paritySafeCanonicalQuotientCoSupportIncidence_packet`

  各 incidenceについて、canonical selected prime `p` と quotient direction `q`
  がともに active、`p ≠ q`、
  `q ∣ squareOffsetSupportQuotient n p r`、
  `p*q ∣ n^2+r`、および `Nat.Coprime (2*n) (p*q)` を満たすことを示す。
  特に `q` の存在は distinct old-prime factorとして保持される。

- `paritySafeDirectionDepth_false_beam_five_two`

  `(n,r)=(5,2)` で `n^2+r=27=3^3` を検証する。active supportは `{3}`、
  support excessは `0` だが、selected primeの quotientにはさらに `3` が残る。
  quotient supportを `3` eraseすると空になり、distinct direction massと
  selected-prime self-depthを混同しないことを Lean 上で固定する。

## strongest-beam judgment

1. `paritySafeSupportExcess` は canonical quotient co-support massへ exact に
   transportできた。
2. transported excessの各 unitは distinct old primes `p,q` と factorization
   `p*q ∣ n^2+r` を与える。
3. selected-prime self-depthは quotient supportから `erase p` するため、この
   massには含まれない。`(5,2)` false beamがその境界を具体化する。
4. これは単なる座標 renameではなく、finite incidence setと product-divisor
   packetを得る reusable factorization stateである。ただし、その stateから
   support excessの universal boundや descentは導いていない。
5. 直近の consumerは PRIM-L017 の
   `not_prime_quotient_iff_self_depth_or_distinct_support` と、PRIM-L018 の
   localized pair ledgerである。PRIM-L019 は cross-seat couplingなので、今回の
   single-seat canonical incidenceをそのまま閉じる consumerではない。

従って、今回の transportは L036 の support excessを old-prime pair/divisor
データへ変換する点で再利用可能だが、Legendre予想へ進むための universal
cardinality inequality、matching、descent providerは依然として未提供である。

## 停止境界

今回、PNT、Mertens/Rosser--Schoenfeld、Jacobsthal、generic sieve、graph/matching
framework、infinite descent、large clique、`LegendreConjecture` theoremは追加していない。

## 検証範囲

Lean 4.32.2 / Mathlib checkoutで次を検証する。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeSupportExcessQuotient
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 Lean sourceについて `sorry`、`admit`、`axiom`、`native_decide` と末尾空白を
監査する。full repository build、commit、push、CIは bounded instruction の範囲外である。
