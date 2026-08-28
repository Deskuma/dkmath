# PRIM-L044 report — parity-safe far-triple half-scale recharge frontier

## Outcome

**Outcome A — HALF-SCALE RETURN / DEPTH RECHARGE FRONTIER**

L043 の far triple cofactor を、同一anchorの first-half coprime base packetへ
戻し、cofactorの任意の prime divisorを half-scale active-prime world と候補supportへ
戻す wrapper を追加した。L043 の depth / fourth-direction disjunction は、depth三分岐を
L018 の実在する `squareAnchorCoprimePrimeSquareOffsets` membershipへ変換し、new-direction
分岐では fourth witness と product divisibility を保持する。

これは有限算術の recharge frontier である。`t < n` は cofactor の scale compression
であって、smaller-anchor `SquareOffsetsFullyCovered t` ではない。

## 実装

追加 module:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge
```

facade `DkMath.NumberTheory.Legendre` から import した。

主な theorem surface:

- `paritySafeHalfScaleActivePrimes`

  `squareAnchorOddActivePrimes n` を `2 * u < n + 2` で絞る同一anchorの有限集合。

- `mem_paritySafeHalfScaleActivePrimes`

  half-scale集合のfilter membership characterization。

- `paritySafeFarTripleCofactor_mem_coprimeBase`

  L043 packetの `0 < t`、`t < n`、`Nat.Coprime (2*n) t` から、
  `t ∈ squareAnchorCoprimeBaseOffsets n` を得る。`coprime_two_mul_iff_coprime_and_odd`
  により同一anchorでの coprime と first-half条件へ戻している。

- `paritySafeFarTripleCofactor_prime_divisor_halfScale_return`

  `Nat.Prime u` かつ `u ∣ t` なら、L043の `u ≤ t` と `2*t < n+2` を合成して
  `u ∈ paritySafeHalfScaleActivePrimes n` を得る。同時に既存の
  `u ∈ paritySafeActiveSupport n r` も返す。

- `paritySafeFarTripleCofactor_depthLedger_or_halfScaleNewDirection`

  L043 の `p^2` / `q^2` / `s^2` depth branch を、L018の
  `squareAnchorCoprimePrimeSquareOffsets` への membershipへ exact に戻す。第四方向では
  prime性、cofactor divisibility、half-scale return、candidate support、三方向との相違、
  `p*q*s*u ∣ n^2+r` を保持する。

- `paritySafeHalfScaleReturn_false_beam_arithmetic`

  指示書の `(62,41)` / `(62,83)` beam を `norm_num` で固定する。二つの異なる far
  factorization がともに cofactor `7` と returned prime `7` を持つため、`t` または `u`
  を residual incidence の injective charge keyとは解釈しない。

## stronger-beam judgment

1. far cofactor `t` は `squareAnchorCoprimeBaseOffsets n` に戻る。**Yes**。
2. `u | t` かつ `Prime u` なら `2*u < n+2` まで強化できる。**Yes**。
3. その `u` は half-scale active set と candidate support の双方に入る。**Yes**。
4. depth三分岐は L018 prime-square incidenceへ exact に戻る。**Yes**。
5. fourth direction は明示 witness として残る。既存L043の三方向との相違条件と
   product divisibilityを保持した。`support.card ≥ 4` の独立補題は、今回の主張に不要な
   Finset bookkeepingを増やさないためoptional範囲として追加していない。
6. `t` / `u` による global injective recharge は可能か。**No**。
   上記 arithmetic false beam が反例となる。
7. residual ledger の universal cardinal contradiction は出たか。**No**。
   half-scale return、depth recharge、fourth witnessだけであり、所有権の全体的な単射や
   cardinal budget消滅は未提供である。
8. smaller-anchor `SquareOffsetsFullyCovered t` は得られたか。**No**。
   `t < n` から full-cover reconstructionへ進むproviderはない。

## 境界

追加していないものは、generic fourth / fifth / k-direction hypergraph、far residual
incidenceから cofactor または returned prime への injectivity、residual ledgerの普遍的
消滅、global cardinal contradiction、smaller-anchor descent、Legendre予想、PNT・sieve・RH
である。

従って今回の形式的な帰結は、

```text
large far triple
  -> same-anchor first-half coprime cofactor
  -> half-scale old-prime return
  -> existing L018 depth incidence or explicit fourth direction
```

までで閉じる。`t` / `u` の noninjective ownership boundary は明示的に残る。

## 検証

Lean 4.32.2 の現行 checkoutで次を実行し、いずれも成功した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarTripleRecharge
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規sourceについて `sorry`、`admit`、`axiom`、`native_decide` および末尾空白を監査した。
full repository build、commit、push、PR、CIは今回の依頼範囲に含めていない。
