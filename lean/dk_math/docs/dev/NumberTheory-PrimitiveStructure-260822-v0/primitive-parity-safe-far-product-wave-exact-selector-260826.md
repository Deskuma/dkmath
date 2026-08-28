# PRIM-L047 report — parity-safe far product-wave exact selector

## Outcome

**Outcome A — EXACT FAR PRODUCT-WAVE SELECTOR**

L046 の far cofactor wave information を L042 の far product-wave upper universeへ戻し、
actual far residual incidence を有限 selector incidence として exact に同定した。
selector の条件は、product-wave hit の reduced cofactor と、seat における canonical
support-prime ownership だけである。

canonical-minimum condition を smaller active divisor の exclusion formへ書き換える
optional A+ 部分は追加していない。canonical equalityそのものは exact selector の一条件
として使用している。

## 実装

追加 module:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector
```

facade `DkMath.NumberTheory.Legendre` から import した。

主な theorem surface:

- `paritySafeFarProductWaveCofactor_packet`

  far key と product-wave hit から quotient `t` を取り、
  `0 < t`、`p*q*s*t = n^2+r`、`2*t < n+2` を得る。これは actual residual incidence に
  限定しない product-wave arithmetic packet である。

- `paritySafeTripleGateFarProductModulus_coprime_two_mul`

  far triple product `p*q*s` が `2*n` と coprime であることを、既存の active-prime
  reduced-residue packet から示した。

- `paritySafeFarProductWave_mem_candidate_iff_cofactor_coprime`

  far product-wave hit 上で

  ```text
  r ∈ squareAnchorOddPointCoprimeOffsets n
    ↔ Nat.Coprime (2*n) (product-wave quotient)
  ```

  を exact に証明した。wave factorization と product modulus の coprimalityを使っている。

- `paritySafeCanonicalFarProductWaveOffsets`

  product-wave hit を reduced cofactor と
  `key.1 = paritySafeCanonicalSupportPrime n r` で filter する exact selector Finset。

- `paritySafeCanonicalFarProductWaveOffset_mem_farResidual`

  selector membershipから actual far residual incidenceを reverse reconstructionする。
  candidate、coveredness、canonical quotient co-support、ordered pair filter、far gate を
  既存 API だけで構成した。generic factorization library は追加していない。

- `paritySafeCanonicalFarResidual_mem_productWaveSelector`

  actual far residual incidenceから selector membershipを得る forward theorem。L042 の
  product-wave membershipと L046 の reduced cofactor packetを接続した。

- `paritySafeCanonicalFarProductWaveIncidences_card_eq_farResidual`

  selector incidence set と actual far residual incidence の card equality を、canonical
  key と seat の map に対する `Finset.card_bij` で証明した。

- `paritySafeCanonicalFarResidual_card_eq_productWaveSelector_sum`

  actual far residual card を exact key-fiber sum

  ```text
  ∑ key ∈ paritySafeTripleGateFarTriples n,
    (paritySafeCanonicalFarProductWaveOffsets n key).card
  ```

  へ展開した。

## judgment

1. far product-wave quotient packet は成立したか。**Yes**。
2. reduced-cofactor と parity-safe candidate の equivalence は成立したか。**Yes**。
3. exact selector Finset は定義されたか。**Yes**。
4. selector から actual far residual incidence を復元できるか。**Yes**。
5. actual far residual incidence から selector へ戻れるか。**Yes**。
6. selected product-wave incidence card と actual far residual card は一致するか。**Yes**。
7. exact key-fiber sum は閉じたか。**Yes**。
8. canonical-minimum exclusion form は閉じたか。**No**。optional A+ の範囲として残した。

## 境界

今回の exactness は finite product-wave universe の ownership refinement である。
product key の global injectivity、harmonic / `O(n log n)` 評価、PNT・Mertens・analytic
sieve、smaller-anchor `SquareOffsetsFullyCovered`、induction・descent、global
contradiction、Legendre 予想、RH は導いていない。

形式的な帰結は、

```text
actual far residual incidence
  ↔ far product-wave hit
      + reduced cofactor quotient
      + canonical support-prime ownership
  ↔ selected product-wave incidence
  = exact sum of selector fibers
```

までで閉じる。

## 検証

Lean 4.32.2 の現行 checkoutで次を実行し、いずれも成功した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarProductWaveSelector
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規 source について `sorry`、`admit`、`axiom`、`native_decide` および末尾空白を監査した。
full repository build、commit、push、PR、CI は今回の依頼範囲に含めていない。
