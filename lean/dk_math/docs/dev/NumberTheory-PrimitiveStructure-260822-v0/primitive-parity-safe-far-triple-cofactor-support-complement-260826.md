# PRIM-L045 report — far-triple cofactor prime-support complement

## Outcome

**Outcome A+ — EXACT COFACTOR-SUPPORT COMPLEMENT / LOCAL OWNERSHIP**

L044の単一returned-prime viewを、cofactor全体の有限prime support
`Nat.primeFactors t`へ拡張した。固定したseat `r`、canonical prime `p`、far residual pair
`(q,s)`に対して、active supportは

```text
paritySafeActiveSupport n r
  = insert p (insert q (insert s (Nat.primeFactors t)))
```

とexactに分解される。no-depth branchでは、三方向がcofactor supportに入らないことを
使い、support cardinalityとerase complementを閉じた。さらにseatとcanonical primeを
固定すれば、同じcofactor prime supportを持つcanonically ordered residual pairは同一と
なるlocal injectivityまで証明した。

これはseat-local ownershipであり、cofactor value、単一prime、seatを忘れたcofactor
supportをglobal charge keyとは解釈しない。

## 実装

追加 module:

```text
DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport
```

facade `DkMath.NumberTheory.Legendre` からimportした。

主なtheorem surface:

- `paritySafeFarTripleCofactorPrimeSupport`

  `Nat.primeFactors (paritySafeFarTripleCofactor n r q s)` を定義。

- `mem_paritySafeFarTripleCofactorPrimeSupport`

  L044の `0 < t` を用いて、support membershipを
  `Nat.Prime u ∧ u ∣ t` とcharacterizeした。

- `paritySafeFarTripleCofactorPrimeSupport_subset_halfScale`
  / `paritySafeFarTripleCofactorPrimeSupport_subset_activeSupport`

  cofactorの全prime supportをhalf-scale active worldと同一candidate supportへ戻す。

- `paritySafeActiveSupport_eq_triple_insert_cofactorPrimeSupport`

  active supportがselected tripleと全cofactor prime supportのinsertで完全に分解される。
  逆向きは `u ∣ p*q*s*t` のprime divisor分解で証明した。

- `paritySafeActiveSupport_card_eq_three_add_cofactorPrimeSupport_card`

  `p^2`, `q^2`, `s^2` がいずれも `n^2+r` を割らない場合、

  ```text
  (paritySafeActiveSupport n r).card =
    3 + (paritySafeFarTripleCofactorPrimeSupport n r q s).card
  ```

  を証明する。

- `paritySafeFarTripleCofactorPrimeSupport_eq_activeSupport_erase_three`

  no-depth branchで、cofactor prime supportがactive supportから `p,q,s` をeraseした
  complementと等しいことを証明する。

- `paritySafeFarTripleCofactorPrimeSupport_local_injective`

  seat `r`、canonical prime、第一のno-depth far pairを固定し、同じcofactor prime support
  を持つ別のcanonically ordered pairが同一pairであることを証明する。したがって
  `support`をseat込みのlocal ownershipへ使える。global injectivityは主張しない。

## 判定と境界

1. 全cofactor prime supportのhalf-scale active/support帰還: **Yes**。
2. active supportのexact triple-plus-cofactor-support decomposition: **Yes**。
3. no-depth cardinal identity: **Yes**。
4. exact erase-complement identity: **Yes**。
5. fixed seat / canonical prime下のlocal injectivity: **Yes — Outcome A+**。
6. `(62,41)/(62,83)` false beamとの整合性: **Yes**。L044のarithmetic beamは維持し、
   seatを忘れたglobal support-key injectivityを導入していない。

local injectivity theoremは第一のpair側のno-depth条件で十分に証明できる形にした。
第二pair側のno-depthを仮定しなくても、第一pairがsupport complementを決め、第二pairの
canonical orderingが復元を強制するためである。

以下は引き続き非目標である。

- cofactor value / returned prime / seatを忘れたprime supportのglobal injectivity
- generic fourth/fifth/k-direction hypergraph
- smaller-anchor `SquareOffsetsFullyCovered t`
- induction、infinite descent、residual massのglobal cardinal contradiction
- PNT、analytic sieve、RH、Legendre予想

## 検証

Lean 4.32.2の現行checkoutで次を実行する。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeFarTripleCofactorSupport
lake build DkMath.NumberTheory.Legendre
git diff --check
```

新規sourceの `sorry`、`admit`、`axiom`、`native_decide` と末尾空白を監査する。full
repository build、commit、push、PR、CIは今回の依頼範囲外である。
