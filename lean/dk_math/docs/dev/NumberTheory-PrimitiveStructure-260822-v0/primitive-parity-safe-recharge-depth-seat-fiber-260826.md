# PRIM-L056 実装報告

## Outcome

Outcome A と判定する。L055 の exact depth branch を、既存 L018 の
coprime prime-square seat ledger に戻し、pair と seat の multiplicity を分離した。
n=58 は要求された算術 false-beam を確認したが、実際の depth-universe membership
までは主張していないため A+ とはしない。

## 実装

追加モジュールは
`DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber`。

- `paritySafeRechargeExactSeat` を exact shell point からの `n^2` offset として定義。
- `paritySafeRechargeExactPair_seat_packet` で、exact pair の seat が
  `squareAnchorOddPointCoprimeOffsets n` に属し、shell-point equation を満たすことを証明。
- `paritySafeRechargeExactDepthPair_primeSquare_seat` で、depth pair が
  `squareAnchorNondivisorPrimes n` のいずれかの
  `squareAnchorCoprimePrimeSquareOffsets` fiber に戻ることを証明。
- `paritySafeRechargeExactDepthSeats` は image として distinct seat を定義し、
  `paritySafeRechargeExactDepthSeats_card_le_primeSquareDepthBudget` で L018 budget 以下を証明。
- `paritySafeRechargeExactDepthPairsAtSeat` と
  `paritySafeRechargeExactDepthPairs_card_eq_sum_seat_fibers` により、pair card は
  occupied seat ごとの fiber card の和になることを証明。fiber の injectivity は仮定しない。
- `paritySafeResidualPairMass_eq_near_add_terminal_add_depth_add_fourth` で、
  L055 split を near/terminal/depth/fourth の global residual ledger に接続。
- `paritySafeRechargeDepthSeat_false_beam_arithmetic` で
  `58^2 + 101 = 3^2*5*7*11`、
  `(3,5,11), t=21` と `(3,7,11), t=15` の双方が product `3465` を与え、
  同一 seat arithmetic へ向かうことを固定。

## 境界

今回証明していないものは以下の通り。

- exact depth pair card 自体を L018 budget 以下とする主張
- seat fiber の card ≤ 1、witness prime の uniqueness、canonical depth prime
- n=58 の false-beam が実際に selected depth universe に属すること
- fifth direction、generic hypergraph/valuation、smaller-anchor descent/induction
- terminal/near/fourth の個別評価、global contradiction、Legendre/RH

## Docstring と検証

新規 module docstring と公開定義・主要定理の docstring に、seat/pair の区別、
finite ledger の意味、非 injective boundary を記載した。

実行した検証:

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber
lake build DkMath.NumberTheory.Legendre
git diff --check
```

commit、push、CI は依頼範囲外のため実施していない。
