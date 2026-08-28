# PRIM-L058 — Exact Depth Fiber / Local Residual-Pair Capacity

## Status

実装済み。PRIM-L057 の paid/unpaid depth ledger を受け、exact-depth の
同一 seat 内 fiber multiplicity を、既存の canonical erased co-support の
unordered residual-pair capacityへ transportした。

検証対象は有限算術の local capacity であり、fiber singleton、一般の
`DepthFiberExcess = 0`、fifth direction、descent、analytic estimate、
Legendre conjecture、RH は主張しない。

## Implemented API

主 module は
`DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberResidualCapacity`。

- `paritySafeRechargeExactKeyOfPair` と packet で exact dual-base pair から
  surviving recharge key を canonical choice する。
- L056 の seat/next-seat return identity を public wrapper として公開した。
- `paritySafeCanonicalResidualPairsAtSeat` を定義し、covered seat でその
  card が
  `Nat.choose ((paritySafeActiveSupport n r).card - 1) 2` に一致することを閉じた。
- exact-depth fiber pair を local residual pair に送り、同一 seat 上で
  `Set.InjOn` を証明した。
- したがって
  `DepthPairsAtSeat.card ≤ choose (ActiveSupport.card - 1) 2`、および collision
  seat の `ActiveSupport.card ≥ 4` を得た。
- collision seat ごとの
  `choose ((ActiveSupport.card - 1)) 2 - 1` を
  `paritySafeRechargeExactDepthResidualPairCapacityExcess` として定義し、
  L057 の `DepthFiberExcess` 以下であることを証明した。
- L057 の residual-mass / prime-pair-overlap upper ledger に、この support-only
  residual capacity を consumer として追加した。
- L057 の n=58 collision witness から
  `4 ≤ (paritySafeActiveSupport 58 101).card` を固定した。

## Proof boundary

reverse key の uniqueness は新しい一般 factorization API を導入せず、
`Classical.choose` の packet と、canonical ownership による first-prime
一致で fixed-seat injection 内に閉じている。residual pair は既存の
L047/L048 selector equivalence と L040/L041 quotient-support packet から
取得した。

今回の capacity は collision seat の multiplicity を support の pair 数で
支払うものであり、collision seat 数だけを support excess で支払う主張や、
fiber excess 全体の無条件消滅を意味しない。

## Validation

`lake env lean`

- `ParitySafeRechargeDepthSeatFiber.lean`
- `ParitySafeRechargeDepthFiberExcess.lean`
- `ParitySafeRechargeDepthFiberResidualCapacity.lean`

を個別に実行し成功した。facade の import を追加後、
`DkMath.NumberTheory.Legendre` も focused build で確認する。

なお build 起動時には既存環境の
`/opt/wonderful/bin/wf-env: Permission denied` が表示されるが、Lean の
終了ステータスは成功している。
