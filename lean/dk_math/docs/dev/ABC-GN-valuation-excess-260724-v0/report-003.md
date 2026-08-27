# Report 003: exponent-exception / non-exceptional GN layer

## Outcome

`ABC-GN-004` is complete (Outcome A).

The new module is:

```text
DkMath/ABC/GNExceptionalSplit.lean
```

It reuses:

```text
DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp
Triple.padic_powerDiff_eq_GN_of_not_dvd_boundary
```

and exports:

```text
Triple.gcd_boundary_GN_dvd_exp
Triple.dvd_exp_of_dvd_boundary_of_dvd_GN
Triple.not_dvd_boundary_of_not_dvd_exp_of_dvd_GN
Triple.padic_powerDiff_eq_GN_of_not_dvd_exp_of_dvd_GN
Triple.coprime_boundary_GN_of_coprime_exp
```

The gcd spine assumes `1 ≤ n` and `0 < T.a`.  The ABC equation gives
`T.b < T.c`, while coprimality of `T.c` and `T.b` follows from `T.hsum` and
`T.hcop`.  A common divisor of `T.a` and `GN n T.a T.b` therefore divides
`n`.  Contraposition gives boundary separation when `q ∤ n`.

The valuation concentration theorem assumes `2 ≤ n`, positive `T.a,T.b`,
`Nat.Prime q`, `q ∤ n`, and `q ∣ GN n T.a T.b`.  Separation supplies
`q ∤ T.a`, after which the checkpoint-002 valuation theorem applies.

`UniqueFactorizationGN` was not imported.  The thinner `Gcd.GN` API was
sufficient.  No aggregator was changed.

## Verification

```text
lake build DkMath.ABC.GNExceptionalSplit
Build completed successfully (8279 jobs).
```

No new `axiom`, `sorry`, or `native_decide` was added.  No FLT7 module or
shared aggregator was changed.

By later explicit User authorization, work continued beyond this checkpoint.

