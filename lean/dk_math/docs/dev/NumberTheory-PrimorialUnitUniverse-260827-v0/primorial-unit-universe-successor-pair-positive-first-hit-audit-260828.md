# PUU-L034 Successor-Pair Positive First-Hit / Adjacent Bad-Phase Isolation Audit

## Scope

This checkpoint adds the successor coupling required after the L033
anchor-seat exclusion audit.  It remains provider-side finite arithmetic and
does not introduce a `2*n` shell width, `SquareCell`, `SquareOffset`, an
escape theorem, primality claims, Jacobsthal machinery, or Legendre consumers.

## Pair coordinate

The module
`DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairAudit`
defines
`squareAnchorSuccessorPairPositiveFirstHit S n hS hSne` as

```text
min (H⁺(n)) (H⁺(n+1))
```

where `H⁺` is the L033 positive first-hit coordinate.  The public API proves
strict positivity, bounds by the left and right first hits, and the one-period
bound.  At the pair distance, one of the two consecutive anchors reaches a
wheel survivor, exposed as a left/right disjunction.

## Threshold semantics

The following public equivalences identify the pair coordinate with adjacent
simultaneous badness:

```text
k ≤ PairH⁺(n)
  ↔ k ≤ H⁺(n) ∧ k ≤ H⁺(n+1)

PairH⁺(n) < k
  ↔ H⁺(n) < k ∨ H⁺(n+1) < k
```

Thus the pair radius measures failure of both adjacent anchors to remain bad
at one common threshold; it is not a graph or longer-window abstraction.

## Pair radius and periodicity

`squareSuccessorPairPositiveFirstHitRadius` is the finite supremum over
`n < M`.  It is proved bounded by
`squarePositiveFirstHitRadius`.  The pair coordinate is also invariant under
`n ↦ n + M`, using the existing same-square-phase period theorem and the
positive first-hit same-phase API.

## Exact regressions

The exported regression theorems use the public positive-profile membership,
survivor, minimality, and finite-supremum APIs.

| basis `S` | square positive radius | successor-pair radius | witness |
|---|---:|---:|---|
| `{2,3}` | `4` | `1` | every adjacent pair has a first hit at most `1` |
| `{2,3,5}` | `6` | `5` | `n=11`: `H⁺(11)=6`, `H⁺(12)=5`, so pair value `5` |

For the second row, the square projections are explicitly proved as
`11^2 mod 30 = 1` and `12^2 mod 30 = 24`.

## Verdict

**Outcome A — SUCCESSOR-PAIR-COUPLING-GAIN-FOUND**

**FINITE STRICT GAIN, NO UNIFORM COVERAGE BOUND YET.**

L033 showed that square phase alone did not improve the tested positive
first-hit radius.  L034 adds genuinely new information through the exact
successor relation between consecutive square phases: the two required
finite tests strictly reduce the worst statistic, `1 < 4` and `5 < 6`.

This does not prove that the reduction is uniformly strict for every finite
prime basis, and it is not an escape or coverage theorem.  Longer windows,
shell widths, primality, asymptotic claims, and downstream consumers remain
outside this checkpoint.

## Validation

Validated with:

```text
lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetSuccessorPairAudit
```

The target completed successfully, including its imported dependency graph.
The new module was exported through
`DkMath.NumberTheory.PrimorialUniverse`, whose module docstring records the
pair semantics, period bound, and finite-only information-gain boundary.
