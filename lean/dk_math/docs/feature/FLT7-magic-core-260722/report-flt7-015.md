# FLT7-015 audit report

## Outcome

Outcome C.

The proposed Part A theorem
`prime_dvd_two_routingCells_implies_eq` is false for the stated input type
`CoprimeTripleRouting`. Consequently the requested stable prime-address packet
cannot be constructed from that theorem, and the exact prime-power development
must not be built on it.

FLT7-014 is preserved unchanged. No prime-power obstruction, recursive
closure, descent, or FLT7 conclusion is claimed.

## Explicit counterexample

Take the nine routing cells to be

```text
       b1  b2  b3
a1      2   1   1
a2      1   2   1
a3      1   1   1
```

and set

```text
a1 = 2, a2 = 2, a3 = 1,
b1 = 2, b2 = 2, b3 = 1.
```

All six product equations required by `CoprimeTripleRouting` hold:

```text
a1 = c11*c12*c13 = 2,
a2 = c21*c22*c23 = 2,
a3 = c31*c32*c33 = 1,
b1 = c11*c21*c31 = 2,
b2 = c12*c22*c32 = 2,
b3 = c13*c23*c33 = 1.
```

Every pair within each row and within each column is coprime, since every such
pair contains at most one entry equal to `2`. Thus this is valid data for
`CoprimeTripleRouting 2 2 1 2 2 1`.

However the prime `q = 2` divides both

```text
routingCell r .y .sevenV     = c11 = 2,
routingCell r .z .leftCubic  = c22 = 2.
```

The two addresses have different rows and different columns. Therefore the
claimed conclusion

```text
row1 = row2 and column1 = column2
```

is false.

## Why the current structure is insufficient

The fields `row1_coprime`, `row2_coprime`, and `row3_coprime` exclude repeated
prime support inside one row. The three `col*_coprime` fields do the same
inside one column. They impose no relation between diagonally separated cells
such as `c11` and `c22`.

The actual `AwayCubicRoutingPacket` has stronger provenance outside the routing
structure:

- its endpoint factors `y`, `z`, and `y+z` are pairwise coprime;
- its root factors `7*vPart`, `leftPart`, and `rightPart` are pairwise coprime.

Those outer hypotheses would exclude the displayed counterexample. They are
not assumptions of the required Part A theorem, so they cannot be silently
used to prove its generic statement.

## Downstream impact

The requested `RoutingPrimeAddress.unique` field depends directly on the false
generic theorem. Parts B-J then use that address as provenance for exact cell,
row, and column depths. Implementing those layers without first correcting the
address theorem would certify an invalid abstraction.

No conclusion can therefore be drawn at this checkpoint about whether all
finite single-cell q-adic layers are soluble. The audit stops before that
question: the proposed address foundation is false as stated.

## Required repair boundary

A corrected checkpoint should choose one of these honest surfaces:

1. add pairwise-coprimality hypotheses for `a1,a2,a3` and `b1,b2,b3` to the
   generic address theorem; or
2. state prime-address uniqueness only for `AwayCubicRoutingPacket`, deriving
   the six outer coprimality facts from its endpoint and root triples; or
3. strengthen `CoprimeTripleRouting` itself with outer row-factor and
   column-factor coprimality, if every intended consumer genuinely requires
   that invariant.

Option 2 is the narrowest repair for FLT7. Once that corrected theorem is
accepted, a new checkpoint can resume exact valuation isolation and the
`ZMod (q^e)` solubility audit. The simultaneous signed global-gluing problem
must remain later work; it cannot yet be designated FLT7-016 because the
prime-power audit has not been validly completed.

## Verification status

The counterexample is a direct evaluation of the fields of
`CoprimeTripleRouting` and `routingCell`. No project Lean source, facade, or
test file was changed. The worktree change for this checkpoint is this report
only.
