# PUU-L033 — Positive-Offset First-Hit / Anchor-Seat Exclusion Audit

## 0. Status / purpose

PUU-L032 completed the square-phase first-hit comparison with

```text
Outcome B — QUADRATIC-RESTRICTION-REAL-BUT-NONUNIFORM.
```

That result is correct for the L032 statistic, but `genericFirstUnreservedOffset`
and `squareAnchorFirstUnreservedOffset` allow offset `t = 0`.

For the next short-prefix program this distinction matters: `t = 0` is the
square-anchor seat itself, while a forward shell begins strictly after the
anchor.  Before introducing successor-pair or basis-growth couplings, audit the
same finite geometry with the anchor seat excluded.

This is still provider-side.  Do **not** introduce the Legendre width `2*n`,
`SquareCell`, `SquareOffset`, or an escape theorem.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetPositiveFirstHitAudit
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFirstHitAudit
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade
docstring.

---

## 1. Positive cyclic first-hit coordinate

Define the least **strictly positive** cyclic offset from a generic label `A`
to a wheel survivor.

A convenient implementation may reuse the L032 first-hit API:

```text
H(A) = genericFirstUnreservedOffset S A

H⁺(A) =
  if H(A) = 0
  then 1 + H(A+1)
  else H(A).
```

An equivalent direct finite definition over positive offsets is acceptable.
The public semantic API is more important than the implementation choice.

Required semantics:

```text
0 < H⁺(A)
H⁺(A) ≤ M
IsPrimeBasisWheelSurvivor S ((A + H⁺(A)) % M)
```

and minimality:

```text
0 < t < H⁺(A)
  -> not IsPrimeBasisWheelSurvivor S ((A+t) % M).
```

Do not silently assume that the positive hit is `< M`; for very small survivor
sets the first positive cyclic return can be exactly `M`.

Suggested names:

```lean
genericFirstPositiveUnreservedOffset
genericFirstPositiveUnreservedOffset_pos
genericFirstPositiveUnreservedOffset_le_period
genericFirstPositiveUnreservedOffset_survivor
genericFirstPositiveUnreservedOffset_minimal
```

---

## 2. Square-anchor positive first hit

Define

```text
squareAnchorFirstPositiveUnreservedOffset S n
  = H⁺(squareAnchorWheelProjection S n).
```

Expose:

```text
squareAnchorFirstPositiveUnreservedOffset_eq_generic
squareAnchorFirstPositiveUnreservedOffset_pos
squareAnchorFirstPositiveUnreservedOffset_le_period
squareAnchorFirstPositiveUnreservedOffset_survivor
squareAnchorFirstPositiveUnreservedOffset_eq_of_samePhase
```

Keep the theorem purely in terms of finite reservation / survivor geometry.

---

## 3. Positive first-hit radii

Define the generic and square-restricted worst positive first-hit radii:

```text
genericPositiveFirstHitRadius
squarePositiveFirstHitRadius
```

with the same label sets as L032, but using `H⁺`.

Prove the subset comparison

```text
squarePositiveFirstHitRadius S hS hSne
  ≤ genericPositiveFirstHitRadius S hS hSne.
```

Also expose the pointwise square bound.

---

## 4. Information audit

The checkpoint is specifically testing whether the L032 quadratic gain survives
when the anchor seat `t=0` is removed.

Required exact regressions:

### `S = {2,3}`, `M = 6`

Target:

```text
GenericPositiveRadius = 4
SquarePositiveRadius  = 4
```

The square phase `A=1` is reachable (`n=1`) and its first **positive** survivor
occurs at offset `4`.

This contrasts with L032:

```text
GenericRadius = 3
SquareRadius  = 2
```

and shows that the previous strict improvement does not survive anchor-seat
exclusion.

### `S = {2,3,5}`, `M = 30`

Target:

```text
GenericPositiveRadius = 6
SquarePositiveRadius  = 6
```

Again the square phase `A=1` is reachable (`n=1`) and the next survivor after
`1` is `7`, giving positive offset `6`.

Use public membership/minimality APIs rather than asserting only the final
numerals.

---

## 5. Verdict

Record exactly one of the following outcomes.

### Outcome A — POSITIVE-OFFSET-QUADRATIC-GAIN-FOUND

Use only if some theorem proves a genuine uniform improvement after excluding
`t=0`.

### Outcome B — ANCHOR-SEAT-GAIN-COLLAPSES

Expected if the required `M=6` and `M=30` regressions both give equality of
square and generic positive radii.

Interpretation:

```text
square phase is a real restriction on the whole cyclic profile,
but square phase alone does not improve the worst forward positive first hit.
```

This is a successful information audit, not a failed checkpoint.

---

## 6. STOP / next-gate rule

Do not add:

- a `2*n` or square-shell width;
- Legendre consumers;
- Jacobsthal / generic maximum-gap machinery;
- prime-existence or primality claims;
- more equivalent first-hit formulas after the verdict is clear.

If Outcome B is obtained, close **square-phase-alone first-hit refinement** as
an obstruction source.  The next checkpoint should then add a genuinely
independent coupling, preferably successor-pair dynamics or basis growth, and
must use the positive-offset statistic rather than benefiting from `t=0`.

Report:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
primorial-unit-universe-positive-offset-first-hit-audit-260828.md
```
