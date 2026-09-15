# review-003 — GNIP-003 Legendre open unit-gnomon bridge

## Verdict

**APPROVED — Outcome A.**

GNIP-003 cleanly identifies the existing Legendre square shell with the open interior of the neutral unit gnomon, without changing the original `SquareCell`, `SquareOffset`, or support semantics.

## Verified production bridge

The new module proves the exact equivalences

```text
SquareOffset n r
  ↔ 1 ≤ r ∧ r < DkMath.Gnomon.oddGnomon n

squareOffsets n
  = Finset.Ico 1 (DkMath.Gnomon.oddGnomon n)
```

and preserves the already-established cardinality

```text
card = 2*n.
```

The excluded endpoint is correctly fixed by

```text
n^2 + oddGnomon n = (n+1)^2.
```

Thus the ordinary Legendre open square interval is exactly the open interior of one unit square-gnomon layer.

## Cosmic consistency

The bridge also uses the approved GNIP-001 orientation

```text
oddGnomon n = GTail 2 1 1 n
```

so the Legendre offset interval is equivalently the open degree-two unit Cosmic shell.

## Frontier preservation

The new theorems

```text
legendreConjecture_iff_open_oddGnomon_prime
squareAnchoredSupportEscape_iff_open_oddGnomon
```

are exact restatements only.  They do not prove the provider, full-cover failure, or prime existence.  This is the correct scope.

## Regression audit

The `n=30` regressions are consistent:

```text
oddGnomon 30 = 61
squareOffsets 30 = Ico 1 61
card = 60
30^2 + 61 = 31^2
```

No primality claim is inferred from `61`.

## Validation assessment

Reported focused builds cover the new bridge, the Legendre aggregate, and the neutral Gnomon facade.  The report records no new warning, `sorry`, `admit`, or `axiom` in changed source.

## Next checkpoint

GNIP-004 should not repeat the 2026-08-25 square-shell transport audit, which already showed that the tautological point rewrite

```text
(n+1)^2 + r = n^2 + (2*n+1+r)
```

does not map the successor shell back into the old `squareOffsets n` window.

The new opportunity is the now-visible balance between:

```text
shell cardinality growth: 2*n -> 2*n+2  (+2)
```

and, when `n+1` is prime, the existing successor theorem that the new threshold prime covers exactly two successor offsets.

GNIP-004 should decide whether this is merely a cardinality coincidence or the boundary of a genuine support-transport / support-firewall law.  In particular, test the exact common-divisor consequence of

```text
(n+1)^2 + r = (n^2 + r) + oddGnomon n.
```

A prime direction present at the same offset before and after the anchor move must divide the unit gnomon increment.  This candidate should be kernel-checked before any broader inversion/projection claim is made.
