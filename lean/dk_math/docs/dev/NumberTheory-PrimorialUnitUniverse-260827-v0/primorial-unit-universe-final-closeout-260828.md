# Primorial Unit Universe — Final Closeout Report

Date: 2026-08-28

Branch: `wip/number-theory-primorial-unit-universe-260827-v0`

Origin develop commit: `96b37e0ab8dc1431f8a17ce8cd817f9723ab864c`

Final implementation checkpoint: PUU-L036

## 1. Final result

The Primorial Unit Universe branch is complete and is closed after L036.

Final mathematical verdict:

```text
Outcome A — TIED-PAIR FRESH-PRIME OBSTRUCTION FOUND

provider obstruction seed found,
but no uniform coverage theorem was proved.
```

The branch succeeded at its intended provider-side task: it built a finite
prime-basis / wheel / square-phase language, audited several apparently promising
but information-neutral routes, and finally isolated a genuine interaction
between adjacent square anchors and fresh-prime basis growth.

It does not prove Legendre's conjecture and does not claim a uniform finite
coverage obstruction.

## 2. Research path

### L001–L010 — finite provider foundation

The branch first established finite prime-basis reservation, unit
synchronization, primorial wheel survivors, fresh-prime raw lifts, the exact
`q-1` replication law, nested projection fibers, and square-anchor / square-shell
projection dynamics.

This supplied the finite provider language independently of a Legendre consumer.

### L011–L015 — consumer bridge and anti-relabeling audit

The square-offset bridge was formalized, but the exact old-basis escape provider
was then proved equivalent to Legendre's conjecture.

This was an important negative result: the route was closed rather than being
relabelled as independent progress.

### L016–L025 — square-phase / CRT / affine geometry

Square phases were decomposed prime-by-prime into sign choices, reconstructed by
CRT, counted as finite fibers, and transported across fresh-prime two-sheet
covers. Lift indices acquired a `+a / 0 / -a` decomposition, affine midpoint,
reflection involution, and finally the normal form

```text
center C(b) = -b / M
radius R(a) =  a / M
phase pair  = C(b) ± R(a).
```

### L026–L030 — transport, monodromy, mixed-radix audit

The deleted center became canonical and movable. The square anchor acquired an
exact successor carry law. Old-period monodromy identified the dynamic plus sheet
with the Euclidean block quotient, and the fresh-prime digit became the actual raw
lift index.

L030 then proved that every admissible mixed-radix coordinate is realized.
Therefore the beautiful coordinate language itself introduced no forbidden
coordinate.

Verdict:

```text
Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET
```

The pure coordinate route was closed.

### L031–L033 — square-shifted profiles and single-phase audit

The unreserved offset profile was proved to be a cyclic translation of the fixed
wheel-survivor pattern by the square phase `n^2 mod M`.

The generic-vs-square first-hit audit showed genuine but nonuniform quadratic
restriction. After excluding the anchor seat `t=0`, the tested worst-case gain
collapsed:

```text
S={2,3}:      GenericPositiveRadius = SquarePositiveRadius = 4
S={2,3,5}:    GenericPositiveRadius = SquarePositiveRadius = 6.
```

Verdicts:

```text
L032 — QUADRATIC-RESTRICTION-REAL-BUT-NONUNIFORM
L033 — ANCHOR-SEAT-GAIN-COLLAPSES
```

The single-square positive first-hit route was closed.

### L034 — successor-pair information gain

The first genuinely stronger interaction after the negative audits was the
adjacent pair

```text
PairH_S^+(n) = min(H_S^+(n), H_S^+(n+1)).
```

Its threshold semantics measure how long both adjacent square anchors can remain
simultaneously bad.

Finite exact regressions gave strict gain:

```text
S={2,3}:      PairRadius = 1 < 4
S={2,3,5}:    PairRadius = 5 < 6.
```

Verdict:

```text
Outcome A — SUCCESSOR-PAIR-COUPLING-GAIN-FOUND
```

### L035 — fresh-prime deletion-delay law

Under fresh insertion `S -> insert q S`, the old positive first hit persists
exactly when the new prime does not delete its raw seat:

```text
H_(insert q S)^+(n) = H_S^+(n)
  iff q does not divide n^2 + H_S^+(n),

H_S^+(n) < H_(insert q S)^+(n)
  iff q divides n^2 + H_S^+(n).
```

Thus basis growth does not move first hits arbitrarily. It changes the old
minimum only through the new fresh-prime deletion channel.

The `30 -> 210` regression demonstrated both branches:

```text
n=1:   6 -> 10 because 7 divides 1^2+6
n=11:  6 ->  6 because 7 does not divide 11^2+6
PairRadius: 5 -> 7.
```

Verdict:

```text
Outcome A — FRESH-PRIME DELETION-DELAY LAW FOUND
```

### L036 — tied-pair fresh-prime obstruction

L036 combined the independent information of L034 and L035.

Suppose an adjacent pair is tied at the old positive first-hit value `h`:

```text
H_S^+(n)   = h
H_S^+(n+1) = h.
```

If inserting fresh prime `q` strictly delays the pair minimum, both old minimizing
seats must be deleted:

```text
q | n^2 + h
q | (n+1)^2 + h.
```

Subtracting gives the provider obstruction

```text
q | 2*n+1.
```

Consequently, under the tied-pair hypothesis,

```text
not (q | 2*n+1) -> pair persistence,
2*n+1 < q       -> pair persistence.
```

The untied branch remains deliberately weaker: strict delay forces deletion of
the unique old minimizing side, but no artificial simultaneous-deletion claim is
made.

Verdict:

```text
Outcome A — TIED-PAIR FRESH-PRIME OBSTRUCTION FOUND
```

This is the final information-audit checkpoint.

## 3. Why the branch is considered successful

The most important result of the branch is not a single large theorem. It is the
combination of positive and negative Lean-verified information audits:

```text
consumer-equivalent old escape                    CLOSED at L015
free mixed-radix coordinate obstruction           CLOSED at L030
single-square positive first-hit obstruction       CLOSED at L033
successor-pair coupling gain                       FOUND at L034
fresh-prime deletion-delay transition              FOUND at L035
tied-pair simultaneous-deletion obstruction        FOUND at L036
```

This prevented the project from mistaking increasingly refined coordinates for
new mathematical information, while preserving the exact structures that did
produce new constraints.

## 4. Final mathematical boundary

The branch does not establish any of the following:

- a uniform upper bound on `H_S^+(n)` across all finite prime bases;
- a uniform upper bound on successor-pair first hits;
- impossibility of complete square-shell coverage;
- existence of a prime between consecutive squares;
- Legendre's conjecture;
- an asymptotic sieve theorem;
- a PowerSwap / GN / CosmicFormula generalization of L036.

The final L036 theorem is therefore classified as an **independent provider
obstruction seed**, not as a consumer theorem.

## 5. Repository disposition

The branch should be merged into `develop` as a completed provider package.
After the merge, this roadmap and branch are historical records and should not be
extended with L037.

Any future work must start on a new branch. Possible future questions include:

- whether the L036 tied-pair obstruction persists or compounds along a longer
  fresh-prime tower;
- whether its `2*n+1` factor admits a natural unit-relative / GN reformulation;
- whether a genuinely independent provider theorem derived from this seed can
  later be read by the Legendre consumer.

Those are new research projects, not unfinished work of this branch.

## 6. Closeout

```text
PUU-L001 ... PUU-L036 : COMPLETE
branch information audit : COMPLETE
final provider verdict    : Outcome A obstruction seed
uniform coverage theorem  : NOT OBTAINED
Legendre conclusion       : NOT CLAIMED
branch                     : CLOSED
```
