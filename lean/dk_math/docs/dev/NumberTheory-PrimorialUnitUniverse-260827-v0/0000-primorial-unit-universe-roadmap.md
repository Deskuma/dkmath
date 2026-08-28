# NumberTheory Primorial Unit Universe — CLOSED Roadmap

> Final revision: 2026-08-28 after PUU-L036
>
> Branch: `wip/number-theory-primorial-unit-universe-260827-v0`
>
> Status: **CLOSED — provider information audit complete**

## 0. Final branch verdict

This branch was opened after closing the Legendre finite-support / residual-ledger
route. Its purpose was not to rename Legendre's conjecture. It was to build an
independent finite arithmetic provider, repeatedly audit its information content,
and stop whenever a route reduced to coordinate bookkeeping or a consumer-equivalent
statement.

The branch closes with the following final verdict:

```text
Outcome A — TIED-PAIR FRESH-PRIME OBSTRUCTION FOUND

provider obstruction seed found,
but no uniform coverage theorem was proved.
```

The final provider implication is:

```text
tied adjacent positive first hits
+ strict delay after inserting fresh prime q
  -> q deletes both old minimizing raw seats
  -> q | ((n+1)^2 + h) - (n^2 + h)
  -> q | (2*n+1).
```

Hence, under the tied-pair hypothesis,

```text
not (q | 2*n+1) -> pair persistence,
2*n+1 < q       -> pair persistence.
```

This is independent provider information. It is not a proof of a uniform
positive-offset bound, not a finite coverage obstruction for all bases, and not
a proof of Legendre's conjecture.

---

## 1. Permanent anti-relabeling gate — L011–L015

L011–L014 connected square offsets to the primorial wheel. L015 proved that the
exact successor old-escape provider is equivalent to Legendre's conjecture.

Permanent rule:

- do not rename a square-shell escape statement and call it an independent provider;
- Legendre remains a consumer / audit target;
- consumer re-entry requires a provider theorem that is already proved without
  importing the Legendre layer.

---

## 2. Completed architecture

### Phase A — finite reservation / unit synchronization — COMPLETE

- L001 finite reservation escape;
- L002 unit coordinate refinement;
- L003 common lattice;
- L004 unit-intersection classification;
- L005 finite-prime synchronization.

### Phase B — finite wheel tower — COMPLETE

- L006 wheel survivors;
- L007 fresh-prime raw lifts and unique deletion;
- L008 exact `q-1` survivor replication;
- L009 nested projection fibers;
- L010 square-anchor / square-shell projection dynamics.

### Phase C — consumer bridge / anti-relabeling audit — COMPLETE / CLOSED

- L011–L014 square-offset / threshold bridge;
- L015 exact old-escape equivalence audit.

### Phase D — square-phase / CRT / affine geometry — COMPLETE

- L016 square-phase symmetry;
- L017 prime-sign dichotomy;
- L018 CRT synthesis;
- L019 square-phase fiber cardinality;
- L020 fresh-prime two-sheet phase cover;
- L021 phase survivor subcover;
- L022 `+a / 0 / -a` lift-index trichotomy;
- L023 affine midpoint;
- L024 reflection involution;
- L025 constant-radius affine normal form.

Static normal form:

```text
center C(b) = -b / M
radius R(a) =  a / M
phase pair  = C(b) ± R(a).
```

### Phase E — transport / mixed-radix coordinates — COMPLETE

- L026 canonical deleted-center transport;
- L027 successor carry law for the moving square anchor;
- L028 old-period monodromy and enlarged-period closure;
- L029 fresh-prime mixed-radix lift digit;
- L030 information audit.

L030 verdict:

```text
Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET
```

Every admissible mixed-radix coordinate is realized. Pure coordinate refinement
was therefore closed as an obstruction source.

### Phase F1 — square-shifted offset profiles — COMPLETE

- L031 square-shifted survivor profile and successor translation;
- L032 generic-vs-square first-hit audit;
- L033 positive-offset / anchor-seat exclusion audit.

L032 verdict:

```text
Outcome B — QUADRATIC-RESTRICTION-REAL-BUT-NONUNIFORM
```

L033 verdict:

```text
Outcome B — ANCHOR-SEAT-GAIN-COLLAPSES
```

Square phase is real information, but square phase alone did not supply a
strictly-forward uniform first-hit improvement. The single-phase positive route
was closed.

### Phase F2 — successor-pair coupling — COMPLETE

L034 introduced

```text
PairH_S^+(n) = min(H_S^+(n), H_S^+(n+1))
```

with exact simultaneous-badness threshold semantics.

Finite regressions showed genuine gain:

```text
S={2,3}:      PairRadius = 1 < 4 = SquarePositiveRadius
S={2,3,5}:    PairRadius = 5 < 6 = SquarePositiveRadius.
```

Verdict:

```text
Outcome A — SUCCESSOR-PAIR-COUPLING-GAIN-FOUND
```

### Phase F3 — fresh-prime basis-growth transport — COMPLETE

L035 proved the exact deletion-delay law:

```text
H_(insert q S)^+(n) = H_S^+(n)
  iff q does not divide n^2 + H_S^+(n),

H_S^+(n) < H_(insert q S)^+(n)
  iff q divides n^2 + H_S^+(n).
```

It also proved pointwise pair monotonicity and pair-radius monotonicity under
fresh basis insertion.

The `30 -> 210` regression separates deletion and persistence explicitly.

Verdict:

```text
Outcome A — FRESH-PRIME DELETION-DELAY LAW FOUND
```

### Phase F4 — pair × basis-growth obstruction — COMPLETE / FINAL

L036 classified persistence / strict delay using the old pair minimizers.
For a tied pair with common old first hit `h`, strict pair delay after inserting
fresh prime `q` forces simultaneous deletion:

```text
q | n^2 + h
q | (n+1)^2 + h.
```

Subtracting the two seats gives

```text
q | 2*n+1.
```

Therefore `q ∤ 2*n+1`, and in particular `2*n+1 < q`, forces persistence of the
tied pair. The untied case is deliberately kept at the weaker one-minimizer
boundary supplied by the actual theorem.

Verdict:

```text
Outcome A — TIED-PAIR FRESH-PRIME OBSTRUCTION FOUND
```

This is the final information-audit checkpoint of the branch.

---

## 3. What the branch proved, and what it did not

Proved / established:

- exact finite wheel and fresh-prime deletion geometry;
- complete square-phase / CRT / affine coordinate language;
- exact moving-anchor and mixed-radix transport;
- explicit negative information audits that close nonproductive coordinate and
  single-phase routes;
- a genuine successor-pair information gain;
- an exact fresh-prime first-hit deletion-delay law;
- the tied-pair fresh-prime divisibility obstruction `q | 2*n+1`.

Not proved:

- a basis-independent uniform bound for positive first hits;
- a universal finite coverage obstruction;
- a square-shell escape theorem;
- Legendre's conjecture;
- a PowerSwap / GN / CosmicFormula generalization of the final obstruction.

Those are not unfinished obligations of this branch. They are separate future
research questions.

---

## 4. Closure rule

The branch is closed after L036.

Do not add L037, longer anchor windows, consumer shell widths, or further
coordinate reformulations here. Any attempt to use the L036 obstruction seed in
Legendre, Unit Universe, PowerSwap, GN, or a broader tower theorem must start on a
new branch and preserve the anti-relabeling gate above.

Final completion sequence:

```text
1. finite reservation / unit synchronization                 DONE
2. exact primorial wheel tower                               DONE
3. consumer bridge / anti-relabeling audit                   DONE / CLOSED
4. square-phase / CRT / affine geometry                      DONE
5. representative and moving-anchor transport                DONE
6. monodromy / mixed-radix coordinates                       DONE
7. mixed-radix information audit                             DONE — Outcome B
8. pure coordinate route                                     CLOSED
9. square-shifted offset profile                             DONE
10. square-phase first-hit audit                              DONE — Outcome B
11. positive-offset first-hit audit                           DONE — Outcome B
12. single-phase positive route                               CLOSED
13. successor-pair coupling                                   DONE — Outcome A
14. fresh-prime deletion-delay transport                      DONE — Outcome A
15. tied-pair fresh-prime obstruction                         DONE — Outcome A
16. branch                                                    CLOSED
```

Central principle retained:

```text
Do not search for a prime directly.
Build an independent finite structure, audit whether it really excludes anything,
and only then let a consumer read the consequence.
```
