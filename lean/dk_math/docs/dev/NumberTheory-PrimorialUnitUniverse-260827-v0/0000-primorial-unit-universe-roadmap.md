# NumberTheory Primorial Unit Universe — Roadmap

> Revised: 2026-08-28 after PUU-L025
>
> Branch: `wip/number-theory-primorial-unit-universe-260827-v0`
>
> This is the current route map.  The branch purpose is unchanged, but the
> implementation has produced a much richer provider-side square-phase geometry
> than the initial checkpoint sketch anticipated.

## 0. Branch purpose

This branch was opened after closing the Legendre finite-support / residual-ledger
route on `wip/number-theory-primitive-structure-260822-v2`.

The purpose is **not** to rename Legendre's conjecture and prove the renamed
statement.  The purpose is to formalize a higher-level finite arithmetic provider
whose consequences can later be read by consumers.

The intended hierarchy is:

```text
finite prime basis / reservation
        ↓
unit-relative coordinates / synchronization
        ↓
primorial finite-wheel tower
        ↓
square-anchor phase geometry
        ↓
transport under representative / anchor / basis motion
        ↓
independent finite coverage obstruction, if one exists
        ↓
consumer re-entry
        ↓
possible Unit Universe / PowerSwap / GN generalization
```

Legendre is therefore a **consumer / audit target**, not the foundational layer.

---

## 1. Original mathematical starting point

For a finite prime basis `S`, let

```text
M(S) := ∏ p ∈ S, p.
```

A natural seat `n` is reserved by `S` when

```text
∃ p ∈ S, p ∣ n.
```

Every basis prime divides `M(S)`, hence `M(S)+1` is not reserved by any member of
`S`.  A prime divisor of `M(S)+1` is therefore outside `S`.

```text
finite basis S
    ↓
period M(S)
    ↓
Euclid escape M(S)+1
    ↓
new prime divisor q ∉ S
```

This is a global finite escape principle.  It does **not** by itself place a prime
inside a prescribed short interval such as a square cell.

The branch seeks the missing finite structure between these two scales.

---

## 2. Permanent correction from PUU-L011–L015

The first roadmap expected a Legendre-specific route roughly of the form

```text
square-hole
  → future reservation closure
  → no new primitive seat
  → contradiction with finite-basis escape.
```

PUU-L011–L014 built the exact square-offset / wheel bridge and successor-threshold
classification.  PUU-L015 then performed the anti-relabeling audit.

The decisive result is

```text
SuccessorOldEscapeProvider ↔ LegendreConjecture.
```

Therefore the strategy

```text
"prove the branch-exact old escape criterion"
```

is **not** an independent provider route.  It is already the consumer statement in
new vocabulary.

PUU-L015 is now a permanent gate:

- do not continue by renaming square-shell escape;
- do not treat a lower bound for the exact old-escape criterion as independent
  information unless it comes from a separately proved provider invariant;
- any future Legendre re-entry must occur only after a theorem has been stated and
  proved entirely inside provider geometry.

---

## 3. PowerSwap / GN status

The initial sketch placed a PowerSwap prime-support connection early in the branch.
The actual implementation instead needed a clean finite synchronization and wheel
layer first.

Actual early order:

```text
L001 finite reservation escape
L002 unit-coordinate refinement
L003 common lattice
L004 unit-intersection classification
L005 finite-prime synchronization
```

**PowerSwap is deferred, not failed and not implemented here yet.**

Preferred future order:

```text
finite provider invariant
    ↓
transport / scaling theorem
    ↓
PowerSwap / GN / CosmicFormula connection, if structurally natural.
```

---

## 4. Implemented architecture

### Phase A — finite reservation and unit synchronization — COMPLETE

#### PUU-L001 — Finite Reservation Escape

- finite prime basis;
- product period;
- `M+1` escape;
- prime outside the finite basis.

#### PUU-L002 — Unit Coordinate Refinement

- common absolute point under different positive units;
- synchronized integer refinement;
- preservation of old coordinate factors.

#### PUU-L003 — Common Lattice

- exact common-lattice parameterization;
- canonical common-point fiber.

#### PUU-L004 — Unit Intersection Classification

- exact intersection / commensurability classification in the implemented setting;
- synchronized vs. unsynchronized coordinate worlds.

#### PUU-L005 — Finite Prime Synchronization

- finite prime scales share the product synchronization period;
- basis-prime reservation is periodic on that lattice.

---

### Phase B — finite wheel tower — COMPLETE

#### PUU-L006 — Wheel Survivor / Reflection

For one period `0 < r < M(S)`, a survivor is a seat not divisible by any basis
prime.  Reduced-residue / coprime equivalence and

```text
r ↔ M(S)-r
```

reflection are formalized.

#### PUU-L007 — Fresh-Prime Lift / Unique Deletion

For fresh prime `q ∉ S`, every old survivor `r` has raw lifts

```text
r + j*M(S),    0 ≤ j < q,
```

and exactly one is divisible by `q`.

#### PUU-L008 — Wheel Replication

The exact global growth law is

```text
|WheelSurvivors(insert q S)|
  = (q-1) * |WheelSurvivors(S)|.
```

#### PUU-L009 — Nested Wheel Projection

The enlarged wheel projects canonically to the old wheel; every old survivor has
an exact fiber of size `q-1`.

#### PUU-L010 — Square-Anchor Orbit

Square anchors and fixed shell offsets are projected modulo the same period.
Reservation is characterized by projected coordinates, and fresh-prime insertion
is coherent with old projection.

PUU-L010 is the provider-side anchor-dynamics entry point to which the branch must
return after the static phase geometry is normalized.

---

### Phase C — Legendre consumer bridge — COMPLETE / CLOSED

#### PUU-L011 — Legendre / Primorial Wheel Bridge

Square-offset coverage is identified with finite-basis reservation.  Within the
bounded square shell, projected survivor is equivalent to the corresponding prime
witness.

#### PUU-L012 — Successor Square-Shell Transition

The successor basis is decomposed into the old basis and a possible threshold
prime; the threshold has only its bounded shell seats.

#### PUU-L013 — Old-Basis Escape / Deletion Capacity

Old-basis escapes and actual projected escapes are compared.

#### PUU-L014 — Twin-Threshold Exception

The second threshold seat is an old-basis escape exactly in the twin-prime case.

#### PUU-L015 — Old-Escape Frontier Equivalence Audit

The branch-exact global provider candidate is shown equivalent to Legendre.

**Status:** consumer reduction limit reached.  This route is closed unless a new,
independently proved provider invariant becomes available.

---

### Phase D — square-anchor phase / CRT / affine provider geometry — COMPLETE

PUU-L016 restarted from the provider layer after the L015 audit.  L016–L025 do not
import the Legendre consumer layer.

#### PUU-L016 — Square-Anchor Phase Symmetry

```text
a² ≡ b² (mod M(S))
```

is promoted to a phase relation.  Same phase preserves every shell-offset
projection and the complete finite-basis reservation pattern.

#### PUU-L017 — Local Prime Sign Dichotomy

For each basis prime `p`:

```text
a² ≡ b² (mod p)
  ↔ a ≡ +b or a ≡ -b (mod p).
```

#### PUU-L018 — Mixed-Sign CRT Synthesis

Local sign profiles and global square phase are equivalent.  Arbitrary mixed signs
are realized by CRT.

#### PUU-L019 — Coprime Phase-Fiber Cardinality

For `Nat.Coprime a M(S)`:

```text
|PhaseFiber_S(a)| = 2 ^ |S.erase 2|.
```

The phase fiber is a Boolean cube of odd-prime sign choices.

#### PUU-L020 — Fresh-Prime Phase-Fiber Cover

```text
fresh odd q : ×2
fresh q = 2 : ×1.
```

Every old phase representative has exactly two enlarged phase lifts for fresh odd
`q`.

#### PUU-L021 — Phase / Survivor Subcover

On a fresh-prime projection fiber:

```text
phase cover : 2 seats
wheel cover : q-1 seats.
```

For `q=3` they are equal; for `3<q` the phase cover is proper.

#### PUU-L022 — Fresh-Prime Lift-Index Trichotomy

```text
q raw indices
  = 1 deleted zero index
  + 2 phase indices (+a and -a)
  + (q-3) neutral surviving indices.
```

#### PUU-L023 — Affine Midpoint Geometry

With raw affine residue map

```text
F(j) = b + j*M  (mod q),
```

the distinguished indices satisfy

```text
jplus - jzero = -(jminus - jzero)
jplus + jminus = 2*jzero.
```

The deleted index is the affine midpoint of the phase pair.

#### PUU-L024 — Reflection Involution / Neutral Two-Cycles

```text
rho(j) = 2*jzero - j
rho(rho(j)) = j
F(rho(j)) = -F(j).
```

Hence

```text
+a phase  ↔ -a phase
0 deleted ↔ 0 deleted
neutral   ↔ neutral.
```

For odd `q`, the deleted center is the unique fixed point; neutral indices occur in
fixed-point-free two-cycles.

#### PUU-L025 — Affine Normal Form / Constant Phase Radius

Let

```text
R(S,q,a) := a * M(S)⁻¹  in ZMod q.
```

The radius is the unique coordinate satisfying

```text
R * M = a.
```

For a coprime anchor it is nonzero.  The phase pair has the explicit normal form

```text
jplus  = jzero + R
jminus = jzero - R
```

and

```text
jplus - jminus = 2*R.
```

Most importantly:

```text
changing the old representative b changes the center,
but does not change R.
```

Thus the static local fresh-prime geometry is now normalized into **center +
constant radius** form.

**Status:** Phase D static geometry is complete enough.  Do not continue with
endless local affine refinements unless they are needed by transport.

---

## 5. Current exact mathematical picture

The same fresh-prime raw fiber now carries three compatible structures.

### Wheel-survivor growth

```text
q raw lifts
  → exactly one deleted lift
  → q-1 survivors.
```

### Square-phase growth

```text
old phase representative
  → exactly two enlarged phase representatives
  → residues +a and -a modulo q.
```

### Affine index-circle geometry

```text
1 deleted center / fixed point
+ 1 phase two-cycle at radius R
+ neutral reflection two-cycles.
```

At cardinality level:

```text
q = 1 + 2 + (q-3).
```

At coordinate level:

```text
center = jzero
phase  = center ± R
R      = a / M.
```

The entire picture is finite provider-side congruence geometry.  No prime-in-square
shell existence theorem was used to obtain it.

---

## 6. Revised research question

The branch should no longer ask

```text
"can we prove an old-basis escape exists?"
```

because PUU-L015 showed that the exact branch version is already Legendre.

The current question is:

> Can the independent wheel / phase / affine geometry force a transport invariant
> or coverage obstruction for a moving square-anchor orbit, without assuming or
> re-encoding square-shell escape?

The missing ingredient is now **dynamics / transport**.

We must understand how the normalized geometry moves when

1. the old representative changes;
2. the square anchor changes;
3. the finite prime basis grows;
4. these operations are iterated through the primorial tower.

---

## 7. Active provider program — Phase E

### Phase E1 — old-representative center transport — ACTIVE

PUU-L025 proved that the radius is fixed.  The moving part is the deleted center.

From

```text
b + jzero*M = 0  (mod q),
```

expect the canonical center coordinate

```text
C(b) = -b / M.
```

Hence

```text
C(b₂) - C(b₁) = (b₁-b₂) / M.
```

The immediate implementation target is **PUU-L026 — Fresh-Prime Deleted-Center
Transport / Old-Representative Translation Law**.

Desired outcome:

```text
old representative b  → translated center C(b)
anchor a              → constant radius R(a)
phase pair             → C(b) ± R(a).
```

The point is not another static affine identity.  It is the first explicit
transport law of the revised roadmap.

### Phase E2 — square-anchor evolution on a fixed basis

After center transport is closed, return to PUU-L010 and the actual anchor step

```text
n² → (n+1)² = n² + (2n+1).
```

The target is an exact provider theorem describing how phase / center / reservation
coordinates move under `n → n+1`.

A useful theorem here must be stated without `SquareCell`,
`escapingSquareOffsets`, `SuccessorOldEscapeCriterion`, or a prime witness.

### Phase E3 — compatibility with fresh-prime tower growth

Combine

```text
anchor evolution
```

with

```text
S → insert q S.
```

Audit:

- whether anchor motion commutes with old/new projection in a useful coordinate;
- how centers and constant radii lift through repeated fresh-prime extensions;
- whether a conserved or forbidden pattern appears under repeated anchor motion;
- whether the transport is coherent across the primorial tower.

### Phase E4 — finite coverage obstruction audit

Only after a genuine transport invariant exists should the branch ask whether it
obstructs complete finite reservation of a moving square-offset window.

Desired direction:

```text
independent provider invariant
    ↓
finite coverage obstruction
    ↓
consumer bridge.
```

Forbidden direction:

```text
rename square-shell escape
    ↓
prove the renamed statement
    ↓
claim a new provider.
```

PUU-L015 remains the anti-relabeling gate.

---

## 8. Legendre re-entry gate

Legendre-specific work may resume only when a theorem satisfies all of:

1. it is naturally stated in `DkMath.NumberTheory.PrimorialUniverse`;
2. it does not import the Legendre consumer layer;
3. it does not assume `SquareCell`, `escapingSquareOffsets`,
   `SuccessorOldEscapeCriterion`, or an equivalent prime witness;
4. it follows from wheel / phase / affine / transport geometry;
5. only after proving it do we ask what it implies for square shells.

If the translated consumer statement is again merely equivalent to Legendre with no
new provider content, record that fact and close the route.

---

## 9. Unit Universe / PowerSwap / GN reconnection

The branch began from a broader DkMath question than Legendre: primitive scales
should be understood relative to synchronized number universes.

That wider objective remains open.

### Unit Universe

L002–L005 provide the coordinate / common-lattice / synchronization foundation.
The current primorial geometry is its discrete finite-prime model.

### PowerSwap

Reconnect only when the provider geometry has a clear scaling statement, such as
phase/reservation data preserved by exponent normalization or a transport theorem
naturally expressible through existing PowerSwap APIs.

### GN / CosmicFormula

Reconnect only after the finite provider theorem has a clear unit-relative
interpretation.

Preferred direction:

```text
finite prime / phase transport geometry
    ↓
unit-relative structural invariant
    ↓
PowerSwap / GN / CosmicFormula generalization.
```

---

## 10. Current non-goals

Do not divert this branch into:

- direct proof of `SuccessorOldEscapeProvider`;
- another old-escape lower bound without an independent invariant;
- generic Jacobsthal / maximum-wheel-gap machinery;
- PNT, RH, analytic sieve, or asymptotic prime density;
- re-opening the old residual-ledger refinements;
- neutral-seat primality/compositeness without a structural reason;
- prime-power modulus generalization before the squarefree geometry is used;
- PowerSwap / GN integration before a concrete transport invariant exists;
- ordered/geodesic notions of circle distance;
- endless local affine lemmas that do not advance representative / anchor / basis
  transport.

The branch is strongest while it stays finite, exact, and provider-side.

---

## 11. Completion criteria

This branch does **not** need a Legendre proof to be mathematically successful.

Current completion sequence:

```text
1. finite reservation / unit synchronization                 DONE
2. exact primorial wheel tower                               DONE
3. exact square-phase / CRT finite-fiber geometry            DONE
4. fresh-prime affine / reflection normal form               DONE through L025
5. representative center transport                           ACTIVE — L026
6. square-anchor / basis transport                            NEXT MAJOR OBJECTIVE
7. independent finite coverage-obstruction audit             FUTURE GATE
8. consumer re-entry, only if earned                         CONDITIONAL
9. Unit Universe / PowerSwap / GN generalization             CONDITIONAL
```

The central research principle is:

```text
Do not search for a prime directly.
Formalize the finite geometry that could make complete reservation structurally
impossible, and let a consumer bridge read the consequence afterwards.
```

PUU-L025 closes the static affine-normal-form phase.  PUU-L026 begins the transport
phase.
