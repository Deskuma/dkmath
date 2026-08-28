# NumberTheory Primorial Unit Universe — Roadmap

> Revised: 2026-08-28
>
> Branch: `wip/number-theory-primorial-unit-universe-260827-v0`
>
> This document is the current route map.  The initial branch purpose is preserved,
> but the checkpoint order and the main provider-side geometry have changed
> substantially after PUU-L015 and PUU-L016–L024.

## 0. Branch purpose — what has not changed

This branch was opened after closing the Legendre finite-support / residual-ledger
route on `wip/number-theory-primitive-structure-260822-v2`.

The purpose is **not** to rename Legendre's conjecture and then prove the renamed
statement.  The purpose is to formalize a higher-level finite arithmetic provider
from which consumer statements may later be derived.

The original hierarchy remains:

1. **Finite prime-basis reservation**
   - a finite set of known prime scales determines a periodic reservation sheet;
   - a finite basis cannot reserve every natural number;
   - a Euclid-type escape forces a prime outside the basis.

2. **Unit-relative coordinates and synchronization**
   - primitive/composite behavior is read relative to a chosen unit coordinate;
   - synchronized refinements preserve the old factor lattice;
   - two units meet on a common integer lattice exactly under the corresponding
     commensurability condition;
   - a finite prime basis has a canonical common synchronization period.

3. **Primorial / finite-wheel geometry**
   - the finite-prime product is the synchronization period;
   - wheel survivors, reflection, fresh-prime lift, unique deletion, replication,
     and nested projection are exact finite structures.

4. **Square-anchor provider geometry**
   - square anchors and square phases are studied modulo the finite-prime period;
   - the aim is to discover an invariant that is independent of a later
     prime-in-square-shell consumer statement.

Legendre remains a **consumer / audit target**, not the foundational layer.
PowerSwap, GN/CosmicFormula, and wider DkMath scaling structures remain possible
later connections, but they should be attached only after an independent finite
provider theorem has been isolated.

---

## 1. Original mathematical starting point

For a finite prime basis `S`, define the synchronization / reservation period

```text
M(S) := ∏ p ∈ S, p.
```

A natural seat `n` is reserved by `S` when

```text
∃ p ∈ S, p ∣ n.
```

Every `p ∈ S` divides `M(S)`, hence no `p ∈ S` divides `M(S) + 1`.
Any prime divisor of `M(S) + 1` is therefore outside `S`.

```text
finite basis S
    ↓
period M(S)
    ↓
Euclid escape M(S)+1
    ↓
new prime divisor q ∉ S
```

This **Finite Reservation Escape** is global finite arithmetic.  It does not by
itself give a prime in a prescribed short interval such as a Legendre square cell.

The original branch idea was to combine this global escape principle with a
primorial reservation pattern and a square-anchor propagation theorem.  The
formal development has shown that this last step requires more care than the
initial roadmap assumed.

---

## 2. Major correction obtained from PUU-L011–L015

The first roadmap expected a Legendre-specific route of the form

```text
square-hole
  → future reservation closure / propagation
  → no new primitive seat
  → contradiction with finite-basis escape.
```

PUU-L011–L014 built the exact bridge from square offsets to primorial-wheel
reservation and classified the successor threshold behavior.  PUU-L015 then
performed the anti-relabeling audit.

The result is decisive:

```text
SuccessorOldEscapeProvider  ↔  LegendreConjecture.
```

More locally, the branch-exact old-basis escape criterion is equivalent to the
existence of an actual escaping square offset / prime witness in the successor
square cell.

Therefore:

- proving a global lower bound for `successorOldBasisEscapingOffsets` is **not**
  automatically a new provider;
- directly proving the branch-exact old-escape criterion would already prove
  Legendre;
- the old-escape frontier is a consumer reformulation, not an independent source
  of information.

This closes the route

```text
"prove old escape exists"
```

as a standalone provider strategy.

Any future Legendre progress from this branch must first come from a theorem stated
and proved independently inside the provider geometry, and only afterwards be
translated into square-cell language.

---

## 3. Another correction: PowerSwap was deferred, not completed

The initial checkpoint sketch placed a PowerSwap prime-support connection very
early.  The implementation did not follow that numbering.

In particular, the actual early development became:

```text
L001 finite reservation escape
L002 unit-coordinate refinement
L003 common lattice
L004 unit-intersection classification
L005 finite-prime synchronization
```

rather than using L005 for PowerSwap.

This is intentional in retrospect.  The finite congruence structure needed a
clean provider layer before exponent-fiber machinery was attached.

**PowerSwap is therefore still a deferred connection.**  It is not a failed
checkpoint and should not be silently treated as implemented.

The preferred future order is:

```text
finite provider invariant
    ↓
transport / scaling theorem
    ↓
PowerSwap / GN / CosmicFormula connection, if structurally natural.
```

---

## 4. Current implemented architecture

### Phase A — finite reservation and unit synchronization — COMPLETE

#### PUU-L001 — Finite Reservation Escape

- finite prime basis;
- product period;
- `M+1` escape;
- prime outside the finite basis.

#### PUU-L002 — Unit Coordinate Refinement

- common absolute point under different positive unit coordinates;
- synchronized integer refinement;
- preservation of the old coordinate factor under refinement.

#### PUU-L003 — Common Lattice

- exact common-lattice parameterization for synchronized integer units;
- canonical fiber form of common points.

#### PUU-L004 — Unit Intersection Classification

- exact intersection / commensurability classification for the implemented unit
  setting;
- separation of synchronized and unsynchronized coordinate worlds.

#### PUU-L005 — Finite Prime Synchronization

- finite prime scales are synchronized by the common product period;
- basis-prime reservation is periodic on that lattice.

These checkpoints implement the branch's original "unit universe + finite prime
basis" foundation.

---

### Phase B — finite wheel tower — COMPLETE

#### PUU-L006 — Wheel Survivor / Reflection

For one period `0 < r < M(S)`:

```text
survivor  :=  no p ∈ S divides r.
```

The reduced-residue / coprime bridge and

```text
r ↔ M(S)-r
```

reflection are formalized.

#### PUU-L007 — Fresh-Prime Lift / Unique Deletion

For fresh prime `q ∉ S`, every old survivor `r` has raw lifts

```text
r + j*M(S),    0 ≤ j < q.
```

Exactly one is divisible by `q`.

#### PUU-L008 — Wheel Replication

The remaining `q-1` lifts are enlarged-wheel survivors, giving the exact growth
law

```text
|WheelSurvivors(insert q S)|
  = (q-1) * |WheelSurvivors(S)|.
```

#### PUU-L009 — Nested Wheel Projection

Reduction modulo the old period projects the enlarged wheel onto the old wheel.
Each old survivor has an exact projection fiber of size `q-1`, compatible with
reflection.

#### PUU-L010 — Square-Anchor Orbit

Square anchors and fixed shell offsets are projected modulo the same finite-prime
period.  Reservation is characterized through the projected coordinate and fresh
prime insertion is coherent with old projection.

This completes the original primorial-wheel replication layer.

---

### Phase C — Legendre consumer bridge and anti-relabeling audit — COMPLETE / CLOSED

#### PUU-L011 — Legendre / Primorial Wheel Bridge

Square-offset coverage is identified with finite-prime reservation, and within the
bounded square shell a projected wheel survivor is exactly the corresponding prime
witness.

#### PUU-L012 — Successor Square-Shell Transition

The successor basis is decomposed into the old basis plus the possible fresh
threshold prime.  The fresh threshold contributes only its two bounded shell seats.

#### PUU-L013 — Successor Old-Basis Escape / Deletion Capacity

Old-basis escaping offsets and actual successor projected escapes are compared.
The prime-threshold branch deletes at most the second threshold seat.

#### PUU-L014 — Twin-Threshold Exception

The second threshold seat is an old-basis escape exactly in the twin-prime case.
Every other old-basis escape is already an actual prime witness.

#### PUU-L015 — Old-Escape Frontier Equivalence Audit

The exact branch criterion is packaged and shown globally equivalent to Legendre.

**Status:** this consumer reduction route has reached its reduction limit.
Do not continue by adding new names for the same square-shell existence statement.

---

### Phase D — square-anchor phase / CRT provider geometry — COMPLETE THROUGH L024

PUU-L016 started a new provider-only route after the L015 audit.
This route does not import the Legendre consumer layer.

#### PUU-L016 — Square-Anchor Phase Symmetry

Define the square phase by equality of square residues modulo the finite basis
period.

```text
a² ≡ b²  (mod M(S)).
```

The same phase preserves every shell-offset projection and therefore the complete
finite-basis reservation / non-reservation pattern.

#### PUU-L017 — Local Prime Sign Dichotomy

For a basis prime `p`:

```text
a² ≡ b² (mod p)
    ↔
a ≡ +b (mod p) or a ≡ -b (mod p).
```

A global square phase descends to a local sign profile.

#### PUU-L018 — Mixed-Sign CRT Synthesis

The converse is established: every local sign profile reconstructs the global
square phase, and arbitrary mixed signs are realizable by CRT.

Thus the global phase is exactly the finite product of local `±` choices, with
expected degeneracy at `p=2` or zero coordinates.

#### PUU-L019 — Coprime Square-Phase Fiber Cardinality

For an anchor coprime to `M(S)`, all odd-prime signs are distinct and the one-period
phase fiber is in bijection with subsets of `S.erase 2`.

```text
|PhaseFiber_S(a)| = 2 ^ |S.erase 2|.
```

Example:

```text
S = {2,3,5}, M = 30, a = 1
PhaseFiber = {1,11,19,29}.
```

#### PUU-L020 — Fresh-Prime Phase-Fiber Cover

Adjoining a fresh odd prime gives an exact two-sheet cover of the old phase fiber.
Fresh `2` contributes no new sign degree.

```text
fresh odd q : ×2
fresh q = 2 : ×1.
```

#### PUU-L021 — Phase / Survivor Subcover

For a coprime anchor, the phase fiber lies inside the wheel survivors.
On each fresh-prime projection fiber:

```text
phase cover : 2 seats
wheel cover : q-1 seats.
```

For `q=3` the two fibers are equal.  For `3<q` the phase fiber is a proper
subcover.

#### PUU-L022 — Fresh-Prime Lift-Index Trichotomy

The `q` raw lift indices decompose exactly as

```text
q raw indices
  = 1 deleted zero index
  + 2 phase indices (+a and -a)
  + (q-3) neutral surviving indices.
```

The three distinguished indices are unique and pairwise distinct under the
coprime / odd-prime hypotheses.

#### PUU-L023 — Affine Midpoint Geometry

The raw lift residue map is affine:

```text
F(j) = b + j*M  (mod q).
```

If `jplus`, `jminus`, and `jzero` map to `+a`, `-a`, and `0`, then

```text
jplus - jzero = -(jminus - jzero)
jplus + jminus = 2*jzero.
```

The deleted index is the unique midpoint of the phase pair for odd `q`.

#### PUU-L024 — Reflection Involution / Neutral Two-Cycles

Reflection about the deleted center

```text
rho(j) = 2*jzero - j
```

satisfies

```text
rho(rho(j)) = j
F(rho(j)) = -F(j).
```

Consequently:

```text
+a phase  ↔ -a phase
0 deleted ↔ 0 deleted
neutral   ↔ neutral.
```

For odd `q`, the deleted center is the unique fixed point and neutral indices
occur in fixed-point-free two-cycles.

This phase / affine route is the main new structure that was absent from the
original roadmap.

---

## 5. Current active checkpoint — PUU-L025

### Fresh-Prime Lift-Index Affine Normal Form / Constant Phase Radius

Let

```text
M := finitePrimeBasisProduct S.
```

Since `M` is invertible modulo a fresh prime `q`, define the phase radius in
`ZMod q` by

```text
R := a / M
```

or equivalently `a * M⁻¹`.

The active target is the explicit normal form

```text
jplus  = jzero + R
jzero  = center
jminus = jzero - R.
```

The key provider invariant is:

```text
changing the old representative b changes the center,
but does not change the phase radius R.
```

Hence also

```text
jplus - jminus = 2*R
```

is independent of the old representative.

This checkpoint remains entirely inside `DkMath.NumberTheory.PrimorialUniverse`.

---

## 6. Current exact mathematical picture

The provider tower now contains two exact fresh-prime growth laws on the same
projection hierarchy.

### Wheel-survivor growth

```text
q raw lifts
  → delete exactly one q-divisible lift
  → q-1 enlarged survivors.
```

### Square-phase growth

For a coprime anchor and fresh odd `q`:

```text
old phase representative
  → exactly two enlarged phase representatives
  → local signs +a and -a modulo q.
```

The phase cover is a subcover of the survivor cover.

### Index-circle geometry

The same raw fiber has the structural decomposition

```text
1 fixed deleted center
+ 1 reflected phase two-cycle
+ neutral reflected two-cycles.
```

Equivalently, at the cardinality level:

```text
q = 1 + 2 + (q-3).
```

For `q=3`, the neutral part vanishes and the phase pair is the whole survivor
fiber.  For `q>3`, neutral survivor two-cycles remain.

The important current observation is that this is **strictly provider-side finite
congruence geometry**.  No prime-in-square-shell existence theorem has been used to
obtain it.

---

## 7. Revised research question

The branch should no longer ask only:

```text
"can we prove an old-basis escape exists?"
```

PUU-L015 showed that the branch-exact version of that question is already
Legendre.

The revised question is:

> Can the independent finite wheel / square-phase / affine geometry force a
> transport invariant or coverage obstruction for a moving square-anchor orbit,
> without assuming or re-encoding square-shell escape?

The missing ingredient is therefore **dynamics / transport**, not another local
existence predicate.

The static geometry is now strong:

- exact wheel fibers;
- exact phase fibers;
- CRT sign coordinates;
- two-sheet fresh-prime phase cover;
- phase/survivor subcover;
- deleted-center midpoint;
- full index-circle reflection involution.

The next major mathematical task is to understand how these structures move when

1. the old representative changes;
2. the square anchor changes;
3. the prime basis grows;
4. these changes are iterated through the primorial tower.

---

## 8. Post-L025 provider program

Checkpoint numbers after L025 should be chosen from actual theorem results rather
than fixed in advance.  The following are research phases, not promises that each
will become exactly one checkpoint.

### Phase E1 — center transport across old representatives

From

```text
b + jzero*M = 0  (mod q)
```

the deleted center should have an explicit affine coordinate depending on `b`.
The aim is to formalize how the center translates when `b` changes, while L025
keeps the radius fixed.

Desired conceptual form:

```text
center(b₂) - center(b₁)
    = affine image of (b₁-b₂),

radius(a,S,q)
    = constant.
```

This would turn each fresh-prime fiber into a family of translated copies of one
canonical phase pair.

### Phase E2 — square-anchor evolution on a fixed basis

Return to PUU-L010 and study the actual anchor step

```text
n² → (n+1)² = n² + (2n+1)
```

through the phase coordinates developed in L016–L025.

The goal is not to prove a prime exists.  The goal is to obtain an exact transport
law for phase / center / reservation data under the anchor increment.

A useful theorem must be stated without `SquareCell`, `escapingSquareOffsets`, or a
prime witness.

### Phase E3 — compatibility with fresh-prime tower growth

Combine:

```text
anchor evolution
```

with

```text
S → insert q S.
```

Questions to audit:

- does anchor motion commute with old/new wheel projection in a useful coordinate?
- how do phase centers lift through the two-sheet cover?
- can the constant-radius description be made coherent across multiple fresh-prime
  insertions?
- is there a conserved or forbidden pattern under repeated anchor motion?

### Phase E4 — finite coverage obstruction audit

Only after a transport invariant exists should the branch ask whether it obstructs
complete reservation of a square-offset window.

The desired direction is

```text
independent provider invariant
    ↓
finite coverage obstruction
    ↓
consumer bridge.
```

The forbidden direction is

```text
redefine square-shell escape
    ↓
prove the redefinition
    ↓
claim a new provider.
```

PUU-L015 is the permanent anti-relabeling gate for this distinction.

---

## 9. Legendre re-entry gate

Legendre-specific work may resume only when there is a theorem satisfying all of
the following:

1. it is naturally stated in `DkMath.NumberTheory.PrimorialUniverse`;
2. it does not import the Legendre consumer layer;
3. it does not assume `SquareCell`, `escapingSquareOffsets`,
   `SuccessorOldEscapeCriterion`, or an equivalent prime witness;
4. it follows from wheel / phase / affine / transport geometry;
5. only after it is proved do we ask what it implies for a square shell.

If the resulting consumer statement is again equivalent to Legendre with no new
provider content, record that fact and close that route rather than iterating new
vocabulary.

This gate is now part of the roadmap, not an incidental checkpoint rule.

---

## 10. Unit Universe / PowerSwap / GN reconnection

The branch started from a broader DkMath question than Legendre: primitive scales
should be understood relative to synchronized number universes, not only as isolated
ordinary primes.

That wider objective remains open.

### Unit Universe

L002–L005 already provide the finite coordinate / common-lattice / synchronization
foundation.  The current primorial geometry is the discrete finite-prime model built
on that foundation.

### PowerSwap

The planned prime-support / exponent-fiber connection is still deferred.
Do not add PowerSwap merely to satisfy the old checkpoint list.

Reconnect it when a provider invariant has a clear scaling statement, for example:

- phase or reservation data stable under an exponent normalization;
- prime-support information that survives coarse/fine power exchange;
- a transport law naturally expressible through `PowNormalForm` or an existing
  PowerSwap API.

### GN / CosmicFormula

GN / CosmicFormula should reconnect only after the finite provider theorem has a
clear unit-relative interpretation.

The intended direction remains:

```text
finite prime / phase geometry
    ↓
unit-relative structural invariant
    ↓
PowerSwap / GN / CosmicFormula generalization.
```

Do not use these layers as decoration around a theorem that is still only a
Legendre reformulation.

---

## 11. Non-goals at the current stage

Do not divert the active branch into:

- direct proof of `SuccessorOldEscapeProvider`;
- another old-escape cardinality lower bound without an independent invariant;
- generic Jacobsthal / maximum-wheel-gap machinery;
- PNT, RH, analytic sieve, or asymptotic prime density;
- re-opening the old residual-ledger refinements;
- neutral-seat primality/compositeness classification without a structural reason;
- prime-power modulus generalization before the squarefree fresh-prime geometry is
  used;
- arbitrary category-theoretic abstraction;
- PowerSwap / GN integration before a concrete transport invariant is ready;
- endless local affine lemmas that do not advance center/anchor/tower transport.

The branch is currently strongest when it stays finite, exact, and provider-side.

---

## 12. Revised completion criteria for this branch

This branch does **not** need a Legendre proof in order to be mathematically
successful.

A satisfactory completion should establish the following sequence as far as Lean
permits:

1. finite reservation / unit synchronization foundation — **done**;
2. exact primorial wheel tower — **done**;
3. exact square-anchor phase / CRT / finite-fiber geometry — **done**;
4. fresh-prime affine / reflection normal form — **in progress through L025**;
5. a nontrivial transport theorem for changing representatives / anchors / basis —
   **next major objective**;
6. an audit of whether that transport theorem gives a genuinely independent finite
   coverage obstruction — **future gate**;
7. if yes, reconnect a consumer such as Legendre;
8. if structurally useful, lift the invariant back into Unit Universe / PowerSwap /
   GN language.

The branch's central research principle is now:

```text
Do not search for a prime directly.
Formalize the finite geometry that makes complete reservation structurally
impossible — if such an obstruction exists — and let the consumer bridge read the
consequence afterwards.
```

That principle is the updated continuation of the original Primorial Unit Universe
objective.
