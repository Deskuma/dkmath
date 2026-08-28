# NumberTheory Primorial Unit Universe — Roadmap

> Revised: 2026-08-28 after PUU-L027
>
> Branch: `wip/number-theory-primorial-unit-universe-260827-v0`
>
> This is the current route map. The original branch purpose is unchanged, but
> the implementation has now moved from static finite geometry into exact
> square-anchor transport.

## 0. Branch purpose

This branch was opened after closing the Legendre finite-support / residual-ledger
route on `wip/number-theory-primitive-structure-260822-v2`.

The purpose is **not** to rename Legendre's conjecture and prove the renamed
statement. The purpose is to formalize a higher-level finite arithmetic provider
whose consequences may later be read by consumers.

The intended hierarchy is now:

```text
finite prime basis / reservation
        ↓
unit-relative coordinates / synchronization
        ↓
primorial finite-wheel tower
        ↓
square-anchor phase / CRT geometry
        ↓
fresh-prime affine geometry
        ↓
representative and square-anchor transport
        ↓
old-period / fresh-prime tower monodromy
        ↓
independent finite coverage obstruction, if one exists
        ↓
consumer re-entry
        ↓
possible Unit Universe / PowerSwap / GN generalization
```

Legendre remains a **consumer / audit target**, not the foundational layer.

---

## 1. Original finite-reservation principle

For a finite prime basis `S`, let

```text
M(S) := ∏ p ∈ S, p.
```

A natural seat `n` is reserved by `S` when

```text
∃ p ∈ S, p ∣ n.
```

Every basis prime divides `M(S)`, hence `M(S)+1` is not reserved by any member of
`S`. Any prime divisor of `M(S)+1` is therefore outside `S`.

```text
finite basis S
    ↓
period M(S)
    ↓
Euclid escape M(S)+1
    ↓
new prime divisor q ∉ S
```

This is a global finite escape principle. It does **not** by itself place a prime
inside a prescribed short interval such as a square cell.

The branch seeks the missing finite structural layer between global finite escape
and local consumer statements.

---

## 2. Permanent anti-relabeling gate from PUU-L011–L015

The first roadmap expected a Legendre-specific route roughly of the form

```text
square-hole
  → future reservation closure
  → no new primitive seat
  → contradiction with finite-basis escape.
```

PUU-L011–L014 built the exact square-offset / wheel bridge and successor-threshold
classification. PUU-L015 then proved the decisive equivalence

```text
SuccessorOldEscapeProvider ↔ LegendreConjecture.
```

Therefore the strategy

```text
"prove the branch-exact old escape criterion"
```

is not an independent provider route. It is already the consumer statement in new
vocabulary.

PUU-L015 is a permanent gate:

- do not continue by renaming square-shell escape;
- do not treat a lower bound for the exact old-escape criterion as new information
  unless it follows from a separately proved provider invariant;
- future Legendre re-entry is allowed only after the provider theorem already
  exists independently in `PrimorialUniverse`.

---

## 3. PowerSwap / GN status

The initial sketch placed a PowerSwap prime-support connection early in the branch.
The actual implementation needed a clean synchronization / wheel / phase provider
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

Preferred later direction:

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

Finite basis, product period, `M+1` escape, prime outside the basis.

#### PUU-L002 — Unit Coordinate Refinement

Common absolute point under different positive units and synchronized integer
refinement.

#### PUU-L003 — Common Lattice

Exact common-lattice parameterization and canonical common-point fiber.

#### PUU-L004 — Unit Intersection Classification

Exact implemented intersection / commensurability classification.

#### PUU-L005 — Finite Prime Synchronization

Finite prime scales share the product synchronization period; reservation is
periodic on that lattice.

---

### Phase B — finite wheel tower — COMPLETE

#### PUU-L006 — Wheel Survivor / Reflection

One-period reduced-residue survivors and

```text
r ↔ M-r
```

reflection.

#### PUU-L007 — Fresh-Prime Lift / Unique Deletion

For fresh prime `q ∉ S`, every old survivor has `q` raw lifts and exactly one is
`q`-divisible.

#### PUU-L008 — Wheel Replication

```text
|WheelSurvivors(insert q S)|
  = (q-1) * |WheelSurvivors(S)|.
```

#### PUU-L009 — Nested Wheel Projection

The enlarged wheel projects canonically to the old wheel; every old survivor has an
exact projection fiber of size `q-1`.

#### PUU-L010 — Square-Anchor Orbit

Square anchors and fixed shell offsets are projected modulo the same period.
The square-value successor law is

```text
n² → (n+1)² = n² + (2*n+1)
```

modulo the finite basis product.

PUU-L010 is the provider-side square-value dynamics entry point.

---

### Phase C — Legendre consumer bridge — COMPLETE / CLOSED

#### PUU-L011 — Legendre / Primorial Wheel Bridge

Square-offset coverage is identified with finite-basis reservation.

#### PUU-L012 — Successor Square-Shell Transition

The successor basis is decomposed into the old basis and a possible threshold
prime.

#### PUU-L013 — Old-Basis Escape / Deletion Capacity

Old-basis escapes and actual projected escapes are compared.

#### PUU-L014 — Twin-Threshold Exception

The second threshold seat is an old-basis escape exactly in the twin-prime case.

#### PUU-L015 — Old-Escape Frontier Equivalence Audit

The branch-exact global provider candidate is shown equivalent to Legendre.

**Status:** consumer reduction limit reached. This route is closed unless a new,
independently proved provider invariant becomes available.

---

### Phase D — square-anchor phase / CRT / affine geometry — COMPLETE

PUU-L016 restarted from the provider layer after the L015 audit. L016–L027 do not
import the Legendre consumer layer.

#### PUU-L016 — Square-Anchor Phase Symmetry

```text
a² ≡ b² (mod M(S))
```

is promoted to a phase relation preserving the complete fixed-offset reservation
pattern.

#### PUU-L017 — Local Prime Sign Dichotomy

For each basis prime:

```text
a² ≡ b²
  ↔ a ≡ +b or a ≡ -b.
```

#### PUU-L018 — Mixed-Sign CRT Synthesis

Local sign profiles and global square phase are equivalent. Arbitrary mixed sign
assignments are CRT-realizable.

#### PUU-L019 — Coprime Phase-Fiber Cardinality

For a coprime anchor:

```text
|PhaseFiber_S(a)| = 2 ^ |S.erase 2|.
```

The phase fiber is a Boolean cube of odd-prime sign choices.

#### PUU-L020 — Fresh-Prime Phase-Fiber Cover

```text
fresh odd q : ×2
fresh q = 2 : ×1.
```

#### PUU-L021 — Phase / Survivor Subcover

On a fresh-prime projection fiber:

```text
phase cover : 2 seats
wheel cover : q-1 seats.
```

For `q=3` they coincide; for `3<q` the phase cover is proper.

#### PUU-L022 — Fresh-Prime Lift-Index Trichotomy

```text
q raw indices
  = 1 deleted zero index
  + 2 phase indices (+a and -a)
  + (q-3) neutral surviving indices.
```

#### PUU-L023 — Affine Midpoint Geometry

For raw affine residue map

```text
F(j) = b + j*M  (mod q),
```

the deleted index is the midpoint of the `+a/-a` phase pair.

#### PUU-L024 — Reflection Involution / Neutral Two-Cycles

```text
rho(j) = 2*jzero - j
rho(rho(j)) = j
F(rho(j)) = -F(j).
```

The deleted center is the unique fixed point for odd `q`; neutral indices occur in
fixed-point-free pairs.

#### PUU-L025 — Affine Normal Form / Constant Phase Radius

Define

```text
R(S,q,a) = a * M(S)⁻¹  in ZMod q.
```

Then

```text
jplus  = jzero + R
jminus = jzero - R
jplus - jminus = 2*R.
```

Changing the old representative changes the center but not the radius.

**Status:** static local affine geometry is complete enough. Further local lemmas
must serve transport rather than become an end in themselves.

---

### Phase E1 — representative transport — COMPLETE

#### PUU-L026 — Deleted-Center Transport / Rigid Phase Translation

Define the canonical center

```text
C(b) = -b * M⁻¹.
```

It is the unique coordinate satisfying

```text
b + C(b)*M = 0.
```

For two old representatives:

```text
C(b₂) - C(b₁) = (b₁-b₂) * M⁻¹.
```

The phase pair is

```text
C(b) ± R(a)
```

and both sheets translate rigidly by exactly the center displacement.

This is the first genuine transport theorem of the revised roadmap.

---

### Phase E2 — moving square-anchor successor transport — COMPLETE

#### PUU-L027 — Canonical Phase Transport / Successor Carry Law

A critical distinction is now formalized:

```text
anchor coordinate     r_n = n mod M
square-value coordinate    = n² mod M = r_n² mod M.
```

The canonical representative satisfies

```text
r_(n+1) = (r_n + 1) mod M.
```

Define the wrap carry by

```text
r_n + 1 = r_(n+1) + carry_n * M,
```

with

```text
carry_n ∈ {0,1}.
```

For a fresh prime `q`, define the moving center/radius

```text
C_n = -r_n / M
R_n =  n  / M
```

inside `ZMod q`. PUU-L027 proves

```text
C_(n+1) - C_n = carry_n - M⁻¹
R_(n+1) - R_n = M⁻¹.
```

Hence the dynamic phase sheets

```text
Pplus_n  = C_n + R_n
Pminus_n = C_n - R_n
```

obey

```text
Pplus_(n+1)  - Pplus_n  = carry_n
Pminus_(n+1) - Pminus_n = carry_n - 2*M⁻¹.
```

Actual deleted / plus / minus lift witnesses over the canonical representative are
connected back to these moving coordinates.

**Status:** one-step square-anchor transport is complete.

---

## 5. Current exact mathematical picture

The branch now has four compatible levels on the same finite-prime hierarchy.

### Wheel level

```text
q raw lifts
  → one deleted
  → q-1 survivors.
```

### Phase level

```text
old phase representative
  → two fresh-prime phase lifts
  → +a / -a.
```

### Static affine level

```text
center C(b) = -b/M
radius R(a) =  a/M
phase pair  = C(b) ± R(a).
```

### Dynamic anchor level

```text
r_n = n mod M
carry_n = old-period wrap bit

Δcenter = carry_n - M⁻¹
Δradius = M⁻¹
Δplus   = carry_n
Δminus  = carry_n - 2*M⁻¹.
```

This is still entirely finite provider-side congruence geometry. No square-shell
prime existence theorem was used to obtain it.

---

## 6. New closed-form observation after PUU-L027

Write the Euclidean decomposition

```text
n = r_n + Q_n * M,
Q_n = n / M.
```

Then the dynamic plus coordinate simplifies to

```text
Pplus_n
  = (-r_n + n) * M⁻¹
  = Q_n          in ZMod q.
```

So the plus sheet is exactly the **old-period block quotient modulo the fresh
prime**.

This explains the L027 carry law:

```text
Q_(n+1) = Q_n + carry_n.
```

It also predicts the whole-period monodromy

```text
n → n+M:
  center unchanged
  radius +1
  plus   +1
  minus  -1.
```

After `q` old-period turns:

```text
n → n+q*M
```

the `ZMod q` phase coordinates return. Since

```text
finitePrimeBasisProduct (insert q S) = q*M
```

for fresh `q`, this is the first direct compatibility expected between moving
anchor dynamics and fresh-prime tower enlargement.

---

## 7. Active provider program — Phase E3

### PUU-L028 — Square-Anchor Block Quotient / Old-Period Monodromy — ACTIVE

The immediate target is to formalize the closed form and period transport predicted
above.

Required core:

```text
Pplus_n = n / M                  in ZMod q
Q_(n+1) = Q_n + carry_n

C_(n+M)      = C_n
R_(n+M)      = R_n + 1
Pplus_(n+M)  = Pplus_n + 1
Pminus_(n+M) = Pminus_n - 1.
```

Then generalize to `k` old periods:

```text
C_(n+kM)      = C_n
R_(n+kM)      = R_n + k
Pplus_(n+kM)  = Pplus_n + k
Pminus_(n+kM) = Pminus_n - k.
```

Finally set `k=q` and identify `q*M` with the enlarged fresh-prime period.

Desired conceptual result:

```text
one old-period revolution:
  phase monodromy (+1,-1)

q old-period revolutions:
  closure at the enlarged fresh-prime period q*M.
```

This is the preferred Phase E3 bridge between anchor dynamics and prime-basis
growth.

---

## 8. Phase E3 continuation after L028

Only after the period monodromy is formalized should the branch choose the next
basis-transport theorem.

Questions to audit:

- does the `q*M` closure coincide naturally with the existing L009/L020 enlarged
  projection fibers?
- can the two phase sheets be viewed as a canonical orbit through all `q` fresh
  index coordinates over successive old-period blocks?
- how does old-period monodromy compose across two successive fresh-prime
  extensions?
- is there a conserved or forbidden pattern under repeated anchor motion through a
  primorial tower?

Do not generalize to an abstract dynamical system before these exact finite
questions are answered.

---

## 9. Phase E4 — finite coverage obstruction audit

Only after a genuine tower-level transport invariant exists should the branch ask
whether it obstructs complete finite reservation of a moving square-offset window.

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

PUU-L015 remains the permanent anti-relabeling gate.

---

## 10. Legendre re-entry gate

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

## 11. Unit Universe / PowerSwap / GN reconnection

The branch began from a broader DkMath question than Legendre: primitive scales
should be understood relative to synchronized number universes.

L002–L005 provide the coordinate / common-lattice / synchronization foundation.
The current primorial geometry is its discrete finite-prime model.

Reconnect PowerSwap or GN/CosmicFormula only when the finite provider geometry has a
clear scaling statement.

Preferred direction:

```text
finite prime / phase transport geometry
    ↓
unit-relative structural invariant
    ↓
PowerSwap / GN / CosmicFormula generalization.
```

---

## 12. Current non-goals

Do not divert this branch into:

- direct proof of `SuccessorOldEscapeProvider`;
- another old-escape lower bound without an independent invariant;
- generic Jacobsthal / maximum-wheel-gap machinery;
- PNT, RH, analytic sieve, or asymptotic prime density;
- re-opening old residual-ledger refinements;
- neutral-seat primality/compositeness without a structural reason;
- prime-power modulus generalization before the squarefree tower geometry is used;
- PowerSwap / GN integration before a concrete tower transport invariant exists;
- ordered/geodesic circle distance;
- claiming `q*M` is a least period before minimality is proved;
- endless local affine lemmas that do not advance anchor / basis transport.

The branch is strongest while it stays finite, exact, and provider-side.

---

## 13. Completion criteria

This branch does **not** need a Legendre proof to be mathematically successful.

Current completion sequence:

```text
1. finite reservation / unit synchronization                 DONE
2. exact primorial wheel tower                               DONE
3. exact square-phase / CRT finite-fiber geometry            DONE
4. fresh-prime affine / reflection normal form               DONE through L025
5. representative center transport                           DONE — L026
6. one-step square-anchor transport                          DONE — L027
7. old-period / enlarged-period monodromy                     ACTIVE — L028
8. multi-level fresh-prime tower transport                    NEXT MAJOR OBJECTIVE
9. independent finite coverage-obstruction audit             FUTURE GATE
10. consumer re-entry, only if earned                        CONDITIONAL
11. Unit Universe / PowerSwap / GN generalization            CONDITIONAL
```

The central research principle remains:

```text
Do not search for a prime directly.
Formalize the finite geometry and transport that could make complete reservation
structurally impossible, and let a consumer bridge read the consequence afterwards.
```
