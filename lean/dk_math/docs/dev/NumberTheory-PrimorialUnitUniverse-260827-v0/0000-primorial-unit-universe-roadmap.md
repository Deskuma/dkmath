# NumberTheory Primorial Unit Universe — Roadmap

> Revised: 2026-08-28 after PUU-L032
>
> Branch: `wip/number-theory-primorial-unit-universe-260827-v0`

## 0. Branch purpose

This branch was opened after closing the Legendre finite-support / residual-ledger
route.  Its purpose is **not** to rename Legendre's conjecture and prove the
renamed statement.  The purpose is to build an independent finite arithmetic
provider, audit its information content, and only then ask what a consumer can
read from it.

Current hierarchy:

```text
finite prime basis / reservation
        ↓
unit-relative synchronization
        ↓
primorial finite-wheel tower
        ↓
square-anchor phase / CRT geometry
        ↓
fresh-prime affine geometry
        ↓
representative / anchor transport
        ↓
mixed-radix tower coordinates
        ↓
INFORMATION AUDIT — coordinate route closed
        ↓
square-value × offset-profile interaction
        ↓
first-hit information audits
        ↓
additional independent coupling, if needed
        ↓
finite coverage obstruction, if one exists
        ↓
consumer re-entry
        ↓
possible Unit Universe / PowerSwap / GN generalization
```

Legendre remains a **consumer / audit target**, not the foundational layer.

---

## 1. Permanent anti-relabeling gate — PUU-L011–L015

PUU-L011–L014 built the exact square-offset / primorial-wheel bridge and
successor-threshold classification.  PUU-L015 then proved

```text
SuccessorOldEscapeProvider ↔ LegendreConjecture.
```

Therefore the exact old-escape criterion is not an independent provider route.

Permanent rule:

- do not rename square-shell escape and call it a provider;
- do not treat a bound for the exact old-escape criterion as new information
  unless it follows from an independently proved provider invariant;
- Legendre re-entry is allowed only after the provider theorem already exists
  inside `PrimorialUniverse`.

---

## 2. PowerSwap / GN status

PowerSwap / GN / CosmicFormula integration is **deferred, not failed**.
Reconnect it only after the finite provider layer produces a clear scaling or
unit-relative invariant.

Preferred later order:

```text
finite provider invariant
    ↓
transport / scaling theorem
    ↓
PowerSwap / GN / CosmicFormula connection, if structurally natural
```

---

## 3. Implemented architecture

### Phase A — finite reservation and unit synchronization — COMPLETE

- **L001** finite reservation escape;
- **L002** unit-coordinate refinement;
- **L003** common lattice;
- **L004** unit-intersection classification;
- **L005** finite-prime synchronization.

### Phase B — finite wheel tower — COMPLETE

- **L006** wheel survivor / reduced-residue reflection;
- **L007** fresh-prime raw lifts / unique deletion;
- **L008** exact survivor replication by factor `q-1`;
- **L009** nested wheel projection and exact projection fibers;
- **L010** square-anchor and square-shell projection dynamics.

### Phase C — Legendre consumer bridge — COMPLETE / CLOSED

- **L011** square-offset / primorial-wheel bridge;
- **L012** successor threshold decomposition;
- **L013** old-basis escape / deletion-capacity comparison;
- **L014** twin-threshold exception;
- **L015** exact old-escape frontier equivalence audit.

Status: consumer reduction limit reached.  This route stays closed until a
new provider invariant exists independently.

### Phase D — square-anchor phase / CRT / affine geometry — COMPLETE

- **L016** square-anchor phase symmetry;
- **L017** local prime-sign dichotomy;
- **L018** mixed-sign CRT synthesis;
- **L019** coprime phase fiber as a Boolean sign cube;
- **L020** fresh-prime phase-fiber two-sheet cover;
- **L021** phase cover as a two-seat subcover of the `q-1` survivor fiber;
- **L022** `+a / 0 / -a` lift-index trichotomy;
- **L023** affine midpoint geometry;
- **L024** reflection involution and neutral two-cycles;
- **L025** affine normal form with constant phase radius.

Core static form:

```text
center C(b) = -b / M
radius R(a) =  a / M
phase pair  = C(b) ± R(a)
```

### Phase E1 — representative transport — COMPLETE

**L026** introduced the canonical deleted center and rigid phase translation:

```text
C(b₂) - C(b₁) = (b₁-b₂) / M.
```

### Phase E2 — moving square-anchor transport — COMPLETE

**L027** separated

```text
anchor coordinate       r_n = n mod M
square-value coordinate     = n² mod M = r_n² mod M
```

and proved exact successor dynamics with a `0/1` carry:

```text
Δcenter = carry_n - M⁻¹
Δradius = M⁻¹
Δplus   = carry_n
Δminus  = carry_n - 2*M⁻¹.
```

### Phase E3 — period / mixed-radix tower coordinates — COMPLETE

**L028** identified the block quotient `Q_S(n)=n/M`, proved

```text
Pplus_n = Q_S(n)  in ZMod q,
```

and obtained `(+1,-1)` old-period monodromy with closure after `q` old periods.

**L029** introduced

```text
digit_q(n) = Q_S(n) mod q
```

and proved the mixed-radix decomposition

```text
n = r_S(n)
    + digit_q(n) * M
    + Q_(insert q S)(n) * (q*M),
```

with the enlarged canonical representative equal to the actual old raw lift at
that digit.

---

## 4. L030 information audit — COMPLETE / COORDINATE ROUTE CLOSED

Verdict:

```text
Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET
```

Every admissible mixed-radix pair is realized by the explicit anchor

```text
n = r + d*M,
```

and enlarged reservation reduces exactly to old reservation plus the existing
fresh-prime unique-deletion rule.

Therefore the pure coordinate / quotient / digit route is **closed as a source
of new obstruction**.  L016–L030 remain the complete coordinate language, but
more equivalent coordinate identities do not count as new provider information.

---

## 5. Phase F1 — square-value / offset-profile coupling — COMPLETE

### PUU-L031 — Square-Shifted Survivor Offset Profile

Define

```text
Profile_S(n)
  = { t < M | ¬ ReservedByPrimeBasis S (n²+t) }.
```

L031 proves the exact translated-survivor form

```text
t ∈ Profile_S(n)
  ↔ t < M ∧ ((n² mod M)+t) mod M is a wheel survivor.
```

Consequences:

- `|Profile_S(n)| = |WheelSurvivors(S)|`;
- same square phase gives identical profiles;
- successor transport is the cyclic shift by the odd increment `2*n+1`.

Information verdict:

```text
new information = square-phase-dependent cyclic translation only.
```

Whole-period cardinality and transport do not by themselves give a short-prefix
or first-hit obstruction.

---

## 6. Phase F2 — square-phase first-hit audit — COMPLETE

### PUU-L032 — Square-Phase First-Hit Radius / Generic-Shift Comparison

L032 compares arbitrary cyclic labels with labels reachable as

```text
A_n = n² mod M.
```

It defines generic and square-restricted first-hit radii and proves

```text
SquareRadius(S) ≤ GenericRadius(S).
```

Exact finite regressions:

```text
S={2,3}, M=6:
  GenericRadius = 3
  SquareRadius  = 2

S={2,3,5}, M=30:
  GenericRadius = 5
  SquareRadius  = 5
  reachable square label 24 attains the generic worst case.
```

Verdict:

```text
Outcome B — QUADRATIC-RESTRICTION-REAL-BUT-NONUNIFORM
```

Square phase is genuine information, but square phase alone does not give a
uniform first-hit obstruction.

### Important semantic note after L032

The L032 statistic allows offset `t=0`.  That is correct for the defined cyclic
first-hit quantity, but `t=0` is the square-anchor seat itself.  Before using
first-hit data as a forward short-prefix statistic, the anchor seat must be
excluded explicitly.

---

## 7. Phase F3 — positive-offset first-hit audit — ACTIVE

### PUU-L033 — Positive-Offset First-Hit / Anchor-Seat Exclusion Audit

Define the least strictly positive cyclic hit `H⁺(A)` and its generic / square
worst-case radii.

Required semantics:

```text
0 < H⁺(A) ≤ M
(A + H⁺(A)) mod M is a wheel survivor
no smaller positive offset is a survivor.
```

Required finite regressions:

```text
S={2,3}, M=6:
  GenericPositiveRadius = 4
  SquarePositiveRadius  = 4

S={2,3,5}, M=30:
  GenericPositiveRadius = 6
  SquarePositiveRadius  = 6
```

The audit asks whether the L032 quadratic gain survives after excluding the
anchor seat.

Expected verdict if both equalities are formalized:

```text
Outcome B — ANCHOR-SEAT-GAIN-COLLAPSES
```

If so, close **square-phase-alone first-hit refinement** and add a genuinely
independent coupling next.  Preferred candidates are successor-pair dynamics
or basis growth, using the positive-offset statistic.

---

## 8. Next information gate after L033

Do not choose the next route merely because another identity is available.
After the positive-offset audit, require an interaction absent from a single
square phase.

Primary candidate:

```text
successor pair
  (n² mod M, (n+1)² mod M)
```

with the exact relation

```text
(n+1)² - n² = 2*n+1.
```

The desired question is whether two adjacent square anchors can simultaneously
support long positive reserved prefixes.  This is different information from
the single-phase radius.

Alternative candidate:

```text
basis growth S -> insert q S
```

but only if the theorem uses more than the already-audited unique-deletion
coordinate law.

---

## 9. Legendre re-entry gate

Legendre-specific work may resume only if a theorem satisfies all of:

1. it is naturally stated in `DkMath.NumberTheory.PrimorialUniverse`;
2. it does not import the Legendre consumer layer;
3. it does not assume `SquareCell`, `escapingSquareOffsets`,
   `SuccessorOldEscapeCriterion`, or an equivalent prime witness;
4. it follows from independently proved finite wheel / square / transport
   geometry;
5. only after proving it do we ask what it implies for square shells.

If the translated consumer statement is again merely equivalent to Legendre,
record that fact and close the route.

---

## 10. Current non-goals

Do not divert this branch into:

- direct proof of `SuccessorOldEscapeProvider`;
- renamed square-shell escape criteria;
- more mixed-radix identities without new information content;
- generic Jacobsthal / maximum-wheel-gap machinery as the primary route;
- PNT / RH / analytic sieve / asymptotic density;
- neutral-seat primality/compositeness without a structural reason;
- prime-power modulus generalization before the squarefree geometry is used;
- PowerSwap / GN integration before a concrete finite invariant exists;
- least-period claims not already proved;
- endless local affine or first-hit lemmas.

---

## 11. Completion sequence

```text
1. finite reservation / unit synchronization                 DONE
2. exact primorial wheel tower                               DONE
3. square-phase / CRT finite geometry                        DONE
4. fresh-prime affine normal form                            DONE
5. representative transport                                 DONE
6. one-step square-anchor transport                          DONE
7. old-period / fresh-prime monodromy                        DONE
8. mixed-radix static/dynamic identification                 DONE
9. mixed-radix information audit                             DONE — Outcome B
10. pure coordinate refinement route                         CLOSED
11. square-value / offset-profile coupling                   DONE — L031
12. square-phase first-hit audit                              DONE — L032 / Outcome B
13. positive-offset first-hit audit                           ACTIVE — L033
14. additional independent coupling                          NEXT GATE
15. finite coverage obstruction                              CONDITIONAL
16. consumer re-entry                                        CONDITIONAL
17. Unit Universe / PowerSwap / GN generalization            CONDITIONAL
```

Central research principle:

```text
Do not search for a prime directly.
Build an independent finite structure, audit whether it really excludes anything,
and only then let a consumer read the consequence.
```
