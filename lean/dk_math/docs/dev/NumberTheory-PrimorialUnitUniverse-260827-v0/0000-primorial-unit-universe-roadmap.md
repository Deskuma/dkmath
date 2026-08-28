# NumberTheory Primorial Unit Universe — Roadmap

> Revised: 2026-08-28 after PUU-L030
>
> Branch: `wip/number-theory-primorial-unit-universe-260827-v0`

## 0. Branch purpose

This branch was opened after closing the Legendre finite-support / residual-ledger route.
Its purpose is **not** to rename Legendre's conjecture and prove the renamed statement.
The purpose is to build an independent finite arithmetic provider and only later ask what a consumer can read from it.

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
INFORMATION AUDIT
        ↓
square-value × offset-profile interaction
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

A seat is reserved when some basis prime divides it.
Every basis prime divides `M(S)`, hence `M(S)+1` is not reserved by any member of `S`.
Any prime divisor of `M(S)+1` is therefore fresh.

```text
finite basis S
    ↓
period M(S)
    ↓
Euclid escape M(S)+1
    ↓
new prime divisor q ∉ S
```

This is a global finite escape principle. It does **not** by itself place a prime inside a prescribed short interval.
The branch seeks an independent finite structural layer between global escape and local consumer statements.

---

## 2. Permanent anti-relabeling gate — PUU-L011–L015

PUU-L011–L014 built the exact square-offset / wheel bridge and successor-threshold classification.
PUU-L015 then proved

```text
SuccessorOldEscapeProvider ↔ LegendreConjecture.
```

Therefore a proof of that exact old-escape criterion is not an independent provider route.

Permanent rule:

- do not rename square-shell escape and call it a provider;
- do not treat a lower bound for the exact old-escape criterion as new information unless it follows from an independently proved provider invariant;
- Legendre re-entry is allowed only after the provider theorem already exists inside `PrimorialUniverse`.

---

## 3. PowerSwap / GN status

PowerSwap / GN / CosmicFormula integration is **deferred, not failed**.
The current branch first builds and audits the finite provider geometry.

Preferred later order:

```text
finite provider invariant
    ↓
transport / scaling theorem
    ↓
PowerSwap / GN / CosmicFormula connection, if structurally natural
```

---

## 4. Implemented architecture

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

Status: consumer reduction limit reached. This route stays closed until a genuinely new provider invariant exists.

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

**L026** introduced the canonical deleted center and proved rigid translation of the phase pair under old-representative change:

```text
C(b₂) - C(b₁) = (b₁-b₂) / M.
```

### Phase E2 — moving square-anchor transport — COMPLETE

**L027** separated

```text
anchor coordinate      r_n = n mod M
square-value coordinate     = n² mod M = r_n² mod M
```

and proved the exact successor dynamics with `0/1` carry:

```text
Δcenter = carry_n - M⁻¹
Δradius = M⁻¹
Δplus   = carry_n
Δminus  = carry_n - 2*M⁻¹.
```

### Phase E3 — period / mixed-radix tower coordinates — COMPLETE

**L028** identified the old-period block quotient

```text
Q_S(n) = n / M
```

and proved

```text
Pplus_n = Q_S(n)  in ZMod q.
```

One old-period turn gives monodromy

```text
center fixed
radius +1
plus   +1
minus  -1
```

and `q` old-period turns close at the enlarged period `q*M`.

**L029** introduced the fresh-prime mixed-radix digit

```text
digit_q(n) = Q_S(n) mod q
```

and proved

```text
Q_S(n) = digit_q(n) + q * Q_(insert q S)(n)
```

and

```text
n = r_S(n)
    + digit_q(n) * M
    + Q_(insert q S)(n) * (q*M).
```

The enlarged canonical representative is exactly the old raw lift at that digit:

```text
r_(insert q S)(n)
  = primeBasisWheelLift S (r_S(n)) (digit_q(n)).
```

Moreover the dynamic plus sheet, fresh-prime digit, actual raw plus-lift index, and enlarged projection-fiber representative are all the same coordinate description.

---

## 5. PUU-L030 information audit — COMPLETE

### Verdict

```text
Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET
```

L030 proved the mixed-radix coordinate system is complete, not restrictive.

For every admissible pair

```text
0 ≤ r < M
0 ≤ d < q
```

the explicit anchor

```text
n = r + d*M
```

realizes

```text
r_S(n) = r
digit_q(n) = d
r_(insert q S)(n) = primeBasisWheelLift S r d.
```

Thus every raw coordinate occurs.

Reservation also reduces exactly to the existing fresh-prime deletion rule:

```text
Reserved_(insert q S)(r+dM)
  ↔ Reserved_S(r) ∨ q ∣ (r+dM).
```

Over an old survivor, exactly one digit is deleted.

### Consequence

The pure coordinate / quotient / digit transport route is now **CLOSED as a source of new obstruction**.

L016–L030 remain valuable as a complete finite coordinate system, but no theorem in that route excludes an admissible raw coordinate or forces a new coverage obstruction.

Do not continue with more equivalent quotient/digit identities unless a later interaction requires them.

---

## 6. Revised research question after L030

The question is no longer

```text
Can mixed-radix transport itself forbid a coordinate?
```

L030 answered: no.

The next question is:

> What extra restriction appears when the complete coordinate system is forced to pass through the square-value geometry `n²` and a simultaneous offset reservation profile?

This adds a genuine interaction absent from the free mixed-radix grid.

For one old period,

```text
t ↦ n² + t mod M
```

selects the reservation profile seen from the square anchor.
The translation parameter is not arbitrary data: it is the square phase

```text
A_n = n² mod M.
```

This is the next provider-side information source to audit.

---

## 7. Phase F1 — square-value / offset-profile coupling — ACTIVE

### PUU-L031 — Square-Shifted Survivor Offset Profile / Quadratic Translation Coupling

Define the one-period unreserved offset profile

```text
Profile_S(n)
  = { t < M | ¬ ReservedByPrimeBasis S (n²+t) }.
```

The immediate targets are:

```text
t ∈ Profile_S(n)
  ↔ squareShellWheelProjection S n t is a wheel survivor
```

and the exact cyclic-translation description

```text
Profile_S(n)
  = inverse-translate(WheelSurvivors(S), n² mod M).
```

Consequences to formalize:

- whole-period cardinality is preserved;
- same square phase gives the same whole offset profile;
- `n -> n+1` transports the profile by the odd square increment `2*n+1` modulo `M`.

This checkpoint must **not** ask for a short-prefix escape yet.

The purpose is to reintroduce square-value information after the L030 free-coordinate audit.

---

## 8. Phase F2 — short-prefix / first-hit information audit — FUTURE GATE

Only after L031 should the branch ask whether quadratic translation restricts the beginning of the profile in a way that is stronger than generic wheel geometry.

Potential provider-side questions:

```text
For a square-phase translation, how long can the initial reserved run be?
Does restricting translation parameters to square phases improve the generic worst-case profile?
Does successor transport force incompatible long reserved prefixes at adjacent anchors?
```

This phase must not immediately set the prefix length to the Legendre shell width and call the result a provider.

Preferred order:

```text
square-shifted finite profile
    ↓
generic first-hit / prefix statistic
    ↓
information-gain audit
    ↓
only then compare with a consumer window
```

Generic Jacobsthal machinery is still not the preferred route; the point is to exploit the **quadratic restriction on the translation parameter**, not arbitrary wheel gaps.

---

## 9. Legendre re-entry gate

Legendre-specific work may resume only if a theorem satisfies all of:

1. it is naturally stated in `DkMath.NumberTheory.PrimorialUniverse`;
2. it does not import the Legendre consumer layer;
3. it does not assume `SquareCell`, `escapingSquareOffsets`, `SuccessorOldEscapeCriterion`, or an equivalent prime witness;
4. it follows from wheel / phase / square-value / transport geometry;
5. only after proving it do we ask what it implies for square shells.

If the translated consumer statement is again merely equivalent to Legendre with no new provider information, record that fact and close the route.

---

## 10. Unit Universe / PowerSwap / GN reconnection

The branch still serves the broader DkMath objective of primitive scales relative to synchronized number universes.

L002–L005 provide the unit/common-lattice synchronization foundation.
The current primorial construction is its finite squarefree prime model.

Reconnect PowerSwap / GN / CosmicFormula only when a finite provider theorem has a clear scaling or unit-relative interpretation.

---

## 11. Current non-goals

Do not divert this branch into:

- direct proof of `SuccessorOldEscapeProvider`;
- another renamed old-escape criterion;
- more mixed-radix coordinate identities without new information content;
- generic Jacobsthal / maximum-wheel-gap machinery as the primary route;
- PNT / RH / analytic sieve / asymptotic density;
- neutral-seat primality/compositeness without a structural reason;
- prime-power modulus generalization before the squarefree geometry is used;
- PowerSwap / GN integration before a concrete finite invariant exists;
- least-period claims not already proved;
- endless local affine lemmas.

The branch is strongest while it stays finite, exact, provider-side, and explicit about information gain.

---

## 12. Completion criteria

This branch does **not** need a Legendre proof to be mathematically successful.

Current sequence:

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
11. square-value / offset-profile coupling                   ACTIVE — L031
12. short-prefix / first-hit information audit               FUTURE GATE
13. consumer re-entry                                        CONDITIONAL
14. Unit Universe / PowerSwap / GN generalization            CONDITIONAL
```

Central research principle:

```text
Do not search for a prime directly.
Build an independent finite structure, audit whether it really excludes anything,
and only then let a consumer read the consequence.
```
