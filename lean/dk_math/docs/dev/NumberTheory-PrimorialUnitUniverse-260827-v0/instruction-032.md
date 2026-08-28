# PUU-L032 — Square-Phase First-Hit Radius / Generic-Shift Comparison Audit

## 0. Status / purpose

PUU-L031 completed the square-shifted survivor profile:

```text
Profile_S(n)
  = { t < M | (n^2 + t) mod M is a wheel survivor }
```

with exact cyclic translation, cardinality preservation, same-phase invariance,
and successor transport.

The new information in L031 is that the translation label is not an arbitrary
old-wheel coordinate but the square phase

```text
A_n = n^2 mod M.
```

L031 deliberately stopped before any short-prefix / first-hit claim.

PUU-L032 is an **information-gain audit** for this quadratic restriction.  Measure
the first unreserved offset for arbitrary cyclic shifts and compare it with the
first-hit behavior obtained only from reachable square shifts.

Do not import Legendre consumers.  Do not use `SquareCell`, `SquareOffset`,
`escapingSquareOffsets`, or a bound involving `2*n`.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetFirstHitAudit
```

Preferred import:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetProfile
import Mathlib.Tactic
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade
docstring.

---

## 1. Generic shifted survivor profile

L031 only defines the profile coming from a square anchor.  For the audit, add a
provider-side generic cyclic-shift profile for an arbitrary bounded wheel label
`A`.

Suggested shape:

```lean
noncomputable def genericUnreservedOffsetProfile
    (S : Finset ℕ) (A : ℕ) : Finset ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).filter
    (fun t =>
      IsPrimeBasisWheelSurvivor S
        ((A + t) % finitePrimeBasisProduct S))
```

A `primeBasisWheelSurvivors` membership version is equally acceptable.

Expose the natural membership theorem and prove that the square profile is the
generic profile at the square-value coordinate:

```text
Profile_S(n)
  = GenericProfile_S(squareAnchorWheelProjection S n).
```

This bridge should reuse L031 rather than duplicate reservation reasoning.

---

## 2. Nonemptiness and first-hit coordinate

For a nonempty finite prime basis, prove that every generic profile is nonempty.
An explicit translation to the wheel survivor `1` is acceptable; alternatively
reuse a suitable existing survivor nonemptiness theorem if one already exists.

Define the least bounded offset in a nonempty profile.  Suggested shapes:

```lean
noncomputable def genericFirstUnreservedOffset
    (S : Finset ℕ) (A : ℕ) : ℕ := ...

noncomputable def squareAnchorFirstUnreservedOffset
    (S : Finset ℕ) (n : ℕ) : ℕ := ...
```

Using `Finset.min'`, `Nat.find`, or an equivalent finite construction is fine.
Keep the hypotheses on theorems explicit rather than hiding impossible default
values in the mathematical API.

Required semantics:

```text
first < M
first belongs to the corresponding profile
all smaller offsets are not in the profile.
```

Then identify

```text
squareAnchorFirstUnreservedOffset S n
  = genericFirstUnreservedOffset S (squareAnchorWheelProjection S n).
```

Same square phase must therefore give the same first-hit coordinate.

---

## 3. Reachable square-phase labels

Define the finite set of square-value labels reachable in one old period, for
example

```lean
noncomputable def squareAnchorReachablePhaseLabels
    (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).image
    (squareAnchorWheelProjection S)
```

or an equivalent Finset.

Expose membership in a mathematically useful form:

```text
A in SquareLabels(S)
  ↔ exists n < M, squareAnchorWheelProjection S n = A.
```

Do not identify this with an abstract quadratic-residue type unless that is
already natural in the current API.

---

## 4. Generic and square-restricted worst first-hit radius

Define two finite worst-case quantities over one period:

```text
GenericRadius(S)
  = max first-hit over all A < M

SquareRadius(S)
  = max first-hit over reachable square labels A.
```

Equivalent `Finset.sup`, `max'`, or image-based definitions are acceptable.
Prove the basic comparison

```text
SquareRadius(S) <= GenericRadius(S).
```

This inequality is expected simply because square labels form a subset of all
wheel labels.  It is not yet a new obstruction.

Also prove that every square-anchor first hit is bounded by `SquareRadius(S)`.
Keep all bounds inside one old period; do not introduce `2*n`.

---

## 5. Information-gain audit: strictness is not automatic

This checkpoint must determine whether the quadratic restriction gives a
**uniform strict improvement** over arbitrary shifts.

Use small exact regressions to prevent overclaiming.

### Required `{2,3}`, `M=6` regression

Wheel survivors are `{1,5}`.  Verify through the public first-hit API that

```text
GenericRadius({2,3}) = 3
SquareRadius({2,3})  = 2.
```

Thus square restriction is genuinely informative for this basis.

A visible witness is:

```text
arbitrary shift A=2  has first hit 3,
while the worst reachable square phase has first hit 2.
```

### Required `{2,3,5}`, `M=30` regression

Verify through the same public API that

```text
GenericRadius({2,3,5}) = 5
SquareRadius({2,3,5})  = 5.
```

A square phase reaches a generic worst case; for example `12^2 mod 30 = 24`, and
starting from label `24` the next wheel survivor is reached after five steps.

This regression is important: it rules out the blanket theorem

```text
SquareRadius(S) < GenericRadius(S)
```

for all finite prime bases.

If Lean discovers that either numerical expectation above is wrong, record the
actual exact values instead of forcing the expected regression.

---

## 6. Required verdict

The report must explicitly choose the strongest supported verdict.

### Outcome A — UNIFORM-SQUARE-FIRST-HIT-IMPROVEMENT

Use this only if a genuinely general theorem stronger than
`SquareRadius <= GenericRadius` is proved under a natural provider-side hypothesis.
A finite example of strictness is not enough.

### Outcome B — QUADRATIC-RESTRICTION-REAL-BUT-NONUNIFORM

Expected if the audit proves:

```text
SquareRadius <= GenericRadius
```

and exhibits both

```text
strict improvement for some finite basis,
no improvement for another finite basis.
```

This means square-phase restriction carries real information, but square phase
alone does not provide a uniform coverage obstruction.

### Outcome C — NO-FIRST-HIT-INFORMATION

Use only if even the square-restricted first-hit family collapses completely to
arbitrary shifts in every tested/proved sense.

Outcome B is a successful A+ checkpoint if proved exactly.

---

## 7. STOP boundary

Do **not** proceed in this checkpoint to:

- `t <= 2*n` or any square-cell bound;
- Legendre or `escapingSquareOffsets`;
- generic Jacobsthal / wheel-gap theory;
- asymptotic estimates;
- PNT / RH / analytic sieve;
- PowerSwap / GN / CosmicFormula;
- prime powers;
- claims that square restriction always improves the first hit;
- basis growth tied to the anchor `n`.

The purpose is to isolate exactly how much information **square phase alone** adds.

---

## 8. Report

Create:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
primorial-unit-universe-square-phase-first-hit-audit-260828.md
```

The report must state:

1. generic shifted profile definition;
2. first-hit semantics;
3. reachable square-phase labels;
4. generic vs square-restricted worst radius;
5. exact `{2,3}` regression;
6. exact `{2,3,5}` regression;
7. the information-gain verdict;
8. whether square phase alone is sufficient to justify continuing toward a
   coverage obstruction.

If Outcome B holds, explicitly state that the next useful interaction must add
something beyond square phase alone — for example basis growth / another coupled
coordinate — rather than more first-hit identities.

---

## 9. A+ criteria

A+ requires all of:

- [ ] generic shifted survivor profile;
- [ ] bridge from L031 square profile to generic shift at `n^2 mod M`;
- [ ] profile nonemptiness;
- [ ] exact least/first-hit API;
- [ ] first-hit membership and minimality;
- [ ] same-phase first-hit invariance;
- [ ] reachable square-label Finset;
- [ ] generic worst first-hit radius;
- [ ] square-restricted worst first-hit radius;
- [ ] theorem `SquareRadius <= GenericRadius`;
- [ ] `{2,3}` strict regression;
- [ ] `{2,3,5}` equality regression;
- [ ] explicit information-gain verdict;
- [ ] no consumer / gap / analytic escalation.
