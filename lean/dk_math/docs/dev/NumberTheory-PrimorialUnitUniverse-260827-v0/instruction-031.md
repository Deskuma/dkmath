# PUU-L031 — Square-Shifted Survivor Offset Profile / Quadratic Translation Coupling

## 0. Status / purpose

PUU-L030 completed the mixed-radix information audit with

```text
Outcome B — COORDINATE-COMPLETE / NO-OBSTRUCTION-YET.
```

The pure coordinate / quotient / digit transport route is therefore closed as an obstruction source: every bounded `(old coordinate, fresh digit)` pair is realized, and enlarged reservation reduces exactly to the existing old-reservation / fresh-prime-deletion rule.

The next checkpoint must add a genuinely new interaction rather than another coordinate identity.

Return to the square-value layer from PUU-L010 / PUU-L016.  For a moving anchor `n`, shell offsets are not arbitrary enlarged coordinates; they appear through

```text
n^2 + t.
```

Modulo an old finite basis product `M`, the complete one-period non-reservation profile is therefore the wheel-survivor set viewed through the square-dependent translation

```text
t ↦ n^2 + t mod M.
```

PUU-L031 should formalize this **square-shifted survivor profile** and its exact dependence on square phase.  This is a provider-side finite theorem only.  Do not ask yet whether a short prefix of the profile is nonempty.

Preferred module:

```lean
DkMath.NumberTheory.PrimorialUniverse.SquareAnchorOffsetProfile
```

Preferred imports:

```lean
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseMixedRadixAudit
import DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhase
```

Export through `DkMath.NumberTheory.PrimorialUniverse` and update the facade docstring.

---

## 1. One-period square-shell unreserved profile

Define a finite set of offsets in one old period.  A suggested shape is

```lean
noncomputable def squareAnchorUnreservedOffsetProfile
    (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (finitePrimeBasisProduct S)).filter
    (fun t => ¬ ReservedByPrimeBasis S (n ^ 2 + t))
```

An equivalent `Fin (M)` / `ZMod M` representation is acceptable if it makes cyclic translation cleaner.  Keep a public natural-offset membership theorem in either case.

Expose:

```text
t ∈ profile(S,n)
  ↔ t < M ∧ ¬ ReservedByPrimeBasis S (n^2+t).
```

Under `S.Nonempty`, connect membership to the existing wheel-survivor projection API:

```text
t ∈ profile(S,n)
  ↔ t < M ∧
    IsPrimeBasisWheelSurvivor S (squareShellWheelProjection S n t).
```

Reuse `squareShell_not_reserved_iff_projection_survivor`; do not duplicate its divisibility proof.

---

## 2. Exact cyclic-translation description

The central theorem should say that the whole profile is the inverse cyclic translate of the old wheel-survivor set by the square anchor coordinate.

Conceptually, with

```text
A_n := squareAnchorWheelProjection S n = n^2 mod M,
```

the profile is

```text
Profile_S(n)
  = { t in [0,M) | (A_n + t) mod M ∈ WheelSurvivors(S) }.
```

This can be exposed as an exact membership theorem if Finset equality is awkward.

Preferred public theorem concept:

```lean
squareAnchorUnreservedOffsetProfile_mem_iff_translated_survivor
```

with the right side explicitly using

```lean
(squareAnchorWheelProjection S n + t) % M.
```

The point is that the offset profile is not an independent new set: it is a **cyclic translation of the fixed survivor pattern**.

If convenient, define a reusable cyclic-translation operator on one-period Finsets / `Fin M` and prove an actual Finset equality.

---

## 3. Cardinality preservation

Because cyclic translation is a permutation of one period, prove that for nonempty finite prime basis the square-shifted unreserved profile has the same cardinality as the wheel survivor set:

```text
|Profile_S(n)| = |WheelSurvivors(S)|.
```

Preferred theorem:

```lean
card_squareAnchorUnreservedOffsetProfile
```

Do not introduce Euler-phi if not already needed.  The theorem should be stated using the existing `primeBasisWheelSurvivors` cardinality.

This is a whole-period statement only; it says nothing about how early the first unreserved offset occurs.

---

## 4. Same-square-phase profile invariance

Package the pointwise L016 reservation invariant as equality of whole profiles:

```lean
SameSquareAnchorPhase S a b
  -> Profile_S(a) = Profile_S(b).
```

Preferred theorem:

```lean
squareAnchorUnreservedOffsetProfile_eq_of_samePhase
```

Reuse `not_reservedByPrimeBasis_square_add_iff_of_sameAnchorPhase`.

This should make explicit that the one-period offset profile factors through square phase rather than the full anchor coordinate.

---

## 5. Successor translation law

PUU-L010 gives

```text
A_(n+1) = (A_n + (2*n+1)) mod M.
```

Derive the corresponding profile transport:

```text
Profile_S(n+1)
```

is the cyclic translate of `Profile_S(n)` by the negative odd increment `2*n+1` modulo `M`.

The exact API may be a pointwise equivalence, e.g. conceptually

```text
t ∈ Profile_S(n+1)
  ↔ ((t + (2*n+1)) mod M) ∈ Profile_S(n)
```

or the inverse orientation, provided the sign/orientation is verified carefully.

Preferred theorem name:

```lean
squareAnchorUnreservedOffsetProfile_succ_transport
```

Do not guess the sign: derive it from `squareShellWheelProjection_eq_anchor_add` and `squareAnchorWheelProjection_succ` and make the regression test verify the orientation.

---

## 6. Quadratic-phase restriction / information-content statement

Record the conceptual difference from PUU-L030:

```text
raw mixed-radix coordinates: every bounded coordinate occurs
square-shell profiles: translation parameter is A_n = n^2 mod M
```

Thus the reachable profiles are indexed by square phases, and anchors in the same square phase give identical profiles.

Do **not** yet claim that this restriction forces a short-offset escape or improves a wheel-gap bound.

A lightweight theorem showing that the profile map factors through `SameSquareAnchorPhase` is sufficient; Section 4 already provides the main formal content.

---

## 7. Visible `{2,3}` regression

Use `S={2,3}`, `M=6` and at least two anchors whose square phases differ, plus one reflected same-phase pair.

Suggested visible checks:

```text
n=1: A=1
n=2: A=4
n=5: A=1
```

so `n=1` and `n=5` must have identical offset profiles, while `n=2` gives the corresponding different cyclic shift.

Also verify one successor step to fix the orientation of the odd-increment translation law.

Use public profile / phase / successor APIs rather than only `norm_num` on raw divisibility.

---

## 8. Boundary / anti-relabeling gate

This checkpoint must remain provider-side.

Do not import or define:

- `DkMath.NumberTheory.Legendre` consumers;
- `SquareCell`;
- `SquareOffset` / `escapingSquareOffsets`;
- a bound such as `t ≤ 2*n` as a theorem target;
- square-shell prime existence;
- generic Jacobsthal / maximum wheel-gap machinery;
- neutral-seat primality / compositeness;
- PNT / RH;
- PowerSwap / GN / CosmicFormula.

The new information is **quadratic translation coupling of the whole finite reservation profile**, not a short-interval conclusion.

---

## 9. A+ criteria

PUU-L031 is A+ if it provides:

1. a public one-period square-shell unreserved offset profile;
2. exact membership equivalence to translated wheel survivors;
3. whole-period cardinality preservation;
4. equality of profiles for same square phase;
5. exact successor profile translation by the odd square increment;
6. a visible `{2,3}` regression checking phase equality and translation orientation;
7. no Legendre / escape / generic gap conclusion.

Report to:

```text
lean/dk_math/docs/dev/NumberTheory-PrimorialUnitUniverse-260827-v0/
primorial-unit-universe-square-shifted-survivor-offset-profile-260828.md
```

At the end of the report, explicitly state whether L031 has produced any information beyond:

```text
fixed wheel-survivor pattern + square-phase-dependent cyclic translation.
```

If not, say so.  The following checkpoint should then audit the **short-prefix / first-hit interaction of quadratic shifts**, not add more whole-period translation identities.
