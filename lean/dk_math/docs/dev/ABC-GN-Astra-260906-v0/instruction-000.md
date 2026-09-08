# instruction-000 — ABC–GN Astra reconnaissance

## Role

Act as a research mathematician and Lean 4 investigator inside the current
DkMath workspace.

This is a **reconnaissance checkpoint**, not a production implementation
checkpoint.

The purpose is to determine which parts of the proposed new cubic attack are
actually true in the current library and which are false, redundant, or blocked
by a sharper obstruction.

## Repository / branch

```text
repository: Deskuma/dkmath
branch:     wip/ABC-GN-astra-260906-v0
base:       develop
campaign directory:
  lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/
```

At the beginning, verify the actual branch HEAD and compare it with current
`develop`. Record the SHA in the report.

## Read first

Read these current source files before searching broadly:

```text
lean/dk_math/DkMath/ABC/GNExcessLargeBoundaryPacket.lean
lean/dk_math/DkMath/ABC/GNWieferichAccumulation.lean
lean/dk_math/DkMath/ABC/GNCubicPetalWieferich.lean
lean/dk_math/DkMath/ABC/GNCubicOrientedContract.lean
lean/dk_math/DkMath/ABC/GNJointContractEquivalence.lean

lean/dk_math/DkMath/NumberTheory/GNThreePrimeArithmetic.lean
lean/dk_math/DkMath/NumberTheory/GNThreeHenselLift.lean
lean/dk_math/DkMath/NumberTheory/GNThreeHenselDepth.lean
lean/dk_math/DkMath/NumberTheory/GNWieferich.lean
```

Also inspect imports and nearby theorems as needed.

Do not trust old checkpoint prose when it disagrees with current Lean source.

## Hard restrictions

1. Do **not** use `DkMath.ABC.abc_main_axiom` as an assumption.
2. Do **not** modify `ABCMainTheorem.lean`.
3. Do **not** add a new global ABC contract in this checkpoint.
4. Do **not** claim ABC has been proved.
5. Do **not** assume GN-Wieferich lifts are rare or impossible.
6. Do **not** interpret finite Hensel uniqueness as a global density theorem.
7. Production Lean modules under `DkMath/ABC` should remain unchanged during
   this checkpoint unless a tiny temporary experiment absolutely requires a
   local tracked file. Prefer scratch files outside the tracked tree.

## Task A — reconstruct the exact current frontier

Report the exact current theorem chain for:

```text
repeated prime-power part
  ↔ repeated support
  ↔ non-exceptional GN-Wieferich support
  ↔ large-boundary modulus
```

Identify:

- the exact target profile mass,
- the exact root-address charge,
- the current `3/4` boundary estimate,
- where the large-profile **sum** remains open,
- whether any later file already improves this estimate.

Do not infer from names; quote theorem identifiers.

## Task B — cubic orientation identity

Let

```text
F := GN 3 a b
G := GN 3 b a
```

Verify in exact algebra:

```text
(3*b - 9*a) * F + (3*a + 5*b) * G = 14*b^3
(3*a - 9*b) * G + (3*b + 5*a) * F = 14*a^3
```

Because these coefficients can be negative, an `Int` formulation is likely
cleaner than `Nat`.

Then investigate and, if true, prove in a scratch Lean file a theorem of the
mathematical form:

```text
Nat.Coprime a b
  -> Nat.gcd (GN 3 a b) (GN 3 b a) ∣ 14.
```

A different but equivalent `Int.gcd` / divisibility formulation is acceptable
if it is substantially easier and transports cleanly back to `Nat`.

### Consequence audit

Determine whether the gcd result really implies:

```text
for every prime q,
  not (q^2 ∣ GN 3 a b and q^2 ∣ GN 3 b a).
```

Then determine whether this transports to:

```text
Disjoint
  (GNNonExceptionalWieferichPrimeSet 3 a b)
  (GNNonExceptionalWieferichPrimeSet 3 b a)
```

under the positivity/coprimality hypotheses required by the current API.

If an exceptional prime such as `2` or `7` requires special handling,
identify it exactly instead of hiding it.

## Task C — mandatory counterexample / regression search

Check the concrete coprime triple:

```text
a = 605
b = 370688
c = 371293
```

Verify exactly:

- `a + b = c`,
- `Nat.Coprime a b`,
- factorization of `GN 3 a b`,
- factorization of `GN 3 b a`,
- repeated-prime sets in both orientations.

The expected regression pattern is:

```text
both orientations have repeated prime powers,
but the repeated-prime supports are not the same.
```

If the stated numeric example is wrong, say so and replace it with a correct
small example found by exact search.

Also search for counterexamples to each stronger tempting claim:

- one orientation is always squarefree,
- one orientation is always Wieferich-free,
- both repeated moduli cannot be large,
- repeated-support disjointness itself.

The goal is to kill false claims now.

## Task D — cubic `3/8` boundary-weight experiment

Inspect the current definitions behind

```text
GNExcessRootAddressCharge
GNExcessActiveProfileMass
GNNonExceptionalRepeatedPart
GNExcess_target_boundaryWeight_le_repeatedPart_rpow
```

Do not invent a new surrogate quantity.

Specialize to exponent `p = 3`.

Verify that every active non-exceptional support prime satisfies the exact
current theorem needed to derive:

```text
q % 3 = 1
```

and hence, for prime `q`,

```text
7 <= q.
```

Then test whether the existing proof architecture supports the dedicated
inequality at `t = 3/8`:

```text
rootAddressCharge *
  exp ((3/8) * activeProfileMass)
<=
  (GNNonExceptionalRepeatedPart 3 a b : ℝ) ^ (3/8).
```

A `1/2` endpoint may be proved first as a sanity check.

The key per-prime arithmetic to validate is:

```text
2^8 <= q^3
```

for every active cubic prime `q`.

Do not report success from a paper derivation alone. Attempt a Lean scratch
proof using the current exact definitions.

## Task E — small-profile compatibility reconnaissance

Read the local / finite Euler-product theorems used by the existing half-weight
small-profile estimate.

Answer:

1. Is the parameter fixed syntactically at `1/2`, or is there already a
   general parameter?
2. Would `3/8` make the local geometric decay stronger?
3. What is the smallest theorem surface needed to specialize the existing
   machinery to `3/8`?
4. Would this be a small refactor or a rebuild of the old tower?

Do not implement the refactor yet.

## Task F — paired-orientation feasibility

Using the results from B–E, assess whether the next meaningful checkpoint
should be:

```text
A. orientation gcd / repeated-support disjointness production theorem

B. cubic 3/8 boundary theorem

C. paired-orientation CRT profile experiment

D. abandon this route because a counterexample destroys the expected gain
```

Do not choose by aesthetics. Choose by the strongest verified new information.

## Lean experimentation rules

You may use:

- `#check`,
- `#print`,
- small `example` theorems,
- `ring`, `ring_nf`, `omega`, `norm_num`,
- temporary definitions,
- exact finite numeric calculations,
- local helper lemmas.

Prefer a temporary scratch Lean file outside tracked production modules.

If a useful proof only works because an imported theorem already assumes a
research contract equivalent to ABC, flag that dependency and reject the proof
for this campaign.

## Required output

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v0/report-000.md
```

The report must contain:

1. branch / HEAD / inspected files,
2. exact current frontier theorem map,
3. result of Task B,
4. result of numeric falsification/regression tests,
5. result of the `3/8` Lean experiment,
6. small-profile parameter audit,
7. all counterexamples found,
8. exact remaining obstruction,
9. recommendation for `instruction-001.md`,
10. one of these outcomes:

```text
Outcome A — new theorem path survives and is ready for production
Outcome B — partial theorem survives but main gain is unproved
Outcome C — proposed route is false / redundant; pivot required
Outcome D — existing library already contains the needed result
```

## Success criterion

This checkpoint succeeds even if the proposed attack fails.

A high-quality counterexample or a precise proof that the `3/8` estimate does
not help the large-profile sum is a successful result.

The only unacceptable result is to move into a long implementation chain
without first determining what is actually true.
