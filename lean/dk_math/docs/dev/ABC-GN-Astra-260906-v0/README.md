# ABC–GN Astra Campaign 260906 v0

## Purpose

This directory is the working documentation hub for a renewed attack on the
remaining ABC–GN frontier.

The campaign starts from the current `develop` branch and reuses the strongest
verified DkMath assets available after the July ABC–GN Ultra campaign,
especially:

- exact ABC square-tail / radical identities,
- intrinsic `abcEpsilon` / quality identities,
- odd-prime GN joint-pressure machinery,
- exact repeated-prime-power / GN-Wieferich interpretation,
- cubic Petal orientation,
- degree-three GN prime-shell arithmetic,
- finite arbitrary-depth simple-root Hensel lifting.

The immediate goal is **not** to claim or force an ABC proof. The first goal is
to re-open the large-boundary frontier with the new degree-three local theory,
falsify weak ideas early, and identify a genuinely stronger coupling mechanism.

## Conversation key

```text
cid: 6a9d367b-6bd8-83ee-9da0-4bb28291b80f
```

This CID identifies the ChatGPT research conversation that initiated this
campaign. Use it as the human-context key when correlating design decisions,
research notes, and later checkpoint reports.

## Branch

```text
base:   develop
branch: wip/ABC-GN-astra-260906-v0
base develop HEAD at campaign start:
cb89c5a747f0f74cc9aa10a0cc50cf97bb569ed8
```

## Current status at campaign start

The public ABC endpoint is still axiom-backed through `abc_main_axiom`.
This campaign must not use that axiom as mathematical input and must not claim
that ABC has been proved.

The July Ultra campaign already exposed the remaining difficulty very sharply:

```text
fresh non-exceptional support mass
+
non-exceptional valuation excess
        ↓
uniform joint pressure
        ↓
ABC
```

The corresponding uniform joint contract is known to have full ABC strength,
so merely re-packaging that contract is not progress.

The current large-boundary arithmetic object is exact:

```text
GNNonExceptionalRepeatedPart
  = repeated prime-power part
  = piSqRad * sqTail
  = piSqRad^2 * twoTail
```

Its support is exactly the non-exceptional GN-Wieferich support.

## New weapons

Since the July campaign, DkMath gained a degree-three local theory strong enough
to change the reconnaissance strategy:

- primitive non-ramified cubic GN primes are simple roots,
- finite Hensel correction digits are unique,
- arbitrary finite depth lifting is available,
- derivative nondegeneracy is stable under the lifted branch.

This means deep GN-Wieferich lifting itself cannot simply be declared
impossible. The new target is a **coupling obstruction**: large repeated depth
must be shown incompatible with the original ABC radical/quality geometry, or
forced into a stronger paired-orientation / descent mechanism.

## First hypotheses to investigate

### H1 — cubic orientation repeated-support disjointness

For

```text
F = GN 3 a b
G = GN 3 b a
```

the integer identities

```text
(3*b - 9*a) * F + (3*a + 5*b) * G = 14*b^3
(3*a - 9*b) * G + (3*b + 5*a) * F = 14*a^3
```

suggest that under `Nat.Coprime a b`,

```text
gcd F G ∣ 14.
```

A key candidate consequence is that no prime square can divide both cubic
orientations, hence their repeated / Wieferich prime supports are disjoint.

This must be proved or falsified before being used.

### H2 — cubic boundary exponent improvement

The current general odd-prime large-boundary estimate reaches an exponent
`3/4` at the half-weight endpoint.

At cubic exponent `p = 3`, every non-exceptional order prime satisfies
`q % 3 = 1`, hence prime `q >= 7`. Since `2^8 <= 7^3`, the cubic
root-address factor may admit a dedicated `t = 3/8` estimate of the form

```text
cubic boundary weight <= repeatedPart^(3/8).
```

This is a candidate improvement only. It must be reconstructed from the
actual current definitions and proved in Lean before being used downstream.

## Files

- [ROADMAP.md](ROADMAP.md) — current strategy and stop/go gates.
- [instruction-000.md](instruction-000.md) — read-only reconnaissance task for
  the first Astra/Codex pass.
- [report-000.md](report-000.md) — completed reconnaissance: scratch Lean proves
  orientation gcd / repeated-support separation, coprime repeated moduli, and
  the actual cubic `3/8` target weight bound. The large-profile sum and ABC
  quality coupling remain open (Outcome B).
- [scratch-000.lean.txt](scratch-000.lean.txt),
  [numeric-000.py](numeric-000.py), and
  [validation-000.txt](validation-000.txt) — replayable proof and experiment
  evidence; no production theorem is exported at ASTRA-000.
- [report-002.md](report-002.md) — realizability-aware profile foundation:
  realized large profiles, generic height admissibility, cubic height bridge,
  and exclusion of the known 7/13 ghost profile.
- [report-003.md](report-003.md) — exact realized-profile image, disjoint
  fibers, interval coverage, and cardinal partition.
- [report-004.md](report-004.md) — ghost-free exponential moment bridge with
  the realized large-boundary contribution.
- [report-005.md](report-005.md) — cubic `3/8` transfer from realized large
  fibers to the realized joint-modulus moment.
- [report-006.md](report-006.md) — extraction of distinct realized cubic
  joint moduli and the quadratic divisor bridge.
- [report-007.md](report-007.md) — ASTRA research boundary: complement,
  Pell, spacing, and incidence obstruction ledger.
- [report-008.md](report-008.md) — LUNA canonical repeated/complement
  production API and quadratic spacing foundation.
- [report-009.md](report-009.md) — LUNA Pell family and exact
  squarefull-block incidence obstruction.
- [report-010.md](report-010.md) — LUNA exact realized-modulus dyadic
  shell partition and moment bookkeeping.
- [report-011.md](report-011.md) — LUNA exact witness images, modulus fibers,
  shell partition, complement packets, and spacing.
- [report-012.md](report-012.md) — LUNA complement slices, injective incidence
  pairs, shell projections, and the exact three-way finite ledger.
- [report-013.md](report-013.md) — LUNA squareful parity decomposition and
  exact negative-Pell shell coordinates.
- [report-014.md](report-014.md) — LUNA square-cube quotient coordinates,
  squarefree Pell-parameter fibers, and the exact four-way shell ledger.
- [report-015.md](report-015.md) — LUNA primitive divisibility, support,
  coprimality, gcd, and prime-square Pell packets.
- [report-016.md](report-016.md) — LUNA exceptional-three sector normalization,
  exact gcd classification, and the two fixed-`T` normal forms.

## Research discipline

- Read current GitHub source before relying on old notes.
- Prefer theorem/counterexample outcomes over narrative plausibility.
- Use Lean scratch experiments and numerical falsification aggressively.
- Do not add a new global ABC contract unless a strictly new theorem has first
  been isolated.
- Do not use `abc_main_axiom` as an assumption.
- Do not interpret finite Hensel lifting as evidence that deep lifts disappear.
- Stop a route immediately when a concrete counterexample invalidates it.
