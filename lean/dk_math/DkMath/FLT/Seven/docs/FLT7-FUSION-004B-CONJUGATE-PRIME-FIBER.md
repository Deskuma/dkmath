# FLT7-FUSION-004B conjugate-prime fibre checkpoint

Date: 2026-07-30

Repository: `Deskuma/dkmath`  
Pull request: `#74`  
Base branch: `develop`  
Work branch: `wip/FLT7-fusion-004b-conjugate-fiber-260730`  
Starting merge checkpoint: `bac2a3b1f5881a4341138e7d47429c98ca9ca4b1`

## Completion status

NORMAL / N1 is complete with Outcome A.

Lean now proves:

```text
P * Pbar <= realPrimeFiberIdeal
realPrimeFiberIdeal = P * Pbar
ConjugatePrimeFiberProductEqualityObligation
```

The proof uses the explicit quadratic `re/im` coordinates. The two kernel
equations are evaluation at `ratio` and `ratio⁻¹`; exact order seven separates
those roots, forcing both coordinates into the common real-cubic kernel.

See
`FLT7-FUSION-004B-CONJUGATE-PRIME-FIBER-REPORT.md`.
The additive/global N2 work has not begun.

## Purpose

PR #73 completed the first FLT7-FUSION expedition through exact prime-load
allocation, exact real-cubic valuation, finite global load factorization, and
the first concrete degree-six orientation layer.

This checkpoint isolates the single local obligation left at that boundary.
It must continue from the existing concrete carrier and prime-address packets;
it must not restart from the original Fermat equation or replace the proved
orientation data with a weaker abstract model.

## Inherited Lean facts

For every canonical `CyclotomicLinearPrimeAddress`, the implementation has:

- the real-cubic evaluation kernel `p`;
- the oriented degree-one maximal kernel `P`;
- the conjugate degree-one maximal kernel `Pbar`;
- `P ≠ Pbar`;
- `P ⊔ Pbar = ⊤`;
- both contractions to the same real-cubic kernel `p`;
- both contractions to `(q)` over `ℤ`;
- residue quotient cardinality `q` for both kernels;
- opposite membership of the oriented and conjugate linear carriers.

The extended real prime is

```text
realPrimeFiberIdeal = Ideal.map ofReal p.
```

Lean already proves

```text
realPrimeFiberIdeal <= P * Pbar.
```

## FUSION-004B initial obligation

The exact remaining proposition is

```text
ConjugatePrimeFiberProductEqualityObligation
```

and is equivalent to the reverse containment

```text
P * Pbar <= realPrimeFiberIdeal.
```

The initial target is therefore the exact equality

```text
realPrimeFiberIdeal = P * Pbar.
```

An equivalent finite-index, quotient-cardinality, explicit quadratic-fibre,
or contraction-extension theorem is acceptable only if it preserves the
existing oriented prime data and closes the same equality without adding it as
an assumption.

## Stop boundary

Completing the fibre equality finishes the local degree-six orientation
checkpoint. It does not by itself provide:

- a proof that the carrier is the full degree-six ring of integers;
- a primitive reconstructed integer or quadratic Fermat chart;
- positivity and primitive coprimality for a new FLT7 triple;
- a strict well-founded decrease;
- an inhabited descent provider;
- terminal contradiction;
- FLT7.

After the equality is proved, the additive reconstruction frontier must be
reviewed again before the next implementation stage is selected.

## Execution plan

The approved budget strategy is documented in:

```text
FLT7-FUSION-004B-ULTRA-ROADMAP.md
```

The directly executable Codex contract is:

```text
FLT7-FUSION-004B-CODEX-EXECUTION-INSTRUCTIONS.md
```

The completed run was fixed to:

```text
EXECUTION_MODE = NORMAL
ACTIVE_PHASE   = N1
```

Ultra is reserved for the later global oriented/additive reconstruction
frontier.  It must not be activated for the current local reverse-containment
lemma unless the NORMAL run proves that the local problem hides a genuinely
new major mathematical layer and records that exact obstruction.
