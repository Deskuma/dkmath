# FLT7TC-005R34 — Cyclic Galois orbit and exact 1-to-2 common-prime allocation

## Scope

This report records the R34 implementation work under the attached
instruction. The checkpoint is restricted to the Galois orbit, rotation/
membership orientation, the two-gap-primes forcing step, and the exact
one-versus-two cardinality result. Norm valuation equalities and the canonical
`C,U,V` normal form are outside this checkpoint.

## Initial audit

- R33 exports the actual ring-of-integers principal-ideal split,
  ideal-coprimality, `q ∣ a`, and the exclusive allocation xor for every prime
  above a common norm prime.
- R30 exports complete splitting, `primesOver.ncard = 3`, and unit
  ramification/inertia indices for every common norm prime.
- R27 exports the exact three-term square-twisted additive equation and the
  nonzero/unit facts for its coefficients and rotated roots.
- The Galois support file already defines the order-three field automorphism,
  its restriction to the ring of integers, and the `IsGalois` instance.

## Scratch / verification log

The exact Galois action type and membership orientation are recorded here as
they are kernel-checked. Mathlib's ideal action is the inverse/comap action:

```text
Ideal.pointwise_smul_eq_comap
  : sigma • P = Ideal.comap (RingEquiv.symm (... sigma)) P
```

Consequently the production membership bridge is oriented as

```text
model (rotate x) ∈ sigma • P ↔ model x ∈ P.
```

The reusable scratch file
`DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicPrimeAllocationScratch.lean`
kernel-checks the order-three actor, the ring-action transport, the concrete
rotation membership equivalences, the squared-action form, the two-root
forcing argument, and the distinct-prime address alternative.

## Implemented results

- Exposed `directOrbitGaloisSigma := fieldRotateEquiv`, its order-three and
  nonidentity facts, the three-element classification, and the equality of
  its ring-of-integers action with `ringOfIntegersRotateEquiv`.
- Added concrete model rotation and one-/two-step membership transport lemmas.
- Added `directOrbitGalois_distinct_prime_address`, giving the two possible
  sigma-addresses for distinct primes above the same rational prime, and
  `directOrbitGalois_prime_orbit_eq_primesOver` for the full Galois orbit.
- Added `directOrbit_two_rotated_gap_roots_mem_imp_all_three_mem`; it maps the
  R27 identity into the ring of integers, uses only ideal membership and unit
  coefficients, and obtains the third root by prime-ideal radicality.
- Added `directOrbit_two_gap_primes_imp_all_gap`; two distinct gap primes force
  every prime above the common norm prime to be a gap prime. R33 xor together
  with the R29 quotient witness then gives a singleton gap set.
- Added the public cardinality theorems
  `directOrbitSquareRefinement_common_prime_gap_ncard` and
  `directOrbitSquareRefinement_common_prime_quotient_ncard`, proving the exact
  `1` and `2` counts by the R30 three-prime split and the R33 xor partition.

## Verification log

- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation`
  passed after the production proof repairs.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicPrimeAllocationApi.lean`
  passed with the R34 actor, transport, forcing, address, orbit, and
  cardinality exports.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicPrimeAllocationAxiom.lean`
  passed; the new theorems report only the repository's existing
  `propext`, `Classical.choice`, and `Quot.sound` dependencies.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicPrimeAllocationScratch.lean`
  passed with warnings only from intentional exploratory `#check` output and
  local proof-shape linting.
- `lake build DkMath.FLT.Seven` passed, confirming the public FLT7 facade
  still builds with the R34 production import surface.
- `git diff --check` passed. The untracked report and scratch files were also
  checked with `git diff --no-index --check`; both produced no whitespace
  diagnostics.
- The R34 production, API, axiom, scratch, and report files contain no
  `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom` declarations.

## Current status

R34 is implemented through the exact 1-to-2 allocation endpoint. No
valuation, canonical `C,U,V`, successor/descent, or FLT7 contradiction claim
is made here.
