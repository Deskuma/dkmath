# FLT7 current state freeze

This is the compact restart point for the closed FLT7-specific branch.
The project-local directory containing this file is the canonical checkpoint
document directory.

## A. Kernel-checked Core

### C = 1 branch

The final usable endpoint consists of the exact Thomas F5 realization, the
deep-S / `7^8` structure, the Thomas unit in `SevenRealCubic`, and the checked
finite-Hensel power extraction.  Fixed-`n = 6` Thomas completeness remains
external and unclosed.

### C > 1 branch

The final usable endpoint contains:

- `q ∣ c` implies `q % 7 = 1`;
- the Kummer-compatible prime sieve;
- `q ≥ 379`, `c ≥ 379`, and `379 * u^5 < v`;
- quotient/gap orientation and ratio/inverse orientation;
- real Kummer phase/inversion blindness;
- the phase-corrected degree-six linear carrier;
- exact current/conjugate kernel ownership;
- the selected real factor;
- selected-factor uniqueness;
- real-prime fibre equality;
- exact selected-factor multiplicity `14 * eQ` with `eQ > 0`.

These are the final specialized local facts consumed by the R64 Outcome B
endpoint.

## B. Explicitly deferred FLT7-only work

The following four obligations are DEFERRED, not TODO items for this branch:

- degree-six carrier exact upper cutoff — DEFERRED;
- global aggregation of oriented degree-six prime powers — DEFERRED;
- terminal contradiction — DEFERRED;
- final FLT7 theorem — DEFERRED.

No FLT7-specific implementation of these obligations belongs after this
freeze.

## C. Closed routes

Do not reopen these routes without genuinely new input:

- the naive `q % 28` multiplication route;
- real Kummer phase as an orientation detector;
- pure finite-Hensel iteration without a strict successor;
- reuse of the historical signed-root terminal contradiction;
- treating arbitrary residue-field equivalence as Galois-canonical.

## D. Re-entry condition

FLT7 work may resume only after a genuinely GENERAL theorem supplies new
input that specializes to one of the four deferred FLT7 obligations.  The
general target and required order are in `GENERALIZATION_HANDOFF.md`.
