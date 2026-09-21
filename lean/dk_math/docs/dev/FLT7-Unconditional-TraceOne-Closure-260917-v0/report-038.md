# FLT7TC-005R32 — Cube-defect normal form

## Scope

This report records the R32 implementation of the arithmetic normal form attached
to the current square-refinement packet.  The attached instruction is the
implementation contract; it does not enlarge the user request into a search for
a contradiction or a successor/descent theorem.

## Initial audit

- The current source already provides `R * S = a^3`, positivity of the two
  square-root norms, and `R^2 < a`.
- R31 provides the current-packet theorem that a prime common to `R` and `S` is
  `1` or `6` modulo `7`; it does not provide `gcd R S = 1`.
- Mathlib provides the natural-number factorization ledger, prime-factor finite
  products, and squarefree factorization criteria needed for a finite-product
  construction.
- The implementation will use one common finite prime support for `R` and `S`.
  This keeps the complementary `D1,D2` kernels literally identical on both
  sides, including primes occurring only in the cubic part of `S`.

## Scratch result 1

`DkMathTest/FLT/SevenCubeDefectScratch.lean` now kernel-checks the finite
factor-product lemmas for:

- the modulo-three exponent identity;
- the complementary exponent identity from `eR + eS = 3 * ea`;
- `R = D1 * D2^2 * U^3`;
- `S = D1^2 * D2 * V^3` using the same filtered defect products;
- squarefreeness of each defect product and coprimality of `D1,D2`.

The scratch build was run sequentially with:

    lake build DkMathTest.FLT.SevenCubeDefectScratch

The remaining work is to move these neutral arithmetic lemmas into a production
module, add the valuation/support and height applications, then instantiate the
current FLT7 packet.

## Scratch / verification log

Further entries are appended as the implementation and sequential Lean checks
progress.

## Current status

The production module `DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCubeDefect`
now contains the finite factorization ledger and the current-packet
instantiation.  The generic theorem constructs positive `D1,D2,U,V` with
the required two norm factorizations, squarefreeness, coprimality,
`D1 * D2 ∣ gcd R S`, exceptional-prime support, and the height inequality.

The current packet theorem transports these fields to
`DirectOrbitCubeDefectPacket` using the R31 common-prime residue theorem.
The facade export and dedicated API/axiom audit files were added.

## Sequential verification

- `lake build DkMathTest.FLT.SevenCubeDefectScratch`: passed.
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCubeDefect`: passed;
  only existing-style deprecation/unused-simp-argument warnings remain.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCubeDefectApi`:
  passed; all public definitions and the current-packet constructor are
  visible.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCubeDefectAxiom`:
  passed; the audited declarations report only `propext`, `Classical.choice`,
  and `Quot.sound`.
- `lake build DkMath.FLT.Seven`: passed with the new facade export.
- The final scratch rebuild passed again.  A targeted scan found no `sorry`,
  `admit`, or `unsafe` in the new production, API, and scratch files, and
  `git diff --check` passed.

## Outcome

**Outcome B — cube-defect normal form and `±1 mod 7` support are kernel-checked.**
The implementation does not derive `D1 = D2 = 1`, rational norm
coprimality, a contradiction, or FLT7 closure.  The R32 endpoint is the
normal-form packet required by the instruction.
