# FLT7TC-005R29 — Norm-prime to distinct prime ideals above q

## Scope

This report records the implementation work for `instruction-035.md`.  The
target is the current square packet from R28 and the actual ring of integers
`𝓞 SevenRealCubic.Field`; historical prime-support packets and any FLT
closure claim remain out of scope.

## Initial audit

- R28 already provides `IsCoprime r s`, the scalar/product identities, and
  positivity of the two current model norms.
- Mathlib provides
  `Ideal.absNorm_span_singleton` and
  `Ideal.exists_isMaximal_dvd_of_dvd_absNorm'`.  The latter returns
  `P.IsMaximal`, `P.under ℤ = Ideal.span {(q : ℤ)}`, and `P ∣ I`.
- In a Dedekind domain, `Ideal.dvd_iff_le` converts this ideal divisibility
  into the reverse-inclusion relation needed to expose generator membership.
- `Ideal.primesOver` is the set of prime ideals lying over the rational
  prime ideal, so two distinct maximal ideals give the requested cardinality
  lower bound.
- The model-to-ring-of-integers equivalence is available as
  `SevenRealCubic.modelEquivRingOfIntegers`.  The norm transport must be
  checked explicitly; no element-level assertion is being promoted to a
  rational norm-support assertion.

## Scratch verification plan

The scratch file will check the exact norm transport, principal-ideal
absolute norm identity, ideal-divisor membership conversion, coprime
transport, distinctness, and the `ncard` lower bound before the public API is
facaded.

## Implementation log

Further entries are appended as each focused check completes.

## Initial scratch check

The persistent scratch file confirms the exact use of
`Algebra.norm_eq_of_equiv_equiv` together with the explicit three-coordinate
determinant calculation.  This establishes

`Algebra.norm ℤ (modelEquivRingOfIntegers x) = SevenRealCubicInt.norm x`

without asserting any rational prime support for the element itself.

## Production implementation

Added `PrimeTraceOneDirectRealCubicSquareIdealSupport.lean` with:

- the principal-ideal absolute norm bridge for the current model elements;
- conversion from ideal divisibility to membership of the actual ring of
  integers;
- transport of R28 coprimality through the model/ring-of-integers
  equivalence;
- two maximal prime ideals above a common rational norm prime, with the two
  principal-ideal divisibility statements and a kernel-checked proof that the
  ideals are distinct;
- the resulting lower bound
  `2 ≤ (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Field)).ncard`.

The facade import and API/axiom audit files were added.  The production file
elaborated successfully; Lean emitted only the existing-style `letI` linter
warning for the local maximal-ideal instance.

## Verification results

All checks were run sequentially:

1. `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport`
   completed successfully.
2. `lake build DkMath.FLT.Seven` completed successfully with the new facade
   import.
3. The public API test elaborated successfully.
4. The axiom audit reported only
   `[propext, Classical.choice, Quot.sound]` for each of the five new public
   declarations.
5. The persistent scratch file elaborated successfully and rechecked the
   norm-transport and Mathlib theorem signatures.
6. Source scans found no `sorry`, `admit`, `unsafe`, or `axiom` declaration in
   the production/source scratch files; the only `axioms` matches are the
   intentional audit commands.  The tracked and newly added files passed
   whitespace checks.

R29 is therefore recorded as a completed ideal-support layer for a supplied
common norm prime.  No complete-splitting or FLT-closure statement was added.


## Outcome

**Outcome B — COMMON NORM PRIME -> TWO DISTINCT PRIMES ABOVE q GREEN;
COMPLETE-SPLITTING BRIDGE IS NEXT.**

The current production theorem reaches two distinct maximal ideals above the
same rational prime and the lower bound on primesOver cardinality. It does not
yet prove the real cubic field is Galois at the field level, complete
splitting, or the residue criterion q ≡ ±1 (mod 7).
