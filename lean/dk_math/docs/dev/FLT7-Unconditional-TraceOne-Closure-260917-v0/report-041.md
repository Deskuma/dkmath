# FLT7TC-005R35 — exact norm valuations and canonical common factor

## Scope

This report records the R35 investigation and the kernel-checked results as
they are obtained.  R34 supplies the exact one-versus-two ideal allocation;
R35 requires its multiplicity and norm-exponent transport, followed by the
canonical `C = gcd R S` normal form.

## Initial investigation

- The R32 cube-defect packet is a neutral factorization ledger.  It records
  `R.factorization q + S.factorization q = 3 * a.factorization q`, but it does
  not by itself identify the canonical common factor.
- Mathlib exposes the required ideal-theoretic map formula through
  `emultiplicity_map_eq_ramificationIdx'_mul` and the principal-ideal bridge
  through `Ideal.multiplicity_span_eq_multiplicity` and
  `Nat.multiplicity_eq_factorization`.
- The R30 complete-split theorem supplies ramification index and inertia degree
  one for the common norm-prime surface.  The R29 absolute-norm bridge is
  available for the two principal square-root ideals.

## Implementation log

Further entries are appended below after each focused experiment or validated
production change.

### Production Part A and Part B

Added `PrimeTraceOneDirectRealCubicCanonicalCommonFactor.lean` and exported it
through `DkMath.FLT.Seven`. The production scalar theorem
`directOrbitCanonicalCommonFactor_scalar_ideal_multiplicity` proves, for every
prime ideal `P` above a common norm prime, the exact coefficient
`multiplicity P (span {a}) = a.factorization q`. It uses the scalar ideal map,
the R30 ramification-index-one result, integer ideal multiplicity, and the
factorization API.

The production theorem
`directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities` combines
the R33 principal-ideal product and xor with `emultiplicity_mul`. It exports
the two exclusive alternatives: the gap side has coefficient `m` and quotient
side coefficient `0`, or conversely, where `m = a.factorization q`.

The focused production build passed. The canonical `C,U,V` packet and the
ideal-norm to natural-factorization transport remain the next frontier; no
global norm-exponent equality is asserted from cardinality alone.

### Outcome

**Outcome C.** The common-prime ideal multiplicity layer is kernel-checked.
The precise remaining frontier is transporting the ideal multiplicities to
global `Nat.factorization` coefficients of the two absolute norms, after which
the canonical common-factor construction can be implemented without changing
the R32 packet.

### Scratch validation: principal-ideal scalar multiplicity

The focused scratch theorem now compiles for a common norm prime `q` and every
prime ideal `P` above `(q)`.  It uses `Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul`, converts the integer principal-ideal multiplicity with `Ideal.multiplicity_span_eq_multiplicity`, and closes the scalar exponent with `Int.multiplicity_natAbs` followed by `Nat.multiplicity_eq_factorization`.  The ramification factor is discharged from R30's complete-split theorem, so this is an ideal-theoretic valuation proof rather than a consequence of `R*S=a^3`.

### Verification

- `lake build DkMath.FLT.Seven` passed.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorApi` passed and printed both public theorem types.
- `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorAxiom` passed; both public theorems depend only on `[propext, Classical.choice, Quot.sound]`.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCanonicalCommonFactorScratch.lean` passed with a linter warning only.
- `git diff --check` and the corresponding `git diff --no-index --check` checks reported no whitespace errors for the new production, test, scratch, and report files; the forbidden-construct scan found no matches in the new Lean source files.
