# FLT7TC-005R30 — Real-cubic Galois bridge and complete splitting of common norm primes

## Scope

This report records the implementation work for `instruction-036.md`.  The
target is the current R29 ideal-support theorem, the actual ring of integers
of `SevenRealCubic.Field`, and the field-level cyclic Galois/splitting API.
The residue criterion `q ≡ ±1 (mod 7)`, historical routing packets, and FLT7
closure remain outside this checkpoint.

## Initial audit

- R29 currently proves two distinct maximal ideals above every supplied common
  norm prime and the corresponding `primesOver` cardinality lower bound.
- The previous report's classification is corrected here to Outcome B: R29 is
  the two-prime stage, not complete splitting.
- The existing code exposes
  `SevenRealCubic.ringOfIntegersRotateEquiv` and the theta orbit identities;
  the field extension must be constructed through the fraction-field API.
- The exact Mathlib names and hypotheses for fraction-field ring equivalences,
  polynomial splitting, `Normal`, `IsGalois`, and the Galois prime-decomposition
  formula are being checked before production edits.

## Scratch verification plan

The persistent scratch file will first check the field-rotation construction,
its rational-algebra commutation, order-three/nontriviality facts, cubic root
transport, and the relevant Galois/ramification theorem signatures.  Each
successful experiment will be recorded below.

## Implementation log

- The persistent scratch compiled after checking the fraction-field ring
  equivalence, its `ℚ`-algebra commutation, root transport under an algebra
  equivalence, the generator-fixing extensionality lemma, and a cubic split
  proof by extracting one linear factor and applying
  `Polynomial.Splits.of_natDegree_eq_two` to the quadratic quotient.
- The production file now exports the fraction-field rotation
  `SevenRealCubic.fieldRotateEquiv`, its integer compatibility, order-three
  action, and nontriviality.  The nontriviality witness is the explicit
  `alphaInteger` orbit and is kernel-checked.
- The actual ring-of-integers ideal
  `SevenRealCubic.P7 = Ideal.span {thetaI}` is proved prime and maximal.  The
  transported identity `span {(7 : O)} = P7 ^ 3` gives uniqueness of the
  prime above `(7)` and `primesOver.ncard = 1`.
- The R29 principal-ideal norm and membership bridges are reused to prove
  separately that `7` divides neither current square-root norm.  The
  separate public results are
  `directOrbitSquareRefinement_gapSquareRoot_not_seven_norm_dvd` and
  `directOrbitSquareRefinement_quotientSquareRoot_not_seven_norm_dvd`.
- The field roots `theta0`, `theta1`, and `theta2` are transported by the
  field rotation and proved pairwise distinct.  The mapped cubic polynomial
  is proved split in the field; the splitting-field instance then supplies
  `Normal ℚ Field` and `IsGalois ℚ Field`.
- The Mathlib Galois prime-decomposition identity is instantiated for
  `ℤ ⊂ 𝓞 Field` and `Gal(Field / ℚ)`.  Combining its right-hand side
  `Nat.card = 3` with R29's lower bound `ncard ≥ 2` proves, for every supplied
  common norm prime, `ncard = 3` and both ramification and inertia indices are
  one.  The residue congruence audit remains intentionally unimplemented.

## Focused validation log

- `lake env lean DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean` passed.
- `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareGaloisSupport` passed as a single Lean build.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareGaloisSupportScratch.lean` passed; only the existing deprecated ramification import and minor linter warnings remain.
- `lake build DkMath.FLT.Seven` passed as the sequential facade build.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareGaloisSupportApi.lean` passed and printed the intended public rotation, ideal-support, root, splitting, Galois, and complete-splitting declarations.
- `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSquareGaloisSupportAxiom.lean` passed.  The audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; no project-specific axiom was introduced.
- The forbidden-construct scan over production, scratch, and API files found no `sorry`, `admit`, `unsafe`, or `axiom`.  `git diff --check` and no-index whitespace checks for the new files were clean.
