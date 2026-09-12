# FLT prime-generalization Phase 5 — Gauss cyclotomic form to TraceOne adapter

## Scope and outcome

This report implements the bounded contract in `instruction-005.md`.  The
phase adds the neutral algebraic adapter between

```text
4 * V = R^2 - discr s * S^2
```

and a `TraceOneInt s` norm.  It does not construct coordinates for every odd
prime, modify the FLT3/FLT5/FLT7 proof towers, or claim a general FLT result.

The result is `PGEN-GAUSS-ADAPTER-GREEN`: the neutral adapter and the finite
`p = 3, 5, 7, 11, 13` normalization checks compile.  The arbitrary-prime
Gaussian-period to integral-coordinate construction remains unformalized.

## Part A — neutral TraceOne adapter

Extended:

```text
DkMath/NumberTheory/TraceOneDiscriminantAxis.lean
```

with the following production theorems:

```text
norm_eq_of_discriminant_form
discriminant_form_of_norm_eq
norm_eq_of_gauss_coordinates
```

The forward theorem uses the existing exact identity

```text
4 * norm ⟨A,B⟩ = (2*A+B)^2 - discr s * B^2
```

and cancels the nonzero integer factor `4`.  The converse packages the same
identity from a norm equality.  No positivity or sign assumption is used.

The Gauss-coordinate theorem is division-free: it takes
`hR : R = 2*A + S` and the quadratic form identity, then produces
`norm ⟨A,S⟩ = V`.  Thus the integral half-coordinate is explicit rather than
being hidden behind rational division.

## Part B — signed discriminant packet boundary

The existing
`PrimeDiscriminantPacket.discr_eq_or_neg` theorem is reused.  It derives

```text
discr s = (p : ℤ) ∨ discr s = -(p : ℤ)
```

from `Nat.Prime p` and `Int.natAbs (discr s) = p`; no unsafe signed Nat
formula is added to the packet.

The concrete probe signs are recorded and proved directly:

```text
discr (-3) = -11
discr 3 = 13
```

These are the `p = 11` and `p = 13` instances of the expected signed
discriminant pattern.  No generic proof of
`(-1)^((p-1)/2) * p` is claimed here.

## Part C — p=11 and p=13 adapter paths

Updated:

```text
DkMathTest/FLT/Prime/QuadraticCyclotomicBridgeProbe.lean
```

The existing coordinate polynomials are retained:

```text
A11 = z^5 - z^3*y^2 + z^2*y^3 - z*y^4 - y^5
B11 = z^4*y + z*y^4

A13 = z^6 + 2*z^4*y^2 - z^3*y^3 + 2*z^2*y^4 + y^6
B13 = z^5*y + z^3*y^3 + z*y^5
```

The probe now defines

```text
R11 = 2*A11 + B11, S11 = B11
R13 = 2*A13 + B13, S13 = B13
```

and proves:

```text
4 * GTailCyclotomicShell 11 (z-y) y
  = R11^2 - (-11) * S11^2

4 * GTailCyclotomicShell 13 (z-y) y
  = R13^2 - 13 * S13^2
```

It also proves the parity relations `R11-S11=2*A11` and
`R13-S13=2*A13`, together with the endpoint identities
`(z-y)+y=z`.

The main `norm11` and `norm13` theorem paths now call
`norm_eq_of_gauss_coordinates`.  The former direct polynomial proofs remain
as `norm11_direct` and `norm13_direct` regression checks.

## Part D — p=3, p=5, p=7 normalization audit

Updated:

```text
DkMathTest/FLT/Prime/TraceOneDiscriminantAxisCompatibility.lean
```

The existing bridge theorems are not rewritten.  Instead, each is followed by
the neutral `four_mul_traceOneNorm_eq_discriminant` identity:

- `S0_nat_eq_traceOneNorm_negOne` gives the `D = -3` form;
- `goldenNorm_eq_traceOneNorm_one` gives the `D = 5` form;
- `cyclotomicSeven_eq_traceOneNorm_negTwo` gives the `D = -7` form.

This is a normalization audit of the already-proved finite family, not a
refactor of any FLT3/FLT5/FLT7 tower.

## Part E — pinned Mathlib boundary

The pinned Mathlib source exposes relevant Gauss-sum and character facts,
including:

- `gaussSum`, `gaussSum_mul_gaussSum_eq_card`, `gaussSum_sq`,
  `MulChar.IsQuadratic.gaussSum_frob`, `Char.card_pow_char_pow`, and
  `Char.card_pow_card` in `Mathlib.NumberTheory.GaussSum`;
- `ZMod.euler_criterion`, `legendreSym.eq_pow`, and the Legendre-symbol
  character API in `Mathlib.NumberTheory.LegendreSymbol.Basic`;
- `ZMod.gauss_lemma` and `ZMod.eisenstein_lemma` in
  `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas`;
- `quadraticChar_card_card`, `quadraticChar_odd_prime`, and
  `FiniteField.isSquare_odd_prime_iff` in
  `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`;
- `Polynomial.cyclotomic_prime`,
  `Polynomial.cyclotomic_prime_mul_X_sub_one`, and
  `Polynomial.cyclotomic_prime_pow_eq_geom_sum` in the pinned cyclotomic
  polynomial API.

Classification: `PGEN-GAUSS-DERIVABLE` for the bounded audit.  The character,
Gauss-sum, and prime cyclotomic-shell infrastructure is present, but Mathlib
does not provide the required integral coordinate construction.

The remaining theorem is a genuine mathematical adapter, not a missing
definition:

```text
for every odd prime p, construct integral homogeneous R_p,S_p with
4 * GTailCyclotomicShell p (z-y) y
  = R_p(z,y)^2 - D_p * S_p(z,y)^2,
D_p = (-1)^((p-1)/2) * p,
and prove R_p - S_p = 2*A_p.
```

The missing formal bridge is the quadratic-residue/nonresidue
Gaussian-period construction, its integral coordinates, and its norm/form
identity.  The finite p=11 and p=13 polynomial witnesses do not supply that
arbitrary-prime construction.

## Verification

The required focused builds passed:

```text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisAxiomAudit
```

The axiom audit includes the three new adapter declarations and reports only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is present.
Changed production and test sources contain no `sorry` or `axiom` construct.
`git diff --check` is green.

No general FLT theorem or arbitrary-prime cyclotomic coordinate theorem is
claimed.
