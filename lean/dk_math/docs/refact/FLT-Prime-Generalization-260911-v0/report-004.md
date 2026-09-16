# FLT prime-generalization Phase 4 — TraceOne discriminant axis and quadratic cyclotomic bridge probe

## Scope and outcome

This report implements the bounded contract in `instruction-004.md`.  The
work stops at a neutral prime-discriminant `TraceOneInt` layer and two explicit
cyclotomic probes.  It does not generalize the full cyclotomic field, alter
the proved FLT3/FLT5/FLT7 endpoints, or claim a general FLT theorem.

The result is `PGEN-TRACEONE-AXIS`: the arithmetic of `2 * tau - 1`, its
sign-safe finite depth, and its terminal peel are generic under an explicit
prime-absolute-discriminant packet.  The arbitrary-prime quadratic
cyclotomic bridge remains open.

## Part A — generic discriminant-axis production API

Added:

```text
DkMath/NumberTheory/TraceOneDiscriminantAxis.lean
```

in namespace `DkMath.NumberTheory.TraceOneQuadratic`.  The module imports only
the neutral `TraceOneQuadratic` layer and generic `padicValNat` support; it
does not import any Seven module.

The following identities are proved for
`discrAxis s := 2 * tau s - 1`:

```text
discrAxis s = ⟨-1, 2⟩
discrAxis s ^ 2 = ofInt s (discr s)
conj (discrAxis s) = -discrAxis s
norm (discrAxis s) = -discr s
trace (discrAxis s * ⟨c,d⟩) = discr s * d
discrAxis s ∣ x ↔ discr s ∣ trace x
```

The converse divisibility proof uses the requested explicit witness
`⟨2 * s * k - a, k⟩`.

`PrimeDiscriminantPacket p s` contains exactly the bounded input data
`Nat.Prime p` and `Int.natAbs (discr s) = p`.  From it the module proves:

```text
(p : ℤ) ∣ norm x ↔ (p : ℤ) ∣ trace x
discrAxis s ∣ x ↔ p ∣ Int.natAbs (norm x)
```

The proof uses
`4 * norm x = trace x ^ 2 - discr s * x.snd ^ 2`, integer primality, and a
separate exclusion of the factor `2`; it does not assume that the indefinite
`s = 1` norm is positive.

## Part B — finite powers and terminal depth

Added the sign-safe depth

```text
discrAxisDepth p x := padicValNat p (Int.natAbs (norm x))
```

under the packet, with these results:

```text
Int.natAbs (norm (discrAxis s ^ n)) = p ^ n
discrAxis s ^ n ∣ x ↔ p ^ n ∣ Int.natAbs (norm x)
norm x ≠ 0 →
  (discrAxis s ^ n ∣ x ↔ n ≤ discrAxisDepth p x)
```

`exists_terminal_discrAxis_core` supplies a quotient after the maximal
finite depth.  It proves nonzero residual norm, absence of another axis
factor, absence of a residual `p` factor in the natural absolute norm, exact
natural norm factorization, and `1 ≤ Int.natAbs (norm y)`.  The only required
nonzero hypothesis is `norm x ≠ 0`.

## Part C — existing concrete families and Seven compatibility

Added:

```text
DkMathTest/FLT/Prime/TraceOneDiscriminantAxisCompatibility.lean
```

The test constructs packets for the three audited concrete samples:

```text
p = 3, s = -1, discr s = -3
p = 5, s =  1, discr s =  5
p = 7, s = -2, discr s = -7
```

For `p = 7`, it verifies `discr (-2) = -7`, its natural absolute value,
`discrAxis (-2) = sevenAxis`, generic one-layer and finite-power divisibility,
generic valuation depth, and equality with `sevenAxisDepth`.

The existing concrete bridge surface remains available and was compiled:

```text
DkMath.FLT.S0_nat_eq_traceOneNorm_negOne
DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one
DkMath.FLT.Seven.cyclotomicSeven_eq_traceOneNorm_negTwo
DkMath.FLT.Seven.sevenAxis_pow_dvd_iff_pow_seven_dvd_norm
DkMath.FLT.Seven.sevenAxis_pow_dvd_iff_le_sevenAxisDepth
```

These remain a proved 3-sample family (`s = -1, 1, -2`), not an arbitrary
prime cyclotomic theorem.  Existing Seven wrappers were retained.

## Part D — explicit `p = 11` and `p = 13` probes

Added:

```text
DkMathTest/FLT/Prime/QuadraticCyclotomicBridgeProbe.lean
```

For `p = 11`, `s = -3`, the specified coordinates

```text
A11 = z^5 - z^3*y^2 + z^2*y^3 - z*y^4 - y^5
B11 = z^4*y + z*y^4
```

are proved to satisfy the `s = -3` trace-one norm identity, both against
`GTailCyclotomicShell 11 (z - y) y` and against its expanded homogeneous
degree-10 shell.

For `p = 13`, `s = 3`, the specified coordinates

```text
A13 = z^6 + 2*z^4*y^2 - z^3*y^3 + 2*z^2*y^4 + y^6
B13 = z^5*y + z^3*y^3 + z*y^5
```

are proved analogously against `GTailCyclotomicShell 13 (z - y) y` and the
expanded homogeneous degree-12 shell.  Both probes explicitly record the
endpoint identity `(z - y) + y = z`.

These are exact finite polynomial identities.  They are probes only; no
arbitrary-prime coordinate construction is inferred from them.

## Mathlib API audit and missing bridge

The pinned Mathlib sources expose the following relevant declarations:

- `Mathlib.NumberTheory.GaussSum`: `gaussSum`,
  `gaussSum_mul_gaussSum_eq_card`, `gaussSum_sq`,
  `MulChar.IsQuadratic.gaussSum_frob`,
  `MulChar.IsQuadratic.gaussSum_frob_iter`, `Char.card_pow_char_pow`,
  `Char.card_pow_card`, and `FiniteField.two_pow_card`.
- `Mathlib.NumberTheory.LegendreSymbol.Basic`:
  `legendreSym`, `legendreSym.eq_pow`, `legendreSym.eq_one_or_neg_one`,
  `legendreSym.eq_zero_iff`, and `ZMod.euler_criterion`.
- `Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas`:
  `ZMod.gauss_lemma`, `ZMod.eisenstein_lemma_aux`, and
  `ZMod.eisenstein_lemma`.
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`:
  `quadraticChar_card_card`, `quadraticChar_odd_prime`, and
  `FiniteField.isSquare_odd_prime_iff`.
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`:
  `Polynomial.cyclotomic_prime`,
  `Polynomial.cyclotomic_prime_mul_X_sub_one`, and
  `Polynomial.cyclotomic_prime_pow_eq_geom_sum`.
- The project shell API used by the probes is
  `DkMath.CosmicFormula.GTailCyclotomicShell` and
  `GTailCyclotomicHomEval_prime_eq_shell`.

The missing bridge is precise: the audited APIs do not provide a construction
which turns the quadratic residue/nonresidue character or Gaussian-period
data for an arbitrary odd prime into integral coordinates `A_p, B_p` in a
chosen `TraceOneInt s` order, together with the corresponding norm polynomial
and the signed discriminant identity
`D_p = (-1)^((p-1)/2) * p`.  Establishing that construction and its integral
coordinate/norm compatibility is a future bridge candidate.  This phase does
not claim it.

## Verification

Focused builds passed:

```text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisAxiomAudit
```

`git diff --check` passed.  The changed production and test sources contain
no `sorry` or `axiom` construct.  The explicit axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound` for the checked declarations;
no `sorryAx` is present.

No FLT3, FLT5, FLT7, general FLT, ABC, or arbitrary-prime cyclotomic theorem
is claimed by this phase.
