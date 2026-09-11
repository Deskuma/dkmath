# FLT prime-generalization Phase 12 — quadratic Gauss normalization and integral `S_p`

## Goal

Close the next bounded frontier after Phase 11:

```text
Dpoly^2 integral over Z                    [GREEN: Phase 11]
quadratic Gauss square root of D_p         [THIS PHASE]
common quadratic-character eigenspace      [THIS PHASE]
integral S_p extraction                     [THIS PHASE TARGET]
R_p - S_p = 2 A_p parity / TraceOne bridge [NEXT]
```

The preferred success classification is:

```text
PGEN-GAUSS-SQUARE-NORMALIZATION-GREEN
```

Do **not** modify FLT3/FLT5/FLT7 endpoints and do not claim general FLT.

---

## A. Promote the signed prime discriminant to production

The Phase-6 test-side definitions should now become a neutral production API,
preferably in a small module such as

```text
DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean
```

or, if dependency direction is cleaner, alongside `TraceOneDiscriminantAxis`.

For an odd prime `p`, define a canonical signed discriminant

```text
D_p = if p % 4 = 1 then p else -p
```

as an integer, and the corresponding trace-one parameter

```text
s_p = (D_p - 1) / 4.
```

Promote/prove the already-audited facts:

```text
D_p =  p or D_p = -p
Int.natAbs D_p = p
D_p % 4 = 1
1 + 4 * s_p = D_p
```

with the exact minimal odd-prime hypotheses Lean needs.

Also provide a canonical

```text
PrimeDiscriminantPacket p s_p
```

bridge if convenient.

Do not encode the sign through unsafe Nat subtraction.

---

## B. Construct the quadratic Gauss element in the chosen cyclotomic extension

Work over the Phase-9 ambient specialized to `Q`:

```lean
[Field L] [Algebra ℚ L]
{p : ℕ} [Fact p.Prime]
[IsCyclotomicExtension {p} ℚ L]
ζ : L
hζ : IsPrimitiveRoot ζ p
```

and assume/prove oddness (`p ≠ 2`) where genuinely required.

Audit the pinned Mathlib Gauss-sum normalization first. Preferred route:
reuse the existing quadratic-character/Gauss-sum theorem (`gaussSum_sq` or the
quadratic-character specialization) rather than reproving the classical sum.
If the exact existing API does not match the selected primitive root `ζ`, add
a thin project wrapper or define the finite quadratic Gauss sum directly and
bridge it to the pinned theorem.

Introduce an element, notation here only:

```text
G_p(ζ) : L
```

with production theorem

```text
quadraticGauss_sq : G_p(ζ)^2 = algebraMap ℤ L D_p
```

(up to the exact cast-normalized form preferred by Lean).

Required consequence:

```text
quadraticGauss_ne_zero
```

for odd prime `p`.

### B1. Galois character law

For `σ : L ≃ₐ[ℚ] L`, extract its nonzero exponent using the Phase-9
`cyclotomicAut_power_spec` API. Prove the Gauss element transforms by the same
quadratic character as `Dpoly`:

```text
square exponent    -> σ(G_p) =  G_p
nonsquare exponent -> σ(G_p) = -G_p
```

A single sign/character theorem is welcome if it is cleaner.

Do not duplicate the Phase-8/9 QR/QNR permutation proofs unnecessarily.

---

## C. Put each `Dpoly` coefficient in the same one-dimensional character eigenspace

For each monomial index `d`, let

```text
c_d := coeff d (Dpoly ζ).
```

Phase 8/9 already proves that `c_d` transforms with sign `+/-` according to
the same square/nonsquare exponent class as `Dpoly`.

Using `G_p ≠ 0`, define or existentially obtain

```text
q_d : ℚ
```

such that

```text
c_d = algebraMap ℚ L q_d * G_p
```

(or the commuted multiplication form).

Preferred proof route:

1. In `L`, form `c_d / G_p`.
2. Show every `σ : L ≃ₐ[ℚ] L` fixes this quotient because numerator and
   denominator acquire the same sign.
3. Reuse Phase-10 fixed-field descent to place the quotient in
   `Set.range (algebraMap ℚ L)`.

Package a reusable theorem such as

```text
coeff_Dpoly_eq_gauss_mul_rat
```

without exporting arbitrary `Classical.choose` values when an existential
statement suffices.

At this checkpoint it is acceptable to classify

```text
PGEN-GAUSS-SQRT-GREEN
```

if B succeeds but C unexpectedly exposes a real API obstruction. Continue to
D/E when possible.

---

## D. Squarefree-prime rational denominator lemma

This is the key arithmetic shortcut. Add a neutral rational lemma (low-level
number theory module if reusable) expressing:

> If `p` is prime, `q : ℚ`, and `±p * q^2` is an integer, then `q` is an
> integer.

A convenient Lean shape is any equivalent statement, for example:

```text
Nat.Prime p ->
(∃ z : ℤ, (z : ℚ) = (p : ℚ) * q^2) ->
∃ a : ℤ, (a : ℚ) = q
```

and the negative-sign variant should be discharged by sign normalization, not
by duplicating the denominator proof.

Preferred arithmetic proof:
write `q` in reduced numerator/denominator form and derive

```text
den(q)^2 | p,
```

then use primality/squarefreeness to force `den(q)=1`.

Audit pinned `Rat.num` / `Rat.den` / normalization APIs before hand-building
fraction theory. If Mathlib already has a theorem that rational integral over
`Z` is integer and you can prove integrality of `q` from the square relation,
that route is also acceptable, but do not assume quotient-integrality without
proof.

---

## E. Recover integral coefficients of `S_p`

Take a coefficient factorization

```text
c_d = G_p * q_d,
```

with `q_d : ℚ` from C.

Since Phase 11 proves `c_d` is integral over `ℤ`, so is `c_d^2`. Using

```text
G_p^2 = D_p
```

obtain in `L`

```text
c_d^2 = D_p * q_d^2.
```

The right side is rational. Pull its integrality back along `ℚ -> L`, then
use the Phase-11 rational-integral-to-integer bridge to obtain

```text
D_p * q_d^2 ∈ ℤ.
```

Apply Part D and `Int.natAbs D_p = p` to conclude

```text
q_d ∈ ℤ.
```

Then use `MvPolynomial.mem_range_map_iff_coeffs_subset` to construct

```lean
∃ SZ : MvPolynomial (Fin 2) ℤ,
  MvPolynomial.map (algebraMap ℤ L) SZ * MvPolynomial.C G_p =
    Dpoly (p := p) ζ
```

or the equivalent constant-times-polynomial orientation.

Prefer a statement whose squaring immediately yields the discriminant-square
normal form.

---

## F. Discriminant-square normalization

From E and `quadraticGauss_sq`, prove the polynomial identity in `L`:

```text
Dpoly ζ ^ 2
  = C (algebraMap ℤ L D_p) * (map (algebraMap ℤ L) SZ)^2.
```

If convenient, additionally descend this to a pure integer-polynomial
existence statement compatible with Phase 11:

```text
∃ SZ D2Z : MvPolynomial (Fin 2) ℤ,
  map D2Z = Dpoly ζ ^ 2 ∧
  D2Z = C D_p * SZ^2.
```

Do not depend on definitional equality with the noncanonical Phase-11 `D2Z`
witness.

The preferred final production endpoint is an existential `SZ` plus the
mapped identity.

---

## G. Finite compatibility

Add focused tests for

```text
p = 3, 5, 7, 11, 13.
```

For `p=11` and `p=13`, compare the new square normalization with the existing
explicit Gauss/TraceOne regression:

```text
D_11 = -11
D_13 =  13
```

and the existing explicit `S11 = B11`, `S13 = B13` square identities where
possible. Do **not** require the newly existentially obtained `SZ` witness to
be definitionally equal to `B11`/`B13`; equality up to sign or merely equality
of squares is sufficient for this phase.

Keep existing

```text
QR/QNR -> shell -> TraceOne norm
```

compatibility green.

---

## H. Explicit non-goals

Do not yet prove:

```text
R_p - S_p = 2 * A_p
arbitrary-prime TraceOne norm coordinates A_p,S_p
unit/class-group/descent contradiction
general FLT
```

Those belong to the next phase after an integral `S_p` exists.

---

## I. Stop conditions and classifications

Report the highest reached point precisely:

```text
PGEN-GAUSS-SQRT-GREEN
  Gauss element, square `G^2=D_p`, and character action are proved.

PGEN-GAUSS-S-RATIONAL-GREEN
  additionally `Dpoly = G * S_Q` with `S_Q ∈ ℚ[X,Y]`.

PGEN-GAUSS-SQUARE-NORMALIZATION-GREEN
  additionally `S_Z ∈ ℤ[X,Y]` and
  `Dpoly^2 = D_p * S_Z^2` are proved.
```

Stop and report rather than smuggling in an assumption if any of these occurs:

1. the pinned Gauss-sum theorem has a normalization incompatible with the
   selected primitive root and no proved bridge is available;
2. the Galois sign law for the Gauss element needs an unproved character
   theorem;
3. fixed-field descent only yields a larger field than `ℚ`;
4. the rational squarefree-denominator lemma cannot be closed without a new
   arithmetic assumption;
5. integrality of `Dpoly` coefficients is insufficient for the proposed
   coefficient argument.

---

## J. Verification

At minimum build:

```bash
lake build DkMath.NumberTheory.PrimeQuadraticDiscriminant      # if created
lake build DkMath.NumberTheory.CyclotomicQRGaloisRealization
lake build DkMath.NumberTheory.CyclotomicQRCoefficientDescent
lake build DkMath.NumberTheory.CyclotomicQRIntegralDescent
lake build DkMath.NumberTheory.CyclotomicQRGaussNormalization  # suggested new module
lake build DkMathTest.FLT.Prime.CyclotomicQRGaussNormalizationProbe
lake build DkMathTest.FLT.Prime.CyclotomicQRGaussNormalizationCompatibility
lake build DkMathTest.FLT.Prime.CyclotomicQRGaussNormalizationAxiomAudit
lake build DkMath.FLT.Seven
```

Use exact actual module names if different.

Run `#print axioms` on the central Gauss-square theorem, character-action
theorem, rational/integer coefficient bridge, and final `SZ` existence
endpoint. No `sorryAx`, new `sorry`, or explicit `axiom`.

Record `git diff --check`, warning scan, and the exact pinned Mathlib Gauss-sum
API used.
