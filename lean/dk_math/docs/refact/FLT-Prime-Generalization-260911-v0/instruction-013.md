# FLT prime-generalization Phase 13 — integral parity and arbitrary-prime TraceOne bridge

## Goal

Close the remaining quadratic-cyclotomic front-end gap after Phase 12.

Phase 12 already supplies, for every odd prime `p`, an integral polynomial `SZ` such that the antisymmetric QR/QNR factor satisfies

```text
Dpoly = quadraticGauss * map(SZ)
```

and hence

```text
Dpoly^2 = D_p * map(SZ)^2,
D_p = signedPrimeDiscriminant p.
```

Phase 11 supplies an integral polynomial `RZ` mapping to `Rpoly`.

The target of this phase is to prove that `RZ` and `SZ` have the same coefficient parity, extract an integral half-coordinate `AZ`, and use the existing neutral Gauss-form adapter to obtain an arbitrary-odd-prime `TraceOneInt (signedPrimeParameter p)` norm representation of the homogeneous prime cyclotomic shell.

Target classification:

```text
PGEN-TRACEONE-PRIME-BRIDGE-GREEN
```

Do **not** attempt any FLT descent, unit classification, PID/UFD/class-group theorem, or contradiction in this phase.

---

## Mathematical target

Write

```text
D_p := signedPrimeDiscriminant p
s_p := signedPrimeParameter p
```

so that, for prime `p ≠ 2`,

```text
discr s_p = D_p
D_p ≡ 1 (mod 4).
```

Let

```text
RZ, SZ ∈ ℤ[X,Y]
```

be the integral symmetric and Gaussian-normalized antisymmetric coordinates obtained from Phases 11 and 12.

First prove the integral Gauss form

```text
4 * C_p = RZ^2 - D_p * SZ^2
```

where

```text
C_p(X,Y) = Σ_{k=0}^{p-1} X^k Y^(p-1-k).
```

Because `D_p ≡ 1 (mod 4)`, reduction modulo `2` gives

```text
RZ^2 = SZ^2  in  𝔽₂[X,Y].
```

Since `𝔽₂[X,Y]` is reduced / an integral domain,

```text
RZ = SZ  (mod 2).
```

Therefore every coefficient of `RZ - SZ` is even, so construct

```text
AZ ∈ ℤ[X,Y]
```

with

```text
RZ = 2 * AZ + SZ.
```

Then the Phase-5 adapter gives

```text
Norm_{TraceOne(s_p)}(AZ(z,y), SZ(z,y))
  = C_p(z,y)
  = GTailCyclotomicShell p (z-y) y.
```

This is the required arbitrary-prime TraceOne bridge.

---

## Part A — polynomial-level homogeneous shell

Add a production definition, preferably in a new neutral module

```text
DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean
```

or, if dependency direction is cleaner, a small shell helper imported by it.

Define an integer homogeneous shell polynomial, e.g.

```lean
def primeCyclotomicShellPoly (p : ℕ) : MvPolynomial (Fin 2) ℤ :=
  ∑ k ∈ Finset.range p,
    MvPolynomial.X 0 ^ k * MvPolynomial.X 1 ^ (p - 1 - k)
```

Name may vary, but keep the object canonical and production-visible.

Required evaluation theorem:

```lean
theorem eval_primeCyclotomicShellPoly
    (p : ℕ) (z y : ℤ) :
    MvPolynomial.eval ![z, y] (primeCyclotomicShellPoly p) =
      GTailCyclotomicShell p (z - y) y
```

Use the endpoint identity `(z - y) + y = z` explicitly.  Do not divide by an endpoint.

### Polynomial C3 lift

Phase 7 proved the evaluated C3 identity.  For this phase, prove the polynomial-level version in the chosen cyclotomic field:

```lean
MvPolynomial.map (algebraMap ℤ L) (primeCyclotomicShellPoly p)
  = qrFactorPoly ζ * qnrFactorPoly ζ
```

for the usual cyclotomic ambient.

Do **not** infer polynomial equality merely from pointwise evaluation over a field.  Prove it as a typed polynomial identity, using the existing finite-product / primitive-root / homogenization machinery from Phases 7–8.

If a more generic coefficient-ring shell polynomial theorem falls out naturally, promote it; otherwise the integral-to-cyclotomic statement above is sufficient.

---

## Part B — integral Gauss-form packet

Use the existing production theorems:

```text
exists_Rpoly_over_int
exists_Dpoly_over_gauss_int
quadraticGauss_sq
```

and the definitions

```text
Rpoly = qrFactorPoly + qnrFactorPoly
Dpoly = qrFactorPoly - qnrFactorPoly
```

together with the neutral identity

```text
(U + V)^2 - (U - V)^2 = 4 * U * V.
```

Construct `RZ` and `SZ` and prove, over `ℤ[X,Y]`, the exact identity

```lean
MvPolynomial.C 4 * primeCyclotomicShellPoly p =
  RZ ^ 2 -
    MvPolynomial.C (signedPrimeDiscriminant p) * SZ ^ 2
```

(or the symmetric reversed equality).

The proof should proceed by mapping the integer polynomial identity to `L`, rewriting with the Phase-11/12 mapping equalities, the polynomial C3 lift, and `quadraticGauss_sq`, then cancelling via injectivity of

```text
MvPolynomial.map (algebraMap ℤ L).
```

Do not use an unproved uniqueness assertion for the Phase-11/12 existential witnesses.

It is acceptable to package the witnesses in a structure if that reduces later plumbing, e.g.

```text
IntegralGaussCoordinatePacket
```

with fields for `RZ`, `SZ`, the map equalities, and the integer Gauss form.  A structure is optional; the theorem content is mandatory.

---

## Part C — parity in characteristic two

Reduce the integral Gauss form modulo two.

Use

```text
signedPrimeDiscriminant_mod_four
```

to obtain the needed reduction

```text
D_p = 1 in ZMod 2.
```

Prove

```lean
MvPolynomial.map (Int.castRingHom (ZMod 2)) RZ =
  MvPolynomial.map (Int.castRingHom (ZMod 2)) SZ
```

or an equivalent statement.

Preferred proof shape:

1. map the integer Gauss form to `MvPolynomial (Fin 2) (ZMod 2)`;
2. `4 = 0` and `D_p = 1` give `R₂^2 = S₂^2`;
3. use that `MvPolynomial (Fin 2) (ZMod 2)` has no zero divisors;
4. in characteristic two, `R₂ = -R₂`, so the two square roots `±S₂` coincide;
5. conclude `R₂ = S₂`.

Avoid coefficient-by-coefficient expansion of polynomial squares unless the pinned API makes the domain proof substantially harder.

Add a reusable parity lemma if useful:

```lean
map_modTwo_eq_iff_coeff_sub_even
```

or a narrower helper sufficient to derive

```lean
∀ d, 2 ∣ MvPolynomial.coeff d RZ - MvPolynomial.coeff d SZ.
```

---

## Part D — integral half-coordinate extraction

From coefficient parity construct

```text
AZ : MvPolynomial (Fin 2) ℤ
```

with the exact polynomial identity

```lean
RZ = MvPolynomial.C 2 * AZ + SZ.
```

Do not introduce rational division in the final object.

A safe construction is coefficientwise using the finite-support coefficient `Finsupp`, as in the existing Phase-12 witness construction.  For each coefficient use the proven divisibility by `2` to choose an integer half.

Required theorem shape:

```lean
theorem exists_half_difference
    (hmod2 : map_mod2 RZ = map_mod2 SZ) :
    ∃ AZ : MvPolynomial (Fin 2) ℤ,
      RZ = MvPolynomial.C 2 * AZ + SZ
```

A generic theorem over integer multivariate polynomials is preferred if it is no harder than the specialized statement.

---

## Part E — arbitrary-prime TraceOne bridge

Let

```text
s_p := signedPrimeParameter p.
```

Use

```text
discr_signedPrimeParameter
norm_eq_of_gauss_coordinates
```

and the polynomial identities from Parts B–D.

For `z y : ℤ`, define/evaluate

```text
A := eval ![z,y] AZ
S := eval ![z,y] SZ
R := eval ![z,y] RZ
V := GTailCyclotomicShell p (z-y) y.
```

Derive

```text
R = 2*A + S
4*V = R^2 - discr(s_p)*S^2
```

and conclude

```lean
norm (⟨A, S⟩ : TraceOneInt (signedPrimeParameter p)) =
  GTailCyclotomicShell p (z - y) y.
```

### Mandatory production endpoint

Provide a theorem equivalent to:

```lean
theorem exists_prime_traceOne_coordinates
    {L : Type*} [Field L] [Algebra ℚ L]
    {p : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2) (ζ : L) (hζ : IsPrimitiveRoot ζ p) :
    ∃ AZ SZ : MvPolynomial (Fin 2) ℤ,
      ∀ z y : ℤ,
        norm
          (⟨MvPolynomial.eval ![z,y] AZ,
             MvPolynomial.eval ![z,y] SZ⟩ :
            TraceOneInt (signedPrimeParameter p)) =
          GTailCyclotomicShell p (z - y) y
```

The exact binder/order may differ.  It is also acceptable, and arguably better, to return `RZ` plus the identities in a packet and derive the norm theorem as a corollary.

### Optional clean prime-only wrapper

If the pinned API makes it straightforward, instantiate the generic theorem in the canonical

```text
CyclotomicField p ℚ
```

with `IsCyclotomicExtension.zeta` and expose a corollary whose only mathematical hypotheses are

```text
p.Prime
p ≠ 2.
```

Do not force this wrapper if it creates unrelated instance/import complexity; the generic cyclotomic-extension endpoint is mandatory and sufficient.

---

## Part F — GTail/GN-facing corollary

The shell theorem is the mandatory endpoint.  Additionally, if the existing cast API makes this bounded, add a natural endpoint corollary for a positive gap, for example

```text
b < a
```

connecting

```text
GTail p 1 (a - b) b
```

(or legacy `GN p (a-b) b`) to the same TraceOne norm after integer casts.

Do not spend disproportionate effort on this wrapper.  If the cast/zero-gap bookkeeping is noisy, report it as a compatibility follow-up and keep the production shell theorem as the canonical result.

---

## Part G — compatibility checks

Add focused tests, suggested names:

```text
DkMathTest/FLT/Prime/CyclotomicQRTraceOneBridgeProbe.lean
DkMathTest/FLT/Prime/CyclotomicQRTraceOneBridgeCompatibility.lean
DkMathTest/FLT/Prime/CyclotomicQRTraceOneBridgeAxiomAudit.lean
```

Required finite regressions:

```text
p = 3, 5, 7, 11, 13.
```

Check the signed parameters:

```text
p=3  -> s=-1
p=5  -> s= 1
p=7  -> s=-2
p=11 -> s=-3
p=13 -> s= 3
```

For `p=11` and `p=13`, confirm compatibility with the existing exact shell/norm theorems `norm11` / `norm13` or their current names.  Do **not** require the existential `AZ/SZ` witnesses to be definitionally equal to the old explicit `A11/B11` and `A13/B13`; sign and witness conventions may differ.  Equality of the norm target is sufficient.

For `p=3,5,7`, rebuild the existing TraceOne bridge compatibility targets.  Again, do not rewrite the existing FLT towers.

Rebuild:

```text
lake build DkMath.FLT.Seven
```

as a regression guard.

---

## Part H — axiom/trust audit

Add focused `#print axioms` coverage for at least:

```text
polynomial C3 shell lift
integer Gauss-form theorem
mod-two parity theorem
half-coordinate extraction theorem
arbitrary-prime TraceOne bridge theorem
```

Required trust result:

```text
no sorryAx
no new sorry
no explicit axiom
```

Inherited `propext`, `Classical.choice`, and `Quot.sound` are acceptable.

Also run:

```text
git diff --check
```

and a fresh warning scan.

---

## Expected classification

Outcome A:

```text
PGEN-TRACEONE-PRIME-BRIDGE-GREEN
```

Meaning that for every odd prime `p`, DkMath has a kernel-checked integral quadratic-coordinate realization of the prime homogeneous cyclotomic / GTail shell in

```text
TraceOneInt (signedPrimeParameter p)
```

with discriminant

```text
signedPrimeDiscriminant p = ±p.
```

Outcome B:

```text
PGEN-TRACEONE-PARITY-FRONTIER
```

if the integer Gauss form is obtained but the mod-two / half-coordinate extraction cannot be closed with the pinned API.

Outcome C:

```text
PGEN-TRACEONE-SHELL-POLY-FRONTIER
```

if the first genuine blocker is the polynomial-level C3 shell identity.

Record the exact first missing theorem and do not replace it with an assumption.

---

## Non-goals

This phase must **not** claim or attempt:

- general FLT;
- an FLT contradiction for arbitrary `p`;
- Euclidean/PID/UFD structure of `TraceOneInt (signedPrimeParameter p)`;
- trivial class group;
- unit classification for arbitrary `p`;
- Kummer regular-prime arguments;
- ideal principalization;
- rewriting the existing FLT3, FLT5, or FLT7 proof towers.

Even Outcome A completes only the general quadratic cyclotomic front-end.  The next audit boundary would be the arithmetic/descent layer after this front-end, where class groups, units, and principalization may become genuinely exponent-dependent.

---

## Report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-013.md
```

Report:

1. exact polynomial shell API added;
2. exact `RZ/SZ/AZ` existence statements;
3. how the mod-two parity proof is discharged;
4. exact arbitrary-prime TraceOne theorem statement;
5. p=3/5/7/11/13 regressions;
6. whether a GTail/GN natural wrapper was added;
7. axiom audit;
8. focused build commands/results;
9. the next genuine FLT-specific boundary after the quadratic front-end.
