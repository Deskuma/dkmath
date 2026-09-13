# FLT prime-generalization Phase 7 — QR/QNR cyclotomic product identification

## Goal

Phase 6 stopped at `PGEN-GAUSS-QR-PARTITION`: QR/QNR finite combinatorics and weak product recombination are GREEN, while the first missing theorem is the identification of the full nonzero-root product with the homogeneous prime cyclotomic shell.

This phase is intentionally bounded to that C3 frontier. Do **not** attempt coefficient descent, integral Gaussian-period coordinates, class-group arguments, or any FLT contradiction.

The target is to determine whether the following layer can be kernel-checked for an arbitrary odd prime `p`:

```text
QR product * QNR product
  = product over all nonzero powers of a primitive p-th root
  = GTailCyclotomicShell p (z-y) y
```

Classification on success: `PGEN-GAUSS-FACTOR-GREEN`.

## A. Work in a typed primitive-root ambient ring

Create a test-first module, suggested path:

```text
DkMathTest/FLT/Prime/CyclotomicQRProductProbe.lean
```

Use a field or integral domain `K` with the minimum assumptions required by the pinned Mathlib API. Prefer a direct primitive-root hypothesis rather than constructing a full cyclotomic field if possible:

```lean
variable {K : Type*} [Field K]
variable {p : ℕ} (hp : p.Prime)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
```

If `CharZero K`, `NeZero p`, or stronger assumptions are genuinely required by the pinned API, record them explicitly and justify them in the report. Do not add assumptions merely for convenience.

Audit the pinned Mathlib source for the exact available forms of:

- `IsPrimitiveRoot.nthRoots_eq`
- `IsPrimitiveRoot.nthRoots_one_nodup`
- `IsPrimitiveRoot.zmodEquivZPowers`
- `primitiveRoots`
- `nthRootsFinset_eq_of_prime`
- polynomial root-product identities such as `Polynomial.roots_prod_X_sub_C`
- cyclotomic splitting / `Polynomial.cyclotomic_prime`

Current upstream Mathlib has these families, but the pinned checkout is authoritative.

## B. Define the evaluated primitive-root factors

For endpoints `X Y : K`, define a factor indexed by a residue class `a : ZMod p` using its canonical representative:

```text
rootFactor ζ a X Y := X - ζ^(a.val) * Y
```

Keep the endpoint convention compatible with DkMath:

```text
X = (z - y) + y = z
Y = y
```

Reuse the Phase-6 `qrFinset`, `qnrFinset`, and `nonzeroResidues` definitions if practical. Avoid duplicating their QR/QNR proofs.

Prove the direct recombination theorem in this concrete setting:

```text
(∏ a ∈ qrFinset p, rootFactor ζ a X Y) *
(∏ a ∈ qnrFinset p, rootFactor ζ a X Y)
=
∏ a ∈ nonzeroResidues p, rootFactor ζ a X Y
```

This should be a specialization of the Phase-6 weak product theorem, not a new combinatorial proof.

## C1. Identify nonzero powers with the nontrivial p-th roots

Prove that for prime `p`, the values

```text
ζ^(a.val),  a ∈ nonzeroResidues p
```

are exactly the nontrivial `p`-th roots of unity, with no duplication.

Preferred route:

1. use `hζ.pow_inj` / `hζ.zmodEquivZPowers` or an equivalent pinned theorem for injectivity;
2. use primeness of `p` to show every nonzero exponent gives a primitive `p`-th root;
3. identify the image with `primitiveRoots p K`, or with `nthRootsFinset p 1 \ {1}`.

Do not silently identify `ZMod p` exponents with naturals without proving the representative bounds/injectivity conditions needed by Lean.

Record separately:

```text
C1a: injective exponent image
C1b: image = primitiveRoots p K
C1c: image = nthRootsFinset p 1 \ {1}
```

It is acceptable for one of these formulations to be much easier than the others. Keep the strongest clean theorem actually supported by the pinned API.

## C2. Polynomial/product bridge

Prove a polynomial or evaluated-product identity for the nontrivial roots. Preferred target:

```text
∏ a ∈ nonzeroResidues p, (X - ζ^(a.val) * Y)
  = ∑ k ∈ Finset.range p, X^k * Y^(p-1-k)
```

which is exactly the homogeneous prime cyclotomic shell.

Possible proof routes, in preferred order:

### Route 1 — cyclotomic polynomial roots

Show that the monic polynomial with roots `ζ^a` for nonzero classes equals `Polynomial.cyclotomic p K`, then evaluate/homogenize.

Use `Polynomial.cyclotomic_prime` only after the root/product equality is established; do not replace the root argument by coefficient brute force.

### Route 2 — nth roots minus the trivial root

Use a primitive-root factorization of

```text
T^p - 1 = ∏_{a : ZMod p} (T - ζ^a)
```

then split off the `a = 0` / root `1` factor and compare with the geometric sum

```text
(T^p - 1) = (T - 1) * (1 + T + ... + T^(p-1)).
```

After this one-variable identity, homogenize to `(X,Y)` without dividing by `Y`.

### Route 3 — root multiset equality

If pinned APIs make the previous routes awkward, prove equality of monic polynomials by equal root multisets and degree, then evaluate.

Avoid field division by `X`, `Y`, or `X-Y`; the final theorem should remain division-free and valid at zero endpoints when algebraically meaningful.

## C3. Connect to DkMath shell

Once C2 is GREEN, prove the exact DkMath statement:

```lean
(∏ a ∈ qrFinset p, rootFactor ζ a ((z - y) + y) y) *
(∏ a ∈ qnrFinset p, rootFactor ζ a ((z - y) + y) y)
  = GTailCyclotomicShell p (z - y) y
```

for the appropriate casts into `K`.

Also provide the cleaner endpoint version:

```text
QRProduct ζ X Y * QNRProduct ζ X Y
  = GTailCyclotomicShell p (X - Y) Y
```

only if the subtraction/cast assumptions are clean. Otherwise retain `X = x + u` and state the theorem directly in `(x,u)` coordinates:

```text
QRProduct ζ (x+u) u * QNRProduct ζ (x+u) u
  = GTailCyclotomicShell p x u.
```

This is probably the safest canonical DkMath form.

## D. Finite regressions

Instantiate C3 for at least:

```text
p = 3, 5, 7, 11, 13
```

The purpose is only to ensure the generic product theorem agrees with the existing finite bridge family. Do not rebuild the explicit `A11/B11` or `A13/B13` coordinates here.

For `p = 11,13`, check compatibility at the level:

```text
QRProduct * QNRProduct = shell = norm(existing explicit TraceOne coordinates)
```

using the existing Phase-5/6 probe theorems.

## E. Do not cross into coefficient descent

Stop once the product identity is established.

Do **not** yet prove:

- Galois conjugation swaps QR and QNR products;
- `QRProduct + QNRProduct` lies in `ℤ[X,Y]`;
- `(QRProduct - QNRProduct)^2 = D_p * S_p^2` with integral `S_p`;
- parity / `R_p-S_p = 2A_p`;
- arbitrary-prime `TraceOneInt` integral coordinates.

Those are Phase 8 / C4 candidates.

If C3 itself fails, report the exact first obstruction and classify it as one of:

```text
PGEN-C3-ROOT-ENUMERATION-BLOCKED
PGEN-C3-POLYNOMIAL-FACTOR-BLOCKED
PGEN-C3-HOMOGENIZATION-BLOCKED
PGEN-C3-PINNED-API-MISSING
```

Do not work around a genuine API/theorem gap by inserting a new axiom.

## F. Production promotion policy

Keep the implementation in `DkMathTest` until the full arbitrary-prime C3 theorem is GREEN.

If C3 is proved with clean assumptions and no FLT imports, promote the neutral theorem to a production module, suggested path:

```text
DkMath/NumberTheory/CyclotomicQRProduct.lean
```

Production code must depend only on NumberTheory / Mathlib primitives, not `DkMath.FLT.*`.

The QR/QNR finite-set API may be promoted with it if it is genuinely reusable and not test-specific.

## G. Verification and report

Add:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-007.md
```

Report:

1. exact assumptions on `K`, `p`, and `ζ`;
2. which primitive-root/cyclotomic pinned APIs were used;
3. C1/C2/C3 status separately;
4. whether the result was promoted to production;
5. p=3,5,7,11,13 regression status;
6. first remaining theorem for C4 coefficient descent;
7. axiom audit.

Required focused builds should include all newly added modules plus:

```text
lake build DkMath.Lib.Cosmic.GTailCyclotomic
lake build DkMath.NumberTheory.QuadraticConjugateFactor
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMathTest.FLT.Prime.GaussianPeriodFactorizationCompatibility
lake build DkMathTest.FLT.Prime.QuadraticCyclotomicBridgeProbe
lake build DkMath.FLT.Seven
```

Run `git diff --check`, source scan for `sorry` / explicit `axiom`, and `#print axioms` for every new public theorem. `sorryAx` is forbidden.

## Success meaning

A GREEN Phase 7 means only:

```text
quadratic residue/nonresidue primitive-root factors
  recombine to the arbitrary-prime GTail cyclotomic shell.
```

It does **not** yet give integral Gaussian-period coordinates, a general quadratic `TraceOne` bridge, or general FLT.
