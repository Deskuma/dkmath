# IPSM-005 — Gate 3B.1 review and quadratic / Gram obstruction roadmap

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / quadratic-form audit / no RH claim

---

## 0. Review result

The current implementation of

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
```

has been inspected after IPSM-004.

Review classification:

```text
Gate 3B.0 genuine complex surface reconstruction
  GREEN

Gate 3B.1a pointwise deoriented source
  GREEN

Gate 3B.1b explicit radial comparison
  GREEN

Gate 3B.1c independent positive energy
  NOT YET FOUND
```

The implementation correctly stops before asserting nonnegativity, a defect sign, a height limit, or RH.

---

## 1. Gate 3B.1a preserves the correct source information

The pointwise objects are now defined before interval integration:

```lean
pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand
pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand
pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand
pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand
```

and their interval lifts reconstruct the genuine complex vertical surface exactly.

This is the correct level at which to search for a quadratic or Gram mechanism, because no real projection has yet discarded the imaginary source information.

The key structural simplification is that every source right-edge integrand has the form

```text
(source factor) * Complex.I
```

and the deorientation map is multiplication by `-Complex.I`.

Therefore the pointwise deoriented source should admit exact simplification theorems of the form

```text
prime deoriented integrand
  = Mellin quadratic weight * finite von-Mangoldt / PHZ factor

archimedean deoriented integrand
  = Mellin quadratic weight * archimedean logarithmic-derivative factor

elementary deoriented integrand
  = Mellin quadratic weight * elementary correction factor
```

with no remaining path-orientation `I`.

These simplifications should be made explicit before attempting a Gram decomposition.  They expose the true algebraic type of the source.

---

## 2. Gate 3B.1b fixes the sign target correctly

The current comparison target is

$$
R(W):=\pi\,Q(W.R).
$$

The scalar excess is exactly

$$
E_{\varepsilon,X}(W)=\operatorname{Re}\mathcal W_{\varepsilon,X}(W)-R(W).
$$

This is compatible with the already Green identity

$$
E_{\varepsilon,X}(W)=-\pi D_{\varepsilon,X}(W).
$$

Thus the prime-side sign problem has not changed form under the complex reconstruction: a genuine positive-energy mechanism must explain why the real part of the whole complex surface dominates the radial comparison target.

The radial target is not to be replaced by a field whose assumption is equivalent to `0 <= E`.

---

## 3. First quadratic-form audit: the current source is bilinear, not yet Hermitian

After deorientation, the right-edge source is structurally a product

```text
Mellin quadratic weight
  * logarithmic-derivative / arithmetic source factor
```

before taking a real part and integrating.

This is a complex bilinear product.  A positive Gram form normally requires a Hermitian structure such as

```text
z * conj z
```

or, more generally,

```text
sum_i,j conj(v_i) * G_ij * v_j
```

with a positive-semidefinite matrix `G`.

No such conjugate-self pairing is present in Gate 3B.1a merely from deorientation and source reconstruction.

Therefore the next audit must not assume that a `normSq` representation exists just because the final scalar is real.

The missing mathematical content, if a positive Gram form exists, is an independent identity that relates the second source factor to a conjugate / mirror transform of the first factor, or embeds both factors into a known positive-semidefinite kernel.

---

## 4. Generic bilinear sign obstruction

The elementary algebra itself warns against pointwise positivity.

For a complex number `a`, a real-part bilinear expression

$$
\operatorname{Re}(a b)
$$

has no fixed sign when `b` is unrestricted.

For example, taking `b = conj a` yields a nonnegative norm square, while taking `b = -conj a` yields its negative.

Thus a theorem of the schematic form

```text
Re(weight * sourceFactor) >= 0
```

cannot follow from complex multiplication alone.

Applied to the present source, this means that positivity requires a specific relation between

```text
Mellin quadratic weight
```

and

```text
prime + archimedean + elementary logarithmic-derivative source
```

or a nonlocal relation after integration / mirror pairing.

This is a structural obstruction to a naive pointwise square completion, not a proof that no deeper global energy identity exists.

---

## 5. Existing zero-side anti-mirror energy is not a prime-side provider

The repository already contains a genuine positive norm-square object:

```lean
pascalCriticalMirrorZeroWindowAntiMirrorEnergy
```

and on a boundary-safe radius the fixed Xi defect is exactly that energy.

This is useful as a comparison template because it shows what a real positive-energy theorem looks like: a multiplicity-weighted finite sum of `Complex.normSq` values with an exact bridge to the defect.

However, that theorem is zero-side and already represents the nonnegative defect.

It must not be imported back into Gate 3B as the desired opposite sign mechanism.  Doing so would merely recover the known inequality `0 <= D`, not the required independent prime-side direction.

The prime-side provider must be derived from arithmetic / explicit-formula source data with independent mathematical content.

---

## 6. Gate 3B.1c explicit audit sequence

Before declaring a named obstruction, perform the following finite exact checks.

### Gate 3B.1c-A — remove orientation completely at pointwise level

Add exact theorems exposing the deoriented products without `Complex.I`.

Suggested theorem surface:

```lean
pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand_eq
pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand_eq
pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand_eq
pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand_eq_weight_mul_decomposed
```

The last theorem should combine the three source factors if the existing decomposition API makes this exact at the finite cutoff level.

### Gate 3B.1c-B — conjugation / mirror test

Check whether the finite pointwise source satisfies any exact relation of the form

```text
sourceFactor(t)
  = conj(sourceFactor(-t))
```

or a centered-mirror variant compatible with the Mellin weight.

Even if such a relation holds, record precisely what it gives after pairing `t` and `-t`.  Symmetry making an integral real is not the same as positivity.

### Gate 3B.1c-C — Gram candidate test

A valid candidate must produce an exact identity whose right-hand side is visibly nonnegative by existing algebra, for example:

```text
finite sum of normSq
integral of normSq with nonnegative real weight
positive-semidefinite finite Gram matrix
CF2D q2 mass with an independently proved comparison
```

The candidate must bridge to the existing scalar excess itself, not merely to an unrelated nonnegative quantity.

### Gate 3B.1c-D — affine-shape obstruction if no bridge appears

If the source identities yield only

```text
E = Re(complexWholeSurface) - radialComparison
```

with no independent relation between the two terms, close the purely algebraic route with a named obstruction.

A useful abstract theorem can show that the affine shape `Re z - q` has both signs even for `q >= 0`, so representation alone cannot imply nonnegativity.

This would not rule out an analytic, mirror, spectral, or arithmetic provider.  It would only prove that Gate 3A/3B representation identities by themselves are insufficient.

---

## 7. Recommended named obstruction boundary

If Gate 3B.1c-A/B/C yields no positive-semidefinite identity, add a named marker such as

```text
PascalCenteredXiPrimeSidePointwiseGramObstruction
```

or

```text
PascalCenteredXiPrimeSideAffineExcessSignObstruction
```

with a precise scope:

```text
- deorientation is exact
- t / -t or mirror pairing may enforce reality
- reality alone does not imply positivity
- affine excess representation alone has no definite sign
- no prime-side Gram identity has been derived from current source algebra
```

Do not encode the absence of a theorem as an unprovable proposition.  The obstruction should be a positive mathematical statement, for example an explicit abstract counterexample showing that the generic algebraic form admits both signs.

---

## 8. Decision tree after Gate 3B.1c

```text
pointwise source simplification
  -> conjugation / mirror audit
      -> exact positive-semidefinite Gram identity found
          -> bridge Gram energy to scalar excess
          -> finite nonnegativity theorem
          -> Gate 2 ordered sign transport
      -> no positive-semidefinite identity
          -> named algebraic obstruction
          -> close Gate 3B algebraic route
          -> move to a genuinely new analytic / spectral provider
```

The branch should not continue manufacturing wrappers after the named obstruction.  At that point a new mathematical input is required.

---

## 9. Non-goals

IPSM-005 does not claim:

```text
finite excess nonnegativity
finite defect nonpositivity
pointwise source positivity
existence of a Gram form
absence of every possible global energy identity
T -> infinity
X <-> epsilon exchange
joint limit
fixed defect vanishing
Riemann Hypothesis
```

---

## 10. Next checkpoint

```text
Gate 3B.1a
  GREEN

Gate 3B.1b
  GREEN

Gate 3B.1c-A
  exact pointwise deorientation simplification

Gate 3B.1c-B
  conjugation / t <-> -t / centered-mirror audit

Gate 3B.1c-C
  positive-semidefinite Gram candidate test

Gate 3B.1c-D
  if C fails: named affine / bilinear sign obstruction
```

The next implementation should stop immediately if a genuine positive-semidefinite bridge appears; otherwise it should close the current algebraic route cleanly with a named obstruction rather than assume the desired sign.
