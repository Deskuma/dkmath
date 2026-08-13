# IPSM-006 — Gate 3B algebraic-route closeout and provider handoff

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 3B algebraic route closed / independent sign provider still open / no RH claim

---

## 0. Closeout decision

Gate 3B has now reached the intended audit boundary.

```text
Gate 3B.0
  genuine complex whole-surface reconstruction
  GREEN

Gate 3B.1a
  pointwise deorientation and source reconstruction
  GREEN

Gate 3B.1b
  explicit radial comparison target
  GREEN

Gate 3B.1c-A
  complete pointwise removal of contour I
  GREEN

Gate 3B.1c-B
  bilinear versus Hermitian algebra audit
  OBSTRUCTION GREEN

Gate 3B.1c-C
  independent positive-semidefinite Gram bridge
  NOT FOUND

Gate 3B.1c-D
  affine/bilinear sign obstruction
  GREEN
```

The current algebraic route is therefore closed as an independent positivity route.

This is not a claim that no analytic, mirror, spectral, operator, or arithmetic positivity theorem can exist.  It is a precise statement that the present deorientation + bilinear source + affine radial subtraction does not itself force the required sign.

---

## 1. Exact pointwise source normal form now available

The implementation proves that after removing the vertical contour orientation, the prime, archimedean, and elementary pieces become ordinary products with no remaining path `Complex.I`.

The combined pointwise vertical source is exactly of the form

$$
G_{\varepsilon,X,W}(t)=q_{\varepsilon,W}(t)\,L_{X,W}(t).
$$

Here `q` is the centered Mellin quadratic weight evaluated on the centered right edge, while `L` is the finite decomposed logarithmic-derivative source consisting of the prime cutoff plus the archimedean and elementary corrections.

In Lean this is fixed by

```lean
pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand_eq
pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand_eq
pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand_eq
pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand_eq_weight_mul_decomposed
```

This is the strongest useful algebraic normal form reached in Gate 3B.

---

## 2. What the normal form does not contain

The pointwise product is bilinear.  It is not automatically a Hermitian self-pairing.

A genuine positive square has the algebraic shape

$$
\operatorname{Re}(z\overline z)=|z|^2\ge0.
$$

But changing the first factor already reverses the sign:

$$
\operatorname{Re}((-z)\overline z)=-|z|^2\le0.
$$

The module records this contrast explicitly in

```lean
pascalCenteredXiPrimeSide_conj_pair_is_normSq
pascalCenteredXiPrimeSide_neg_conj_pair_is_neg_normSq
```

Therefore a Gram or norm-square argument requires an additional theorem identifying the actual second source factor with an appropriate conjugate or adjoint partner.  Such an identity is not supplied by deorientation alone.

---

## 3. Affine excess obstruction

The finite scalar sign target remains

$$
E_{\varepsilon,X}(W)=\operatorname{Re}\mathcal W_{\varepsilon,X}(W)-\pi Q(W.R).
$$

and the already Green algebra gives

$$
E_{\varepsilon,X}(W)=-\pi D_{\varepsilon,X}(W).
$$

Hence `E >= 0` is exactly the desired finite prime-side sign statement.

However, a real-part observable minus a nonnegative radial scalar has no algebraic sign merely from that affine form.  The abstract theorem

```lean
pascalCenteredXiPrimeSide_affine_excess_has_both_signs
```

records this logical insufficiency.

Important interpretation:

```text
PROVED:
  the abstract affine schema permits both signs.

NOT PROVED:
  the actual RH arithmetic surface takes both signs.
```

The theorem is an obstruction to deriving positivity from the schema alone, not a sign-change theorem for the concrete arithmetic excess.

---

## 4. Gate 3B named obstruction

The obstruction can now be stated precisely.

```text
Current source data provides:

  complex deorientation
  exact pointwise bilinear product
  exact finite integration
  exact whole complex surface
  exact radial affine comparison

Current source data does not provide:

  conjugate/adjoint identification of the decomposed source
  positive-semidefinite Gram matrix
  positive measure representation of the excess
  norm-square identity for the finite excess
  lower bound forcing wholeSurface.re >= pi * radialMass
```

Accordingly, no theorem named as an `EnergyProvider` or `NonnegativityProvider` should be introduced from these identities alone.

Suggested audit name:

```text
PascalCenteredXiPrimeSideBilinearAffineSignObstruction
```

A separate Lean structure is not required unless later provider work benefits from referencing the obstruction as data.  The existing concrete algebraic theorems plus this checkpoint are already sufficient to close the route.

---

## 5. Gate 3B final status

```text
Gate 3B purpose:
  determine whether the currently exposed finite complex arithmetic surface
  already hides an algebraic square / Gram positivity mechanism.

Result:
  NO SUCH MECHANISM HAS BEEN DERIVED.

Closeout classification:
  ALGEBRAIC ROUTE CLOSED BY NAMED OBSTRUCTION BOUNDARY.
```

This is a successful audit result.  It prevents later proofs from silently treating reality, deorientation, or an affine subtraction as positivity.

---

## 6. Next frontier — independent provider discovery

The next work must add genuinely new mathematical content.  Three provider families remain logically admissible.

### Provider A — analytic inequality

Required shape:

```text
properties of the actual Mellin weight
+ properties of the actual decomposed logarithmic derivative
+ finite contour geometry
-> wholeSurface.re >= pi * radialMass
```

A valid analytic provider must prove a concrete inequality for the existing source functions.  It must not contain the target inequality as a hypothesis under another name.

Potential audit directions include:

```text
- t <-> -t pairing after the full decomposed source is substituted
- convexity / positive-kernel representation of the quadratic Mellin weight
- integration-by-parts identity producing an explicit square plus boundary terms
- finite reproducing-kernel or Plancherel identity
```

No such theorem is claimed here.

### Provider B — mirror / adjoint bridge

Required shape:

```text
actual source at the paired point
= conjugate or adjoint transform of the original source
```

followed by an exact pairing that produces a Hermitian form.

The key requirement is that the conjugate partner must come from an independently proved functional/mirror identity of the concrete arithmetic source.  It cannot be inserted syntactically just to create `z * conj z`.

A reality theorem alone is insufficient; positivity requires positive-semidefinite pairing.

### Provider C — spectral / operator positivity

Required shape may be one of

```text
E = integral |F|^2 dmu, with mu positive
E = <Tf,f>, with T positive semidefinite
E = finite Gram quadratic form, with PSD matrix proved independently
E >= c * ||f||^2, with c >= 0 proved independently
```

The bridge must identify the resulting energy with the existing finite scalar excess, or prove a lower bound strong enough to imply its nonnegativity.

Again, defining an energy after the fact as `E` itself is not a provider.

---

## 7. Independence contract for every future provider

Any future sign provider must pass all of the following checks.

```text
1. It is stated using source-level analytic / mirror / spectral hypotheses,
   not the desired excess sign.

2. It does not assume fixed-defect vanishing, RH, or an equivalent statement.

3. It preserves finite T and the top-horizontal contribution unless a separate
   exact theorem removes them.

4. It preserves the established ordered limit:
     X -> infinity first,
     epsilon -> 0+ second.

5. It does not introduce an X <-> epsilon exchange or joint limit without a
   separately proved theorem.

6. Its positivity is independently visible from a norm square, positive
   measure, PSD operator/matrix, or a proved analytic inequality.

7. It connects back to the already fixed scalar excess rather than replacing
   the sign target by a different observable.
```

---

## 8. Recommended next checkpoint split

Do not continue adding algebraic wrappers inside Gate 3B.

Start a new provider-discovery stage.

```text
Gate 4A — mirror/conjugation source audit
  determine the exact t <-> -t and functional-equation transforms
  of the full finite decomposed source.

Gate 4B — analytic positive-kernel audit
  inspect whether the centered Mellin quadratic weight supplies a genuine
  positive kernel after the correct pairing.

Gate 4C — spectral/Gram candidate
  only after 4A or 4B produces a concrete paired structure.

Gate 4D — independent finite sign theorem
  OR provider-specific named obstruction.
```

The recommended first move is Gate 4A because Gate 3B identified the missing algebraic ingredient precisely: a source-derived conjugate/adjoint partner.

---

## 9. Non-goals and non-conclusions

IPSM-006 does not assert any of the following.

```text
actual finite excess changes sign
no analytic positive provider exists
no mirror positive provider exists
no spectral positive provider exists
finite defect is nonpositive
fixed defect vanishes
T -> infinity
top-horizontal disappearance
X <-> epsilon exchange
joint limit
Riemann Hypothesis
```

The only negative conclusion is local and exact:

```text
deorientation + current bilinear source + affine radial subtraction
is insufficient by itself to derive the required positivity.
```

---

## 10. Handoff summary

```text
Representation block XDP-017..021:
  COMPLETE

IPSM Gate 1 normalized decomposition:
  GREEN

IPSM Gate 2 ordered sign transport:
  GREEN

IPSM Gate 3A scalar excess algebra:
  GREEN

IPSM Gate 3B complex reconstruction and algebraic energy audit:
  CLOSED
  obstruction boundary established

Independent prime-side positivity provider:
  OPEN

Next recommended research gate:
  Gate 4A mirror/conjugation source audit
```

The project should now stop treating Gate 3B as an unfinished implementation problem.  Its implementation goal was an audit, and that audit has produced a definitive boundary.  Further progress requires a new theorem, not a new wrapper around the existing algebra.