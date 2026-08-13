# IPSM-015 — Gate 4B.3c2 review and continuous adjoint search roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B.3c2 review / continuous-family and adjoint audit roadmap / no sign or RH claim

---

## 0. Review result

The current implementation in `PascalCenteredXiPrimeSideQuadraticizationAudit` is Green through Gate 4B.3c2.

Verified surfaces:

```text
source-derived centered right-edge node z_W(t)
  GREEN

finite vertical amplitude A_X(t)
  GREEN

RH tau=0 weight = generic Mellin quadratic weight
  GREEN

deoriented factorization q_epsilon(z_W(t)) * A_X(t)
  GREEN

linear box feature B_X(t,u)
  GREEN

normalized u-average of B_X(t,u) = q_epsilon(z_W(t)) * A_X(t)
  GREEN

source-derived adjoint partner
  OPEN

continuous/L2 Gram provider
  OPEN

prime-side PSD bridge
  OPEN
```

The implementation correctly keeps the three variables distinct:

```text
n : arithmetic von-Mangoldt mode

t : contour-height / source-node coordinate

u : logarithmic Mellin-box feature coordinate
```

No theorem currently identifies these variables with one another.

---

## 1. Exact continuous-feature interpretation now available

Write the source-derived node and amplitude as

```text
z_W(t) := pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode W t

A_X(t) := pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude W X t
```

The implemented box feature has the exact shape

$$
B_X(t,u)=z_W(t)^2 e^{u z_W(t)}A_X(t).
$$

This has a canonical interpretation using the generic Gram feature `z * exp(u*z)`.

Define conceptually

$$
c_X(t):=z_W(t)A_X(t),\qquad \phi_W(t,u):=z_W(t)e^{u z_W(t)}.
$$

Then

$$
B_X(t,u)=c_X(t)\phi_W(t,u).
$$

This is source-derived and does not identify the arithmetic index `n` with a Gram node.

Recommended next API names:

```lean
pascalCenteredXiPrimeSideQuadraticizationCoefficientDensity
pascalCenteredXiPrimeSideQuadraticizationGramFeature
pascalCenteredXiPrimeSideQuadraticizationBoxFeature_eq_coefficient_mul_feature
```

The coefficient density should depend on `t`; the cutoff `X` remains inside the amplitude.

---

## 2. The natural continuous family is over contour height t

The generic finite Gram theorem uses a finite family of nodes and coefficients.  The source-derived RH analogue is naturally a continuous family indexed by the finite contour interval in `t`, not by the prime index `n`.

Define the aggregated box feature

$$
F_{\varepsilon,W,X}(u):=\int_{-T}^{T}B_X(t,u)\,dt.
$$

Suggested API:

```lean
pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature
```

The current pointwise box-average theorem suggests the linear vertical identity

$$
\frac1{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}F_{\varepsilon,W,X}(u)\,du=\int_{-T}^{T}q_\varepsilon(z_W(t))A_X(t)\,dt.
$$

This requires only a finite-rectangle integral swap once the needed continuity / interval-integrability obligations are discharged.

This theorem is a linear-source identity, not a positivity theorem.

---

## 3. The continuous PSD candidate is a different object

The source-derived continuous Gram energy suggested by the generic feature construction is

$$
E^{\mathrm{cont}}_{\varepsilon,W,X}:=\frac1{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}\lvert F_{\varepsilon,W,X}(u)\rvert^2\,du.
$$

Suggested API:

```lean
pascalCenteredXiPrimeSideQuadraticizationContinuousGramEnergy
```

At fixed positive `epsilon`, nonnegativity should be immediate from `Complex.normSq_nonneg` after interval-integrability is proved.

However the actual vertical source supplied by the explicit formula is the linear average of `F(u)`, while the PSD object is the norm-square average of `F(u)`.

Therefore the following implication is forbidden without an additional theorem:

```text
continuous Gram energy >= 0
  therefore
prime-side vertical source has the required sign
```

These are different functionals.

---

## 4. Gate 4B.3c3 — what counts as a genuine adjoint provider

The canonical algebraic adjoint of the aggregated feature is simply

```text
star F(u)
```

but defining it is not enough.

A source-derived adjoint provider must identify an already justified prime-side / mirror / horizontal / correction surface whose exact value is the required conjugate partner, or otherwise derive a product pairing from the explicit-formula source itself.

A valid provider must support an identity of the schematic form

$$
\text{source-derived quadratic surface}=\frac1{2\varepsilon}\int F(u)\overline{F(u)}\,du.
$$

It is not acceptable to introduce `star F` as a new auxiliary definition and then call the resulting norm square the arithmetic source.

The source must generate the second factor independently.

---

## 5. Current mirror information does not yet supply this finite-cutoff adjoint

Gate 4A proved mirror symmetry for the full fixed-Xi source, but it did not produce a finite von-Mangoldt cutoff conjugate/adjoint identity.

The current Gate 4B.3c2 vertical amplitude contains:

```text
finite prime cutoff
archimedean correction
elementary correction
```

The top-horizontal correction is intentionally outside that amplitude.

Therefore the next audit must separately ask whether the required adjoint is supplied by:

```text
A. t -> -t conjugation of the complete finite vertical amplitude
B. left/right contour pairing
C. functional-equation reflection after finite-cutoff completion
D. top-horizontal correction
E. radial comparison term
F. none of the above
```

Reality or mirror symmetry alone is insufficient.  The theorem must create the Hermitian second factor needed by the quadratic energy.

---

## 6. Continuous Gram expansion target

If the continuous family is introduced, the corresponding off-diagonal form should have two independent contour variables `t` and `s`.

The formal target is the continuous analogue of the generic Gram form:

$$
\iint c_X(t)\overline{c_X(s)}K_\varepsilon(z_W(t),z_W(s))\,dt\,ds.
$$

Expanding the coefficient density gives the same cross terms as the norm square of the aggregated feature.

This is where the two-index structure belongs in the RH source audit: the second index is another contour-height variable, not a second von-Mangoldt mode inserted by hand.

No double-integral theorem is required before the simpler norm-square energy surface is established.

---

## 7. Top-horizontal and radial firewall

Even a Green continuous vertical Gram energy would not yet prove positivity of the full scalar excess.

The current whole source still contains a top-horizontal contribution, and the scalar excess also subtracts the radial comparison term.

Thus Gate 4B.3 must preserve the ledger:

```text
vertical linear source
+ top-horizontal correction
- radial comparison
```

A future completion-of-squares argument would have to show exactly how the horizontal and radial pieces participate.  They must not be silently absorbed into the continuous vertical energy.

In particular, no theorem may infer the finite scalar-excess sign from vertical Gram positivity alone.

---

## 8. Recommended next checkpoint

### Gate 4B.3c3-A — continuous coefficient / feature API

Implement:

```text
coefficient density c_X(t)
generic feature phi_W(t,u)
BoxFeature = c_X(t) * phi_W(t,u)
aggregated feature F_X(u)
```

### Gate 4B.3c3-B — finite rectangle linear reconstruction

Prove, if the installed interval-integral API permits cleanly:

```text
normalized u-average of aggregated feature
  =
finite deoriented vertical integral
```

Do not add limits.

### Gate 4B.3c3-C — continuous Gram energy

Define the norm-square energy of the aggregated feature and prove fixed-`epsilon` nonnegativity.

This certifies only the continuous feature family, not the prime-side sign.

### Gate 4B.3c3-D — adjoint source search

Audit the existing finite source surfaces for an exact provider of `conj(F_X(u))` or an equivalent Hermitian partner.

If found, prove the exact provider theorem before using positivity.

If not found, record a named obstruction such as:

```text
PrimeSideContinuousAdjointProviderGap
```

The obstruction must mean only that the current source ledger lacks the required theorem.  It must not claim that no analytic or spectral provider can exist.

### Gate 4B.3c4 — whole-excess quadraticization

Only after a genuine adjoint/provider is established should the project attempt to connect the PSD energy to the top-horizontal and radial terms and hence to the finite scalar excess.

---

## 9. Stop conditions

Do not:

```text
identify n with t or u
use prime modes as Gram nodes without a theorem
manufacture the adjoint by definition and call it source-derived
drop archimedean or elementary corrections
fold the top-horizontal term into the vertical amplitude by convention
ignore the radial comparison
infer sign from reality or Hermitian symmetry alone
exchange X and epsilon limits
introduce T -> infinity
claim RH
```

---

## 10. Current status

```text
Gate 4B.2 generic Mellin PSD kernel
  CLOSED / GREEN

Gate 4B.3c0 index semantics
  GREEN

Gate 4B.3c1 finite vertical amplitude
  GREEN

Gate 4B.3c2 linear box-feature reconstruction
  GREEN

Gate 4B.3c3 continuous/L2 family and adjoint search
  NEXT

Gate 4B.3c4 source-derived PSD bridge to whole excess
  OPEN
```

The next load-bearing question is now precise: the source-derived continuous feature is available, but does the finite explicit-formula ledger supply its Hermitian adjoint partner?