# IPSM-003 — Gate 3A semantic review and Gate 3B complex-surface roadmap

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / semantic correction / no RH claim

---

## 0. Review result

The following are Green and should be retained:

```text
Gate 1
  normalized real four-term decomposition

Gate 2
  ordered-limit nonpositivity transport

Gate 3A scalar layer
  scalar surface
  scalar excess
  excess = -pi * finite defect
  excess >= 0 iff finite defect <= 0
```

The public imports are also present in `DkMath.RH`:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
```

The finite scalar identity is valid and useful:

$$
E_{\varepsilon,X}(W)=-\pi D_{\varepsilon,X}(W).
$$

Hence the sign target is exactly:

$$
0\le E_{\varepsilon,X}(W)\iff D_{\varepsilon,X}(W)\le0.
$$

No sign theorem is present yet.

---

## 1. Important semantic distinction in the current Gate 3A implementation

The current definitions

```lean
pascalCenteredXiMellinQuadraticPrimeVerticalBase
pascalCenteredXiMellinQuadraticArchimedeanVerticalBase
pascalCenteredXiMellinQuadraticElementaryVerticalBase
```

are not yet the original complex right-edge quantities with the path-orientation `Complex.I` removed.

For example, the prime definition is currently constructed from the already real-valued normalized contribution:

```lean
(pascalCenteredXiMellinQuadraticNormalizedPrimeContribution ε W X : ℂ) *
  (Real.pi : ℂ)
```

Therefore its imaginary part is identically zero by construction.

The same is true for the current archimedean and elementary `VerticalBase` definitions.

So these three objects are mathematically valid scalar lifts, but they do not preserve the complex information of the original right-edge integrals.

This distinction does not invalidate Gate 3A scalar identities.  It matters only for Gate 3B, because a square / energy audit should not begin from a complex quantity whose imaginary part was discarded and then re-embedded into `ℂ`.

### Review classification

```text
Gate 3A scalar normalization:
  GREEN

Current VerticalBase naming/comment semantics:
  TOO STRONG

Use of current VerticalBase as a genuine complex energy carrier:
  DO NOT DO THIS
```

---

## 2. Source-level orientation fact

The XDP source objects genuinely carry the right-edge differential inside their integrands.

The prime cutoff integrand ends with:

```lean
* Complex.I
```

The archimedean right-edge integrand ends with:

```lean
* Complex.I
```

The elementary right-edge integrand ends with:

```lean
* Complex.I
```

Thus a genuine deorientation can be defined directly on the original complex contour quantity, before taking a real part.

A generic algebraic helper is sufficient:

```lean
noncomputable def pascalCenteredXiVerticalDeorient (z : ℂ) : ℂ :=
  -Complex.I * z
```

For an already oriented right-edge integral `z`, this retains all complex information while removing the path-orientation factor.

The normalization relation should be proved from the original complex `z`, not reconstructed from its normalized real part.

Conceptually:

$$
\operatorname{Re}\left((2\pi i)^{-1}(2z)\right)=\frac{\operatorname{Re}(-iz)}{\pi}.
$$

This is the genuine orientation theorem needed before Gate 3B.

---

## 3. Recommended Gate 3B.0 — genuine complex vertical surface

Introduce source-level oriented pieces using the original finite contour quantities.

Suggested structure:

```text
prime oriented right-edge quantity
archimedean oriented right-edge quantity
elementary oriented right-edge quantity
```

Then define their sum before real projection.

```lean
pascalCenteredXiMellinQuadraticOrientedVerticalSurface
```

and deorient only once:

```lean
pascalCenteredXiMellinQuadraticComplexVerticalSurface :=
  pascalCenteredXiVerticalDeorient
    pascalCenteredXiMellinQuadraticOrientedVerticalSurface
```

The exact source theorem should then identify its real part with the existing Gate 3A vertical scalar.

The important discipline is:

```text
original complex contour data
  -> deorientation in ℂ
  -> sum in ℂ
  -> real projection
```

not:

```text
original complex contour data
  -> normalized real projection
  -> cast back to ℂ
```

---

## 4. Top-horizontal term and a genuine whole complex surface

The top-horizontal contribution has the other contour orientation and currently contributes through its imaginary part.

Let the genuine deoriented vertical surface be `V` and the original top-horizontal complex contribution be `H`.

The Gate 3A scalar surface has the form:

$$
S_{\varepsilon,X}(W)=\operatorname{Re}V_{\varepsilon,X}(W)+\operatorname{Im}H_{\varepsilon}(W).
$$

But multiplication by `-i` converts the imaginary part of `H` into a real part:

$$
\operatorname{Re}(-iH)=\operatorname{Im}H.
$$

Therefore define a genuine whole complex surface candidate:

```lean
pascalCenteredXiMellinQuadraticComplexWholeSurface :=
  pascalCenteredXiMellinQuadraticComplexVerticalSurface -
    Complex.I * pascalCenteredXiMellinQuadraticHorizontalBase
```

Then the desired exact representation is:

$$
S_{\varepsilon,X}(W)=\operatorname{Re}\mathcal W_{\varepsilon,X}(W).
$$

This is a better Gate 3B input because `W` retains both real and imaginary information.

---

## 5. Excess in genuine complex form

The existing scalar excess should remain the sign target.

After the genuine whole complex surface is available, prove only the representation:

$$
E_{\varepsilon,X}(W)=\operatorname{Re}\mathcal W_{\varepsilon,X}(W)-\pi Q(W.R).
$$

Together with the already Green theorem:

$$
E_{\varepsilon,X}(W)=-\pi D_{\varepsilon,X}(W).
$$

This creates one scalar object for the entire sign audit without discarding the complex source data too early.

---

## 6. Gate 3B square / energy audit

Only after Sections 3–5 are Green should the actual energy search begin.

The target question is not to introduce a provider saying `0 <= E`.

The target question is whether the genuine source algebra yields an independent representation such as:

```text
E = explicit square mass
E = finite sum of nonnegative square masses
E = pair energy
E = CF2D q2 difference with an independently known orientation
```

or whether no such representation follows from the present identities.

A successful provider must expose its own mathematical content.  It must not merely contain a field equivalent to:

```lean
0 ≤ pascalCenteredXiMellinQuadraticScalarExcess ε W X
```

because that would simply rename the desired sign theorem.

If the exact algebra does not produce a square / energy decomposition, record a named obstruction rather than inserting the wanted inequality as an assumption.

Suggested module remains:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
```

but divide its internal status explicitly into:

```text
Gate 3A:
  scalar orientation / excess algebra

Gate 3B.0:
  genuine complex surface reconstruction

Gate 3B.1:
  square / energy search

Gate 3B.2:
  independent sign theorem or named obstruction
```

---

## 7. Recommended handling of the current `VerticalBase` names

Two safe choices exist.

### Option A — rename now

Rename the current three objects to make their actual role explicit, for example:

```text
PrimeVerticalScalarLift
ArchimedeanVerticalScalarLift
ElementaryVerticalScalarLift
```

This is semantically cleanest while the branch is still WIP.

### Option B — preserve names but demote their role

Keep the current names to avoid churn, but change comments to state that they are scalar lifts of normalized real contributions, not genuine deoriented contour quantities.

Then introduce new source-level names containing `Complex` or `Deoriented` for Gate 3B.

Option A is preferred before merge because the current comments say the path-orientation `I` was removed, which is stronger than what the definitions prove.

---

## 8. Next Green checkpoint

Before starting any positivity proof, require the following exact theorems to be Green:

```text
1. generic complex vertical deorientation identity
2. source-level prime deorientation identity
3. source-level archimedean deorientation identity
4. source-level elementary deorientation identity
5. genuine complex vertical surface definition
6. genuine complex whole surface definition
7. scalarSurface = re(complexWholeSurface)
8. scalarExcess = re(complexWholeSurface) - pi * radialMass
```

These are representation theorems only.

After that, inspect the genuine whole surface for a square / energy identity.

---

## 9. Non-goals

IPSM-003 introduces no claim of:

```text
finite scalar excess nonnegativity
finite arithmetic defect nonpositivity
prime term definite sign
correction term definite sign
square decomposition existence
T -> infinity
X <-> epsilon exchange
joint limit
fixed defect vanishing
Riemann Hypothesis
```

---

## 10. Checkpoint summary

```text
Gate 1:
  GREEN

Gate 2:
  GREEN

Gate 3A scalar algebra:
  GREEN

Gate 3A complex-carrier semantics:
  requires correction before energy search

Next:
  Gate 3B.0 genuine complex surface reconstruction
  -> Gate 3B.1 square / energy audit
  -> independent sign theorem or named obstruction
```
