# IPSM-002 — Gate 1/2 review and Gate 3A roadmap

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / next-step roadmap / no RH claim

---

## 0. Purpose

This note reviews the implemented module

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
```

and fixes the next implementation target before beginning the whole-surface sign search.

The purpose is not to introduce a sign provider.  It is to preserve the separation between:

```text
representation
order-closed limit transport
actual prime-side sign mechanism
```

The sign mechanism remains open.

---

## 1. Gate 1 review — Green

Implemented surface:

```text
prime contribution
archimedean contribution
elementary contribution
top-horizontal contribution
```

Each term is named as the real part of the normalized finite arithmetic contribution, and the theorem

```lean
pascalCenteredXiMellinQuadraticNormalizedArithmeticApproximant_re_eq_four_terms
```

proves the exact four-term decomposition.

Review result:

```text
GREEN
```

Important properties preserved by the implementation:

```text
- finite top-horizontal contribution is retained
- no term is assigned a definite sign
- no T → ∞ argument is introduced
- no X ↔ ε exchange is introduced
- no RH-equivalent provider is hidden in the representation layer
```

This is the correct Gate 1 scope.

---

## 2. Gate 2 review — Green

Implemented adapters:

```lean
pascalCenteredXiArithmeticDefectEndpoint_nonpos_of_eventually_approximant_nonpos
pascalCenteredXiFixedDefect_nonpos_of_eventually_endpoint_nonpos
```

Both use `le_of_tendsto` only to preserve membership in the closed order half-line `(-∞, 0]` under the already-proved ordered limits.

Review result:

```text
GREEN
```

The logical direction remains conditional:

$$
(\forall^{\mathrm{eventually}} X,\ D_{\varepsilon,X}(W)\le0)\Longrightarrow D_\varepsilon(W)\le0.
$$

$$
(\forall^{\mathrm{eventually}} \varepsilon\to0^+,\ D_\varepsilon(W)\le0)\Longrightarrow D_\Xi(W.R)\le0.
$$

No finite-cutoff sign theorem is asserted.  The adapters therefore do not constitute a defect-vanishing or RH provider.

---

## 3. Integration note — public import still pending

At the reviewed branch state, `DkMath/RH.lean` imports

```text
DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
```

but does not yet publicly import

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
```

The module-specific build can therefore be Green while public-root reachability remains unchecked.

Recommended integration step after the next local edit:

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
```

followed by the project-standard root validation.

This is an integration item only, not a mathematical Gap.

---

## 4. Gate 3 should begin with orientation normalization

Do not begin Gate 3 by postulating a square or energy identity.

First expose the exact real scalar carried by the finite arithmetic surface after the `(2πi)⁻¹` normalization.

The right-edge prime, archimedean, and elementary terms are vertical contributions whose displayed integrands carry the path-orientation factor `Complex.I`.

For such a vertical base contribution `V`, the normalized doubled contribution has the algebraic form

$$
(2\pi i)^{-1}\,2(Vi)=V/\pi.
$$

Therefore its real part is the real part of the vertical base divided by `π`.

The top-horizontal contribution has a different path orientation and must not be folded into this rule blindly.  For a top contribution `H`,

$$
\operatorname{Re}((2\pi i)^{-1}\,2H)=\operatorname{Im}(H)/\pi.
$$

This orientation difference should be made explicit in Lean before any sign argument.

---

## 5. Gate 3A — normalized scalar surface

Introduce named base observables, or equivalent helper theorems, so that the three vertical corrections and the top-horizontal correction are represented without an opaque outer complex normalization.

Candidate theorem surface:

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_re_div_pi
pascalCenteredXiMellinQuadraticNormalizedArchimedeanContribution_eq_re_div_pi
pascalCenteredXiMellinQuadraticNormalizedElementaryContribution_eq_re_div_pi
pascalCenteredXiMellinQuadraticNormalizedTopContribution_eq_im_div_pi
```

The exact naming may follow the local API, but the mathematical target is the same.

Then define or expose a whole vertical base surface

```text
V_{ε,X}
  = prime vertical base
  + archimedean vertical base
  + elementary vertical base
```

and retain a separate top-horizontal base `H_ε`.

The normalized arithmetic real surface should then reduce to a single scalar identity of the form

$$
\operatorname{Re}A_{\varepsilon,X}(W)=\bigl(V_{\varepsilon,X}^{\mathrm{re}}(W)+H_\varepsilon^{\mathrm{im}}(W)\bigr)/\pi.
$$

This is the preferred Gate 3A normal form.

---

## 6. Prime-side excess — same scalar target for the sign audit

After Gate 3A, define the scalar excess

$$
E_{\varepsilon,X}(W):=V_{\varepsilon,X}^{\mathrm{re}}(W)+H_\varepsilon^{\mathrm{im}}(W)-\pi Q(W.R).
$$

Using the existing defect definition, target an exact identity

$$
E_{\varepsilon,X}(W)=-\pi D_{\varepsilon,X}(W).
$$

Since `π > 0`, this gives the equivalent finite sign target

$$
0\le E_{\varepsilon,X}(W)\Longleftrightarrow D_{\varepsilon,X}(W)\le0.
$$

This is the quantity that later square / energy candidates should realize.

Do not use `D_{ε,X} ≤ 0` itself as a provider in the Gate 3 implementation.  The point of `E_{ε,X}` is to expose a prime-side scalar that can potentially acquire an independent structural representation.

---

## 7. Gate 3B — whole-surface square / energy audit

Only after Gate 3A and the exact excess identity are Green, search for an independent representation such as

```text
finite square sum
finite pair energy
integrated square mass
critical-mirror paired energy
CF2D q2 comparison
```

whose nonnegativity is structural and does not restate the desired defect sign.

The audit question is:

```text
Can the same scalar E_{ε,X}(W) be represented by an independently nonnegative object?
```

A successful route would have the shape

```text
E_{ε,X}(W)
  = independently nonnegative finite energy
```

followed by Gate 2 transport.

An unsuccessful route should be recorded as a named obstruction rather than patched with a sign assumption.

Suggested obstruction name if needed:

```text
PascalCenteredXiPrimeSideWholeSurfaceEnergyObstruction
```

---

## 8. What must not be dropped

Gate 3 must continue to preserve the finite explicit-formula bookkeeping.

```text
- prime term alone is not the whole surface
- archimedean correction remains present
- elementary correction remains present
- top-horizontal correction remains present
- fixed finite height remains present
```

In particular, the top-horizontal term is structurally indispensable until an independent theorem proves a valid elimination or absorption mechanism.

Do not infer full-surface sign from `vonMangoldt n ≥ 0`.

The continuous-frequency audit in IPSM-001 already shows that the quadratic Mellin kernel retains oscillatory frequency dependence, so coefficient positivity alone is not a sufficient sign mechanism.

---

## 9. Recommended next module

Keep the current Gate 1/2 module stable.

Recommended new module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit
```

Suggested internal sequence:

```text
Gate 3A.1  orientation-normalized vertical helper identities
Gate 3A.2  top-horizontal imaginary normalization identity
Gate 3A.3  whole normalized scalar-surface identity
Gate 3A.4  prime-side excess definition
Gate 3A.5  excess = -π * finite defect
Gate 3A.6  excess nonnegative iff finite defect nonpositive
Gate 3B    independent square / energy search
```

The first six items are representation/algebra only.  They should be Green before introducing any new analytic sign argument.

---

## 10. Validation checkpoint

Current user-reported validation for Gate 1/2:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
./lb DkMath.RH.CFBRC.PascalCenteredXiPrimeSideSignAudit
git diff --check
```

all Green.

After adding the public import and Gate 3A module, also validate root reachability using the project-standard `DkMath.RH` build path.

---

## 11. Research checkpoint

```text
XDP representation block:
  COMPLETE

IPSM Gate 1:
  normalized real four-term decomposition
  GREEN

IPSM Gate 2:
  ordered-limit sign transport
  GREEN

IPSM Gate 3A:
  orientation normalization
  whole scalar surface
  prime-side excess exact identity
  NEXT

IPSM Gate 3B:
  independent whole-surface square / energy representation
  OPEN

IPSM Gate 4:
  independent inequality or named obstruction
  OPEN
```

No RH claim is made by this note.
