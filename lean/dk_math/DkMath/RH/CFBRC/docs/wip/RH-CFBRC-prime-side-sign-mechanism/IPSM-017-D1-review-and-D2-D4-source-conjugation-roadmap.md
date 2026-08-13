# IPSM-017 — D1 review and D2–D4 source-conjugation roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B.3c3-D audit / no sign claim / no RH claim

---

## 0. Review result

The new right-edge geometry theorem is Green:

```lean
pascalCenteredXiPrimeSideQuadraticizationRightEdgeNode_neg_eq_conj
```

It proves that the source-derived centered node at `-t` is the complex conjugate of the node at `t`.

The named gap

```lean
PascalCenteredXiPrimeSideQuadraticizationAdjointProviderGap.currentFiniteLedger
```

is also acceptable as an audit marker. It must continue to be read only as “the current finite ledger has not yet supplied the required provider”, not as a theorem that no provider can exist.

Current classification:

```text
right-edge centered geometry conjugation   GREEN
continuous Gram energy                     GREEN
finite PHZ conjugation                     OPEN
archimedean conjugation                    OPEN
elementary conjugation                     OPEN
full vertical amplitude conjugation        OPEN
source-derived aggregate adjoint            OPEN
quadraticization bridge                    OPEN
prime-side sign                            NOT CLAIMED
RH                                         NOT CLAIMED
```

---

## 1. Important provider-contract correction

The current structure contains

```lean
source_derived : Prop
```

as a free data field. This does not require evidence that the adjoint came from an existing source observable. A constructor may choose any proposition there, including `True` or `False`.

Therefore do not treat this field as a provenance certificate and do not instantiate the current provider merely by defining a conjugate function.

After D2–D4 are resolved, replace or supplement it with a theorem-bearing contract whose fields explicitly identify the source observable used to obtain the adjoint. The contract should contain an equality produced by the finite source symmetry itself, rather than a free `Prop` label.

---

## 2. D2 — finite PHZ conjugation

Target a source-level theorem before touching the full amplitude.

Suggested theorem shape:

```lean
pascalPrimePowerPHZFiniteUpTo_conj
    (X : ℕ) (s : ℂ) :
    pascalPrimePowerPHZFiniteUpTo X (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalPrimePowerPHZFiniteUpTo X s)
```

The preferred proof surface is the already-established finite von-Mangoldt expansion:

```lean
pascalPrimePowerPHZFiniteUpTo_eq_vonMangoldt_sum
```

Each coefficient `ArithmeticFunction.vonMangoldt q` is real. The remaining obligation is conjugation of the complex power with natural-number real base. The pinned Mathlib API should be checked by compilation; current Mathlib exposes `Complex.cpow_conj` / `Complex.conj_cpow` for this purpose.

Keep the `q = 0` totalization visible if simplification does not close it automatically. Do not replace the finite PHZ by an infinite L-series in this theorem.

Acceptance condition for D2: exact equality at every finite `X`, with no `X → ∞` argument.

---

## 3. D3 — elementary correction conjugation

This should be algebraic and independent of the other two source terms.

Suggested theorem shape:

```lean
pascalXiElementaryLogDerivCorrection_conj
    (s : ℂ) :
    pascalXiElementaryLogDerivCorrection (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalXiElementaryLogDerivCorrection s)
```

The definition is the rational expression

```lean
-1 / s + 1 / (1 - s)
```

so the proof should use only the ring-homomorphism properties of complex conjugation and totalized inversion. No nonvanishing assumptions should be added merely for this identity.

Acceptance condition for D3: global pointwise equality.

---

## 4. D4 — archimedean correction conjugation

This is the most API-sensitive source component.

The target is:

```lean
pascalXiArchimedeanLogDeriv_conj
    (s : ℂ) :
    pascalXiArchimedeanLogDeriv (starRingEnd ℂ s) =
      starRingEnd ℂ (pascalXiArchimedeanLogDeriv s)
```

The definition is

```lean
-logDeriv Complex.Gammaℝ s
```

so a robust route is:

```text
Gammaℝ(conj s) = conj(Gammaℝ s)
  -> derivative conjugation
  -> logDeriv conjugation
  -> negative logDeriv conjugation
```

Current Mathlib provides `Complex.Gamma_conj` and derivative-star transport in `Mathlib.Analysis.Calculus.Deriv.Star` (`deriv_conj_conj`). `Gammaℝ` itself is defined from a positive-real `π` complex power times `Complex.Gamma`, so first expose a local `Gammaℝ` conjugation lemma if no direct theorem is available in the pinned version.

Do not infer this theorem from the completed-Xi functional equation. It is a local property of the archimedean factor and should remain independent of RH-specific mirror machinery.

Acceptance condition for D4: pointwise equality at the level used by the finite right-edge amplitude. If the totalized `logDeriv` API requires a narrower statement, record the exact hypotheses instead of hiding them.

---

## 5. Assemble full amplitude conjugation only after D2–D4

First expose ordinary right-edge conjugation:

```text
s_W(-t) = conj(s_W(t)).
```

Then combine D2, D3 and D4 to prove:

```lean
pascalCenteredXiPrimeSideQuadraticizationVerticalAmplitude_neg_eq_conj
```

with intended content

```text
A_X(-t) = conj(A_X(t)).
```

This theorem must still contain the finite PHZ cutoff `X`. No infinite-source replacement is allowed.

Next derive, using the already Green node identity:

```text
CoefficientDensity(-t) = conj(CoefficientDensity(t))
GramFeature(-t,u)       = conj(GramFeature(t,u))   for real u
BoxFeature(-t,u)        = conj(BoxFeature(t,u)).
```

These are source-conjugation facts, not positivity theorems.

---

## 6. Expected aggregate consequence: reality, not quadraticization

If

```text
BoxFeature(-t,u) = conj(BoxFeature(t,u))
```

is Green on the symmetric interval `[-T,T]`, then the natural next theorem is that the aggregated feature is real in the complex-conjugation sense:

```text
AggregatedBoxFeature W X u =
  conj(AggregatedBoxFeature W X u).
```

This is the strongest source-derived adjoint candidate currently visible from `t ↦ -t` symmetry.

At that point a genuine provenance theorem can state that the adjoint is supplied by the same mirrored finite source, rather than by syntactically defining `conj F`.

However this still does not identify the linear explicit-formula observable with the continuous Gram energy.

Keep the following distinction explicit:

```text
source reality / adjoint availability
  !=
Hermitian product identity
  !=
whole scalar-excess identity.
```

---

## 7. Existing contour mirror theorems do not close the product bridge

The currently available left/right and horizontal theorems provide additive identities such as:

```text
left vertical = right vertical
vertical pair = 2 * right
bottom horizontal = top horizontal
horizontal pair = 2 * top.
```

These are reflection and reality surfaces. They do not multiply a source by its adjoint and therefore do not by themselves produce `normSq` or the continuous Gram energy.

Do not turn an additive doubling theorem into a Hermitian product theorem by renaming the second copy “adjoint”.

---

## 8. Top-horizontal and radial firewall

Even if D2–D4 and aggregate reality are all Green, the continuous Gram energy is still built only from the vertical source family.

The finite arithmetic ledger still contains the explicit top-horizontal term, and the scalar excess also contains the radial subtraction.

Therefore the following remain separate obligations:

```text
vertical linear source -> vertical Gram energy       OPEN
top-horizontal contribution -> quadratic provider   OPEN
radial subtraction -> compatible positive form      OPEN
whole scalar excess -> PSD quantity                  OPEN
```

No vertical-source theorem may silently absorb those terms.

---

## 9. Next checkpoint

Recommended order:

```text
D2  finite PHZ conjugation
D3  elementary correction conjugation
D4  Gammaℝ / archimedean logDeriv conjugation
D5  full finite vertical amplitude conjugation
D6  coefficient / feature / BoxFeature conjugation
D7  symmetric-t aggregate reality
D8  hardened source-derived adjoint contract
```

After D8, re-evaluate the remaining quadraticization problem. The likely next question is no longer whether an adjoint exists, but whether the existing linear contour identity contains an exact polarization or autocorrelation identity producing the Hermitian product.

---

## 10. Non-goals

This checkpoint introduces no claim of:

```text
prime-side scalar excess nonnegativity
finite arithmetic defect nonpositivity
whole-excess = continuous Gram energy
horizontal absorption
radial absorption
limit exchange
joint limit
T -> infinity
fixed defect vanishing
Riemann Hypothesis
```
