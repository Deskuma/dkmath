# IPSM-004 — Gate 3B.0 review and Gate 3B.1 energy-provider contract

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / next-step contract / no RH claim

---

## 0. Review result

The following checkpoint is Green and should be retained.

```text
Gate 1
  normalized real four-term decomposition

Gate 2
  ordered-limit sign transport

Gate 3A
  scalar orientation layer
  scalar surface
  scalar excess
  excess = -pi * finite defect

Gate 3B.0
  genuine source-level complex reconstruction
```

The Gate 3B.0 implementation now starts from the original finite right-edge contour quantities, deorients them in `ℂ`, retains the top-horizontal source as a complex quantity, and only then projects the whole complex surface to its real part.

This fixes the semantic issue identified in IPSM-003.

---

## 1. Gate 3B.0 exact source chain

The following source-level pieces are now explicit.

```lean
pascalCenteredXiMellinQuadraticOrientedPrimeSurface
pascalCenteredXiMellinQuadraticOrientedArchimedeanSurface
pascalCenteredXiMellinQuadraticOrientedElementarySurface
```

The vertical deorientation is performed by

```lean
pascalCenteredXiVerticalDeorient
```

with the source-level complex operation applied before real projection.

The genuine vertical and whole complex surfaces are then defined by

```lean
pascalCenteredXiMellinQuadraticComplexVerticalSurface
pascalCenteredXiMellinQuadraticComplexWholeSurface
```

The load-bearing representation theorem is

```lean
pascalCenteredXiMellinQuadraticComplexWholeSurface_re_eq_scalarSurface
```

and the sign target is transported to the genuine complex carrier by

```lean
pascalCenteredXiMellinQuadraticScalarExcess_eq_complexWholeSurface_re_sub_radial
```

Thus the finite scalar excess is now represented without reconstructing lost imaginary data.

$$
E_{\varepsilon,X}(W)=\operatorname{Re}\mathcal W_{\varepsilon,X}(W)-\pi Q(W.R).
$$

Together with Gate 3A,

$$
E_{\varepsilon,X}(W)=-\pi D_{\varepsilon,X}(W).
$$

No sign conclusion follows from these identities alone.

### Review classification

```text
Gate 3B.0 source semantics:
  GREEN

Complex information retention:
  GREEN

Finite sign theorem:
  NOT PRESENT

Square / energy representation:
  NOT PRESENT
```

---

## 2. Important comparison with the existing zero-side energy

The repository already contains the finite zero-side anti-mirror energy

```lean
pascalCriticalMirrorZeroWindowAntiMirrorEnergy
```

and, on boundary-safe radii,

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional_eq_antiMirrorEnergy
```

identifies the fixed Xi defect with that nonnegative energy.

This is useful as a consistency surface, but it is not the missing prime-side provider.

The zero-side identity has the direction

```text
fixed Xi defect
  = anti-mirror norm-square energy
  >= 0
```

whereas the prime-side objective requires an independent mechanism for the opposite finite sign after ordered limiting.

Therefore Gate 3B.1 must not repackage the existing anti-mirror energy as the new provider.

If a proposed prime-side energy is definitionally or theorem-wise reducible to

```lean
pascalCenteredXiFixedSecondMomentDefectFunctional
pascalCriticalMirrorZeroWindowAntiMirrorEnergy
pascalCriticalMirrorZeroWindowHorizontalEnergy
```

then it is not independent enough for the present sign search.

---

## 3. Gate 3B.1 acceptance criterion

A candidate finite complex energy is acceptable only if all of the following are visible in its theorem surface.

### A. Prime-side construction

The object must be built from finite arithmetic / contour source data such as

```text
finite von Mangoldt cutoff
Mellin quadratic weight
archimedean correction
elementary correction
top-horizontal source
residue-window geometry
```

and not from a zero-window sum or the fixed defect itself.

### B. Nonnegativity by construction

The nonnegativity proof must come from an independently recognizable positive object, for example

```text
Complex.normSq
finite sum of nonnegative norm squares
integral of a nonnegative square mass
Gram / inner-product positive-semidefinite form
CF2D q2 with an independently established comparison
```

It is not acceptable to define

```text
energy := scalarExcess
```

and then place `0 <= energy` in a provider field.

That would only rename the desired sign theorem.

### C. Exact bridge to the scalar excess

The candidate must prove one of the following kinds of statements from exact algebra.

```text
scalarExcess = energy

energy <= scalarExcess

scalarExcess = energy + independently nonnegative remainder
```

A mere correlation, asymptotic analogy, or common limit target is not sufficient.

### D. Finite-window discipline

The bridge must retain the current finite rectangle height and top-horizontal contribution.

Do not introduce

```text
T -> infinity
horizontal disappearance
X <-> epsilon exchange
joint limit
```

inside Gate 3B.1.

---

## 4. Structural form of the energy problem

The genuine whole surface is a complex linear contour quantity, while a manifestly nonnegative energy is normally quadratic.

Therefore the missing theorem cannot arise merely from naming the current complex surface.

The load-bearing question is whether the exact source algebra admits a completion of square or a positive-semidefinite pairing in which the radial term is the diagonal part.

A successful identity would have a schematic form such as

```text
Re(complexWholeSurface)
  = pi * radialMass + positiveEnergy
```

or more generally

```text
Re(complexWholeSurface) - pi * radialMass
  = positiveEnergy + positiveRemainder.
```

That left-hand side is exactly the scalar excess.

This is the central Gate 3B.1 question.

---

## 5. Recommended Gate 3B.1 audit order

Do not begin by guessing a global square identity.  Inspect the source in the following order.

### Step 1 — pointwise deoriented integrands

Name the deoriented prime, archimedean, and elementary integrands before interval integration.

The goal is to expose the finite complex algebra at a single height `t`.

Suggested naming family:

```text
pascalCenteredXiMellinQuadraticPrimeDeorientedIntegrand
pascalCenteredXiMellinQuadraticArchimedeanDeorientedIntegrand
pascalCenteredXiMellinQuadraticElementaryDeorientedIntegrand
pascalCenteredXiMellinQuadraticDeorientedVerticalIntegrand
```

Then prove that their interval integrals reconstruct the existing complex vertical surface.

### Step 2 — isolate the radial comparison term

Expose `pi * radialMass` as a named scalar comparison target rather than hiding it only inside `scalarExcess`.

Do not identify it with a positive arithmetic form unless an exact theorem supplies that identification.

### Step 3 — search for pointwise quadratic completion

At each fixed `t`, test whether the deoriented vertical source plus the horizontal boundary bookkeeping admits an identity of the form

```text
radial diagonal
+ cross term
+ conjugate cross term
= norm square
```

or a finite Gram form.

If this fails already pointwise, record that failure before trying an integrated identity.

### Step 4 — finite integral / finite sum lift

Only after a pointwise or finite-sum positive identity is explicit should it be lifted through the finite interval integral and finite von Mangoldt sum.

### Step 5 — decision

There are only two acceptable outcomes.

```text
A. independent positive energy found
   -> prove exact excess bridge
   -> Gate 3B.2 finite sign theorem

B. no independent positive decomposition follows
   -> record named obstruction
   -> do not insert the desired sign as a hypothesis
```

---

## 6. Strong warning about tautological energies

Because Gate 3A already proves

$$
0\le E_{\varepsilon,X}(W)\iff D_{\varepsilon,X}(W)\le0,
$$

any unconditional proof of finite excess nonnegativity is already the missing finite sign theorem.

Therefore a structure like

```lean
structure PascalCenteredXiPrimeSideEnergyProvider where
  energy : ℝ
  energy_nonneg : 0 ≤ energy
  excess_eq_energy : scalarExcess = energy
```

is acceptable only if `energy` itself is concretely constructed from source-level data and `energy_nonneg` is proved from that construction.

If `energy` is opaque, arbitrary, or defined from `scalarExcess`, the structure is logically empty and must be rejected.

---

## 7. Existing zero-side energy is a diagnostic, not a provider

The finite anti-mirror identity is still valuable for auditing any proposed prime-side energy.

At the ordered endpoint, a genuine opposite-sign prime-side energy would meet the already Green zero-side identity on the same fixed Xi defect.

Therefore any successful Gate 3B provider should ultimately explain why the same scalar that is represented zero-side as anti-mirror square mass acquires an opposite inequality from arithmetic source data.

That is precisely the nontrivial mathematical content being sought.

Do not hide this collision inside a definition.

---

## 8. Next implementation checkpoint

Recommended next checkpoint:

```text
Gate 3B.1a
  pointwise deoriented source integrands
  exact reconstruction of complex vertical surface

Gate 3B.1b
  explicit radial comparison target
  pointwise / finite-sum quadratic-completion audit

Gate 3B.1c
  finite positive energy identity
  OR named obstruction
```

Suggested module strategy:

```text
keep PascalCenteredXiPrimeSideWholeSurfaceEnergyAudit.lean
for representation and local audit,

split a new module only if a genuine positive form is found.
```

Possible new module name after a successful discovery:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteEnergyProvider
```

Do not create that module merely to hold an assumed sign.

---

## 9. Non-goals

IPSM-004 introduces no claim of:

```text
finite scalar excess nonnegativity
finite arithmetic defect nonpositivity
prime term definite sign
correction term definite sign
positive energy existence
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

Gate 3A:
  GREEN

Gate 3B.0 genuine complex reconstruction:
  GREEN

Next:
  Gate 3B.1a pointwise source reconstruction
  -> Gate 3B.1b quadratic-completion audit
  -> Gate 3B.1c positive energy OR named obstruction
```

The key rule for the next phase is simple:

```text
nonnegativity must come from the internal structure of a concretely constructed source-level energy,
not from a renamed scalar-excess sign assumption.
```
