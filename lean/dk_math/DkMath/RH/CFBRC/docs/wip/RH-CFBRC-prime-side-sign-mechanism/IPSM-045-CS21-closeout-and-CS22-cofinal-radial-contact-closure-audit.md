# IPSM-045 — CS21 closeout and CS22 cofinal radial-contact closure audit

## Status

CS21 is accepted as **Green-B** on branch
`wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`.

Verified CS21 ingredients:

- exact absolute defect/tail adapters;
- fixed-`ε` eventual smallness of the absolute tail projection;
- the cofinal finite upper-anchor contract;
- exact strength classification
  `CofinalFiniteUpperAnchorAt ε W r ↔ D_{ε,∞}(W) ≤ r`;
- a finite good-cutoff package and its endpoint upper-bound adapter;
- vanishing good-cutoff family implies the existing fixed-window vanishing upper envelope;
- the finite von-Mangoldt / archimedean / elementary / top-horizontal source ledger remains explicit;
- the missing independent cofinal upper-anchor provider remains a named gap.

No universal tail sign, monotonicity, terminal ceiling, infinite exchange,
endpoint sign, fixed-defect RH argument, or RH conclusion is authorized by
CS21.

---

## Why CS22 is a closure audit rather than a new sign attack

The CS21 condition

```text
D_{ε,X}(W) ≤ r
```

is not a new geometric object.  Earlier Q3 work already connected the finite
arithmetic defect to the finite prime-side scalar surface and the fixed radial
second moment.

Write conceptually

```text
Q_R := pascalCenteredXiFixedRadialSecondMomentFunctional W.R
S_{ε,X} := finite prime-side scalar surface
D_{ε,X} := Q_R - Re(normalized arithmetic approximant)
```

and reuse the existing theorem identifying

```text
S_{ε,X} = π * Re(normalized arithmetic approximant).
```

Then the exact relation is

$$
\pi D_{\varepsilon,X}
=
\pi Q_R-S_{\varepsilon,X}.
$$

CS22 should formalize this as a named **finite radial-contact deficit** and
prove that the CS21 cofinal anchor is precisely the cofinal/tolerant version
of the old Q3 radial-comparison frontier.

This is strategically important.  The long CS10--CS21 route should not create
an apparently new provider gap if it has in fact returned to the same finite
radial comparison in a weaker, better-targeted form.

---

## CS22-A — finite radial-contact deficit

Introduce a real-valued named quantity, for example

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteRadialContactDeficit
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  Real.pi * pascalCenteredXiFixedRadialSecondMomentFunctional W.R -
    pascalCenteredXiPrimeSideQuadraticizationScalarSurface ε W X
```

Use the exact scalar-surface name already present in the repository; do not
invent a duplicate surface if an existing definition can be reused.

Target theorem:

```text
FiniteRadialContactDeficit ε W X
  = π * D_{ε,X}(W).
```

The orientation must be checked carefully.  The intended sign convention is

```text
D_{ε,X} ≤ 0
↔
π Q_R ≤ S_{ε,X}.
```

Do not reverse this sign.

---

## CS22-B — pointwise finite anchor as radial contact

For arbitrary `r : ℝ`, prove an exact order adapter of the form

```text
D_{ε,X}(W) ≤ r
↔
FiniteRadialContactDeficit ε W X ≤ π * r.
```

Equivalently, expose the scalar-surface form

$$
D_{\varepsilon,X}\le r
\iff
\pi(Q_R-r)\le S_{\varepsilon,X}.
$$

This is finite algebra only.  It is not a provider.

For `r = 0`, recover the original radial comparison exactly:

```text
D_{ε,X} ≤ 0
↔
π Q_R ≤ S_{ε,X}.
```

If the older Q3 theorem already states this, prove the new theorem by reusing
it rather than duplicating the algebra.

---

## CS22-C — cofinal radial-contact contract

Define a cofinal finite radial-contact contract directly in geometric units.
A convenient shape is

```lean
def PascalCenteredXiPrimeSideCofinalRadialContactAt
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (R : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ, N ≤ X ∧
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X ≤ R + η
```

The capital `R` above is only a tolerance target and may be renamed to avoid
confusion with `W.R`.

Then prove the scaling equivalence, using `Real.pi_pos` explicitly:

```text
CofinalFiniteUpperAnchorAt ε W r
↔
CofinalRadialContactAt ε W (π * r).
```

Because the two contracts quantify over arbitrary positive tolerances, the
proof must transport tolerance in both directions by multiplying/dividing by
`π`; do not silently identify the two tolerances.

---

## CS22-D — zero-target cofinal radial contact

Specialize the preceding theorem to `r = 0`.

The geometric target becomes

$$
\forall \eta>0,\ \forall N,\ \exists X\ge N:
\pi Q_R-S_{\varepsilon,X}\le\eta.
$$

Equivalently,

$$
S_{\varepsilon,X}\ge\pi Q_R-\eta.
$$

Name this zero-target form if it improves readability, for example

```lean
PascalCenteredXiPrimeSideCofinalRadialContactZeroAt ε W
```

or retain the general contract with target `0`.

This formulation deliberately allows:

- oscillation in `X`;
- temporary overshoot;
- negative individual prime-power modes;
- cancellation between distinct prime rays.

It asks only for arbitrarily late finite surfaces that approach the radial
mass from below up to arbitrary tolerance.

---

## CS22-E — reconnect to CS21 endpoint classification

Combine CS21 with CS22-C to expose the exact fixed-`ε` strength theorem

```text
CofinalRadialContactAt ε W (π * r)
↔
D_{ε,∞}(W) ≤ r.
```

In particular,

```text
CofinalRadialContactAt ε W 0
↔
D_{ε,∞}(W) ≤ 0.
```

This theorem is a **strength classification**, not an independent prime-side
proof of the left-hand side.

Do not use fixed-defect nonnegativity to prove the contact contract.

---

## CS22-F — vanishing family adapter

If useful, define a family-level radial-contact package corresponding exactly
to the CS21 `VanishingGoodCutoffFamily` / CS9 vanishing upper-envelope route.

The minimal useful statement is that a family of cofinal radial contacts with
a target `r(ε)` satisfying

```text
r(ε) → 0
```

provides the existing vanishing upper envelope after applying the CS21
endpoint classification.

Avoid introducing a stronger universal-in-`X` condition.

The family may be kept as a theorem over an existing function `r` rather than
a new structure if that minimizes API surface.

---

## CS22-G — close the research loop explicitly

Add a theorem or documented theorem chain making the following equivalence
visible at fixed positive `ε`:

```text
cofinal finite arithmetic upper anchor
↔
cofinal finite radial contact
↔
endpoint upper bound.
```

This should be described as the **CS10--CS22 closure loop**:

```text
finite prime source
→ signed tail
→ natural modes
→ prime-power rays
→ geometric compression
→ polarization / q2
→ aggregate imbalance
→ good cofinal cutoff
→ radial-contact deficit
→ original finite radial comparison surface.
```

The purpose is to prove that the route has not hidden a new sign assumption.
It has instead identified the weakest cofinal form of the original Q3
comparison that is sufficient for the endpoint argument.

---

## CS22-H — source frontier

If no independent source-derived cofinal radial-contact theorem is available,
record a named gap, for example

```lean
inductive PascalCenteredXiPrimeSideCofinalRadialContactGap : Prop
  | noIndependentCofinalRadialContactProvider
```

This gap is expected to be equivalent in strength to the CS21 cofinal-anchor
gap at fixed `ε`; the value of CS22 is the geometric identification, not a new
provider.

Do not leave both gaps looking like unrelated mathematical obligations.
Document their exact equivalence.

---

## Provider firewall

CS22 must not use any of the following as a proof of cofinal radial contact:

- fixed-Xi defect nonnegativity;
- horizontal zero energy;
- fixed-defect vanishing / all-window-zeros-critical equivalence;
- an RH hypothesis or RH-equivalent zero-side theorem;
- synthetic `S_{ε,X} ≥ π Q_R` assumptions;
- universal mode positivity;
- universal cutoff monotonicity;
- universal tail sign;
- an infinite sum/integral exchange not already certified.

Existing zero-side theorems may be cited only in comments or later strength
classification, never as the prime-side contact provider.

---

## Green criteria

CS22 is **Green-B** if it closes all of the following without a synthetic
provider:

1. define the finite radial-contact deficit from existing finite scalar and
   radial surfaces;
2. prove `FiniteRadialContactDeficit = π * D_{ε,X}` exactly;
3. prove the pointwise finite-anchor/radial-contact equivalence;
4. define the cofinal radial-contact contract;
5. prove cofinal-anchor ↔ cofinal-radial-contact with correct `π` tolerance
   scaling;
6. reconnect the cofinal radial contact to the CS21 endpoint upper-bound
   classification;
7. make the CS10--CS22 closure loop explicit;
8. retain any missing independent radial-contact provider as a named gap.

No endpoint sign, fixed-defect sign, vanishing fixed defect, or RH conclusion
is authorized in this checkpoint.
