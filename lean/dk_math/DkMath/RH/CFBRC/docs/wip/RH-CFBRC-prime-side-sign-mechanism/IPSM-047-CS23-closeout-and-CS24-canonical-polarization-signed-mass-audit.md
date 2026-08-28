# IPSM-047 — CS23 closeout and CS24 canonical polarization signed-mass audit

## Status

CS23 is **Green-B**.

The complete finite normalized source is now source-complete, and the finite radial-contact deficit has the exact form

$$G_{\varepsilon,W,X}=\pi\bigl(Q_R-\operatorname{CompleteSource}_{\varepsilon,W,X}\bigr).$$

CS23 also proves the abstract adapter

$$G=R-M,\qquad M\ge 0,\qquad R\le\eta\quad\Longrightarrow\quad G\le\eta,$$

and proves that the signed-mass equation together with `M ≥ 0` alone does **not** imply the required sign. The missing object is therefore no longer an adapter: it is a source-derived signed-mass/remainder certificate.

This document defines CS24. The purpose is to instantiate the mass part canonically from the already proved CS17 aggregate polarization, without importing any zero-side sign theorem or RH-equivalent provider.

## 1. Existing Green inputs

Use only the following already proved prime-side facts.

1. `PascalCenteredXiPrimeSideSignAudit`
   - exact four-term normalized real source
   - normalized prime contribution
   - normalized archimedean contribution
   - normalized elementary contribution
   - normalized top-horizontal contribution

2. CS17 `PascalCenteredXiPrimeSideNormalizedRayPolarizationOrderingAudit`
   - aggregate plus energy is nonnegative
   - aggregate minus energy is nonnegative
   - exact finite mode ledger

$$4\sum_{n\le X}\Lambda(n)K_{\varepsilon,W}(n)
=E^{\mathrm{agg}}_+(\varepsilon,W,X)-E^{\mathrm{agg}}_-(\varepsilon,W,X).$$

3. CS11/CS12 finite symmetric pairing machinery
   - conjugation on the right edge
   - finite interval integrability
   - full symmetric interval to half-interval real projection

4. CS22/CS23
   - finite radial-contact deficit
   - exact relation to the finite arithmetic defect
   - complete-source identity

No endpoint sign, fixed-Xi defect sign, RH frontier theorem, infinite prime sum exchange, or infinite Euler-product argument is allowed in CS24.

## 2. CS24-A — normalize the finite prime contribution exactly

The first task is to prove the exact normalization factor rather than assume it.

Target theorem shape:

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_two_div_pi_modeSum
```

with mathematical content

$$\operatorname{PrimeContribution}_{\varepsilon,W,X}
=\frac{2}{\pi}\sum_{n\le X}\Lambda(n)K_{\varepsilon,W}(n).$$

The proof should reuse the CS11 conjugation pattern for the finite PHZ source. Do not introduce an infinite sum. The source is the same finite symmetric right-edge integral already present in `pascalCenteredXiMellinQuadraticNormalizedPrimeContribution`.

Then combine it with CS17 to prove

$$\operatorname{PrimeContribution}_{\varepsilon,W,X}
=\frac{E^{\mathrm{agg}}_+(\varepsilon,W,X)-E^{\mathrm{agg}}_-(\varepsilon,W,X)}{2\pi}.$$

Suggested theorem name:

```lean
pascalCenteredXiMellinQuadraticNormalizedPrimeContribution_eq_aggregateEnergyDifference_div_two_pi
```

**Checkpoint:** if the Lean normalization produces a different sign or scalar factor, stop and correct the downstream formulas. Do not force the intended factor by algebraic rewriting.

## 3. CS24-B — isolate the correction-only source

Define the cutoff-independent correction source

```lean
pascalCenteredXiPrimeSideIndependentCorrectionSourceReal
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ
```

by

$$C_{\varepsilon,W}
=A_{\varepsilon,W}+E_{\varepsilon,W}+T_{\varepsilon,W},$$

where the three terms are the existing normalized archimedean, elementary, and top-horizontal contributions.

Prove the exact split

$$\operatorname{CompleteSource}_{\varepsilon,W,X}
=\operatorname{PrimeContribution}_{\varepsilon,W,X}+C_{\varepsilon,W}.$$

This is algebra only.

## 4. CS24-C — canonical mass and canonical remainder

Define

$$M^{\mathrm{can}}_{\varepsilon,W,X}
:=\frac12 E^{\mathrm{agg}}_+(\varepsilon,W,X),$$

and

$$R^{\mathrm{can}}_{\varepsilon,W,X}
:=\pi\bigl(Q_R-C_{\varepsilon,W}\bigr)
+\frac12E^{\mathrm{agg}}_-(\varepsilon,W,X).$$

Suggested Lean names:

```lean
pascalCenteredXiPrimeSideCanonicalPolarizationMass
pascalCenteredXiPrimeSideCanonicalPolarizationRemainder
```

Prove immediately from CS17:

```lean
pascalCenteredXiPrimeSideCanonicalPolarizationMass_nonneg
```

with

$$0\le M^{\mathrm{can}}_{\varepsilon,W,X}.$$

Then prove the central exact decomposition

$$G_{\varepsilon,W,X}
=R^{\mathrm{can}}_{\varepsilon,W,X}
-M^{\mathrm{can}}_{\varepsilon,W,X}.$$

Suggested theorem:

```lean
pascalCenteredXiPrimeSideFiniteRadialContactDeficit_eq_canonicalRemainder_sub_mass
```

This is the first desired source-derived instantiation of the abstract CS23 signed-mass equation.

## 5. CS24-D — identify the correction baseline with cutoff zero

Because the finite von-Mangoldt source vanishes at cutoff zero, audit whether the following exact identity holds:

$$B_{\varepsilon,W}
:=\pi\bigl(Q_R-C_{\varepsilon,W}\bigr)
=G_{\varepsilon,W,0}.$$

Do not assume this from intuition. Prove the zero-cutoff prime contribution and aggregate energies vanish using the actual repository cutoff convention.

If it closes, derive

$$R^{\mathrm{can}}_{\varepsilon,W,X}
=G_{\varepsilon,W,0}+\frac12E^{\mathrm{agg}}_-(\varepsilon,W,X).$$

This identity is useful for strength classification.

## 6. CS24-E — remainder strength audit

Since aggregate minus energy is nonnegative, prove

$$G_{\varepsilon,W,0}
\le R^{\mathrm{can}}_{\varepsilon,W,X}.$$

Therefore any cofinal small-remainder provider

$$\forall\eta>0\;\forall N\;\exists X\ge N:
R^{\mathrm{can}}_{\varepsilon,W,X}\le\eta$$

necessarily forces

$$G_{\varepsilon,W,0}\le0.$$

This is a **strength audit**, not a sign theorem.

It tells us whether the canonical cumulative-polarization decomposition is too strong: if its remainder requires an independent zero-cutoff contact theorem, then CS24 must record that fact rather than advertise the decomposition as a solved provider.

Suggested theorem shape:

```lean
pascalCenteredXiPrimeSideCanonicalRemainder_cofinalSmall_implies_zeroCutoff_nonpos
```

## 7. CS24-F — conditional provider adapter

Define a source-specific contract, if useful:

```lean
def PascalCenteredXiPrimeSideCanonicalPolarizationRemainderCofinalSmallAt ... : Prop :=
  ∀ η : ℝ, 0 < η → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧
    pascalCenteredXiPrimeSideCanonicalPolarizationRemainder ε W X ≤ η
```

Then prove

$$\text{canonical remainder cofinally small}
\Longrightarrow
\text{CS22 zero-target cofinal radial contact}.$$

The proof must use the exact canonical decomposition and the already proved mass nonnegativity. It must not simply invoke an equivalent endpoint-sign predicate.

## 8. What counts as progress

CS24 is **Green** only if it independently proves the canonical remainder is cofinally small from finite prime/correction structure.

CS24 is **Green-B** if it proves:

- the prime normalization factor exactly;
- the aggregate-energy expression for the normalized prime contribution;
- the correction-only split;
- a genuine source-derived nonnegative mass;
- the exact canonical signed-mass decomposition;
- the strength/necessary-condition audit;
- and leaves cofinal smallness as a named gap.

That Green-B outcome is still substantial: CS23's abstract `M` has then been replaced by a concrete nonnegative prime-side quadratic mass.

## 9. Firewall

Do not use any of the following as the remainder provider:

- fixed-Xi defect nonnegativity or vanishing;
- horizontal zero energy;
- `all zeros critical` or RH-equivalent statements;
- CS9 upper-envelope classification in the provider direction;
- CS21/CS22 cofinal-anchor/contact predicates merely renamed;
- terminal ceiling or universal tail sign;
- an infinite prime-ray or Euler-product exchange;
- an assumed ordering between aggregate plus and minus energies.

The only acceptable new sign input is a theorem derived from the finite source itself.

## 10. Expected next fork

After CS24 there are two legitimate outcomes.

### Route A — canonical remainder is tractable

If the correction baseline and aggregate minus energy admit a source-derived upper estimate, continue directly to a cofinal remainder theorem.

### Route B — canonical remainder is too strong

If CS24 proves that cofinal smallness already requires a new zero-cutoff sign or an implausible control of the nonnegative minus energy, freeze the cumulative polarization route and move to a **block-local / averaged signed-mass decomposition**. The goal there is to preserve cancellation inside the remainder instead of separating all of `E_-` as a positive remainder term.

This fork must be decided by Lean facts, not by preferred geometry.
