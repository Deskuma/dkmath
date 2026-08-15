# IPSM-052 — CS28 closeout and CS29 finite-potential rectangle / scalar-mismatch audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS28 verdict: **Green-B**.

Lean has now established:

- an explicit finite top-edge factor-safety contract,
- fixed-Xi top-edge decomposition under that contract,
- the finite arithmetic top companion as an exact path integral with coefficient `2`,
- the finite zeta-cutoff mismatch as a difference of two finite interval integrals,
- exact-source vanishing as a conditional theorem only,
- the finite top ledger with zeta / archimedean / elementary / arithmetic pieces,
- and the separation between the corner endpoint difference and the actual fixed-Xi top contribution.

No independent mismatch estimate, infinite prime expansion on the top edge, endpoint sign, or RH statement has been introduced.

## 1. CS29 motivation: do not over-target the complex top mismatch

The normalized arithmetic source always enters through

```text
Re ((2π i)⁻¹ Z).
```

For any `Z : ℂ`, this is determined only by `Z.im`:

```text
Re ((2π i)⁻¹ Z) = Z.im / (2π).
```

Therefore a bound on the full complex mismatch, or on its complex norm, is stronger than the prime-side radial-contact route actually needs.

CS29 must expose the **scalar mismatch component** that survives the normalization.

At the same time, the CS27 finite aggregate phase potential is a finite holomorphic potential. Its four oriented edge endpoint jumps telescope exactly. The finite arithmetic top companion is therefore not an isolated object: it is one edge of a closed finite potential rectangle.

The next audit should establish both facts before asking for any new estimate.

## 2. CS29-A — normalized complex scalar adapter

Export a generic theorem, with exact normalization:

```lean
theorem normalized_by_two_pi_i_re
    (z : ℂ) :
    (((2 * Real.pi * Complex.I)⁻¹) * z).re =
      z.im / (2 * Real.pi)
```

Use `Real.pi_ne_zero`; do not hide a sign convention.

Define the scalar finite top mismatch:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  (((2 * Real.pi * Complex.I)⁻¹) *
    pascalCenteredXiPrimeSideTopZetaCutoffMismatch ε W X).re
```

Prove the exact imaginary-part form:

```text
TopMismatchScalar = Im(TopZetaCutoffMismatch)/(2π).
```

No norm estimate is required.

## 3. CS29-B — conjugation of the finite holomorphic potential

Prove the source-derived conjugation identities:

```text
Φ_r(conj z) = conj(Φ_r(z))
Ψ_{ε,n}(conj z) = conj(Ψ_{ε,n}(z))
Ψ^{agg}_{ε,W,X}(conj z) = conj(Ψ^{agg}_{ε,W,X}(z)).
```

All frequencies and carriers are real, and the sum is finite.

This should include both the `r = 0` and `r ≠ 0` branches of the complex phase potential.

## 4. CS29-C — centered rectangle corners

Let

```text
a := W.rectangle.σ - 1/2,
RT :=  a + iT,
LT := -a + iT,
RB :=  a - iT,
LB := -a - iT.
```

Prefer named helper definitions if they reduce repeated coordinate algebra.

Prove the expected conjugations:

```text
RB = conj RT,
LB = conj LT.
```

## 5. CS29-D — four finite arithmetic edge companions

Using the CS27 aggregate complex phase potential, define oriented endpoint jumps:

```text
RightCompanion  := Ψ(RT) - Ψ(RB)
TopCompanion    := Ψ(LT) - Ψ(RT)
LeftCompanion   := Ψ(LB) - Ψ(LT)
BottomCompanion := Ψ(RB) - Ψ(LB)
```

The orientation must match the existing repository rectangle convention:

- right: bottom → top,
- top: right → left,
- left: top → bottom,
- bottom: left → right.

Prove exact telescoping:

```text
RightCompanion + TopCompanion + LeftCompanion + BottomCompanion = 0.
```

This is finite algebra, not a residue theorem.

## 6. CS29-E — identify existing CS27/CS28 objects

Prove that the new `TopCompanion` is exactly

```lean
pascalCenteredXiPrimeSideFiniteArithmeticTopEdgeCompanion ε W X.
```

Do not redefine or duplicate that object if a theorem is enough.

Also prove the top/bottom conjugation relation with the correct orientation:

```text
BottomCompanion = -conj(TopCompanion).
```

Consequently

```text
TopCompanion + BottomCompanion = 2 i * Im(TopCompanion).
```

Use an exact complex statement; do not infer a sign.

## 7. CS29-F — right companion is the aggregate interaction carrier

Prove the right-edge path identity for the finite arithmetic source:

```text
RightCompanion
  = 2 * ∫_{-T}^{T}
      hε(centered right node) * PHZ_X(right edge) * i dt.
```

This is the finite aggregate potential fundamental theorem along the right edge.

Then use the existing conjugation pairing / CS25 interaction identity to prove the sharper endpoint statement

```text
RightCompanion = 2 * i * AggregateInteraction(ε,W,X).
```

Check the factor `2` carefully. The existing aggregate potential itself already contains the leading factor `2`.

As a consistency theorem, recover

```text
NormalizedPrimeContribution = AggregateInteraction / π.
```

from this companion identity. This theorem is a cross-check, not a new provider.

## 8. CS29-G — normalized top ledger

Take the exact CS28 top ledger

```text
2 TopXi
  = TopArithmeticCompanion
    + 2 TopArch
    + 2 TopElem
    + TopZetaCutoffMismatch
```

and apply the repository normalization `(2π i)⁻¹` followed by `Complex.re`.

Define scalar companions if useful, and prove an exact real ledger of the form

```text
NormalizedTopContribution
  = TopArithmeticCompanionScalar
    + TopArchScalar
    + TopElemScalar
    + TopMismatchScalar.
```

Reuse existing normalized correction definitions whenever their orientation and factor conventions match. If they do not match, prove an explicit adapter instead of silently identifying them.

## 9. CS29-H — strength classification

Record formally that a scalar mismatch estimate is strictly weaker than a full complex-norm estimate.

A pure algebraic countermodel is sufficient, e.g. show that the normalized real component can vanish while the complex number is nonzero / has arbitrarily large real part.

The research consequence is:

> Future prime-side provider work should target the scalar component or a closed-contour combination, not full complex mismatch smallness unless a source theorem naturally provides the stronger estimate.

Do not claim that the scalar mismatch is small.

## 10. CS29-I — finite rectangle closure is not a top-mismatch estimate

The exact telescoping identity

```text
Right + Top + Left + Bottom = 0
```

must not be misread as `TopMismatch = 0`.

It applies to the finite arithmetic potential companions only.

The actual fixed-Xi top source still differs from the finite arithmetic top companion by the CS28 zeta/correction ledger.

Keep this firewall explicit in comments and theorem names.

## 11. Optional CS29-J — closed-contour residual object

If the preceding identities are clean, define a **closed-contour residual ledger** that combines the actual fixed-Xi contour source with the four finite arithmetic companions.

The finite arithmetic companion contour contributes zero by telescoping, so this object should make explicit which actual fixed-Xi / correction / mismatch terms survive.

This is allowed as a structural identity only.

Do not use zero-side fixed-defect nonnegativity, RH equivalence, or residue positivity as a sign provider.

## 12. Expected verdicts

### Green

A new source-derived scalar or closed-contour estimate is proved independently of the desired radial contact.

### Green-B

The four-edge finite potential closure, interaction/right-edge identification, and scalar mismatch reduction all close exactly, but no independent scalar mismatch estimate is obtained.

This is the expected outcome.

### Yellow

Only part of the edge/path identifications can be closed because of a genuine API or regularity obstruction. Record the precise missing statement.

### Red

Any implementation that:

- expands `-ζ'/ζ` as an infinite prime series on the top edge,
- assumes `TopMismatch → 0`,
- equates the finite companion contour with the actual fixed-Xi contour,
- uses zero-side fixed defect / RH equivalence as the provider,
- or infers a sign from complex conjugation / telescoping alone.

## 13. Named frontier

If no independent estimate appears, introduce a narrowed frontier such as

```lean
inductive PascalCenteredXiPrimeSideFiniteContourScalarMismatchGap : Prop
  | noIndependentScalarOrClosedContourMismatchEstimate
```

Do not delete CS28's mismatch gap unless a theorem genuinely discharges it.

## 14. Validation

Run at least:

```text
lake env lean <new-CS29-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 15. Research interpretation

The current chain is now:

```text
finite radial deficit
→ interaction only
→ phase boundary
→ holomorphic finite potential
→ finite top path companion
→ actual fixed-Xi top mismatch.
```

CS29 should add the missing geometric statement:

```text
finite potential = exact closed rectangle (zero telescoping charge),
```

while simultaneously weakening the analytic frontier from a full complex mismatch to the one real scalar component that actually enters the normalized radial-contact problem.

This prevents the next stage from trying to prove a stronger top-edge convergence statement than the RH prime-side mechanism actually needs.
