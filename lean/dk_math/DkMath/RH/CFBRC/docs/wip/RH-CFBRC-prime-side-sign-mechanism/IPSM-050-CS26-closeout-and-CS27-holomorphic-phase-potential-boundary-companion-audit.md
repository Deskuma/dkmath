# IPSM-050 — CS26 closeout and CS27 holomorphic phase-potential / boundary-companion audit

## 0. Status

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

CS26 verdict: **Green-B**.

CS26 has now proved, at fixed finite `ε`, residue window `W`, and cutoff `X`:

- the nonzero-frequency closed form of the finite phase primitive,
- the exact two-frequency representation of each finite mode kernel,
- the exact finite closed-phase ledger for aggregate interaction,
- vanishing of the `n = 0,1` von-Mangoldt source coefficients,
- nonvanishing of both phase frequencies under `0 < ε < log 2` and `2 ≤ n`,
- no sign, no infinite exchange, no endpoint sign, and no RH conclusion.

The remaining CS26 marker is the comparison with the fixed-Xi top-horizontal correction.

## 1. Important geometry firewall

Do **not** identify the CS26 phase boundary directly with
`pascalCenteredXiTopHorizontalContribution`.

They are not presently the same kind of object.

- The CS26 closed phase term is obtained by integrating one finite arithmetic mode along the **right vertical direction** and reducing that integral to endpoint values at height `T`.
- `pascalCenteredXiTopHorizontalContribution` is an integral of the **fixed-Xi weighted negative logarithmic derivative along the entire top horizontal edge**.

Therefore an equality of the form

`closed phase endpoint = top-horizontal contribution`

must not be introduced without an explicit path/primitive bridge.

The correct next object is a holomorphic primitive shared by both path directions.

## 2. CS27-A — complex phase potential

For real frequency `r`, define a complex potential with a safe zero-frequency branch:

```lean
noncomputable def pascalCenteredXiPrimeSideComplexPhasePotential
    (r : ℝ) (z : ℂ) : ℂ :=
  if r = 0 then z ^ 2 / 2
  else Complex.exp ((r : ℂ) * z) * (((r : ℂ) * z) - 1) / ((r : ℂ) ^ 2)
```

Prove the derivative identity for all real `r`:

```text
(d/dz) Φ_r(z) = z * exp(r z).
```

Prefer `HasDerivAt` / `HasFDerivAt` statements that can be reused by interval-integral fundamental-theorem adapters.

The `r = 0` branch must be real mathematics, not a totalized division trick.

## 3. CS27-B — recover the CS26 real primitive as a vertical endpoint jump

Let `a,T,r : ℝ` and `z_T := a + T i`.

Prove an exact theorem of the form

```text
PhasePrimitive(a,r,T)
  = Im (Φ_r(a + iT) - Φ_r(a)).
```

Then prove `Im (Φ_r(a)) = 0` for real `a,r`, giving the shorter form

```text
PhasePrimitive(a,r,T) = Im (Φ_r(a + iT)).
```

This theorem should reproduce both:

- the CS26 nonzero-frequency closed form,
- the CS13 zero-frequency value `a*T`.

No sign is inferred.

## 4. CS27-C — one-mode holomorphic Mellin potential

For positive natural mode `n`, use the CS26 frequencies

```text
r₊ = ε - log n,
r₋ = -ε - log n,
carrier = (2ε)⁻¹ exp(-(1/2) log n).
```

Define the complex one-mode potential

```text
Ψ_{ε,n}(z) := carrier * (Φ_{r₊}(z) - Φ_{r₋}(z)).
```

Prove source-derivative recovery:

```text
Ψ'_{ε,n}(z)
  = mellinQuadraticBoxWeight ε z * n^{-(1/2+z)}.
```

Use the repository's existing `Complex.cpow` transport carefully. Do not hide branch assumptions.

Then identify the CS26 finite mode kernel as the imaginary part of the oriented right-edge potential jump.

Conceptually:

```text
K_{ε,W}(n)
  = Im (Ψ_{ε,n}(a+iT) - Ψ_{ε,n}(a)),
  a = σ - 1/2.
```

For real lower endpoint `a`, the lower imaginary contribution should vanish.

## 5. CS27-D — finite aggregate complex phase potential

Define the finite von-Mangoldt-weighted potential

```text
Ψ_{ε,W,X}^{agg}(z)
  := 2 * Σ_{n≤X} Λ(n) Ψ_{ε,n}(z).
```

Keep this sum finite.

Prove the exact interaction endpoint theorem

```text
AggregateInteraction(ε,W,X)
  = Im (Ψ^{agg}(a+iT) - Ψ^{agg}(a)).
```

If the lower endpoint is real-valued, simplify to

```text
AggregateInteraction(ε,W,X)
  = Im Ψ^{agg}(a+iT).
```

This gives a complex-potential interpretation of the CS25 interaction, without introducing a sign provider.

## 6. CS27-E — top-edge finite arithmetic companion

Only after the complex potential is established, define the **finite arithmetic top-edge companion** from the same source:

```text
TopPrimeCompanion(ε,W,X)
  := Ψ^{agg}(-a+iT) - Ψ^{agg}(a+iT),
  a = σ - 1/2.
```

Prove that this is exactly the oriented top-edge integral of the corresponding finite arithmetic Mellin one-form.

This is a finite fundamental-theorem identity. It is **not** yet the repository fixed-Xi top-horizontal correction.

Also prove the analogous right-vertical endpoint identity and, if useful, the four-edge telescoping identity for this finite holomorphic arithmetic source.

This is the correct mathematical bridge between an endpoint boundary expression and a horizontal path integral.

## 7. CS27-F — compare with the actual fixed-Xi top source

The repository top correction is

```lean
pascalCenteredXiTopHorizontalContribution
  (pascalCenteredXiMellinSecondDifferenceWeight ε 0)
  W.toContourTransportWindow
```

and integrates the fixed-Xi weighted negative log derivative along the full top edge.

Audit whether the top-edge boundary-safety hypotheses already suffice to prove the pointwise decomposition

```text
centered-Xi neg-log-deriv
  = ordinary-zeta neg-log-deriv
    + archimedean
    + elementary
```

on the top edge.

If it is derivable, expose it as an exact top-edge decomposition theorem.

However, do **not** replace the ordinary-zeta top-edge term by an infinite prime series inside the critical strip. The right-edge `Re(s)>1` Dirichlet-series theorem does not automatically extend across the horizontal edge.

## 8. CS27-G — define the genuine top-boundary mismatch

If an exact finite top companion is available, define a mismatch object rather than assuming cancellation:

```text
TopMismatch
  := actual fixed-Xi top contribution
     - finite arithmetic top companion
     - any explicitly justified correction companions.
```

The exact signs and normalization must be derived from the existing contour orientation.

The goal is a decomposition such as

```text
G(ε,W,X)
  = baseline_without_matched_boundary
    + TopMismatch(ε,W,X)
    - interior/interaction remainder,
```

only if the source algebra genuinely yields it.

A new provider is progress only if `TopMismatch` is structurally smaller or admits an independent estimate. Merely renaming the old radial-contact gap is not progress.

## 9. Expected outcomes

### Green

A genuinely source-derived top-boundary cancellation removes a nontrivial part of the CS25 baseline or interaction frontier, with no sign assumption.

### Green-B

The holomorphic phase potential, finite top companion, and exact mismatch ledger are proved, but no independent bound/sign for the mismatch is obtained.

### Yellow

The complex potential closes, but the actual fixed-Xi top term cannot be compared without a new analytic-continuation/logarithm provider. Record the precise missing hypothesis rather than inserting one.

### Red

Any implementation that silently identifies a right-edge endpoint with the whole top-edge integral, expands `-ζ'/ζ` into an infinite prime series where `Re(s)≤1`, assumes the desired interaction reach, invokes the zero-side fixed defect as provider, or derives RH.

## 10. Required named frontier

If the comparison still does not close, keep a named frontier with semantics narrower than the old generic provider gap, for example:

```lean
inductive PascalCenteredXiPrimeSideHolomorphicPhaseTopMismatchGap : Prop
  | noIndependentTopMismatchEstimate
```

Do not delete the prior gaps unless an exact theorem genuinely discharges them.

## 11. Validation

Run at least:

```text
lake env lean <new-CS27-file>
lake build DkMath.RH
git diff --check
```

No new `sorry`, `axiom`, or `native_decide`.

## 12. Research interpretation

CS25 showed that the finite prime-side cutoff dependence is interaction-only:

```text
G_X = G_0 - I_X.
```

CS26 showed that `I_X` is a finite phase-boundary ledger.

CS27 should now explain **what boundary that phase actually belongs to**. The expected answer is not “the top correction by definition,” but “the endpoint of a holomorphic finite-mode potential.” Once that potential is explicit, vertical and horizontal path contributions become two views of the same finite one-form, and only then can the actual fixed-Xi top correction be compared without circularity.
