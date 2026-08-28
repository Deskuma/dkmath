# XDP-005 result: Mellin spectral weight and fixed-Xi contour adapter

## Route and scope

XDP-005 uses Route C.  Positive compact Mellin data are converted into a
globally differentiable centered spectral weight, which is then passed directly
to the existing generic fixed centered-Xi outer-contour residue theorem.

The implementation does not use finite interpolation as a substitute for a
global zero-side identity.  The contour itself performs the finite spectral
localization inside the safe radius.

## Gate A: Mellin holomorphicity

The new generic module is
`DkMath.Analysis.MellinCompactSupportHolomorphic`.

The theorem is:

```lean
theorem differentiable_mellin_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (_hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (fun s : ℂ => mellin h s)
```

The public API retains the same mathematical hypotheses as XDP-004; the
unused inequality is named `_hab` only because the actual differentiability
proof does not need to inspect the ordering once support has already been
given as `[a,b]`.  It remains part of the contract for consistency with the
compact-positive-support provider.

The pinned Mathlib theorem used is:

```lean
theorem mellin_differentiableAt_of_isBigO_rpow
    [NormedSpace ℂ E] {a b : ℝ} {f : ℝ → E} {s : ℂ}
    (hfc : LocallyIntegrableOn f (Ioi 0))
    (hf_top : f =O[atTop] (· ^ (-a)))
    (hs_top : s.re < a)
    (hf_bot : f =O[𝓝[>] 0] (· ^ (-b)))
    (hs_bot : b < s.re) :
    DifferentiableAt ℂ (mellin f) s
```

For the support contract, `ContinuousOn h (Icc a b)` gives integrability of
the compact indicator.  The support containment then identifies `h` with that
indicator on the positive ray and gives `LocallyIntegrableOn h (Ioi 0)`.  The
same containment makes `h` eventually zero at `atTop` and at `𝓝[>] 0`; hence
the two `IsBigO` hypotheses are obtained for arbitrary endpoint exponents.
For each requested `s`, the proof chooses the exponents `s.re + 1` and
`s.re - 1`.

## Gate B: centered spectral weight

The definition is:

```lean
noncomputable def centeredMellinSpectralWeight (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  mellin h ((1 : ℂ) / 2 + z)
```

The composition theorem is:

```lean
theorem differentiable_centeredMellinSpectralWeight_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (centeredMellinSpectralWeight h)
```

The pointwise companion
`differentiableAt_centeredMellinSpectralWeight_of_support_subset_Icc_pos`
is also exposed.  It is only affine composition; no new Mellin calculation is
introduced.

## Gate C: mirror/reflection surface

The generic reflection surface is:

```lean
theorem centeredMellinSpectralWeight_mirror_of_support_subset_Icc_pos
    {h : ℝ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b)) (z : ℂ) :
    centeredMellinSpectralWeight (mellinCriticalMirror h) z =
      (starRingEnd ℂ) (centeredMellinSpectralWeight h
        (-(starRingEnd ℂ) z))
```

This is obtained by composing the XDP-004 centered reflection theorem.  The
mirror-side convergence provider is not reproved here.

## Gate D: fixed-Xi contour bridge

The new CFBRC module is
`DkMath.RH.CFBRC.PascalCenteredXiMellinWeightedOuterContourBridge`.

Its principal theorem is:

```lean
theorem pascalCenteredXiMellinWeightedOuterContourMass_eq
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    pascalCenteredXiWeightedOuterContourMass
        (centeredMellinSpectralWeight h) R =
      -(2 * Real.pi * Complex.I) *
        pascalCenteredXiZeroDiskWeightedMoment
          (centeredMellinSpectralWeight h) R
```

The normalized endpoint is:

```lean
theorem pascalCenteredXiNormalizedMellinWeightedOuterContourMass_eq
    {h : ℝ → ℂ} {a b R : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support h ⊆ Set.Icc a b)
    (hcont : ContinuousOn h (Set.Icc a b))
    (hR : IsPascalCenteredXiBoundarySafeRadius R) :
    (2 * Real.pi * Complex.I)⁻¹ *
        pascalCenteredXiWeightedOuterContourMass
          (centeredMellinSpectralWeight h) R =
      -pascalCenteredXiZeroDiskWeightedMoment
        (centeredMellinSpectralWeight h) R
```

Both theorems are thin applications of the existing
`pascalCenteredXiWeightedOuterContourMass_eq` and
`pascalCenteredXiNormalizedWeightedOuterContourMass_eq`.  Principal parts,
removable patches, and circle-integral arguments are not duplicated.

## Gate E decision

No generic transport theorem from the centered Xi zero-disk weighted moment to
the uncentered `pascalCriticalMirrorZeroWindow` weighted moment was added.
The requested XDP-005 endpoint is already the finite centered-Xi zero-disk
moment, and the existing transport infrastructure is specialized in places to
the earlier observables.  Adding a second generic multiplicity transport layer
would enlarge this phase without strengthening the fixed-contour adapter.

## Mathematical boundaries and XDP-006 handoff

The following remain intentionally unproved:

- `centeredMellinSpectralWeight h z = z ^ 2`;
- hard radial or finite-window cutoff realization by a Mellin transform;
- finite interpolation as a global explicit-formula zero sum;
- Guinand--Weil, Li, Weil positivity, prime-side transport, defect sign or
  vanishing, and RH.

The contour equality is a representation bridge, not a provider theorem.  The
next phase must decide how, if at all, to recover the second weight `z ^ 2`:
approximate identities near `x = 1`, fixed-contour uniform approximation, or an
alternative weighted defect family.  No global equality with `z ^ 2` is assumed
in this phase.

## Validation

- `lake env lean DkMath/Analysis/MellinCompactSupportHolomorphic.lean` — Green.
- `lake env lean DkMath/RH/CFBRC/PascalCenteredXiMellinWeightedOuterContourBridge.lean`
  — Green after building the generic dependency.
- Root imports were added to `DkMath/Analysis.lean` and `DkMath/RH.lean`.
- Repository-wide `./lean-build.sh` — Green.
- Repository-wide `./lean-test.sh` — Green.
- `git diff --check` and equivalent checks for the new untracked files — Green.
- Existing unrelated modules still replay their pre-existing `sorry` warnings;
  the two new Lean modules contain none of the prohibited proof shortcuts.
- No new proof hole, axiom, native evaluation shortcut, or unrelated theorem
  is introduced.
