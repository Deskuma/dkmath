# XDP-004 result: safe-radius annulus and compact Mellin admissibility

## Scope closed

XDP-004 is implemented with the two requested reusable cores.

### H1: safe-radius annulus and finite-window stability

`DkMath.RH.CFBRC.PascalCenteredXiSafeRadiusAnnulusBridge` uses the finite
radial-gap route.  For a boundary-safe radius
`IsPascalCenteredXiBoundarySafeRadius R`, the finite centered zero set in the
disk of radius `R + 1` is mapped to its finite set of radial distances.  Since
the safe-radius hypothesis excludes `R` from that finite image, a positive
minimum radial gap exists.  Intersecting that gap with `1` and `R / 2` gives a
positive annulus width.

The public results are:

- `exists_pascalCenteredXi_zeroFreeRadialAnnulus`: a positive annulus around
  `R` contains no centered Xi zero;
- `exists_pascalCenteredXi_safeRadius_zeroDisk_stability`: the centered finite
  zero disk is locally constant under `|r - R| < ε`;
- `exists_pascalCenteredXi_safeRadius_window_stability`: the repository's
  existing `pascalCriticalMirrorZeroWindow` is locally constant under the same
  perturbation.

The last theorem transports membership through the existing
`sub_center_mem_pascalCenteredXiZeros_iff_nontrivial` equivalence and therefore
does not introduce a second definition of the zero window.

### H2: positive compact-support Mellin admissibility

`DkMath.Analysis.MellinCompactSupport` provides the generic Mellin core.  The
minimal hypotheses for arbitrary complex Mellin parameter are explicit:

```text
0 < a,  a ≤ b,
support h ⊆ Icc a b,
ContinuousOn h (Icc a b).
```

The principal theorem is
`mellinConvergent_of_support_subset_Icc_pos`.  The companion
`mellinConvergent_of_pos_support_subset_Icc_pos` records only support on the
positive integration domain.  This is useful for totalized mirror functions,
whose values outside the positive domain must not be silently interpreted as a
classical global support statement.

The mirror transport results are:

- `mellinCriticalMirror_support_pos_subset`, transporting support to the
  reciprocal interval `Icc b⁻¹ a⁻¹`;
- `continuousOn_mellinCriticalMirror_of_support_subset_Icc_pos`;
- `mellinConvergent_mellinCriticalMirror_of_support_subset_Icc_pos`;
- `mellin_mellinCriticalMirror_of_support_subset_Icc_pos`, which supplies both
  convergence hypotheses to the XDP-003 reflection theorem;
- `mellin_mellinCriticalMirror_centered_of_support_subset_Icc_pos`, its
  centered-parameter form.

The proof uses compact-interval continuity and Bochner integrability of an
indicator, together with the positive lower endpoint.  `HasCompactSupport`
alone is deliberately not accepted: a compact support touching zero does not
give convergence for every complex Mellin exponent.

## Explicit mathematical boundary

The requested H1 and H2 providers are closed, but the following stronger
statement is not a consequence of these hypotheses and is intentionally not
claimed here: identifying the hard radial spectral indicator (or the finite
zero-window cutoff) with a Mellin transform of a positive compactly supported
weight.  A Mellin transform of a compactly supported continuous function has
additional regularity and cannot be identified with an arbitrary discontinuous
hard cutoff without a separate realization theorem.  No Guinand--Weil
identity, explicit formula, RH conclusion, Xi-defect vanishing, or spectral
realization theorem is therefore added in XDP-004.

This is the handoff to XDP-005: any future spectral bridge must state its
realization hypotheses and prove the corresponding transform identity instead
of reusing the convergence provider as if it supplied that identity.

For the next audit, Route I (an admissible Mellin family with a separately
proved approximation or interpolation statement) is the lower-cost first
candidate: XDP-004 already supplies its convergence and reflection endpoint.
That recommendation is only a work-order recommendation, not an assertion
that the required approximation theorem exists.  Route C (fixed-Xi contour
transport with Mellin weights) remains an alternative if the missing
interpolation statement cannot be established.

## Validation

- `lake env lean DkMath/Analysis/MellinCompactSupport.lean` — Green.
- `lake env lean DkMath/RH/CFBRC/PascalCenteredXiSafeRadiusAnnulusBridge.lean`
  — Green.
- Root imports were added to `DkMath/Analysis.lean` and `DkMath/RH.lean`.
- Repository-wide `./lean-build.sh` — Green.
- Repository-wide `./lean-test.sh` — Green.
- `git diff --check` — Green; the equivalent no-index checks for the three new
  untracked files also produced no whitespace diagnostics.
- The root gates replayed only pre-existing `declaration uses sorry` warnings
  in unrelated modules; the two new Lean modules contain none of the
  prohibited proof shortcuts.

No new proof hole, axiom, native evaluation shortcut, or project-wide setting
change is used.
