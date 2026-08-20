# CKSS-001 common-kernel source API audit report

Date: 2026-08-20

## 1. Executive decision

The current pinned Mathlib/DkMath stack is classified as:

```text
FUNCTIONAL-EQUATION-TRANSPORT-ONLY
```

Mathlib exposes the completed-zeta Mellin construction and its functional
equation, but the reflected side is obtained through the FE-pair involution,
reciprocal-variable change, and the final functional-equation rewrite.  It
does not expose a new pre-reflection object containing both zero-derived
original and critical-mirror amplitudes with one common source variable,
measure, kernel, and scale.

**CKSS-002 MUST NOT START.**

## 2. Repository orientation

- branch: `wip/RH-CFBRC-common-kernel-second-source-260820-v0`
- HEAD at inspection: `a7e4f87116e1cae058a6f554090ed721c573d2a3`
- toolchain: `leanprover/lean4:v4.32.2`
- current CKSS stage: CKSS-001 common-kernel source API audit
- global objective: obtain an independent zero-derived common source before
  reflection, if the pinned API contains one
- load-bearing provider boundary: no RH-equivalent provider, raw-ratio upper
  bound, fixed-Xi vanishing statement, or reverse energy inequality is used
- next unresolved Gap: an exact source-preserving theorem giving independent
  same-scale coupling of the two zero-derived endpoint amplitudes

The repository is on the requested branch and was clean at the initial
inspection.  The public ZDSS-005 import was added by CKSS-000 and is recorded
in `0002-CKSS-000-frontier-consolidation-report.md`.

## 3. Exact declaration inventory

The audit used the installed sources under `.lake/packages/mathlib`, not
current Mathlib master.

### 3.1 Abstract Mellin FE-pair layer

Source: `Mathlib/NumberTheory/LSeries/AbstractFuncEq.lean`.

| declaration | exact role | source-rank reading |
|---|---|---|
| `WeakFEPair` | stores `f`, `g`, weight `k`, root number `ε`, constants, integrability/decay, and `f (1/x) = (ε * x^k) • g x` | a paired pair of kernels; the second side is tied to the first by reciprocal transport |
| `WeakFEPair.symm` | swaps `f` and `g`, replacing `ε` by `ε⁻¹` | invertible endpoint swap, not an independent source |
| `WeakFEPair.hasMellin` | identifies `Λ` with the Mellin transform of `f - f₀` in the convergence half-plane | one-side Mellin access, not a joint two-amplitude integral |
| `WeakFEPair.functional_equation` | `P.Λ (P.k - s) = P.ε • P.symm.Λ s` | final transport identity |
| `IsStrongFEPair.hasMellin` | `HasMellin P.f s (P.Λ s)` for a strong pair | still one function at a time; no common positive detector |

The key types are at lines 78–95, 405–428, and 481–485 of the pinned source.
The abstract proof uses Mellin scaling and the substitution `t ↦ t⁻¹`; it
does not construct a joint source integral with both endpoint amplitudes.

### 3.2 Even Hurwitz/Riemann-zeta kernel layer

Source: `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`.

| declaration | exact role | source-rank reading |
|---|---|---|
| `HurwitzZeta.evenKernel` | Jacobi-theta-based even kernel on the positive ray | original Mellin kernel |
| `HurwitzZeta.cosKernel` | cosine/theta-side kernel on the positive ray | separate reflected-side kernel |
| `HurwitzZeta.evenKernel_functional_equation` | `evenKernel a x = x^(-1/2) * cosKernel a (1/x)` | reciprocal-variable functional-equation transport |
| `HurwitzZeta.hurwitzEvenFEPair` | instantiates `WeakFEPair` with `f = evenKernel a`, `g = cosKernel a`, `k = 1/2`, `ε = 1` | packages the transport; does not add an independent source rank |
| `HurwitzZeta.completedHurwitzZetaEven` | `((hurwitzEvenFEPair a).Λ (s/2))/2` | completed transform of the original member |
| `HurwitzZeta.completedCosZeta` | `((hurwitzEvenFEPair a).symm.Λ (s/2))/2` | completed transform of the swapped member |
| `HurwitzZeta.completedHurwitzZetaEven_one_sub` | `completedHurwitzZetaEven a (1-s) = completedCosZeta a s` | final reflected equality |
| `HurwitzZeta.hasSum_int_completedHurwitzZetaEven` | Mellin/Dirichlet-series relation in `1 < re s` | source representation for the even side only |
| `HurwitzZeta.hasSum_int_completedCosZeta` | Mellin/Dirichlet-series relation in `1 < re s` | source representation for the cosine side only |

The definitions and kernel identity are at lines 62–145 and 253–322.  The
functional equations are at lines 364–392.  The Mellin representations are
explicitly reduced to `mellin (evenKernel - constant)` and
`mellin (cosKernel - constant)` at lines 497–501 and 537–542.

### 3.3 Riemann-zeta specialization

Source: `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`.

| declaration | exact role | source-rank reading |
|---|---|---|
| `completedRiemannZeta` | definition as `completedHurwitzZetaEven 0` | specialization only |
| `HurwitzZeta.completedCosZeta_zero` | identifies `completedCosZeta 0` with `completedRiemannZeta` using `hurwitzEvenFEPair_zero_symm` | symmetry/transport only |
| `completedRiemannZeta_one_sub` | `completedRiemannZeta (1-s) = completedRiemannZeta s` | final reflection equality |
| `completedZeta_eq_tsum_of_one_lt_re` | completed zeta Dirichlet-series expression for `1 < re s` | one-sided convergence-region formula |

The Riemann specialization does not add a common-kernel source object.

## 4. Dependency/source chain

The exact chain in the pinned stack is:

```text
jacobiTheta₂
  -> evenKernel / cosKernel
  -> evenKernel_functional_equation
  -> hurwitzEvenFEPair : WeakFEPair
  -> WeakFEPair.Λ / WeakFEPair.symm.Λ
  -> completedHurwitzZetaEven / completedCosZeta
  -> completedHurwitzZetaEven_one_sub
  -> completedRiemannZeta_one_sub
```

`WeakFEPair.hasMellin` supplies the Mellin transform of a single member
(`f - f₀` in its general form).  The `g` member appears through `symm` and the
functional equation.  The source is therefore two related kernels joined by
an involutive transport, not one joint source expression containing both
amplitudes before reflection.

## 5. Source-rank analysis

The candidate fails the CKSS common-source test for the following exact
reasons:

1. `evenKernel_functional_equation` replaces `x` by `1/x` and applies the
   Mellin weight.  This is precisely an allowed transport in the source-rank
   firewall.
2. `WeakFEPair.symm` is an invertible swap of the two members.  It does not
   create an independent zero-derived coordinate.
3. `completedHurwitzZetaEven_one_sub` is proved from
   `WeakFEPair.functional_equation`; it is a final reflected equality, not a
   pre-reflection common-kernel representation.
4. At `a = 0`, `evenKernel_eq_cosKernel_of_zero` and
   `hurwitzEvenFEPair_zero_symm` further collapse the two sides by symmetry.

Thus the API contains a mathematically meaningful FE-pair source, but no
source-rank increase of the kind required by CKSS.  It is not appropriate to
rename this pair as a new common-kernel zero source.

## 6. Positivity-direction analysis

The source APIs inspected here provide no zero-derived positive scalar matched
to the completed-zeta source.  They also provide no inequality of the form
needed to upper-control a diagonal energy from smallness of a whole
oscillatory Mellin integral.  Any positivity obtained by taking a norm square
would be post-processing, and the general direction remains

```text
norm(whole integral)^2 <= integral of pointwise norm-square.
```

No reverse Cauchy--Schwarz, triangle, Parseval/Bessel, or Gram inequality is
silently used.

## 7. Duplicate-route analysis

The following existing DkMath routes were checked against the candidate:

| existing route | result of comparison |
|---|---|
| `DkMath.Analysis.MellinCriticalMirror` | exact Mellin reflection by inversion and conjugation; transport-only, explicitly zero-independent |
| `DkMath.Analysis.MellinQuadraticGramKernel` | fixed-`ε` positive Gram candidate; positivity is introduced after quadraticization and is not a zero-derived common source |
| `DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticRealizationBridge` | finite centered-Xi second-moment/contour representation; an existing fixed-Xi route, not an independent completed-zeta source |
| `DkMath.RH.CFBRC.PascalCenteredXiWeilMirrorDefectBridge` | finite Weil-style mirror/defect identity; representation and transport only, not a vanishing provider |
| `DkMath.RH.CFBRC.MellinCenteredMirrorAdapter` | coordinate identification between generic Mellin reflection and `criticalMirror`; no new source rank |

The candidate therefore duplicates the same reflection/Gram/fixed-Xi roles and
does not authorize a new quadraticization route.

## 8. Lean implementation

CKSS-000 added the missing public import:

```text
DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
```

No CKSS-001 source module was added.  Under the selected classification, a new
module would overstate transport as an independent source.  The relevant
Mathlib declarations were audited directly from the pinned source, and the
existing DkMath module docstrings already state the applicable no-RH and no-
provider boundaries.  No new theorem, assumption, axiom, `sorry`, `admit`, or
heuristic approximate functional equation was introduced for CKSS-001.

## 9. Build results

The following focused checks passed before and after the CKSS-000 import:

```text
lake build DkMath.RH.CFBRC.ZeroDerivedSameScaleCrossEndpointCouplingAudit
lake build DkMath.RH
```

The final root build completed successfully (9097 jobs).  The focused module
was replayed successfully through the root import surface.  Since CKSS-001
adds no load-bearing theorem, there is no new theorem-specific `#print axioms`
obligation; the imported ZDSS module remains the existing audited artifact.

## 10. Smallest next unresolved Gap

The smallest missing infrastructure is an exact theorem that exposes, before
functional-equation transport, a single source object whose same integration
or summation variable and normalization simultaneously carry the original and
critical-mirror zero-derived amplitudes.  The current `WeakFEPair` API does
not meet this requirement because its second member is supplied through the
reciprocal FE relation and `symm`.

This is an API/source gap for the CKSS objective, not evidence that the
completed-zeta functional equation itself is absent.

## 11. CKSS-002 authorization

CKSS-002 is not authorized mathematically:

```text
CKSS-002 MUST NOT START
```

The route should remain closed until an independent common source is exposed
and its source rank is certified before any positivity or factorization step.
