# XDP-003 — Mellin centered-mirror test adapter 実装結果

## 1. 採用 module path

- generic Core: `DkMath/Analysis/MellinCriticalMirror.lean`
- CFBRC thin adapter: `DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean`
- public imports: `DkMath/Analysis.lean` and `DkMath/RH.lean`

The generic definitions are in `DkMath.Analysis`; the CFBRC namespace is used
only for the coordinate-identification bridge.

## 2. 採用した proof route

採用は B1 (existing Mellin lemmas を compose) である。

1. `mellin_cpow_smul` が positive ray の `x⁻¹` factor を Mellin parameter
   の `-1` shift に変換する。
2. `mellin_comp_inv` が `x ↦ x⁻¹` の substitution を行う。
3. `integral_conj` と `Complex.conj_cpow` が complex conjugation を
   set integral と Mellin exponent に移す。

逆変数積分の直接 B2 証明は実装していない。

## 3. Exact theorem names and signatures

Core API:

```lean
noncomputable def DkMath.Analysis.mellinCriticalMirror
    (h : ℝ → ℂ) (x : ℝ) : ℂ

theorem DkMath.Analysis.mellinCriticalMirror_involutive_on_pos
    (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinCriticalMirror (mellinCriticalMirror h) x = h x

theorem DkMath.Analysis.mellinCriticalMirror_involutive_of_pos
    (h : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    mellinCriticalMirror (mellinCriticalMirror h) x = h x

theorem DkMath.Analysis.one_sub_conj_half_add (z : ℂ) :
    1 - (starRingEnd ℂ) ((1 : ℂ) / 2 + z) =
      (1 : ℂ) / 2 - (starRingEnd ℂ) z

theorem DkMath.Analysis.mellin_mellinCriticalMirror
    (h : ℝ → ℂ) (s : ℂ)
    (_hconv₁ : MellinConvergent (mellinCriticalMirror h) s)
    (hconv₂ : MellinConvergent h (1 - (starRingEnd ℂ) s)) :
    mellin (mellinCriticalMirror h) s =
      (starRingEnd ℂ) (mellin h (1 - (starRingEnd ℂ) s))

theorem DkMath.Analysis.mellin_mellinCriticalMirror_centered
    (h : ℝ → ℂ) (z : ℂ)
    (hconv₁ : MellinConvergent (mellinCriticalMirror h) ((1 : ℂ) / 2 + z))
    (hconv₂ : MellinConvergent h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) :
    mellin (mellinCriticalMirror h) ((1 : ℂ) / 2 + z) =
      (starRingEnd ℂ)
        (mellin h ((1 : ℂ) / 2 - (starRingEnd ℂ) z))

theorem DkMath.Analysis.mellin_mellinCriticalMirror_half_add
    (h : ℝ → ℂ) (z : ℂ)
    (hconv₁ : MellinConvergent (mellinCriticalMirror h) ((1 : ℂ) / 2 + z))
    (hconv₂ : MellinConvergent h ((1 : ℂ) / 2 - (starRingEnd ℂ) z)) :
    mellin (mellinCriticalMirror h) ((1 : ℂ) / 2 + z) =
      (starRingEnd ℂ)
        (mellin h ((1 : ℂ) / 2 - (starRingEnd ℂ) z))
```

The source-level binder `_hconv₁` is intentionally explicit: it records the
mirror-side domain required by the adapter contract, although Mathlib's
totalized Mellin equalities make it unnecessary in the kernel proof.

CFBRC bridge API:

```lean
theorem DkMath.RH.CFBRCProjection.one_sub_conj_eq_criticalMirror
    (s : ℂ) :
    1 - (starRingEnd ℂ) s = criticalMirror s

theorem DkMath.RH.CFBRCProjection.mellinCenteredReflectionParameter_eq_criticalMirror
    (z : ℂ) :
    (1 : ℂ) / 2 - (starRingEnd ℂ) z =
      criticalMirror ((1 : ℂ) / 2 + z)
```

## 4. Convergence / integrability hypotheses

The main theorem exposes both sides of the intended domain:

- `_hconv₁`: `M (mellinCriticalMirror h) s` is `MellinConvergent`.
- `hconv₂`: `M h (1 - conj s)` is `MellinConvergent`.

The second hypothesis is used to instantiate the conjugate-integral helper at
`1 - s`; the first is deliberately retained in the public signature so that
the mirror-side convergence obligation is not hidden by Mathlib's convention
that a non-integrable Mellin integral is totalized to zero. No compact support,
Schwartz condition, or convergence of a later CFBRC test family is inferred.

## 5. Reused Mathlib lemmas

- `MellinConvergent`
- `mellin_cpow_smul`
- `mellin_comp_inv`
- `Complex.conj_cpow`
- `integral_conj`
- `MeasureTheory.setIntegral_congr_fun`

## 6. Centered CFBRC bridge

The generic centered identity is

```text
M(mirror h)(1/2 + z) = conj (M h (1/2 - conj z)).
```

The thin adapter identifies `1 - conj s` with the existing CFBRC
`criticalMirror s`, and identifies the centered parameter `1/2 - conj z`
with `criticalMirror (1/2 + z)`. The existing
`centeredComplex_criticalMirror_eq_neg_conj` theorem is imported and reused;
no zero predicate is involved.

## 7. Optional self-dual API

Not added. It is not an XDP-003 required endpoint and would introduce a
functional fixed-point API without being needed by the Mellin reflection or
CFBRC coordinate bridge.

## 8. Build / test result

The following gates were run for this implementation:

- `lake env lean DkMath/Analysis/MellinCriticalMirror.lean` — Green
- `lake build DkMath.Analysis.MellinCriticalMirror` — Green
- `lake env lean DkMath/RH/CFBRC/MellinCenteredMirrorAdapter.lean` — Green
- `./lean-build.sh` — Green
- `./lean-test.sh` — Green
- `git diff --check` — Green (new untracked files also had no whitespace
  diagnostics under `git diff --no-index --check`)

The repository-level wrapper gates completed successfully. The pre-existing
repository `declaration uses sorry` warnings remain outside this XDP-003 change.

## 9. H1 / H2 boundary

H1 (hard radial zero-window cutoff) and H2 (the unbounded centered coordinate
`s - 1/2`) are intentionally unresolved. They cannot be closed by this
generic reflection theorem: doing so would require a localized admissible test
family and new support/convergence arguments, not a consequence of the
algebraic Mellin reflection identity. In particular, this implementation does
not identify a zero-window indicator with a Mellin test function, does not
declare `s - 1/2` admissible, and does not assume a safe-radius smooth cutoff.

The module docstrings record the same mathematical boundary. This is the
deliberate XDP-003 stopping condition, not a proof gap in the stated generic
theorems.

## 10. Minimal XDP-004 handoff

XDP-004 can use `mellin_mellinCriticalMirror_centered` together with
`mellinCenteredReflectionParameter_eq_criticalMirror` as the algebraic
reflection contract. Its remaining task is to construct and prove convergence
for a localized admissible Mellin test family, while keeping H1/H2 explicit.

## Classical boundary

This result does not implement or claim a classical Weil criterion, a
Guinand--Weil explicit formula, zeta or Xi continuation, a zero classification,
or an RH implication.
