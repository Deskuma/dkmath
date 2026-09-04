# FLT3U-003 実装報告: Eisenstein Coordinate Substrate

## 選択した型と座標規約

新規 module [EisensteinSubstrate.lean](../../../DkMath/FLT/Three/EisensteinSubstrate.lean)
を追加した。既存の
`DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)` を
`EisensteinInt` として使い、`eisensteinCoord r s := ⟨r, s⟩` とした。

基底元は `eisensteinTau := tau (-1)` であり、規約は

```text
tau^2 = tau - 1
N(r + s*tau) = r^2 + r*s + s^2
```

である。古典的な omega basis の `r - s` 規約は導入していない。

## Production theorem surface

- `eisenstein_tau_sq`: `tau^2 = tau - 1`
- `eisenstein_conj_coords`: `conj ⟨r,s⟩ = ⟨r+s,-s⟩`
- `eisenstein_norm_coords`: `N(⟨r,s⟩) = r^2+r*s+s^2`
- `eisenstein_norm_mul`: norm multiplicativity
- `eisenstein_tau_norm`, `eisenstein_tau_cube`, `eisenstein_tau_sixth`
- `eisensteinRamifier := 1 + eisensteinTau`
- `eisenstein_ramifier_norm`: `N(lambda)=3`
- `eisenstein_ramifier_sq`: `lambda^2 = 3*tau`
- `eisenstein_ramifier_mul_conj`: `lambda * conj lambda = 3`
- `eisenstein_cube_coords`:

  ```text
  (r+s*tau)^3 =
    (r^3 - 3*r*s^2 - s^3) + 3*r*s*(r+s)*tau
  ```

- `eisenstein_cube_snd`: cube second coordinate is exactly
  `3*r*s*(r+s)`
- `eisenstein_norm_nat_coords`: `N(c+b*tau) = (S0_nat c b : ℤ)`
- `gn_three_sub_eq_eisenstein_norm_nat_coords`:

  ```text
  (GN 3 (c-b) b : ℤ) = N(c+b*tau)  -- under b ≤ c
  ```

The GN bridge handles the equality case `b = c` as well as the strict case.
The optional gap-times-norm theorem was not added because it would duplicate
the existing cubic factorization without adding a new production interface.

## Deliberate non-goals

No `EuclideanDomain`, PID/UFD, ideal factorization, ramifier primality or
irreducibility, exact ramifier ownership, conjugate coprimality, cube
extraction, complete unit classification, sector exclusion, strict descent,
or final FLT3 theorem was added. Existing provisional
`GEisensteinDescentFrame` / `GEisensteinCandidate.step` machinery was not used
or repaired.

## Imports and verification

The new module directly imports only:

```text
import DkMath.FLT.Three.CubicValuationDepth
import DkMath.NumberTheory.TraceOneQuadratic
```

It does not import `DkMath.FLT.Main`, `DkMath.FLT.Basic`, `DkMath.FLT.Core`,
`DkMath.FLT.MathlibBridge.FLT34`, `Mathlib.NumberTheory.FLT.Three`, or
`DkMath.FLT.GEisensteinBridge`.

Focused build from `lean/dk_math`:

```text
lake build DkMath.FLT.Three.EisensteinSubstrate
Build completed successfully (8700 jobs).
```

The build is warning-free. Source audits found no new `sorry` or `axiom`, and
the principal theorem axiom audit contains only
`[propext, Classical.choice, Quot.sound]`. The `TraceOneInt (-1)` ring
structure is reused from the kernel-checked source; no unproved algebraic
instance was introduced.

## Remaining gaps and outcome

FLT3U-004 still must establish exact ramifier routing in an FLT3 factorization.
FLT3U-005 still must establish conjugate coprimality after the permitted
ramified factor is removed. Neither follows from this coordinate substrate.

Outcome A: the common TraceOneInt (-1) coordinate convention, ramifier
candidate, cube formula, and `S0/GN3` norm bridge are production-ready for the
next checkpoint. The implementation stops before exact ramifier routing.
