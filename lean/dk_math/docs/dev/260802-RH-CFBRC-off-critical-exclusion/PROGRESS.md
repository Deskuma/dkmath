# RH–CFBRC Off-Critical Exclusion — Progress

## 2026-08-02

### Event 1–4 — degree-two kernel and abstract bridge

Completed and Lean-checked:

- `centeredSigma`
- `offCriticalCFBRC`
- `cfbrcR_two_eq_zero_iff_x_eq_zero`
- `offCriticalCFBRC_two_eq_zero_iff_re_eq_half`
- `ZeroToCFBRCTwoBridge`
- `re_eq_half_of_zeroToCFBRCTwoBridge`

The only future analytic obligation in the degree-two route is `map_zero`.

### Event 5 — general positive-degree exclusion

Completed and Lean-checked in:

```text
DkMath.RH.CFBRC.OffCriticalExclusionGeneral
```

Main theorem:

```lean
theorem cfbrcR_eq_zero_iff_x_eq_zero
    {d : ℕ} (hd : 0 < d) (X Θ : ℝ) :
    cfbrcR d X Θ = 0 ↔ X = 0
```

Centered consequence:

```lean
theorem offCriticalCFBRC_eq_zero_iff_re_eq_half
    {d : ℕ} (hd : 0 < d) (σ Θ : ℝ) :
    offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

General abstract bridge:

- `ZeroToCFBRCBridge`
- `re_eq_half_of_zeroToCFBRCBridge`

Proof route:

1. turn CFBRC zero into equality of complex powers;
2. apply complex norm;
3. cancel the positive natural power on nonnegative real norms;
4. compare `Complex.normSq`;
5. obtain `X^2 + Θ^2 = Θ^2` and conclude `X = 0`.

CI result: success.

### Event 6A — mirror threat-model factorization

Completed and Lean-checked in:

```text
DkMath.RH.CFBRC.MirrorThreatModel
```

Definitions:

```lean
mirrorCFBRC d X Θ
mirrorCFBRCCore d X Θ
```

Exact factorization:

```lean
theorem mirrorCFBRC_eq_boundary_mul_core
```

Mathematically,

$$
M_d(X,\Theta)
=
(X+i\Theta)^d-(-X+i\Theta)^d
=
2X\,K_d(X,\Theta).
$$

Away from `X = 0`, closure is exactly core vanishing:

```lean
theorem mirrorCFBRC_eq_zero_iff_core_eq_zero
```

The first explicit nontrivial branch was fixed at degree three:

```lean
theorem mirrorCFBRC_three_eq_zero_iff (X Θ : ℝ) :
    mirrorCFBRC 3 X Θ = 0 ↔
      X = 0 ∨ X ^ 2 = 3 * Θ ^ 2
```

CI result: success.

## Current boundary

The algebraic exclusion layer is now general in the degree. The remaining load-bearing analytic problem is unchanged:

$$
\operatorname{NontrivialZetaZero}(s)
\longrightarrow
C_d\!\left(s.\operatorname{re}-\frac12,\Theta(s)\right)=0.
$$

Before constructing that bridge, Event 6B will classify mirror-core zeros through roots of unity. This records the complete off-critical threat model that the bridge must avoid.

## Next target

Formalize a root-of-unity classification without introducing division too early:

```lean
mirrorCFBRC d X Θ = 0
→
∃ ω : ℂ, ω ^ d = 1 ∧
  (X : ℂ) + Complex.I * Θ =
    ω * ((-X : ℂ) + Complex.I * Θ)
```

Then separate:

- `ω = 1`, forcing `X = 0`;
- `ω ≠ 1`, the nontrivial cyclotomic threat branches.
