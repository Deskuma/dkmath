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

$$
M_d(X,\Theta)
=
(X+i\Theta)^d-(-X+i\Theta)^d
=
2X\,K_d(X,\Theta).
$$

Lean API:

- `mirrorCFBRC_eq_boundary_mul_core`
- `mirrorCFBRC_eq_zero_iff_core_eq_zero`

The first explicit nontrivial branch was fixed at degree three:

```lean
theorem mirrorCFBRC_three_eq_zero_iff (X Θ : ℝ) :
    mirrorCFBRC 3 X Θ = 0 ↔
      X = 0 ∨ X ^ 2 = 3 * Θ ^ 2
```

CI result: success.

### Event 6B — root-of-unity witness and real branch equations

Completed and Lean-checked in:

```text
DkMath.RH.CFBRC.MirrorRootOfUnity
```

For `X ≠ 0`, mirror closure produces a quotient witness `ω` with

$$
\omega^d=1
$$

and

$$
X+i\Theta
=
\omega(-X+i\Theta).
$$

The witness is nontrivial:

$$
\omega\ne1.
$$

Lean API:

- `mirror_pow_eq_of_mirrorCFBRC_eq_zero`
- `exists_rootOfUnity_witness_of_mirrorCFBRC_eq_zero`
- `mirror_multiplier_ne_one_of_x_ne_zero`
- `exists_nontrivial_rootOfUnity_witness_of_mirrorCFBRC_eq_zero`

Taking real and imaginary parts gives the explicit algebraic branch equations

$$
(1+\operatorname{Re}\omega)X
+
\operatorname{Im}\omega\,\Theta
=0,
$$

$$
\operatorname{Im}\omega\,X
+
(1-\operatorname{Re}\omega)\Theta
=0.
$$

Lean API:

- `mirror_map_implies_linear_branch_equations`
- `exists_nontrivial_rootOfUnity_linear_branch_of_mirrorCFBRC_eq_zero`

CI result: success.

### Event 6C — antipodal/rational branch split

Completed and Lean-checked in the same public module.

For positive degree, `ω^d = 1` implies

$$
|\omega|=1
$$

and hence

$$
(\operatorname{Re}\omega)^2+(\operatorname{Im}\omega)^2=1.
$$

Lean API:

- `norm_eq_one_of_pow_eq_one`
- `re_sq_add_im_sq_eq_one_of_pow_eq_one`

The first branch equation is exposed as

$$
(1+\operatorname{Re}\omega)X
=-\operatorname{Im}\omega\,\Theta.
$$

If `1 + ω.re ≠ 0`, Lean solves it as

$$
X
=
\frac{-\operatorname{Im}\omega\,\Theta}
{1+\operatorname{Re}\omega}.
$$

If `1 + ω.re = 0`, the unit-circle equation forces the antipodal root
`ω = -1`, and the second branch equation forces

$$
\Theta=0.
$$

Lean API:

- `mirror_branch_slope_mul_eq`
- `mirror_branch_x_eq_ratio_mul_theta`
- `theta_eq_zero_of_antipodal_root_branch`
- `exists_rootOfUnity_branch_split_of_mirrorCFBRC_eq_zero`

The module is re-exported from `DkMath.RH`; therefore each successful full
`lake build` traversed the public import graph rather than merely checking an
unreachable file.

CI result: success.

## Current boundary

The standard CFBRC family has no real-input zero away from `X = 0` for any
positive degree. The enlarged mirror family can close away from the centered
line only through a nontrivial root-of-unity branch.

Those branches are now completely reduced to two algebraic cases:

1. the antipodal branch `ω = -1`, which requires `Θ = 0`;
2. a rational-slope branch determined by `Re ω` and `Im ω`.

The remaining load-bearing analytic problem is unchanged:

$$
\operatorname{NontrivialZetaZero}(s)
\longrightarrow
C_d\!\left(s.\operatorname{re}-\frac12,\Theta(s)\right)=0.
$$

A future zeta bridge must either land directly in the standard CFBRC family or
prove that its image cannot enter any nontrivial mirror branch.

## Next target

Connect `ω^d = 1` to a finite root index `k` and the exponential form

$$
\omega
=
\exp\left(\frac{2\pi i k}{d}\right).
$$

On the non-antipodal branch, substitute

$$
\operatorname{Re}\omega
=
\cos\left(\frac{2\pi k}{d}\right),
\qquad
\operatorname{Im}\omega
=
\sin\left(\frac{2\pi k}{d}\right)
$$

into the rational slope and prove the half-angle form

$$
X
=
-\Theta\tan\left(\frac{\pi k}{d}\right).
$$

This will turn the abstract threat model into a finite indexed family of
explicit off-critical candidate lines.
