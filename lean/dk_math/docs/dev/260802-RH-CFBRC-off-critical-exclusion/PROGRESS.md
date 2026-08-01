# RH–CFBRC Off-Critical Exclusion — Progress

## 2026-08-02

## Event 1–4 — degree-two exclusion and abstract bridge

Completed and publicly Lean-checked:

- `centeredSigma`
- `offCriticalCFBRC`
- `cfbrcR_two_eq_zero_iff_x_eq_zero`
- `offCriticalCFBRC_two_eq_zero_iff_re_eq_half`
- `ZeroToCFBRCTwoBridge`
- `re_eq_half_of_zeroToCFBRCTwoBridge`

The degree-two route isolates all future analytic work in `map_zero`.

## Event 5 — all positive degrees

Completed in:

```text
DkMath.RH.CFBRC.OffCriticalExclusionGeneral
```

Main theorem:

```lean
theorem cfbrcR_eq_zero_iff_x_eq_zero
    {d : ℕ} (hd : 0 < d) (X Θ : ℝ) :
    cfbrcR d X Θ = 0 ↔ X = 0
```

Hence, for every positive degree,

$$
\operatorname{offCriticalCFBRC}(d,\sigma,\Theta)=0
\quad\Longleftrightarrow\quad
\sigma=\frac12.
$$

The proof is independent of zeta and compares complex norms of the two powers.

CI result: success through the public `DkMath.RH` import graph.

## Event 6A — mirror threat-model factorization

Completed in:

```text
DkMath.RH.CFBRC.MirrorThreatModel
```

The enlarged symmetric model is

$$
M_d(X,\Theta)
=(X+i\Theta)^d-(-X+i\Theta)^d.
$$

Lean proves the exact factorization

$$
M_d(X,\Theta)=2X\,K_d(X,\Theta),
$$

where `K_d` is `mirrorCFBRCCore`. Away from `X = 0`, mirror closure is exactly
core vanishing. Degree three gives the first explicit nontrivial branch:

$$
M_3(X,\Theta)=0
\quad\Longleftrightarrow\quad
X=0\;\lor\;X^2=3\Theta^2.
$$

CI result: success through the public import graph.

## Event 6B — root-of-unity witness

Completed in:

```text
DkMath.RH.CFBRC.MirrorRootOfUnity
```

For `X ≠ 0`, every mirror closure produces a nontrivial witness `ω` satisfying

$$
\omega^d=1,
\qquad
\omega\ne1,
$$

and

$$
X+i\Theta=\omega(-X+i\Theta).
$$

Taking real and imaginary parts gives

$$
(1+\operatorname{Re}\omega)X
+\operatorname{Im}\omega\,\Theta=0,
$$

$$
\operatorname{Im}\omega\,X
+(1-\operatorname{Re}\omega)\Theta=0.
$$

Positive degree implies `|ω| = 1`. The antipodal branch forces `Θ = 0`; every
ordinary branch satisfies

$$
X=
\frac{-\operatorname{Im}\omega\,\Theta}
{1+\operatorname{Re}\omega}.
$$

CI result: success through the public import graph.

## Event 6C — trigonometric half-angle branch

Completed in:

```text
DkMath.RH.CFBRC.MirrorAngleBranch
```

Writing

$$
\omega=\cos\varphi+i\sin\varphi
$$

turns the ordinary branch into the half-angle line

$$
X=-\Theta\tan\left(\frac\varphi2\right).
$$

The module fixes the real/complex trigonometric-coordinate bridge and the exact
half-angle identity used by the mirror slope.

CI result: success through the public import graph.

## Event 6D — finite root index

Completed in:

```text
DkMath.RH.CFBRC.MirrorIndexedRoot
```

Mathlib's primitive-root API is used to prove that every positive-degree root
of unity has an index `k < d`:

$$
\omega
=
\exp\left(\frac{2\pi i k}{d}\right).
$$

The zero index is excluded by `ω ≠ 1`. Therefore every off-centered mirror
closure is carried by some finite nonzero branch index

$$
1\le k<d.
$$

CI result: success through the public import graph.

## Event 6E — complete explicit threat classification

The indexed multiplier has half-angle

$$
\alpha_{d,k}=\frac{\pi k}{d}.
$$

Lean now proves the complete disjunction

$$
\Theta=0
\quad\lor\quad
\exists\,k<d,\;k\ne0,\;
\cos\alpha_{d,k}\ne0,
\quad
X=-\Theta\tan\alpha_{d,k}.
$$

When `Θ ≠ 0`, the antipodal case is impossible, so every off-centered mirror
closure lies on one of the finitely many explicit tangent lines

$$
X=-\Theta\tan\left(\frac{\pi k}{d}\right),
\qquad 1\le k<d.
$$

Main Lean API:

- `indexedRootBranchUnit_eq_exp`
- `exists_indexed_root_branch_unit_of_pow_eq_one`
- `exists_nonzero_indexed_branch_of_mirrorCFBRC_eq_zero`
- `theta_eq_zero_of_indexed_antipodal_branch`
- `mirrorCFBRC_offcenter_branch_complete`
- `exists_indexed_tangent_branch_of_mirrorCFBRC_eq_zero_of_theta_ne_zero`

CI result: success through the public `DkMath.RH` import graph.

## Current mathematical boundary

The algebraic threat model is complete:

1. the standard CFBRC family closes only at `X = 0`;
2. the enlarged mirror family can close off-center only on a finite indexed
   tangent branch, apart from the degenerate `Θ = 0` antipodal case.

Thus a future zeta bridge has two possible proof routes:

$$
\operatorname{NontrivialZetaZero}(s)
\longrightarrow
C_d\!\left(s.\operatorname{re}-\frac12,\Theta(s)\right)=0,
$$

or, for a mirror-valued bridge, prove that its image enters none of the finite
nontrivial tangent branches.

## Next target — Event 7

Construct a finite complex-vector closure layer that is independent of zeta:

- endpoint sum;
- rotation coordinate;
- positive and negative projected masses;
- transverse imaginary gap;
- permutation invariance of the endpoint;
- closure equivalence

$$
\sum_j v_j=0
\quad\Longleftrightarrow\quad
\text{positiveMass}=\text{negativeMass}
\;\land\;
\text{transverseGap}=0.
$$

This finite theorem will be the algebraic receiving end for a later convergent
or regularized zeta representation. Sorting and spiral drawing remain a visual
projection only and must not alter the endpoint semantics.
