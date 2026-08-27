# RH–CFBRC Off-Critical Exclusion — Implementation Plan

## 0. Research statement

The project does not begin by explaining how prime factors are distributed at a nontrivial zero. It first asks a narrower structural question:

> Can a CFBRC closure polynomial representing the zero-formation mechanism vanish when `σ ≠ 1/2`?

The intended proof architecture is

$$
\text{algebraic exclusion}
\longrightarrow
\text{zero-preserving bridge}
\longrightarrow
\text{critical-line conclusion}.
$$

Only after this location theorem is established do we inspect the natural-number and prime-factor allocation inside the zero state.

## 1. Coordinates and core polynomial

Define the centered real coordinate

$$
X:=\sigma-\frac12.
$$

For real `X`, `Θ` and natural `d`, use the existing CFBRC polynomial

$$
C_d(X,\Theta)
:=(X+i\Theta)^d-(i\Theta)^d.
$$

In Lean this is `DkMath.CFBRC.TrigBridge.cfbrcR d X Θ`.

The desired general algebraic theorem is

$$
d>0
\quad\Longrightarrow\quad
C_d(X,\Theta)=0
\iff
X=0.
$$

The initial implementation proves the `d = 2` case first, because its real component is already fixed by the existing theorem

$$
\operatorname{Re}C_2(X,\Theta)=X^2.
$$

This provides a fully kernel-checkable first exclusion theorem before the general norm argument is introduced.

## 2. Event sequence

### Event 1 — centered coordinate API

Add:

```lean
centeredSigma (σ : ℝ) : ℝ
```

and prove

```lean
centeredSigma σ = 0 ↔ σ = 1 / 2
```

without any zeta dependency.

### Event 2 — standard CFBRC projection

Add:

```lean
offCriticalCFBRC (d : ℕ) (σ Θ : ℝ) : ℂ
```

as

```lean
cfbrcR d (centeredSigma σ) Θ
```

The name records the intended use; the definition itself remains an ordinary CFBRC evaluation.

### Event 3 — first exclusion theorem (`d = 2`)

Prove:

```lean
cfbrcR_two_eq_zero_iff_x_eq_zero (X Θ : ℝ) :
  cfbrcR 2 X Θ = 0 ↔ X = 0
```

using `cfbrc_two_re` and the fact that a complex zero has real part zero.

Then prove:

```lean
offCriticalCFBRC_two_eq_zero_iff_re_eq_half (σ Θ : ℝ) :
  offCriticalCFBRC 2 σ Θ = 0 ↔ σ = 1 / 2
```

This theorem is the first completed off-critical exclusion certificate.

### Event 4 — abstract zero-preserving bridge

Define an interface parameterized by an arbitrary complex predicate `Zero`:

```lean
structure ZeroToCFBRCTwoBridge (Zero : ℂ → Prop) where
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s →
    offCriticalCFBRC 2 s.re (phase s) = 0
```

Prove the generic consequence:

```lean
re_eq_half_of_zeroToCFBRCTwoBridge
```

This theorem must not know what `Zero` means. It isolates the future analytic difficulty in `map_zero`.

### Event 5 — general positive-degree exclusion

Target:

```lean
cfbrcR_eq_zero_iff_x_eq_zero
    {d : ℕ} (hd : 0 < d) (X Θ : ℝ) :
    cfbrcR d X Θ = 0 ↔ X = 0
```

Proposed proof route:

1. Expand `cfbrcR d X Θ = 0` into equality of powers.
2. Apply complex norm or `normSq`.
3. Obtain

$$
(X^2+\Theta^2)^d=(\Theta^2)^d.
$$

4. Use nonnegativity and positive-degree injectivity of powers.
5. Conclude `X^2 = 0`, hence `X = 0`.

Do not add the theorem with `sorry`. If the general proof needs API exploration, retain the completed `d = 2` theorem as the stable public kernel and develop the general theorem in a separate scratch branch or private lemma section.

### Event 6 — mirror-CFBRC threat model

Define

$$
M_d(X,\Theta)
=(X+i\Theta)^d-(-X+i\Theta)^d.
$$

Factor it as

$$
M_d(X,\Theta)=2X\,K_d(X,\Theta).
$$

This is not the standard exclusion polynomial. It is a classification tool for how off-critical closure could arise in a larger symmetric model.

For `X ≠ 0`, classify zeros through

$$
\left(
\frac{X+i\Theta}{-X+i\Theta}
\right)^d=1,
$$

leading to nontrivial cyclotomic branches

$$
X=-\Theta\tan\left(\frac{\pi k}{d}\right).
$$

The purpose of this module is to state the complete threat model that a later zeta bridge must avoid.

### Event 7 — finite complex-vector closure bridge

Define finite vector families representing a convergent or regularized zeta expression. Separate:

- ordering used only for visualization,
- endpoint sum used for closure,
- positive/negative rotated masses,
- transverse imaginary residual.

Prove the finite structural equivalence

$$
\sum_j v_j=0
\iff
\text{massBalance}\land\text{transverseGap}=0.
$$

The artificial reverse-copy spiral is retained only as a control model. The analytic bridge must use a genuine signed or regularized zeta representation.

### Event 8 — completed-zeta / Hardy / HOPC realization

Prefer a completed-zeta or Hardy-normalized formulation to remove trivial zeros and expose the functional-equation symmetry.

Possible strong bridge form:

$$
A(s)\,\Xi_c(s)
=U(s)\,C_d\!\left(s.\operatorname{re}-\frac12,\Theta(s)\right),
$$

with independently proved

$$
A(s)\neq0,
\qquad
U(s)\neq0
$$

in the nontrivial-zero region.

A weaker implication is sufficient for RH:

$$
\operatorname{NontrivialZero}(s)
\longrightarrow
C_d\!\left(s.\operatorname{re}-\frac12,\Theta(s)\right)=0.
$$

The bridge must be auditable and non-circular.

### Event 9 — final contradiction theorem

Assume

$$
\operatorname{NontrivialZero}(s)
\quad\land\quad
s.\operatorname{re}\neq\frac12.
$$

Use the zero-preserving bridge to obtain a standard CFBRC zero. Apply the algebraic off-critical exclusion theorem and derive a contradiction.

The final proof should have the visible shape:

```lean
have hcfbrc := bridge.map_zero hs
have hcenter := (offCriticalExclusion ...).mp hcfbrc
exact hnot hcenter
```

### Event 10 — prime-mass interpretation

After the location theorem, decompose the zero-state vector family through

$$
\log n=\sum_p v_p(n)\log p.
$$

This layer may explain:

- the natural-number mass split,
- the prime-factor contribution allocation,
- proportionality or correspondence with prime distribution,
- the geometric spiral observed in numerical experiments.

It must not be used as an unproved premise of the location theorem.

## 3. Module layout

Initial module:

```text
DkMath/RH/CFBRC/OffCriticalExclusion.lean
```

Planned modules:

```text
DkMath/RH/CFBRC/MirrorBranchClassification.lean
DkMath/RH/CFBRC/FiniteClosure.lean
DkMath/RH/CFBRC/CompletedZetaBridge.lean
DkMath/RH/CFBRC/RiemannHypothesis.lean
DkMath/RH/CFBRC/PrimeMassInterpretation.lean
```

Tests:

```text
DkMathTest/RH/CFBRCOffCriticalExclusion.lean
```

## 4. Acceptance criteria for the first slice

- No `sorry`.
- `lake build DkMath.RH.CFBRC.OffCriticalExclusion` succeeds.
- `lake build DkMathTest.RH.CFBRCOffCriticalExclusion` succeeds.
- `lake build DkMath.RH` succeeds after the import is added.
- The exclusion theorem imports no zeta-zero theorem.
- The generic bridge conclusion is parameterized by an arbitrary `Zero : ℂ → Prop`.
- The project documents clearly distinguish proved algebraic results from the unimplemented analytic bridge.

## 5. Codex handoff after the first commit

Codex should be asked to:

1. run the three builds above,
2. repair only Lean / Mathlib API errors without weakening theorem statements,
3. keep the module free of `sorry` and new axioms,
4. report the exact proof term or API used for each repair,
5. attempt Event 5 only after the `d = 2` slice is green,
6. open a follow-up commit rather than mixing the general-degree experiment into the stable theorem if the proof becomes invasive.

## 6. Current boundary of claims

The completed algebraic theorem will establish that the selected standard CFBRC polynomial has no off-critical zero. It will not by itself establish RH.

The remaining load-bearing statement is the zero-preserving bridge from nontrivial zeta zeros to this standard CFBRC zero locus. That bridge is the final mathematical question and must be proved without encoding the critical-line conclusion into its definitions.