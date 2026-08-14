# IPSM-040 — CS16 closeout and CS17 normalized ray polarization / aggregate ordering audit

## Status

CS16 is accepted as **Green-B**.

Verified source-derived ingredients in `PascalCenteredXiPrimeSideGeometricRaySignedNumeratorAudit.lean`:

- the finite prime-power exponent support is canonically a prefix `Finset.range rayLength`;
- on the residue-window right edge, the fixed-prime ratio satisfies `‖q‖ = p ^ (-σ) < 1`;
- therefore `q ≠ 1`, `1 - q ≠ 0`, and `0 < Complex.normSq (1 - q)`;
- the finite ray amplitude is exactly the weighted finite geometric core with canonical ray length;
- the denominator-free geometric compression is transported to the full weighted ray amplitude;
- the real ray amplitude is exactly a named signed numerator divided by the strictly positive `Complex.normSq (1 - q)` denominator;
- both nonnegative and nonpositive pointwise sign questions are exactly equivalent to the corresponding signed-numerator sign questions;
- the signed numerator is reduced to the four-term endpoint ledger;
- `Complex.normSq (1 - q) = 1 - 2 * q.re + Complex.normSq q` is exposed;
- no independent signed-numerator provider is asserted.

CS16 contains no infinite ray, no infinite sum/integral exchange, no global sign theorem, and no RH conclusion.

The next task is **not** to guess a sign for the four endpoint modes individually.  Instead, polarize the signed numerator into two nonnegative quadratic masses and move the actual cancellation question to an ordering theorem.

---

## CS17 objective

For one prime `p`, one finite cutoff `X`, and one right-edge height `t`, abbreviate conceptually

```text
q(t) = pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t
m    = pascalCenteredXiPrimeSidePrimePowerRayLength X p
h(t) = pascalCenteredXiMellinSecondDifferenceWeight ε 0
         (pascalCenteredXiPrimeSideModePhaseNode W t)
A(t) = h(t) * (q(t) - q(t)^(m+1))
B(t) = 1 - q(t)
```

Then the CS16 signed numerator is

$$
N(t)=\operatorname{Re}(A(t)\overline{B(t)}).
$$

The strictly positive denominator is

$$
D(t)=|B(t)|^2=\operatorname{normSq}(B(t))>0.
$$

The central CS17 identity is the real polarization law

$$
4N(t)=|A(t)+B(t)|^2-|A(t)-B(t)|^2.
$$

Therefore the ray amplitude should admit an exact normalized plus/minus decomposition

$$
4\operatorname{Re}(\operatorname{RayAmplitude}(t))=E_+(t)-E_-(t),
$$

with

$$
E_\pm(t)=\frac{|A(t)\pm B(t)|^2}{|B(t)|^2}\ge 0.
$$

This is the ordinary-complex-analysis shadow of a `q2` polarization.  **Do not import CF2D merely to rename it.**  First close the exact complex identities.  A later sidecar may transport `Complex.normSq` to `Vec.q2` / `cfcos` / `cfsin` if useful.

---

## CS17-A — name the two numerator factors

Introduce small source-level definitions for the two complex factors if that reduces theorem noise.

Suggested shapes:

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayEndpointAmplitude
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (X p : ℕ) (t : ℝ) : ℂ :=
  pascalCenteredXiMellinSecondDifferenceWeight ε 0
      (pascalCenteredXiPrimeSideModePhaseNode W t) *
    (pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t -
      pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t ^
        (pascalCenteredXiPrimeSidePrimePowerRayLength X p + 1))
```

and

```lean
noncomputable def pascalCenteredXiPrimeSideFiniteGeometricRayDenominatorVector
    (W : PascalCenteredXiResidueTransportWindow)
    (p : ℕ) (t : ℝ) : ℂ :=
  1 - pascalCenteredXiPrimeSidePrimeRatioAtRightEdge W p t
```

Exact names may be shortened if necessary.

Prove the adapter

```text
SignedNumerator = Complex.re (A * conj B).
```

This must be `rfl`, `simp`, `ring`, or a short exact rewrite from CS16.  Do not introduce a new provider assumption.

---

## CS17-B — ordinary complex polarization

Prove a reusable finite identity first, preferably independent of the RH namespace data:

```text
4 * Complex.re (A * conj B)
  = Complex.normSq (A + B) - Complex.normSq (A - B).
```

An equivalent `2 * Re = normSq(A+B) - normSq A - normSq B` identity is also useful, but the plus/minus form is preferred because it gives an ordering theorem immediately.

Then specialize to the CS16 signed numerator:

```text
4 * SignedNumerator(t)
  = normSq (A(t) + B(t)) - normSq (A(t) - B(t)).
```

Required sign adapters:

```text
0 ≤ SignedNumerator(t)
  ↔ normSq (A(t) - B(t)) ≤ normSq (A(t) + B(t))

SignedNumerator(t) ≤ 0
  ↔ normSq (A(t) + B(t)) ≤ normSq (A(t) - B(t)).
```

These are algebraic equivalences only, not sign providers.

---

## CS17-C — normalized plus/minus ray densities

Define pointwise densities with the **same strictly positive CS16 denominator**:

```text
RayPlusDensity(t)  = normSq (A(t) + B(t)) / normSq B(t)
RayMinusDensity(t) = normSq (A(t) - B(t)) / normSq B(t).
```

For prime `p`, prove:

```text
0 ≤ RayPlusDensity(t)
0 ≤ RayMinusDensity(t)
```

using only `Complex.normSq_nonneg` and the already-proved strict positivity of `normSq B(t)`.

Then prove the exact normalized polarization

```text
4 * (FinitePrimePowerRayAmplitude ε W X p t).re
  = RayPlusDensity ε W X p t - RayMinusDensity ε W X p t.
```

This should follow from CS16-D plus CS17-B.

Do not infer an ordering from the fact that both densities are nonnegative.

---

## CS17-D — integrated ray energies

The actual CS14/CS15 ray kernel is an interval integral on `[0,T]`.  Define

```text
RayPlusEnergy  = ∫ t in 0..T, RayPlusDensity(t)
RayMinusEnergy = ∫ t in 0..T, RayMinusDensity(t).
```

First certify interval integrability from existing finite-ray continuity / integrability plus the nonvanishing denominator, or prove continuity directly if shorter.

Then prove

$$
4\,\operatorname{RayKernel}_{p,X}=\operatorname{RayPlusEnergy}_{p,X}-\operatorname{RayMinusEnergy}_{p,X}.
$$

Also prove

```text
0 ≤ RayPlusEnergy
0 ≤ RayMinusEnergy
```

because the pointwise densities are nonnegative and `W.rectangle.hT : 0 < T` fixes interval orientation.

Most important exact ordering adapter:

```text
0 ≤ RayKernel
  ↔ RayMinusEnergy ≤ RayPlusEnergy.
```

Optionally add the reverse-sign iff as well.

This is strictly weaker and more relevant than demanding a pointwise numerator sign.

---

## CS17-E — aggregate prime-weighted energies

Per-ray sign is potentially too strong.  The finite arithmetic source only needs the **sum over prime rays**.

Define finite aggregate energies at cutoff `X`:

```text
AggregatePlusEnergy ε W X
  = ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
      Real.log p * RayPlusEnergy ε W X p

AggregateMinusEnergy ε W X
  = ∑ p ∈ pascalPrimeCoordinateSupportUpTo X,
      Real.log p * RayMinusEnergy ε W X p.
```

For support primes, prove `0 < Real.log p` or at least `0 ≤ Real.log p`, then prove both aggregate energies are nonnegative.

Use the CS14 exact ray decomposition and CS17-D to prove the finite mode ledger identity

$$
4\sum_{n\le X}\Lambda(n)K_{\varepsilon,W}(n)
=
\operatorname{AggregatePlusEnergy}_{\varepsilon,W,X}
-
\operatorname{AggregateMinusEnergy}_{\varepsilon,W,X}.
$$

Then prove the aggregate ordering adapter

```text
0 ≤ ∑ n ∈ Finset.range (X + 1),
      vonMangoldt n * FiniteModeKernel ε W n
  ↔ AggregateMinusEnergy ε W X ≤ AggregatePlusEnergy ε W X.
```

This is the preferred sign frontier because it permits cancellation between different prime rays.  Do not require every individual ray to have the same sign unless such a theorem is independently source-derived.

---

## CS17-F — block / cutoff compatibility

CS12 already gives finite block projections as differences of finite mode sums.

Transport the aggregate energy ledger to a finite block `X → Y`:

```text
4 * FinitePrimeBlockProjection ε W X Y
  = (AggregatePlusEnergy ε W Y - AggregatePlusEnergy ε W X)
      -
    (AggregateMinusEnergy ε W Y - AggregateMinusEnergy ε W X).
```

Any algebraically equivalent parenthesization is acceptable.

Important: the differences of aggregate energies are **not** automatically nonnegative.  Do not infer monotonicity from nonnegativity of each aggregate energy.

If a monotonicity theorem appears naturally from the finite support growth, prove it source-first.  Otherwise leave it open.

---

## CS17-G — provider hierarchy

Keep the following strengths explicitly distinct:

1. **Pointwise ray ordering**

```text
∀ t ∈ [0,T], RayMinusDensity(t) ≤ RayPlusDensity(t)
```

This is strongest and may fail because the phase is oscillatory.

2. **Integrated single-ray ordering**

```text
RayMinusEnergy ≤ RayPlusEnergy
```

This allows cancellation in `t` but still asks every prime ray to have one sign.

3. **Aggregate prime-weighted ordering**

```text
AggregateMinusEnergy ≤ AggregatePlusEnergy
```

This also allows cancellation across different base primes and is the weakest of these three.  Prefer this as the actual provider frontier.

If none is source-derived, record only the weakest missing provider as a named gap, for example:

```lean
inductive PascalCenteredXiPrimeSideAggregateRayEnergyOrderingGap : Prop
  | noIndependentAggregateRayEnergyOrderingProvider :
      PascalCenteredXiPrimeSideAggregateRayEnergyOrderingGap
```

Do not add an abstract theorem whose hypothesis is merely the target ordering renamed as a provider.

---

## CS17-H — optional diagnostic at `t = 0`

A local center-height theorem may be useful as a diagnostic, but it is not required for Green-B.

At `t = 0`, for `ε > 0`, `σ > 1`, prime `p`, and nonempty ray length, all scalar pieces become real with `0 < q < 1`.  If inexpensive, prove a theorem showing the signed numerator is nonnegative, or positive when the ray is nonempty.

This would certify the orientation at the center of the vertical window only.

Do **not** extrapolate it to all `t`; the finite phase is oscillatory.

---

## CS17-I — q2 / CF2D sidecar is deferred

The polarization identity

$$
4\operatorname{Re}(A\overline B)=|A+B|^2-|A-B|^2
$$

is exactly a two-dimensional quadratic-mass statement.

After the ordinary complex CS17 layer is Green, a later sidecar may map

```text
Complex.normSq z
```

to the corresponding

```text
Vec.q2 ⟨z.re, z.im⟩
```

and reinterpret plus/minus densities as CF2D quadratic masses.

That sidecar may expose a reusable `q2`, rotation, projection, or collision theorem.  It is intentionally **not** required in CS17, so that no CF2D abstraction can hide a missing arithmetic ordering provider.

---

## Firewall — aggregate ordering is still not the endpoint anchor

Even a successful aggregate ray-ordering theorem controls a finite-mode / cutoff direction.  It does not by itself prove the absolute sign of

```text
pascalCenteredXiMellinQuadraticArithmeticDefectEndpoint ε W.
```

The earlier logical split remains mandatory:

```text
signed cutoff / tail direction
+
independent finite-cutoff anchor or vanishing upper envelope
```

Do not import the fixed-Xi defect nonnegativity, horizontal-energy nonnegativity, or the RH-equivalent fixed-defect vanishing theorem as the missing arithmetic anchor.

---

## Green criteria

CS17 is **Green-B** if it closes all of the following without a synthetic sign assumption:

1. signed numerator is exposed as `Re (A * conj B)` with named source factors;
2. exact plus/minus norm-square polarization is proved;
3. normalized plus/minus densities are defined over the strictly positive CS16 denominator and are nonnegative;
4. finite ray amplitude has exact pointwise plus/minus decomposition;
5. integrated plus/minus ray energies are well-defined, nonnegative, and recover the ray kernel by exact polarization;
6. finite aggregate prime-weighted plus/minus energies are nonnegative;
7. the finite von-Mangoldt mode ledger is exactly the aggregate plus/minus energy difference;
8. finite block compatibility is recorded if proof friction is reasonable;
9. the remaining aggregate ordering provider is kept as a named gap if no source-derived ordering theorem appears;
10. no infinite ray, no infinite sum/integral exchange, no endpoint sign theorem, and no RH conclusion are introduced.

The central strategic reduction is now

```text
finite prime-power ray
→ geometric quotient
→ positive norm-square denominator
→ signed pairing Re(A * conj B)
→ plus/minus quadratic masses
→ integrated / aggregate energy ordering.
```

If the required sign mechanism is genuinely quadratic, CS17 is the smallest currently authorized surface on which it should become visible.
