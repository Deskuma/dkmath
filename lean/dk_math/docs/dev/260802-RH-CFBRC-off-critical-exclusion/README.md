# 260802 RH–CFBRC Off-Critical Exclusion

- Started: 2026-08-02
- Updated: 2026-08-04
- Authors: D. and Wise Wolf
- Base branch: `develop`
- Work branch: `wip/RH-CFBRC-off-critical-exclusion-260802-v2`
- Status: active research; Lean implementation paused at the Abel-projection checkpoint

## Integration checkpoint

The preceding implementation line was integrated into `develop` through PR #76.

```text
merged pull request:
  #76
  WIP: RH–CFBRC critical-mirror Abel projection and moving-frame analysis

verified implementation head:
  70cdbdadc6614d8985d5a0bf92217e1bd2809625

verified workflow:
  Lean CI #857
  run id: 30842691102
  result: success

merge commit:
  9393162c5d89095d55821f832244ce932ffd2ee9

v2 start point:
  develop
  092de0c453566707afd9f54b480fe47540d21794
```

The `v2` branch is the new continuation branch. Its initial change was documentation-only; the inherited Lean implementation is the Green state integrated by PR #76.

The next implementation pass is delegated to Codex GPT-5.6 Luna and must begin from:

```text
RH_CFBRC_Abel_projection_handoff_2026-08-04.md
```

## Purpose

This project separates the RH program into two independently audited layers.

1. Prove algebraically that the selected positive-degree standard CFBRC closure cannot vanish away from the centered line.
2. Construct a non-circular analytic `map_zero` from every nontrivial zeta zero into that standard CFBRC closure.

The centered coordinate is

$$
X = \sigma - \frac12.
$$

Thus `X = 0` is the critical line and `X ≠ 0` is an off-critical candidate.

For positive degree `d`, the standard real-input CFBRC coordinate is

$$
C_d(X,\Theta) = (X+i\Theta)^d-(i\Theta)^d.
$$

Lean proves the exact algebraic exclusion

$$
C_d(X,\Theta)=0 \Longleftrightarrow X=0 \qquad (0<d).
$$

Equivalently,

$$
\mathrm{offCriticalCFBRC}(d,\sigma,\Theta)=0 \Longleftrightarrow \sigma=\frac12 \qquad (0<d).
$$

This theorem is independent of zeta-zero facts.

## Final bridge target

The remaining analytic obligation is a positive-degree bridge whose essential field has the form

$$
\mathrm{NontrivialRiemannZetaZero}(s) \Longrightarrow \mathrm{offCriticalCFBRC}(d,s.\mathrm{re},\Theta(s))=0.
$$

Combining such a `map_zero` with the algebraic exclusion would give

$$
s.\mathrm{re}=\frac12.
$$

The bridge must obey the following audit rules.

- It must be defined off the critical line as well as on it.
- It must not assume `s.re = 1 / 2`.
- Its phase, frame, or normalization must not branch on the desired conclusion.
- Every multiplier used for zero transport must be proved nonzero independently.
- The algebraic exclusion modules must remain independent of zeta analysis.
- Any global balance condition already equivalent to RH must not be imported as an auxiliary lemma.

## Completed Lean-checked architecture

### 1. Positive-degree standard CFBRC exclusion

Implemented in the algebraic exclusion layer:

```lean
cfbrcR_eq_zero_iff_x_eq_zero

offCriticalCFBRC_eq_zero_iff_re_eq_half

ZeroToCFBRCBridge
re_eq_half_of_zeroToCFBRCBridge
```

The analytic difficulty is isolated in `ZeroToCFBRCBridge.map_zero`.

### 2. Mirror-CFBRC threat classification

The enlarged mirror family has been classified through:

- boundary/core factorization;
- nontrivial root-of-unity witnesses;
- finite indexed roots;
- tangent branches;
- antipodal separation.

The standard family closes only at the centered coordinate. The mirror family may possess explicit off-centered branches, so mirror closure itself cannot replace the standard CFBRC target without an additional branch-exclusion theorem.

### 3. Critical-mirror zeta transport

For a nontrivial zeta zero `s`, Lean fixes the critical mirror

$$
\mathrm{criticalMirror}(s)=\overline{1-s}.
$$

The critical mirror is again a nontrivial zeta zero. No Riemann-hypothesis assumption is used in this transport.

### 4. Eta endpoint and energy layers

The implementation includes:

- original and critical-mirror paired endpoint vanishing;
- sum and difference endpoint limits;
- absolute endpoint-energy collapse;
- structural and ordinary-defined normalization layers;
- complete regular/collapsed endpoint-state separation;
- KUS structural-ratio and decoder audit layers.

The structural-ratio API does not redefine ordinary division. At a collapsed endpoint, the result remains a punctured-limit statement rather than a pointwise assignment of `0 / 0 = 1`.

### 5. Exact critical-mirror eta weight transport

Every mirror eta term is the corresponding original eta term multiplied by an exact positive-real amplitude weight.

For informative indices, its norm detects the side of the critical line:

```text
1 / 2 < s.re:
  weight norm > 1

s.re < 1 / 2:
  weight norm < 1

s.re = 1 / 2:
  weight norm = 1
```

The endpoint-increment decoder recovers the centered real coordinate exactly. Its global balance predicate is diagnostic only: Lean audits that imposing global balance on all nontrivial zeros is already equivalent to RH.

### 6. Fixed-frame obstruction interfaces

Two abstract obstruction mechanisms are available:

- a termwise common-half-plane certificate;
- an adjacent-pair common-half-plane certificate.

Either certificate, if independently constructed off the critical line, contradicts the verified projected zero limit and forces `s.re = 1 / 2`.

The adjacent-pair version is weaker because cancellation inside each natural eta pair is permitted.

### 7. Paired defect identity and decay

One critical-mirror defect pair is exactly

```text
etaPairTerm (criticalMirror s) k - etaPairTerm s k
```

and the finite paired defect is exactly the mirror paired partial sum minus the original paired partial sum.

The existing eta-pair derivative estimate transfers one additional decay power to this paired defect.

### 8. Real integral kernel and eventual sign

The paired defect has been lowered to a real integral representation. The completed chain passes through:

```text
off-critical coefficient sign
→ continuous weight threshold and pressure
→ defect-kernel factorization
→ eventual kernel sign
→ integrated defect-pair sign
→ rotated defect-pair projection sign
```

This is stronger than a coefficient-only observation: the sign reaches the actual integrated pair term.

### 9. Pair-left rotating frame

Each pair is moved into its own local frame using

```lean
etaPairBaseRotation s k
```

The rotated pair and its signed vertical projection are

```lean
etaCriticalMirrorRotatedDefectPairTerm s k
etaCriticalMirrorRotatedDefectPairProjection s k
```

The moving-frame projected partial sum is

```lean
etaCriticalMirrorRotatedDefectProjectionPartial K s
```

Write these quantities schematically as `p_K(s)` and `P_K(s)`. Lean proves the exact successor identity

$$
P_{K+1}(s)=P_K(s)+p_K(s).
$$

### 10. Eventual drift and natural-tail monotonicity

For a nonreal nontrivial zeta zero `s`, Lean proves:

```text
1 / 2 < s.re:
  P_K(s) is eventually strictly increasing.

s.re < 1 / 2:
  P_K(s) is eventually strictly decreasing.
```

The result is strengthened to strict monotonicity or strict antitonicity on a complete natural-number tail, including every fixed positive forward block.

### 11. Abel transform and correction limit

The moving-frame paired partial sums possess an exact Abel-transform description. The frame-correction series is summable, and the complex moving-frame partial sums converge to the negative correction `tsum`.

After applying the signed vertical projection, the named real limit is

```lean
etaCriticalMirrorRotatedDefectProjectionLimit s
```

and the remaining distance is

```lean
etaCriticalMirrorRotatedDefectProjectionLimitGap K s
```

### 12. One-sided approach to the Abel limit

The present Green endpoint is:

```text
1 / 2 < s.re:
  P_K(s) is eventually strictly increasing,
  converges to its finite Abel limit from below,
  and the remaining Abel-limit gap is eventually positive.

s.re < 1 / 2:
  P_K(s) is eventually strictly decreasing,
  converges to its finite Abel limit from above,
  and the remaining Abel-limit gap is eventually negative.
```

The complete current dependency chain is therefore

```text
positive-degree standard CFBRC exclusion
→ critical-mirror zero transport
→ exact eta weight transport
→ paired defect identity and decay
→ real defect-pair integral
→ eventual off-critical kernel sign
→ pair-left rotating-frame sign
→ projected successor drift
→ natural-tail strict monotonicity
→ Abel transform and correction limit
→ one-sided approach to the Abel limit
→ eventual sign of the Abel-limit gap
```

## Deliberate mathematical boundary

This project has not yet proved the final zeta-to-CFBRC `map_zero`, off-critical exclusion of nontrivial zeta zeros, or RH.

The following remain unproved:

- the projected Abel limit itself is nonzero;
- the local pair frames combine into one fixed global frame;
- the original complex defect has a non-cancelling global half-plane or sector certificate;
- an off-critical nontrivial zeta zero is impossible;
- `ZeroToCFBRCBridge.map_zero` can be instantiated from the present eta geometry.

The essential warning is

```text
etaPairBaseRotation s k depends on k.
```

The current sign result is therefore a moving-frame theorem. It is not yet a common-half-plane theorem in one fixed complex frame.

A second warning is equally important:

```text
an eventually strict monotone sequence may converge to a finite limit.
```

Strict monotonicity plus convergence is not a contradiction. The Abel-limit result must not be promoted directly into an RH conclusion.

## Next implementation events

Implementation is paused until Codex GPT-5.6 Luna resumes from the handoff document.

The next safe sequence is:

1. Prove summability of the real projected defect-pair series.
2. Name and verify the finite identity

```text
projection partial = Finset.sum over Finset.range
```

3. Identify the Abel-limit gap with the actual infinite projected tail

$$
G_K(s)=\sum_{k=K}^{\infty}p_k(s).
$$

4. Audit the sign direction and every continuous-linear-map/`tsum` exchange in that identity.
5. Study the frame increment

```text
etaPairBaseRotation s (k + 1) / etaPairBaseRotation s k
```

or the corresponding phase difference.
6. Determine whether the accumulated frame rotation is explicitly bounded, summably controlled, or confined to a usable sector.
7. Convert the moving-frame sign into the weakest independently proved fixed-frame or asymptotic-frame obstruction certificate.
8. Only after that certificate is available, construct the positive-degree `map_zero`.

## Required implementation discipline

Each resumed implementation event must follow this order:

1. Add one small production layer.
2. Add its regression test.
3. Connect the public `DkMath.RH` and `DkMathTest` export graphs.
4. Commit the single layer.
5. Check Lean CI once.
6. Stop immediately on any CI failure and report the exact branch head, file, position, and log without applying speculative follow-up fixes.

## Principal production modules at the checkpoint

```text
DkMath.RH.CFBRC.OffCriticalExclusionGeneral
DkMath.RH.CFBRC.MirrorThreatModel
DkMath.RH.CFBRC.CriticalMirrorZeroBridge
DkMath.RH.CFBRC.EtaCriticalMirrorWeightedTransport
DkMath.RH.CFBRC.EtaCriticalMirrorWeightPressure
DkMath.RH.CFBRC.EtaCriticalMirrorPhaseProjection
DkMath.RH.CFBRC.EtaCriticalMirrorPairedPhaseProjection
DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectDecay
DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectIntegral
DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization
DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign
DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairTermEventualSign
DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame
DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform
DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection
DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit
DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjection
DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTailMonotonicity
DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimitSide
```

## Focused build checks

```text
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedDefectIntegral
lake build DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelFactorization
lake build DkMath.RH.CFBRC.EtaCriticalMirrorDefectKernelEventualSign
lake build DkMath.RH.CFBRC.EtaCriticalMirrorDefectPairTermEventualSign
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedRotatingFrame
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedTail
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedTailBound
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTransform
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelCorrection
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimit
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelProjection
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelTailMonotonicity
lake build DkMath.RH.CFBRC.EtaCriticalMirrorPairedAbelLimitSide
lake build DkMath.RH
lake build DkMathTest
```

See [IMPLEMENTATION-PLAN.md](./IMPLEMENTATION-PLAN.md) for the original event plan and [PROGRESS.md](./PROGRESS.md) for the earlier checkpoint history. The current continuation boundary is defined by this README and `RH_CFBRC_Abel_projection_handoff_2026-08-04.md`.
