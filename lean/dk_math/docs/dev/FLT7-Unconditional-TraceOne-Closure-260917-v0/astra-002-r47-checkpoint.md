# FLT7TC-005R47 — Source-sensitive calibration exclusion

## Goal

Promote the Astra-002 kernel-checked calibration exclusion to one independent
production module. The endpoint is `W != rho0`, not `False` for all C=1 packets.

Reference implementation:

`DkMathTest/FLT/SevenCalibrationExclusionAstra02Scratch.lean`

Research derivation and other routes:

`docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/astra-002-report.md`

## Exact public endpoint

Use the current namespaces and implicit packet parameters:

```lean
theorem directOrbitDeepJetWUnit_ne_calibration
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (hc : h.c = 1)
    (eta : SevenRealCubicIntˣ)
    (heta : h.squareRefinement.gapSquareRoot =
      (eta : SevenRealCubicInt) * (h.u : SevenRealCubicInt)) :
    directOrbitDeepJetWUnit h.squareRefinement eta ≠ directOrbitDeepJetRho
```

The production namespace should be `DkMath.FLT.Seven.SevenRealCubic`.
Retain the same `source`, `r`, `p`, and `h` throughout.
An existence wrapper may reuse the existing C=1 scalarization API, but is not
required for this checkpoint. Do not add assumptions to manufacture exclusion.

## File boundary

Create:

`DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCalibrationExclusion.lean`

Its sole project import can be:

```lean
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet
```

The Astra scratch has passed with this import. It does not need the paired
deep-jet module or the R45 depth-nine extraction. Reuse existing seventh-power
coordinate theorems without adding to the heavy coordinate module.

## Internal proof plan

Keep the following helpers private unless a concrete second consumer exists.

1. Prove the source tail identity
   `theta^35 * thetaSevenUnit^12 = -7^11 * (2 + alpha + alpha^2)`.
   First compute `theta^2*thetaSevenUnit = -(2+alpha+alpha^2)`, then use
   `7=theta^3*thetaSevenUnit`. Avoid a fresh expansion of the 35th power.
2. From `p.source_eq_pow`, prove `(p.rho^7).snd = (p.rho^7).thd`.
3. Define the homogeneous quintic
   `F(a,K)=3*a^5+40*a^4*K+295*a^3*K^2+1293*a^2*K^3+3145*a*K^4+3278*K^5`.
   Verify the coefficient defect of `⟨a,K,K⟩^7` is `-49*K^2*F(a,K)`.
   Reuse `thetaLinear_pow_seven` and `thetaSquare_pow_seven`.
4. Prove impossibility of this source-plane equation for
   `K != 0`, `7 | K`, and nonzero theta residue. Cancel `-49*K^2` over the
   integers **before** casting to `ZMod 7`; otherwise the factor 49 loses the equation.
5. From `sigma(x)-x=K*theta^2*rho0`, recover `x=⟨x.fst,K,K⟩`
   using the constant and quadratic alpha coordinates.
6. For the public endpoint, assume `W=rho0`, set
   `K=7^(10+14*k)*(h.u:ℤ)^14`, and use `h.u_pos` and normalization.
   The gap-core expansion is a short ring identity, already in the scratch;
   duplicating that local proof avoids importing the large paired module.
   Finish with the preceding impossibility lemma.

## Integration and verification

- Add the new module to the existing FLT7 public import facade following its
  current organization. Inspect that facade before editing.
- Turn the Astra scratch into a client regression test, or retain a separate
  small test applying the production endpoint with all original parameters.
- Run Lean/Lake targets sequentially, never concurrently. Validate the new
  module first, then its client and the facade. Use cached dependencies;
  do not start a full repository build as part of this narrow checkpoint.
- Print axioms for the public endpoint. Expected:
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- Check new source for placeholders, run whitespace checks, and record exact
  commands and results in the R47 report.

## Acceptance boundary

Success is the stated public inequality, with the attached source-sensitive
proof and a passing client. The immediate consequence for any R45 witness is
that its high-power correction cannot be the identity; this is not a proof
that no nonidentity correction exists.

Do not incorporate the separate `q % 7 = 1` bridge or the degree-six phase
bridge into R47. Do not add a generic Thue solver, fundamental-unit claim,
further Hensel level, successor packet, or terminal FLT theorem.
