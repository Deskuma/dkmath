# FLT3 current production audit — checkpoint 001

Date: 2026-10-04 JST. Scope: source audit for Instruction 001. No production
code changed by this audit. The claims below refer to the current
`DkMath.FLT.Three` tower, not the standalone artifacts or the legacy FLT
aggregator.

## Current entrypoint and closure

`DkMath/FLT/Three.lean` imports
`DkMath.FLT.Three.PositiveCubicNormalization` and
`DkMath.FLT.Three.EisensteinLibBridge`. The completed public endpoint is:

```lean
DkMath.FLT.Three.fermatThree_no_positive_solution
  (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ 3 + b ^ 3 ≠ c ^ 3
```

This normalizes by `d = Nat.gcd a b`, using
`exists_primitiveCubicPack_of_positive_solution`, then invokes
`primitiveCubicPack_false`. The latter performs
`Nat.strong_induction_on (a*b*c)` and calls
`exists_smaller_primitiveCubicPack` at the strictly smaller successor product.
These are explicit same-exponent, positive, primitive successors; a reduced
norm is not being substituted for the successor equation.

The primitive endpoint `FLT_d3_unconditional` additionally takes
`Nat.Coprime a b`. Neither endpoint takes a class-group, phase-exclusion,
descent-provider, or lifting hypothesis.

## Seven-axis matrix

| Axis | Actual current production evidence | Exact content / qualification |
| --- | --- | --- |
| Integer / GN factorization | `SignedThreeAdic.lean`, `SignedThreeAdicPacket`, private `packet_of_a`, `packet_of_b`, `packet_of_c`; `EisensteinSubstrate.lean:141`, `gn_three_sub_eq_eisenstein_norm_nat_coords` | Difference cases use `(c-b)*(c²+c*b+b²)=a³` or the swapped case. Sum case uses `(a+b)*(a²-a*b+b²)=c³`. These are signed orientations of the homogeneous cubic factorization. The algebraic carrier is not the natural linear `packet.carrier`. |
| Algebraic carrier | `EisensteinSubstrate.lean:31`, `EisensteinInt := TraceOneInt (-1)`; `eisensteinCoord`, `eisensteinTau`, `eisenstein_tau_sq`; `SignedThreeAdicPacket.alpha` | Exact chosen coordinates: in orientation a, `alpha=eisensteinCoord (-c) (-b)`; in orientation c, `alpha=eisensteinCoord (-a) b`; orientation b routes by swapping a and b. `tau²=tau-1`, `tau³=-1`, `tau⁶=1`. This is the full degree-two Eisenstein order in trace-one coordinates, not an identification inferred from norm equality. |
| Ramified correction | `eisensteinRamifier := 1+eisensteinTau`; `eisenstein_ramifier_norm`, `eisenstein_ramifier_sq`, `eisenstein_ramifier_mul_conj`; `SignedThreeAdicPowerSplit`; `EisensteinRamifierStrippedPacket.alpha_eq` | `N(lambda)=3`, `lambda²=3*tau`. Exact integer split is `carrier=9*A³`, `residual=3*B³`, `distinguished=3*A*B`, `A,B>0`, `coprime A B`, `3∤B`. One factor is removed by exact coordinates: `alpha=lambda*beta`, `N(beta)=B³`, `beta.snd=3*A³`. There is no production theorem named as an ideal-factorization multiplicity count; the once-stripped factor and `3∤B` are the actual certificates. |
| Normalized power | `beta_relPrime_conj`; `traceOneNegOneEuclideanDomain`; `traceOneNegOneGCDMonoid`; `exists_unit_mul_cube_of_coprime_mul_eq_cube`; `EisensteinCubeUpToUnitPacket.beta_eq` | The route skips an explicit ideal-power packet. It proves element-wise conjugate relative primality, `beta*conj(beta)=B³`, and obtains `beta=epsilon*gamma³` with `epsilon:EisensteinIntˣ` by the generic GCD-monoid theorem `exists_associated_pow_of_mul_eq_pow`. Thus `(beta)=(gamma)³` is a mathematical consequence of the element equality; it is not a newly verified stored ideal theorem here. |
| Unit / phase class | `eisensteinUnit_cases`; `EisensteinUnitSector`; `exists_sector_mul_cube_of_unit`; `EisensteinCubeSectorPacket`; `tau_sector_false`, `tauSq_sector_false`, `sector_eq_one` | All six units are classified. Modulo cubes the explicit three sectors are `{1,tau,tau²}`; signs are absorbed into cubes. Both nontrivial sectors contradict the exact second coordinate and `3∤B`. The remaining sector is forced to one for this packet, not for arbitrary units. |
| Integral / additive landing | `eisenstein_cube_coords`, `eisenstein_cube_snd`; `beta_eq_cube`; `gamma_coordinate_product_eq_A_cube`; `gamma_coordinate_norm_eq_B`; `EisensteinDescentFactorSource` | Exact cube identity yields `r*s*(r+s)=A³` and `r²+r*s+s²=B` for `gamma=(r,s)`. The first relation comes from the exact second coordinate, not the norm. Integer pairwise coprimality and signed roots then recover one of three positive Fermat equations. |
| Strict descent / contradiction | `EisensteinSignedCubeFactors`; `signed_cube_roots_route`; `EisensteinDescentFactorSource.source_A_lt_original_product`; `EisensteinSignedCubeFactors.strict_product_lt`; `PrimitiveCubicStrictDescent`; `exists_smaller_primitiveCubicPack`; `primitiveCubicPack_false` | Positive roots R,S,T have `R*S*T=A<a*b*c`, pairwise coprimality, and an appropriate permutation satisfying FLT3. The source orientation retains which original coordinate equals `3*A*B`, making the strict inequality source-correct. Strong induction closes the contradiction. |

## Actual forward dependency spine

The arithmetic tower used by the constructors is:

```text
positive primitive cubic equation
  -> signedThreeAdicOriginPacket_of_primitive_solution
  -> signedThreeAdicPowerSplit_with_packet (same origin packet)
  -> eisensteinRamifierStrippedPacket_of_powerSplit
  -> eisensteinConjugateCoprimePacket_of_stripped
  -> eisensteinCubeUpToUnitPacket_of_conjugateCoprime
  -> eisensteinCubeSectorPacket_of_cubeUpToUnit
  -> eisensteinExactCubePacket_of_sectorPacket
  -> eisensteinDescentFactorSource_of_primitive_solution
  -> eisensteinSignedCubeFactors_of_source
  -> primitiveCubicStrictDescent
  -> primitiveCubicPack_false
```

The exact cube source constructor preserves the same routed packet using
`signedThreeAdicPowerSplit_with_packet : {s // s.packet = origin.packet}`.
This matters: independent classical choices of two packets would not prove the
required distinguished-coordinate bound.

The `PrimitiveCubicLiftPacket` and `CubicValuationDepth` modules are imported
through the substrate and offer finite nonramified GN APIs. Their existence
does not mean that the completed descent uses their packet as a required
hypothesis. The descent constructors above instead use signed mod-nine
routing, norm-divisibility coprimality, and element extraction.

## Ramified and conjugate certificates in detail

`SignedThreeAdicPacket` records:

```text
carrier,residual,distinguished > 0
carrier * residual = distinguished³
N(alpha) = residual
alpha.snd-alpha.fst = carrier
3 | carrier, 3 | distinguished
residual mod 9 = 3
gcd(carrier,residual) = 3
```

The mod-nine routing establishes exactly one of a,b,c divisible by 3 from
the primitive Fermat equation. The packet orientation is therefore a real
finite state, not a stylistic proof branch. `SignedThreeAdicOriginPacket`
retains the distinguished source coordinate.

For the stripped factor beta, conjugate coprimality is proved without an
ideal or GCD typeclass: every common divisor d has norm dividing both
`B³` and `27*A⁶`, and
`powerSplit_coprime_B3_threeCube_A6` forces `N(d)=1`. The norm-one inverse is
constructed as `conj(d)`. Only after this certificate does the independently
constructed Euclidean-domain instance provide the GCD-monoid extraction.

The production extraction theorem has the exact interface:

```lean
exists_unit_mul_cube_of_coprime_mul_eq_cube
  {x y z : EisensteinInt}
  (hcop : IsUnit (gcd x y)) (hpow : x*y = z^3) :
  ∃ epsilon : EisensteinIntˣ, ∃ gamma : EisensteinInt,
    x = (epsilon : EisensteinInt) * gamma^3
```

For FLT3 its inputs are `x=beta`, `y=conj beta`, `z=(B:EisensteinInt)`.
No completed FLT theorem is used as its extraction lemma.

## Unit elimination is genuinely coordinate-sensitive

`EisensteinCubeSectorPacket.gamma_norm_eq_B` supplies `N(gamma)=B`.
For the tau sector, the second coordinate of `tau*gamma³` is
`r³+3*r²*s-s³`; for tau² it is `r³-3*r*s²-s³`.
Since `beta.snd=3*A³`, either nontrivial sector forces `3 | r-s`,
then `3 | N(gamma)=B`, contradicting `three_not_dvd_B`.

Only then does `beta_eq_cube` conclude the element identity `beta=gamma³`.
The cube second coordinate `3*r*s*(r+s)` and the previously retained exact
coordinate `3*A³` give the additive-factor landing. This is the precise
theorem-level barrier separating power geometry from an integer Fermat
successor. An ideal power and a norm identity alone do not supply it.

`EisensteinSignedCubeFactors` records positive R,S,T, pairwise coprimality,
the three absolute cube identities, and `R*S*T=A`. The sign routing theorem
is an actual disjunction:

```lean
signed_cube_roots_route (p : EisensteinSignedCubeFactors a b c) :
  (p.R^3+p.S^3=p.T^3) ∨
  (p.R^3+p.T^3=p.S^3) ∨
  (p.S^3+p.T^3=p.R^3)
```

`PrimitiveCubicStrictDescent` reconstructs a positive primitive successor for
each branch and stores both `next_product_eq : x*y*z=factors.source.A` and
`measure_lt : x*y*z<a*b*c`.

## Honest reverse projection into the FLT7 sequence

```text
ramified correction:
  alpha = (1+tau)*beta, N(beta)=B³, 3∤B

normalized ideal cube:
  not a separate production packet;
  conjugate coprimality + Euclidean GCD extraction gives the stronger
  beta=epsilon*gamma³ directly, hence the ideal cube as a consequence

unit class:
  six units -> three cube sectors -> exact coordinate excludes tau,tau²

additive landing:
  beta=gamma³ and beta.snd=3*A³ -> r*s*(r+s)=A³
  -> positive pairwise-coprime cube roots and one Fermat permutation

descent:
  successor product A < distinguished=3*A*B <= original product a*b*c
  -> strong induction
```

Thus FLT3 has a substantive analogue of the FLT7 once-ramified receiver,
but its normalized-power step is implemented element-wise and its unit
elimination uses a degree-two-specific cube-coordinate identity. A literal
shared implementation spine cannot be asserted just from these sources.
A common bookkeeping state must retain at least carrier identity, source
orientation, ramified correction, unit-power sector, exact coordinate
landing, and successor/measure certificate. Calling that state a completed
common mathematical theorem would require additional evidence from FLT5/7.

## Current p=3 generic API boundary

The historical statement that the p=3 generic carrier is separated from the
FLT3 carrier is stale for the present sources.
`EisensteinInt` is definitionally `TraceOneInt (-1)`;
`EisensteinLibBridge.traceOneInt_signedPrimeParameter_three_type` checks
`TraceOneInt (signedPrimeParameter 3)=TraceOneInt (-1)`.

There is still a coordinate convention to preserve. The exact bridge is:

```lean
lib_eisensteinCoord_eq_FLT3_coord (m n : ℤ) :
  DkMath.Lib.NumberTheory.eisensteinCoord m n =
    DkMath.FLT.Three.eisensteinCoord m (-n)
```

It is proved by `rfl`; its norm bridge is also definitional. The generic
`eisensteinCubeUnitPowerSectorSystem` packages the existing three sectors and
their completeness. It does not transfer the p=3 coordinate exclusion proof
to p=5/7 merely because the neutral sector interface exists.

## Source and compiled dependency verification

A recursive source import inventory from `DkMath.FLT.Three` contained 80
DkMath modules. Searches of that DkMath import closure found no occurrences
of `fermatLastTheoremThree`, `Mathlib.NumberTheory.FLT.Three`, or
`MathlibBridge.FLT34`. The production `Three` sources also contained no
`sorry`, `admit`, new `axiom`, or `unsafe` declarations in the audit scan.
This is source-level evidence; it does not establish that the umbrella
Mathlib artifact graph excludes the completed Mathlib FLT3 module.

After checkpoint 05, the focused command
`lake env lean docs/dev/FLT357-CrossInvariant-Ultra-261004-v0/checks/SourceDependencyAudit.lean`
passed with exit 0. It recursively traverses each reachable kernel
declaration's type and readable body, including opaque bodies and all
constructors of every reachable inductive (as in `Lean.Util.CollectAxioms`), using
`env.checked.get.find?` and `Expr.getUsedConstants`. For
`fermatThree_no_positive_solution` it visited 15,283 declarations and read
14,092 declaration bodies. Missing declarations and unreadable expected
bodies were both empty. The only axiom leaves were `propext`, `Quot.sound`,
and `Classical.choice`.

No dependency matched the explicit external completed-proof families in the
probe: Mathlib numeric FLT3/4 endpoints, their audited descent namespaces and
private-source names, the local MathlibBridge wrappers, or `sorryAx`.
Generic `FLT.Basic` definitions and conditional reductions were not
misclassified as completed proofs. The exact filters and all outputs are
saved in `logs/source-dependency.log`; the reusable probe also verifies the
FLT5 endpoint and the current FLT7 ideal/element receivers.

This verifies the compiled dependency closure of the named endpoint, rather
than merely the axiom set or the import graph. No production edit or full
Lake build was performed.

## Next audit action

Compare this completed coordinate-specific mechanism with the actual FLT5
closure and the current FLT7 corrected receiver. Decide whether the common
state above has enough actual producer theorems to justify Outcome A/B;
otherwise identify the first carrier/landing theorem at which Outcome C is
forced. Do not introduce a generic descent hypothesis equal to the desired
conclusion.
