# source-coupling-map-005

## Notation and provenance

For fixed `p : RamifiedSignedRootRoutingPacket`, write
`K = p.signedDepth.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket`,
`A = K.quadratic.innerRoot.fst`, `B = K.quadratic.innerRoot.snd`,
`M = |K.innerSndRoot|`, `V = K.quadratic.canonical.verticalGapRoot`,
`C = K.quadratic.compensationRoot`, `Q = p.signedDepth.quotientRoot`.
A prime is ℓ; a chart center is c (not Q).

Below are **existing proved Lean declarations inspected in the live source**, not new proofs supplied by this audit. The required six module families and their direct imports were inspected. Fresh focused validation in gate 005 covers only the standalone diagnostic and its imported cheap-filter dependencies; real-pair inventory is source inspection, not a fresh full-module build.

| Object | Full theorem identifier | Conclusion | Exact extra hypotheses | Attached object / branch | Constrains r=1? | Missing arrow |
| --- | --- | --- | --- | --- | --- | --- |
| M / carrier | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier_eq_seven_pow_four_mul_core_pow | carrier=7^4*M^7 | p only | p / no branch | No; divisor not chosen | carrier to endpoint realization |
| M | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourSeventhCore_pos; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourSeventhCore_not_seven_dvd | M>0 and 7∤M | p only | p | No | chosen r / center |
| carrier depth | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.padicValNat_internalDepthFourCarrier; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.padicValNat_outerDepthFiveCarrier | inner=4, outer=5 | p only | p | No | counterexample descent requires reconstruction |
| N,V,C | DkMath.FLT.Seven.RamifiedRealCubicNormPacket.exists_inner_complementary_seventh_root | ∃N>0: |sndCore(A,B)|=N^7, M*N=V*C, coprime M N, 7∤N | K: RamifiedRealCubicNormPacket | K = actual subpacket of p | No | selected r / endpoint constraint |
| prime support | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourAllocation_prime_support | ∃actual N: ledger plus ℓ∤N and ℓ∣V or ℓ∣C | p; r∈M.divisors; Nat.Prime ℓ; ℓ∣r | same p, no exact branch needed | No: prime cannot divide 1 | support ownership to endpoint/center |
| actual A,B | DkMath.FLT.Seven.RamifiedQuadraticInnerRootPacket.innerRoot_coordinates_isCoprime; DkMath.FLT.Seven.RamifiedQuadraticInnerRootPacket.inner_secondCoordinate_product_eq | IsCoprime A B; |B|*|sndCore(A,B)|=7^4*(V*C)^7 | actual quadratic packet | K.quadratic | No selected r | not a reconstructed endpoint pair |
| norm sources | DkMath.FLT.Seven.RamifiedRealCubicNormPacket.norm_leftSource_eq; DkMath.FLT.Seven.RamifiedRealCubicNormPacket.norm_rightSource_eq; DkMath.FLT.Seven.RamifiedRealCubicNormPacket.signedRootGap_seventhPower_eq | norms=L^7,R^7; R^7-L^7=7*A*B*(A+B) | K only | same A,B,K | No | signed L,R to natural chosen u |
| axis | DkMath.FLT.Seven.RamifiedRealCubicNormPacket.sourceDifference_eq_normalizedAxis_pow_six_mul_pow_seven | source difference=axis^6*normalizedWitness(innerSndRoot)^7 | K only | real cubic sources | No | ring-valued sixth power is not M/r=t^6 |
| real-pair core | DkMath.FLT.Seven.RamifiedSignedRootDepthPacket.norm_realPairCore; DkMath.FLT.Seven.RamifiedSignedRootDepthPacket.realPairCores_pairwiseCoprime | norm(core_i)=-Q; pairwise IsCoprime | signedDepth packet; i:Fin 3 | p.signedDepth | No | Q is quotientRoot, not M or s |
| row-two addresses | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.c21_eq_quotientRoot_innerFst_gcd; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.c22_eq_quotientRoot_innerFst_add_innerSnd_gcd | c21=gcd(|Q|,|A|); c22=gcd(|Q|,|A+B|) | p only | same p routing | No | these gcd loads are not chosen r/s |
| pure column | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.nonempty_col3SeventhPowerSplit; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.exists_row2_twoCellSeventhPowerFactor | c13,c23,c33 are seventh powers; |Q|=c21*c22*t^7 | p only | same p; t=root23 | No | no canonical equality between roots and chosen r |
| whole-core gate | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.quotientRoot_signedSeventhPower_iff_row2_cells; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.nonempty_realPairCoreAssociatedPowerSplit_of_row2_cells | Q signed seventh power iff c21,c22 seventh powers; then full cores have associated seventh roots | iff: p; extraction: witnesses for both row-two cells | same p | No | cell powers themselves not supplied |
| load allocation | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.realPairLoad21_product_associated; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.realPairLoad22_product_associated; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.realPairLoads_isCoprime | gcd-projection products associated to c21/c22; per-core loads coprime | p only; i for coprimality | same p real cubic order | No | integer chosen r / chart coordinate |
| stripped core | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.realPairCore_eq_combinedLoad_mul_strippedCore; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.exists_realPairStrippedCoreProduct_associated_pow; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.nonempty_realPairLoadedPowerSplit | exact load*residual; stripped product and per-core residuals associated to seventh powers | p only | same p; units retained | No | residual extraction ≠ full core extraction or oriented endpoint |
| generic centered chart | DkMath.FLT.Seven.nestedGNAllocation_iff_centered; DkMath.FLT.Seven.nestedRHSAllocation_iff_centered; DkMath.FLT.Seven.nestedAllocation_iff_centered | GN↔center above D; RHS↔ordered center below D; union↔∃center | M,r arbitrary; receiver chart guards retained | generic M, not packet ledger | No blanket exclusion | existence still exact residual equation |
| source equivalences | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_iff_sixth_power_sieved; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_iff_centered | obligation↔exact sieved receiver↔exact centered condition | p only (logical equivalence) | M=actual core; both branches | Does not exclude 1 | neither side inhabited by equivalence |
| perfect-sixth obstruction | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourAllocation_excluded_of_perfectSixth | no exact branch at r | p; r∈M.divisors; M/r=t^6; 9*r^2≤t | same p but additional scalar hypotheses | Only conditional at 1 | literal power and size not established |
| global conditional obstruction | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstruction_excluded_of_perfectSixth_family | ¬reconstruction | p and hfamily for ALL eligible divisors giving literal sixth power + size | source-indexed conditional | Only if hfamily proved | hfamily is an unsupplied obligation |
| phase / root obstruction | DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.no_fullCoordinate_decoder_on_orientedResidualIdeal; DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourReconstructedRoute_root_ne_innerRoot | ideal + seventh power cannot decode all generator coordinates; new away root differs from inner root | decoder: p; route: p, supplied route and carrier equality | same p oriented degree-six ideal / actual route | No | norm/ideal equality cannot select natural chart |

## Import ownership

- NestedReconstruction imports SevenAdicNestedPowerSplit, DepthFourReconstructionAudit, PrimeTraceOneReconstructionRamifiedResolution.
- SixthPowerAllocationSieve imports AllocationResidueSieve; complementary-root theorem is owned by AllocationThreshold (transitively imported).
- CenteredPolynomial imports SixthPowerAllocationSieve; CenteredGnomonGap imports CenteredPolynomial.
- RealPairLoadAllocation imports RealPairCoprimalityNormGate; the latter imports RealPairCarrier, which imports RelativeRealIndex.
- The real-pair load modules contain no `CenteredNestedAllocationCandidate`, `NestedGNAllocationCondition`, `NestedRHSAllocationCondition` or `internalDepthFourSeventhCore` references in the inspected source. This text observation supports the boundary; it is not a global theorem that no connection can exist.

## Direction tracing

Source packet → actual inner coordinates / norm roots / routing cells / load extraction is already present. Source packet plus a supplied divisor → prime-support ownership is present. No chosen reconstructed endpoint is supplied in either arrow.

Exact receiver → centered c uses c=D+2*u in GN and c=D-u-u in the ordered RHS branch. Conversely, centered chart guards recover u and the exact residual via polynomial identities. Reconstruction ↔ centered condition uses these equivalences and preserves existence; it does not discharge it.

The scalar perfect-sixth route needs **both** `M/r=t^6` and `9*r^2≤t`. Neither the congruence sixth-power sieve nor the real-pair associated seventh-power residual gives these statements.

## First missing obligation for the divisor-one perfect-sixth route

The following is an **unproved candidate target, whose truth for actual packets is not established**. It is not an added axiom, API or hypothesis. It isolates the inputs needed to use the already-proved gap obstruction at r=1:

```lean
open DkMath.FLT.Seven
open DkMath.FLT.Seven.RamifiedSignedRootRoutingPacket.QuotientPrimeSupport

theorem source_divisorOne_center_requires_perfectSixth
    (p : RamifiedSignedRootRoutingPacket) {c : ℕ}
    (hc : CenteredNestedAllocationCandidate
      (internalDepthFourSeventhCore p) 1 c) :
    ∃ t : ℕ, internalDepthFourSeventhCore p = t ^ 6 ∧ 9 ≤ t
```

Proving this would already exclude divisor-one exact charts for actual packets by the existing obstruction. It is therefore a substantive unresolved theorem, not a trivial transport. The naked ledger does not establish even its literal-power conclusion. Its failure in a generic arithmetic model does **not** refute the source-packet version, since that model supplies neither p nor hc.

There is currently no justified equality identifying chosen u / c with A, B, L, R or a real-pair residual root. Writing such an equality without a phase/orientation/endpoint proof would manufacture the missing bridge.
