# DRC004–007 complete-support bridge audit

All current endpoints below were checked against production source on 2026-10-04. Regression proofs are preserved in `DkMathTest/FLT/CompleteSupportDRCBridgeAudit.lean`. Scratch `/tmp/FLT7NeutralPowerAudit.lean` verified the neutral finite power-extraction wrapper via `lake env lean` from nested Lake cwd. Their printed dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Current carrier

- `DkMath.FLT.Seven.SevenRealCubic.currentLinearCarrier c` is `ofReal (SevenRealCubicInt.rotateEquiv p.rho) - zeta^(phaseInverseExponent c.phase) * ofReal p.rho`. Carrier type is `SevenCyclotomicDegreeSixInt.Ring = QuadraticAlgebra SevenRealCubicInt (-1) (alpha - 1)`.
- `CurrentCommonPrimeResiduePacket.q_ne_seven` explicitly excludes rational 7; `q_dvd_c` restricts the packet to common-factor rational support.
- Even neutral `CurrentMuSevenResidueAddress` cannot exist at 7: scratch `current_address_excludes_ramified_prime` applies `Units.val` to ratio^7=1, then Frobenius in ZMod7 yields ratio=1, contradicting retained ratio_ne_one.

## DRC004: genuine cyclic power gluing

- File `DkMath/NumberTheory/PrimeCyclicGlue.lean`, namespace `DkMath.NumberTheory`.
- `aks_prime_cyclic_is_pow_of_components (p) [Fact p.Prime] (f : ℤ[X]) (a : ℤ) (b : AdjoinRoot (Polynomial.cyclotomic p ℤ)) (ha : f.eval 1 = a^p) (hb : AdjoinRoot.mk (Polynomial.cyclotomic p ℤ) f = b^p)` concludes `∃ q : AKSCyclicQuotient ℤ p, aksQuotientMap ℤ p f = q^p`.
- Gluing is from two supplied genuine element powers. It does not discover support exponent divisibility in a cyclotomic component and cannot remove an arbitrary unit.
- Current ring has checked integer-ring equivalence in `SevenRamifiedFusionCyclotomicDegreeSixPID`; an AdjoinRoot identification could be built, but it does not provide the absent genuine seventh-power cyclotomic component or augmentation power. Thus representation mismatch is repairable, mathematical hypothesis is absent.

## DRC005: roots of unity / finite Hensel

- File `DkMath/NumberTheory/PrimeShellHensel.lean`, namespace `DkMath.NumberTheory`.
- `primeShell_root_iff {K} [Field K] (p) (g u : K) (hp : (p:K)≠0) (hu : u≠0)` identifies GTail p 1 g u = 0 with nontrivial p-th root `(g+u)/u`.
- `primeShell_dvd_iff_rootOfUnity` requires prime p, `[Fact q.Prime]`, q≠p, and q∤u. It concerns integral scalar GN, whereas current A has real-cubic coefficients and an ideal-power valuation upstairs.
- `exists_primeShell_exact_depth` supplies every positive exact depth k from any simple nonramified seed. It never constrains k to multiples of p.
- Formal shell obstruction: p=7,q=29,u=1,g=15 has GN=17895697, divisible by 29 but not by 29². Its normalized ratio is 16, a nontrivial seventh root modulo29; derivative is nonzero. The same seed yields every positive exact depth by the generic API. This is a model of the isolated shell/residue/Hensel facts, not a Fermat counterexample or full current root packet.

## DRC006: residue factor type

- File `DkMath/Lib/NumberTheory/QuadraticResidueType.lean`; predicates Split/Inert/Ramified classify roots of t²=a+b*t over a field. Odd-characteristic discriminant equivalences and `inert_iff_isField` are available.
- Current base reduction parameters are a=-1, b=evalReal alpha−1, not TraceOne's fixed b=1. The neutral API can specialize those current parameters.
- A supplied current address yields roots ratio and ratio⁻¹. These are distinct because ratio has order7. Current checked fibre equality `CurrentCommonPrimeCyclotomicPacket.residueFiberIdeal_eq_currentConjugateProduct` already supplies the required stronger ideal split for selected rows.
- Classification alone does not show arbitrary support contraction has residue degree1, does not produce a current address, and gives no ideal valuation divisibility. Characteristic2 requires separate root arguments; a field-size or additive-carrier argument is insufficient.

## DRC007: quadratic Gauss / QR half-product

- File `DkMath/NumberTheory/CyclotomicQRProvenanceLift.lean`, namespace of same name; source `TraceOneInt (signedPrimeParameter p)` and rational quadratic companion. For p=7, signed parameter=-2, the quadratic field is Gauss sqrt(-7).
- `coord_image_eq_qr`, `conj_coord_image_eq_qnr` identify integral packet coordinates with three-factor QR/QNR products at p=7. Retained provenance (map_RZ, gauss_difference, half_relation) makes these actual element equations.
- `coord_relative_norm` and `subfield_coord_relative_norm` are N_{E/ℚ} for quadratic E. Current conjugate norm pair is A*starA=ofReal(selectedRealPairCarrier c), lying in real-cubic K. It is a different norm stage N_{L/K}, and neither equality of scalar norms nor equal field degree identifies these elements.
- `integerEmbedding`, `map_coordinate_ideal`, `qr_qnr_ideal_product`, `qrInteger_mem_iff` move known QR coordinates and their principal ideals into an ambient cyclotomic integer ring. They do not classify arbitrary support ideals and do not equate a three-factor product with current A.
- `qrInteger_not_mem_power` takes conjugate-power transport, full ideal extension factorization, contraction, and scalar cutoff as hypotheses. These hypotheses remain unsupplied for arbitrary current support.
- Existing current ring integer-ring equivalence can address ambient representation, but the absent equality between current linear A and a QR half-product persists. N_{L/E}A would involve real Galois-conjugated rho coefficients; it is not the QR product evaluated at fixed integer z,y.

## Galois and conjugation

- `CyclotomicQRGaloisAction.map_rootFactorPoly` permutes roots; square exponents preserve QR, nonsquares swap QR/QNR. `CyclotomicQRGaloisRealization.exists_cyclotomicAut_pow` realizes every nonzero exponent under cyclotomic irreducibility, and `map_Rpoly_of_cyclotomicAut`, `map_Dpoly_of_cyclotomicAut` give invariant sum / signed difference.
- Current explicit ring rotation is independently defined in `SevenRamifiedFusionGlobalOrientedPrimeFactorization`: `SevenCyclotomicDegreeSixInt.rotateEquiv` extends real rotation, sends zeta to zeta², has order3, commutes with star.
- The generic QR action fixes polynomial variables. Applying current rotation to evaluated A moves BOTH rho coefficients and zeta, producing the next real orbit edge, not the same fixed A. Invariance of a QR polynomial cannot be used as invariance of current A.
- Historical cyclicKernel/oriented factorization statements in the same global module are tied to `RamifiedSignedRootRoutingPacket` and its own linear carrier; they cannot be transplanted to current A without an explicit element-level bridge.

## Neutral ownership and normalized route

- `DkMath.Lib.NumberTheory.not_mem_primePower_succ_of_conjugate_norm_cutoff` takes hstarMem, hpair, hmapPow, hcontract, hBetaNot explicitly and needs no primeness assumptions. `CurrentCarrierCutoff` has already discharged them for the selected current row. This neutral theorem alone does not generate any of those data for arbitrary support.
- A promising alternative is strip cyclotomic λ=1−zeta from all six current linear factors, prove their normalized principal ideals pairwise coprime, and prove full normalized product = (extended S ideal)^14. Then every normalized ideal is a 14th power and hence seventh power.
- Mathlib already has `exists_eq_pow_of_mul_eq_pow [GCDMonoid α] [Subsingleton αˣ] (hab : IsUnit(gcd a b)) (h:a*b=c^n):∃d,a=d^n`. Dedekind ideals supply these instances; `Ideal.isCoprime_iff_gcd`, `IsCoprime.prod_right`, and `Finset.mul_prod_erase` apply.
- Scratch `coprime_finite_ideal_factor_of_power` verified this finite extraction wrapper. Missing mathematical data are the actual λ stripping, normalized pairwise coprimality, and complete product identity. No complete rational-address classification is necessary after those are supplied.

## Additional current datum for the normalized route

- `PrimeTraceOneDirectRealCubicOrbitSplit.directOrbit_roots_isCoprime p` proves `IsCoprime p.rho (SevenRealCubicInt.rotateEquiv p.rho)` from the current source packet. Its image under `ofReal` remains coprime. A prime containing two distinct linear factors therefore contains their root difference.
- Mathlib `RingTheory/RootsOfUnity/CyclotomicUnits.lean` provides `IsPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime`: for distinct p-th roots, their difference is associated to zeta−1. `geom_sum_isUnit` gives the corresponding geometric-sum unit for any nonzero exponent modulo p.
- These facts constrain common prime support to the cyclotomic ramified direction. They still require an actual division by λ and proof that the normalized factors have no λ support before full pairwise coprimality is obtained.

## Validation

- Command from `lean/dk_math`: `lake build DkMathTest.FLT.CompleteSupportDRCBridgeAudit`.
- Result: exit 0, 9186 jobs. All six named regression theorems print only `propext`, `Classical.choice`, and `Quot.sound`.
- Durable build log: `docs/dev/FLT7-CompleteSupport-Ultra-261004-v0/logs/drc-bridge-focused.log`.
- New test source and this audit document passed individual `git diff --no-index --check /dev/null <path>` checks.
- These regressions establish the isolated shell-depth obstruction and address exclusion. They neither assert complete-support divisibility for current A nor construct a current FLT7 counterexample model.
