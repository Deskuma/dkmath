# FLT7TC-005R17 report — Real-cubic exact-power orbit and fixed unit-class frontier

## Result

Outcome B: the real-cubic orbit difference is green, the fixed unit class is
decided, and the next precise boundary is the current-route theta-adic
coprimality/descent bridge.

## Report questions

1. The provenance-independent `ZMod 49` theorem proves, for a unit `u`,
   `u` is a seventh power if and only if `u^6 = 1`.  Applying it to the R16
   endpoint shows that the seventh-power gate is equivalent to the existing
   sixth-root condition.  It is therefore locally exhausted, not a
   contradiction and not a reduction of the six endpoint unit classes.

2. For an R16 `DirectCyclotomicNormalizedRootPacket`, the packet
   `DirectRealCubicRootPacket` retains
   `rho = QuadraticAlgebra.norm gammaNorm` and proves
   `directChosenQuotientRealSource r = rho ^ 7`.

3. The same packet proves the exact signed identity
   `SevenRealCubicInt.norm rho = (r.summit.residualRoot : ℤ)`.
   The residual-root seven-unit fact then gives both
   `¬ eisensteinAxis ∣ rho` and nonzero theta residue.

4. The sources and roots at indices `0`, `1`, and `2` are defined by the
   concrete `SevenRealCubicInt.rotateEquiv`.  Their three exact seventh-power
   identities and cyclic closure by `rotateEquiv_three` are kernel checked.

5. The first source difference is factored exactly as
   `orbitUnit01 * (eisensteinAxis^5 * thetaSevenUnit * gapRoot^2)^7`.
   The rotation law for `thetaSevenUnit` is derived from
   `7 = eisensteinAxis^3 * thetaSevenUnit` in the division-free form
   `pairAxisUnit 1 ^ 3 * rotateEquiv thetaSevenUnit = thetaSevenUnit`.

6. `orbitUnit01` is the explicit source-independent element
   `(pairAxisUnit 1 - 1) * alphaAddOneInv * thetaSevenUnit^5`, and its
   `IsUnit` proof is included.

7. The exact fixed class is
   `projectiveLog (Additive.ofMul orbitUnit01Unit) = (0, 5)` in
   `ZMod 7 × ZMod 7`.

8. The class is nonzero, so
   `SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero` proves that
   no unit seventh root of `orbitUnit01Unit` exists.  No pure seventh-power
   difference and no integer FLT7 conclusion is claimed.

9. The clean machinery in `SevenRealCubicThetaCoordinates`,
   `SevenRealCubicThetaSeventhPower`, `SevenRealCubicCoprimeExtraction`, and
   `SevenRealCubicAxisDrop` was audited without instantiating a historical
   receiver.  None currently consumes the direct provenance of `rho1-rho0`:
   the missing theorem is a current-route theta-adic factorization together
   with coprimality of `rho1-rho0` and the homogeneous seventh quotient.
   Consequently no descent state or strict measure is constructed here.

## Validation scope

The production module, its import API, and its axiom audit are the decisive
artifacts.  The production source contains no `sorry`, `admit`, `unsafe`, or
project-level axiom declaration.
