# FLT7-014 implementation report

## Outcome

Outcome A.

```text
The nine first-residue local systems are not an obstruction by themselves.
Every actual non-seven local witness belongs to an explicitly soluble family.
```

This is a positive classification at the first residue layer. It does not
exclude stronger local or global obstructions and does not provide recursive
closure, descent, or FLT7.

## Files changed

- `DkMath/FLT/Seven/RoutingLocalSystems.lean`
- `DkMath/FLT/Seven/RoutingLocalSolubility.lean`
- `DkMath/FLT/Seven/LocalObstructionAudit.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenRoutingLocalSystems.lean`
- `DkMathTest/FLT/SevenLocalObstructionAudit.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-014.md`

## Normalized systems and certificates

`leftCubicNormalized`, `rightCubicNormalized`,
`leftCorrectionNormalized`, and `rightCorrectionNormalized` expose the four
stable integer polynomials. The theorems `leftCubic_scale`,
`rightCubic_scale`, `leftCorrection_scale`, and `rightCorrection_scale` prove
their exact homogenization identities. The two right-hand polynomials are
also related to the left-hand polynomials by the involution `t -> -t-1`.

The public Bezout certificates are:

```text
(60t-88) P(t) + (-6t^2+22t-19) L(t) = 7,
(60t+148) Q(t) + (-6t^2-34t-47) R(t) = 7.
```

After coercion to `ZMod q`, they prove
`leftCorrection_ne_zero_of_leftCubic_eq_zero` and
`rightCorrection_ne_zero_of_rightCubic_eq_zero`: at a corresponding cubic
root, the correction cannot vanish for a prime `q != 7`.

## Typed nine-cell surface

`AwayEndpointLocalEquation` and `AwayEndpointLocalNondegenerate` encode the
three rows `y`, `z`, and `y+z`. `AwayRootLocalEquation` and
`AwayRootLocalNondegenerate` encode the columns `v`, `P`, and `Q`.
`AwayFirstCoordinateLocalEquation` gives the exact FLT7-013 remainder in each
of the nine cells. `AwayRoutingLocalSolution` retains row and column provenance
while packaging endpoint, root, nonvanishing, and first-coordinate facts.

`AwayRoutingPrimeWitness.toLocalSolution` grounds this finite-field surface in
an actual FLT7-013 witness, using the original endpoint and root coordinates
modulo its prime.

## Explicit solubility

`nonempty_localSolution_sevenV` constructs a solution for every row and every
prime, including characteristic two, from a nonzero scale. For the two cubic
columns,

- `nonempty_localSolution_leftCubic_of_root`, and
- `nonempty_localSolution_rightCubic_of_root`

construct all three row solutions from a normalized cubic root when `q != 7`.
They use the prescribed signed correction scale `C`, with `v=C^2`, `u=tC^2`,
and endpoint magnitude `C^5`. Correction nonvanishing supplies every required
nonzero fact.

## Actual-witness classification and summit

`AwayNonSevenLocalSolubilitySource` records whether a witness lies in the
unconditional `sevenV` family or in a left/right cubic family together with
its extracted normalized root. For cubic witnesses, the root is obtained as
`u/v`; root nondegeneracy justifies division.

`localSolubilitySource_of_primeWitness` classifies every actual non-seven
routing witness into one of these explicit families.
`FirstResidueLocalAuditResult` preserves the ramified route and records the
classification in the away route. The checkpoint summit is
`firstResidueLocalAuditResult_of_pack` for every `CounterexamplePack`.

## Optional prime-residue refinement

The optional classification of primes admitting a cubic root by
`q = +/-1 (mod 7)` was not undertaken. It is unnecessary for Outcome A and
would require a separate finite-field/cyclotomic layer.

## Verification

Focused module and symbolic regression-test builds, the `DkMath.FLT.Seven`
facade, and the full `DkMath.FLT` target passed. Public axiom audits report only
Lean/Mathlib foundations (`propext`, `Classical.choice`, and `Quot.sound`). No
`sorry`, `admit`, custom axiom, or `native_decide` was introduced.

## Recommended FLT7-015 boundary

Move beyond first-residue solubility. The most direct next audit is an exact
`q`-adic/full-cell compatibility layer: combine `q^2` or higher congruences
with the exact valuation of a routing cell and its first-coordinate remainder,
then test simultaneous signed compatibility across all nine cells. Global
reconstruction should only follow if that stronger packet supplies the data;
the locally soluble first-residue systems should not be re-audited for a
contradiction they cannot provide.
