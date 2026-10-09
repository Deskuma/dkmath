# Source inventory 010 — q-local square allocation

Instruction date: 2026-10-09. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`; initial clean worktree at `7c7af1d5f6a20dd70f25e6906ec7098ed773695d`. Prerequisites review-009/report-009 and historical constraint-ledger-006 inspected. Step 010 only.

## Carrier and exact input contracts

All new coordinates/factors are naturals. Q=a²+ab+b² and T=GTail 7 1 g c. The original binomial-row index k is the exponent of g; r=1 extracts one g from all terms with k≥1, leaving the normalized tail after the zeroth c⁷ term. This is not a new cyclotomic carrier. Neither Q nor T is redefined as a Norm object.

- `GTailBridge.gtail_seven_eq_of_fermat7Equation`: Fermat7Equation a b c and a+b=c+g give `g*T=7*a*b*(a+b)*Q²`. Its shell requires only the coordinate relation; its exact product adapter requires the exact Fermat equation.
- `GTailConstraintAudit.fermat7_focused_bounds`: positive a,b and exact equation give max a b<c<a+b. Together with the coordinate relation this supplies g≠0. T≠0 follows from positivity of the exact RHS, not a silently assumed residual unit.
- `GTailSevenArithmetic.coprime_product_seven_quadratic`: Coprime a b gives Coprime (a*b*(a+b)) Q. The separate left/right/sum coprimality endpoints have the same sole primitive-pair premise. This excludes q from ordinary factors when prime q divides Q.
- `GTailNat.GTail_not_dvd_of_head_unit_of_prime_dvd_x`: prime p, r<d, `¬p∣choose d r*u^(d-r)` and p∣x imply p∤GTail d r x u. The new seven-row specialization uses choose 7 1=7, q≠7 and q∤c to prove head-unit, without expanding Pascal coefficients.
- `GTailCongruence.GN_modEq_choose_mul_pow_of_dvd_x` gives the corresponding constant-head congruence under modulus dividing x. `prime_dvd_GN_iff_dvd_gap hp` concerns **degree p and modulus p**; it cannot be used as if q were the degree of GTail 7 1.
- `GTailPadic.padicValNat_GTail_eq_zero_of_head_unit_of_prime_dvd_x` packages valuation zero with the same head-unit inputs. `padicValNat_GN_prime_eq_one_of_dvd_gap` concerns degree/modulus p, Coprime g u, p≥3 and p∣g; it is not the q≠7 branch. No global Coprime g c premise is transported from a,b.
- `Lib.NumberTheory.PadicValNat.Vp_ge_one_iff` and `padicValNat_le_iff_dvd`: prime and nonzero factor are required for converting valuation bounds into divisibility. Mathlib mul needs Fact q.Prime and both factors nonzero; pow needs the prime Fact instance, no base-nonzero premise. All product factors are explicitly nonzero here.
- Step 008 `GTailSevenValuation` and `GTailValuationAudit` concern the distinguished prime seven and the residual exact-one layer. Step 009 `SevenUnitAllocation`/`GTailSevenUnitAudit` cancel that layer to get v7(g)=2*v7(Q) under seven-units. For q≠7 the coefficient 7 has valuation zero instead; the q-budget sums both left factor valuations. The new neutral budget does not assume vq(T)=1.

## Minimal new graph and premise differences

Neutral owner imports only GTailNat and Lib.NumberTheory.PadicValNat. Conditional owner imports only GTailConstraintAudit and the new neutral owner. Separate tests import their direct owner. No Seven facade, closure owner, order-21 or Norm/unit-class module is added.

Public neutral endpoints: head exclusion; abstract exact-product budget; square allocation from budget **plus** explicit exclusion. Public conditional endpoints: ordinary-factor q-unit; endpoint q-unit; exclusive support; budget; square allocation. Endpoint-unit derivation is stronger in premises than the requested packet form: it needs prime q, primitive a,b, exact equation and q∣Q, **no positivity, q≠7 or sum relation**. Support exclusivity additionally needs q≠7 and the sum relation, but no positivity. Only the valuation budget/square result need positive a,b to supply nonzero factors. No hidden q∤c assumption is added.

## Bounded overlap inspection, not imported

| Source and named endpoint | Existing contract | Difference |
| --- | --- | --- |
| `CounterexampleRouting.gcd_gap_GN_seven_dvd_seven` | Coprime g y implies gcd(g,GN 7 g y)∣7 | Strong global coprimality premise; the new q exclusion derives only a local endpoint unit for q∣Q. |
| `CounterexampleRouting.branchAway_coprime_gap_GN_seven` | primitive CounterexamplePack and ¬7∣z-y give Coprime (z-y) (GN 7 (z-y) y) | Difference gap z-y, not sum focus a+b-c. No coordinate transfer is proved here. |
| `PrimitiveCyclotomicDepth.not_fortyNine_dvd_GN_seven_sub` | b≤a, Coprime a b and 7∣a-b exclude 49 in GN 7 (a-b) b | Distinguished-seven residual layer; not a q-square budget in the focused product. |
| `SevenBaseTerminalPrimeSupport.mem_awaySevenBaseTerminalPrimeSupport_iff` | membership equals prime q and q∣typed cubic-root load | Support of a typed terminal load, not scalar Q. |
| Same source, `AwaySevenBaseTerminalRoutingPacket.primeSupport_ne_seven` | typed terminal packet and load-support membership imply q≠7 | q≠7 is explicit in this checkpoint; no terminal packet is fabricated from q∣Q. |
| `SevenRamifiedFusionCyclotomicPrimeAddress.prime_dvd_quotientRoot_modSeven_eq_one` | RamifiedSignedRootDepthPacket, prime q dividing its integer quotientRoot imply q%7=1 | Existing typed cyclotomic prime restriction. Its hypotheses are not supplied by q∣Q or q∣T alone. No order-21 inference is pursued. |
| `PrimeTraceOneDirectRealCubicSquarePrimeSupport.directOrbitSquareRefinement_squareRoots_norm_product` | typed refinement over primitive ramified provenance gives natAbs(norm root1)*natAbs(norm root2)=gapSplit.a³ | Ring roots, normalization and cube/norm carrier differ from scalar focused square allocation. |

This is not an exhaustive FLT7 novelty audit. The new coordinate-specific allocation is classified Outcome B: checked necessary conditions, not a separately established independent obstruction.

The historical ledger remains unchanged; report-010 records closure of the deferred q-budget and the precisely justified exclusive allocation under its full hypotheses. All broader reconstruction, order-21 and Norm/unit class targets remain outside scope.

## Final import audit

Neutral owner/test closures: 1078/1079 source names with 4/5 local modules. Conditional owner/test: 8795/8796 with 15/16 local modules. The 17-local-module union is acyclic; neutral contains no FLT modules. Neither new production owner reaches the Seven facade, closure, typed cyclotomic prime-address or unit carrier modules. Complete lists are in `.lake/build/gtail-step010/imports.json`; this is source reachability, not an axiom audit of unrelated external declarations.
