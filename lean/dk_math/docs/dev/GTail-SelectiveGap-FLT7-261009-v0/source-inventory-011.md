# Source inventory 011 — finite-field orders on the tail branch

Date: 2026-10-10 (JST). Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`, initial clean worktree at `2ca56f9cd5cf424c4f1dd35104d56d9c47a61294`. Reviewed review-010/report-010/source-inventory-010. Step 011 only.

## Scalar inputs and exceptions

- `GTailNat.GTail_not_dvd_of_head_unit_of_prime_dvd_x`: prime, r<d, head-unit and prime dividing gap exclude a divisor of the normalized tail. Step 010's `not_prime_dvd_gtail_seven_of_gap` specializes this to q≠7, q∣g and q∤c. Its new q-budget and square allocation require exact product/nonzero factors and separate exclusivity; none alone supplies a seventh root on the g side.
- `GTail.add_pow_eq_mul_GTail_one_add_gap`: all CommSemiring R, all d,x,u give `(x+u)^d=x*GTail d 1 x u+u^d`. Cast the **natural** tail value to ZMod, then use q∣T. The original binomial index k measures powers of g; r=1 extracts one g. No GTail value is silently reinterpreted across rings.
- `GTailCyclotomic.GTail_one_eq_GTailCyclotomicShell`: equality to the homogeneous geometric shell over any CommSemiring, with no nonzero premise. `GTail_one_eq_cyclotomicHomEval_of_prime` gives the prime homogeneous cyclotomic connection. These endpoints were inspected, not imported: the additive scalar identity suffices and avoids polynomial machinery.
- `GTailPrimeAllocationAudit.not_prime_dvd_coordinate_product_of_quadratic`: prime q, primitive a,b and q∣Q exclude q from ab(a+b). `not_prime_dvd_endpoint_of_quadratic` additionally uses exact Fermat equation and gives q∤c, with no positivity/focus/q≠7 premise.
- `prime_focused_support_exclusive`: primitive exact equation, sum relation, prime q≠7 and q∣Q give exclusive support on g or T. Thus q∣T discharges q∤g. `prime_square_focused_allocation` additionally needs positive a,b and supplies the exclusive square disjunction used by optional routing.
- `GTailBridge.gtail_seven_shell` has only the sum relation; `gtail_seven_eq_of_fermat7Equation` requires the exact equation. Neutral order proofs use neither.

Characteristic three is a genuine quadratic exception: a=b=1 has Q=3, unit coordinates and trivial ratio 1; 3∤3-1. Characteristic seven cannot contain a nontrivial seventh root; the tail-order theorem retains explicit q≠7 to match the Step 010 branch, although its root argument itself needs no use of that premise. The gap-unit premise is essential: q=7,g=7,c=2 has q∣T but g zero modulo q. The order-seven conclusion also rules out q=3 by 7∤2.

## Exact finite-field/group APIs

- `Mathlib/Algebra/Field/ZMod.lean`: Field (ZMod q) under `[Fact q.Prime]`. Instantiate this before division; `ZMod.natCast_eq_zero_iff n q` transfers divisibility to zero residues. c and b denominators are nonzero from explicit unit hypotheses.
- `Units.mk0 r hr0` packages a nonzero ratio as a unit. `Units.ext` and coercion congruence transfer pow and nonidentity equations to that unit.
- `Mathlib/GroupTheory/OrderOfElement.lean`, `orderOf_eq_prime`: `[Fact p.Prime]`, u^p=1 and u≠1 give orderOf u=p. It is not inferred merely from a root equation.
- `Mathlib/FieldTheory/Finite/Basic.lean`, `ZMod.card_units q`: `[Fact q.Prime]` gives Fintype.card (ZMod q)ˣ=q-1. `ZMod.orderOf_units_dvd_card_sub_one u` gives orderOf u∣q-1 using the finite unit group. This is the actual existing API used rather than an invented order/cardinality name. Its finite-group exponent proof embodies Lagrange; no arbitrary divisor product inference is used.
- `Nat.Coprime.mul_dvd_of_dvd_of_dvd`: coprime 3,7 combine separate divisibilities into 21∣q-1.

The seventh ratio r=(c+g)/c has r^7=1 from the natural additive shell and tail divisibility, hence r≠0; r≠1 follows from q∤g. The third ratio s=a/b satisfies s²+s+1=0, s³=1 and s≠1; at s=1 the quadratic becomes 3=0, excluded by q≠3. Unit/nonzero a,b make s a genuine unit. No exact Fermat premise enters either construction.

## Bounded existing DkMath overlap

`Lib.NumberTheory.ClassGroupTorsionBridge.classGroupPTorsionFreeAt_of_coprime_card` uses `orderOf_dvd_of_pow_eq_one` and `orderOf_dvd_card` for class-group torsion; that carrier is unrelated and is not imported. Existing `FLT/Seven/SevenRamifiedFusionCyclotomicPrimeAddress.prime_dvd_quotientRoot_modSeven_eq_one` uses a typed RamifiedSignedRootDepthPacket and divisibility of its quotientRoot for a seventh-order prime restriction. Its root-depth/Norm/unit owners are not imported or transported to the scalar Q/T coordinates. No independent obstruction novelty is claimed.

## Narrow ownership

Neutral `Lib.NumberTheory.GTailSevenPrimeOrder` imports GTailNat, Mathlib.FieldTheory.Finite.Basic, FieldSimp and Ring only. Four public theorems: order-seven divisibility, exclusion of q=3 on that tail branch, order-three divisibility and their neutral intersection; one private unit-order helper. Conditional owner imports only GTailPrimeAllocationAudit and the neutral module. Separate direct-import tests preserve the neutral/exact distinction. No facade promotion or whole-suite build.

## Final graph

Header-only closure audit: neutral owner/test 1888/1889 names, 3/4 local modules; conditional owner/test 8797/8798 names, 17/18 local modules. The union of 19 local modules is acyclic; neutral has zero FLT modules. No typed cyclotomic root-depth/Norm/unit owner or closure facade is reached. Complete lists are local `.lake/build/gtail-step011/imports.json`; counts are reachability, not build jobs or public axiom evidence.
