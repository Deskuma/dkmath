# Source inventory 012 — typed quadratic norm readout

Date: 2026-10-10 (JST). Initial branch `feature/GTail-SelectiveGap-FLT7-261009-v0`, clean worktree at `5f1266bda9ff8d6e9d686b1037f3ec4ecb7f7abd`. Read review-011 and reports 010–011. Step 012 only: reuse the implemented quadratic ring and its norm.

## Exact existing carrier and signs

`DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt s` is the integral pair structure with fst/snd in ℤ, relation τ²=τ+s and the implemented ring operations. `norm x : ℤ` is fst²+fst*snd-s*snd². `conj x=⟨fst+snd,-snd⟩`; `traceOne_mul_conj` gives x*conj x=ofInt s (norm x). `traceOne_norm_mul (x y : TraceOneInt s)` gives norm(x*y)=norm x*norm y. `traceOneNorm_neg_one (a b : ℤ)` gives norm(⟨a,b⟩:TraceOneInt(-1))=a²+ab+b².

`Lib.NumberTheory.eisensteinCoord (m n : ℤ)` already equals ⟨m,-n⟩ in TraceOneInt(-1). `norm_eisensteinCoord` reads m²-mn+n²; `norm_eisensteinCoord_mul_sq b c m n` reads norm(beta*gamma²)=norm beta*(norm gamma)². No second ring or invented norm is needed. The new helper specializes this existing coordinate to m=(a:ℤ), n=-(b:ℤ), giving literal ⟨a,b⟩ and the plus-sign Q.

Existing `EisensteinCoordinates` already contains norm multiplicativity, explicit coordinate multiplication/square and conditional element-factor consequences. `traceOneNorm_neg_one` already has the desired integer polynomial; the new natural-input wrapper is a specialization with coherent casts, not a duplicate foundational norm. The targeted search found no existing selectedBody/focused-product endpoint with this norm-square target. Existing `EisensteinLatticeLanding.eisenstein_norm_divisibility_not_sufficient` separately refutes a norm-value-divisibility converse to element divisibility; inspected only, not imported.

## Scalar seventh interior and exact equation

- `GTailSeven.selectedBody_seven_interior`: arbitrary CommSemiring R, x,u give selectedBody 7 (Ico 1 7) x u=7*x*u*(x+u)*(x²+xu+u²)². New theorem uses R=ℤ explicitly, natural input casts, and the existing typed norm multiplicativity.
- `GTailSeven.add_pow_seven_eq_gap_add_interior`: the selected interior plus original endpoint Gap reconstructs (x+u)⁷. No full restatement is added here.
- `GTailBridge.gtail_seven_shell`: arbitrary CommSemiring and a+b=c+g give the non-Fermat shell. `gtail_seven_eq_of_fermat7Equation`: natural exact equation and same sum relation give g*(GTail 7 1 g c)=7ab(a+b)*Q². The new owner casts this exact **natural** equation to integers, leaving the natural GTail term visibly cast.
- Step 010 `GTailPrimeAllocationAudit` supplies local q-unit, budget and exclusive q² allocation with prime, primitive pair, exact equation and positivity where needed. Step 011 `GTailPrimeOrderAudit` supplies tail-guarded order21/routing. These owners were inspected; no q-valuation/order proof is duplicated and neither is imported by the new owner. The scalar norm-divisor iff can serve as a future equivalent input adapter.

## Existing other carriers: source inspection only

`FLT/Seven/QuadraticBridge.cyclotomicSevenToTraceOne z y` belongs to TraceOneInt(-2) and uses explicit cubic coordinates; `cyclotomicSeven_eq_traceOneNorm_negTwo` reads its seventh cyclotomic kernel as that norm. Our α is in TraceOneInt(-1) with linear coordinates; the parameter, discriminant and norm target differ. No map from this α to that other quadratic order is supplied.

`SevenRamifiedFusionCyclotomicDegreeSixCarrier.SevenCyclotomicDegreeSixInt.Ring` is QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1), a quadratic extension over an existing real cubic carrier. Sharing a scalar norm-shaped expression does not identify these rings, signed-root packets, prime ideals or unit-power classes. These heavy typed carriers remain unimported/unchanged.

## New ownership and cast contract

Neutral owner imports only EisensteinCoordinates and GTailSeven. One minimal helper definition, five public theorems: literal coordinate, norm value, multiplicative norm-square, natural/integer norm-divisor iff and integer selected Body norm-square. Norm-square proof directly uses pow_two and traceOne_norm_mul, not a separate quartic calculation.

Conditional owner imports only GTailBridge and the neutral readout. One public theorem with just Fermat7Equation/coordinate relation; no positivity or primitive/unit hypothesis is required by this cast equality. It does not assert an element factorization from a scalar norm equality. Both tests use direct owners, no facade promotion.

`Int.ofNat_dvd` provides the exact cast-divisibility equivalence, valid for arbitrary q including zero; no primality assumption is needed. The iff concerns the integer norm value, not α-divisibility, a ring prime or a chosen ideal above q. Norm is demonstrably noninjective via the explicit different norm-one pair. No nonsquare-unit converse theorem is asserted.

## Final dependency graph audit

Comment-stripped import-header traversal: neutral/owner/neutral-test/owner-test closures contain 1003/8793/1004/8794 source names, respectively, including external terminals. Local DkMath/DkMathTest counts: 10/13/11/14. Local union: 15 vertices, no cycle. Neutral closure contains no FLT module. These are source graph counts, not build jobs or a closure-wide axiom audit. Evidence: `.lake/build/gtail-step012/imports.json`; exact focused builds and new axiom lists are in report-012.
