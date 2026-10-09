# Review 011 — finite-field order intersection at a focused GTail prime

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 011 COMPLETE / Outcome B**

## Reviewed evidence

- `DkMath/Lib/NumberTheory/GTailSevenPrimeOrder.lean` (118 lines).
- `DkMath/FLT/Seven/GTailPrimeOrderAudit.lean` (48 lines).
- `DkMathTest/NumberTheory/GTailSevenPrimeOrder.lean` (62 lines).
- `DkMathTest/FLT/Seven/GTailPrimeOrderAudit.lean` (40 lines).
- `report-011.md`, `source-inventory-011.md` and previously checked Step 010 contracts.

**Review is static GitHub proof-route, declaration and test inspection.** Codex's successful focused builds, Step 010 regressions, and six standard-axiom lists are reported in `report-011.md`; they were **not independently rerun** here.

## Findings

1. The neutral seventh-order result casts the **natural** value `GTail 7 1 g c` into `ZMod q`, avoiding an implicit carrier reinterpretation. The cancellation-free power shell and `q ∣ T` imply `((c+g)/c)^7=1`. Explicit `q∤c`, `q∤g` yield a genuine nonzero, nonidentity ratio. The pre-existing unit-order theorem then gives `7∣q-1`. The q≠7 parameter is retained for the intended branch but is not consumed by the neutral order proof.
2. The neutral third-order result uses `q∣a²+ab+b²`, nonzero a,b modulo q and q≠3 to show `s=a/b` obeys `s²+s+1=0`, `s³=1`, and `s≠1`. The q=3 exception is mathematically essential.
3. On the **Tail side only**, both nontrivial orders apply. Seventh order excludes q=3, and coprimality of 3 and 7 gives `21∣q-1`. No assumption that arbitrary q|Q automatically has order seven is used.
4. The conditional `twentyOne_dvd_prime_sub_one_of_focused_tail` obtains q-unit premises from Step 010's primitive quadratic coprimality, derived endpoint unit and exclusive support. It does not hide an extra `q∤g` hypothesis.
5. The routing theorem `prime_square_dvd_gap_of_not_twentyOne` uses the contrapositive of the guarded Tail theorem and rejects the Tail-square alternative of Step 010's exact exclusive allocation. It correctly **retains positivity** to justify the valuation/nonzero inputs of that allocation.
6. The satisfiable neutral tuple q=43,(a,b,c,g)=(5,8,9,4) verifies both prime-order constraints, scalar coordinate balance, prime-divisibility and seventh-power congruence, but *not* an exact Fermat equation. The q=13 gap-side calibration demonstrates that `21∣q-1` is false as an unguarded inference for all q|Q. Checks at q=3 and q=7 guard the exceptional mechanisms.
7. Four neutral and two conditional public endpoints were checked with the standard axiom set `[propext, Classical.choice, Quot.sound]` per Codex's recorded outputs. No new sorry, axiom, unsafe code, FLT impossibility appeal, Norm/ideal/unit claim, or cyclic neutral→FLT import was introduced.

## Distinguish arithmetic novelty from representation

The new result is a sound **branch-sensitive necessary condition**, but not an independent contradiction, cyclotomic-class statement, or descent mechanism. A previously typed `RamifiedSignedRootDepthPacket` prime-order theorem has different hypotheses and a different carrier; no coordinate map between that packet and this scalar Q/T address is established.

The existing neutral library already provides `DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)`, its multiplicative `norm`, and `DkMath.Lib.NumberTheory.eisensteinCoord`/`norm_eisensteinCoord`. In particular, the quadratic `Q=a²+ab+b²` is the integer norm of `eisensteinCoord (a:ℤ) (-(b:ℤ))`. This is a natural, narrowly scoped next connection; do not invent a second quadratic ring or read a principal ideal/unit-power statement into the scalar norm equality.

## Next step recommendation

Authorize Step 012 as a **typed Eisenstein norm readout**, with the concrete pipeline

```text
Q(a,b) = a²+ab+b²
        = norm(eisensteinCoord (a:ℤ) (-(b:ℤ)))
Q(a,b)² = norm((eisensteinCoord (a:ℤ) (-(b:ℤ)))²)
selected degree-seven interior Body = 7ab(a+b)*norm(α²)
exact conditional focused product = 7ab(a+b)*norm(α²)
```

All integer casts, domains, monomial coefficients and proof dependencies must be checked, with an independent numeric calibration and a noninjective-norm example showing the strict **one-way** nature of norm reading. Do not silently promote a scalar prime factor to a prime ideal, unit, square element, root-depth packet or new FLT7 solution.

**APPROVED / Outcome B.** No PR, merge, facade promotion or unconditional FLT7 claim authorized.
