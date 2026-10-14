# Review 033 — no direct unital ring homs between the Eisenstein and seventh-cyclotomic orders

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 033 COMPLETE / Outcome B**

## Evidence and limitation

Statically reviewed pushed GitHub sources:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean` (61 lines);
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean` (90 lines);
- `report-033.md`, `source-inventory-033.md`, `frontier-033.md`;
- actual `TraceOneQuadratic`, `GTailSevenResidueIdeal`, `GTailCyclotomicLocalEval`, `GTailCyclotomicTailFactorProduct` owners.

This is a **static GitHub proof-route audit** and **not an independently executed Lean build**. Codex reports final focused production/test builds successful, Step032/031 test regressions, 24 checked examples, and six public `#print axioms` checks restricted to `propext`, `Classical.choice`, `Quot.sound` where applicable. First intermediate production build had one style warning from a `letI` notation and was corrected without altering the theorem; final builds and reports show no warnings, forbidden proof placeholders or import cycles.

## Exact mathematical statements checked

Let `E := TraceOneInt (-1)` be the actual discriminant −3 Eisenstein order and `R := SevenCyclotomicDegreeSixInt.Ring` the actual degree-six seventh-cyclotomic integral order.

1. `seven_root_zmod29` kernel checks the nonzero, nonidentity seventh root `7:ZMod29`. Hence the existing **unital** `evalCyclotomicFromSeventhRoot 7 ... : R →+* ZMod29` is well typed; no invented q29 Tail tuple is needed.
2. `no_eisenstein_root_zmod29 (x:ZMod29)` proves no element of this finite field solves `x²−x+1=0`, using exhaustive small `decide`.
3. The private actual E generator relation `(tau (-1))²−tau (-1)+1=0` is proved from the checked `traceOne_tau_sq` and genuine integer coordinates. It is not an invented relation.
4. `not_nonempty_eisenstein_to_seven_cyclotomic` assumes a hypothetical **unital** `f:E→+*R`, composes it with the actual `R→+*ZMod29`, transports the τ relation by `map_pow/sub/add/one/zero`, and contradicts the no-root theorem. Neither injectivity nor surjectivity of f is required.
5. `eisenstein_root_zmod13` proves `4²−4+1=0` in ZMod13, so the preexisting unital `eisensteinResidueRingHom 4 ... : E→+*ZMod13` is real.
6. `no_seven_geom_root_zmod13 (x:ZMod13)` proves no root of the **entire** `1+x+x²+...+x⁶` polynomial. The actual `zeta_geom_sum` in R comes from Step023 and is an integral relation, not the weaker `ζ⁷=1` alone.
7. `not_nonempty_seven_cyclotomic_to_eisenstein` composes hypothetical **unital** `R→+*E` with `E→+*ZMod13`, maps the full seven-term relation, and reaches a finite-field no-root contradiction. It correctly avoids assuming the generator image remains a nontrivial root; the test explicitly shows `1⁷=1` but `Φ₇(1)≠0` in ZMod13.
8. The 24 reported tests independently list all six nontrivial seventh roots in ZMod29 and the two Eisenstein quadratic roots in ZMod13, exhibit the actual evaluation RingHoms, and preserve a **simultaneous pair** of maps E→ZMod43 at 37 and R→ZMod43 at 11. They distinguish `TraceOneInt(-2)` (discriminant −7, old quadratic norm coordinate) from E=`TraceOneInt(-1)` (discriminant −3), as well as the Step032 arithmetic equivalence and its non-Fermat q43 witness.
9. The two no-hom proofs do **not** import/assume FLT7 equation, positivity, primitive data, local GTail support, q-budget, signed-root packets or descent. They are structural results about the two **specific integral orders**.
10. There are six public theorems with report-recorded normal Lean logical axioms, no new axioms, sorry/admit/unsafe/native_decide, or full-suite build claim. Direct new production import is only Step032; no old ring/power/facade code was changed.

## Scientific interpretation and Step 034

**APPROVED — Outcome B.** The previous 'no implemented direct map' gap has become **proved nonexistence of direct unital E→R and R→E RingHoms**. These conclusions do not rule out unital maps from both rings **into a third receiving ring**, embeddings in a common extension, tensor constructions, or scalar/norm pairings; they do not produce an FLT7 contradiction.

**Recommended Step034:** construct a small **actual common receiving ring**, not a new source-to-source hom. A concrete candidate with existing Mathlib infrastructure is:

```text
R := SevenCyclotomicDegreeSixInt.Ring
C := QuadraticAlgebra R (-1) 1
E := TraceOneInt (-1)
ιR : R →+* C                   -- QuadraticAlgebra algebraMap
ιE : E →+* C                   -- (a,b) ↦ (a:R) + (b:R)*QuadraticAlgebra.omega
```

The E generator relation `ω²−ω+1=0` holds by the actual `QuadraticAlgebra` multiplication parameters. The source coordinate formula and direct multiplication must be verified in Lean. This is a *rank-two quadratic algebra over the real R*, hence a candidate `ℤ`-rank-12 common receiver, **not** automatically a field, a domain, a compositum equality or an ideal-transport theorem. Importantly, it does not contradict either proved no-direct-hom.

Useful bounded Step034 endpoints:
- actual typed unital maps `ιE,ιR`, images of τ and ζ and integer-scalar compatibility;
- explicit injectivity of `ιR` (QuadraticAlgebra real coordinate), and `ιE` only if checked integer-coefficient injection through R;
- a shared **q43** residue RingHom `evC:C→+*ZMod43` extending the existing E-root37 and R-root11 evaluations, using `37²−37+1=0`. An explicit coordinate map `u.re,u.im ↦ evR(u.re)+37*evR(u.im)` with checked multiplication is acceptable if Mathlib lacks an easily used lift API;
- state precisely that a shared receiver and q43 reduction do **not** prove global GTail balance, factor identification, prime-ideal-depth transport or away descent.

This proposed C construction and evC are **not Step033 theorems**. If the actual `QuadraticAlgebra` instance/API/cast or existing integral injection proof makes the full package expensive, complete typed maps first and report precise partial status. Do not fabricate embeddings merely from the name 'QuadraticAlgebra'; prove them.

No PR, merge/rebase, facade, all-k valuation, signed packet, unit/class-power extraction or unconditional FLT7 conclusion is authorized.
