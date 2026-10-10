# Instruction 033 — finite-field obstruction to a direct Eisenstein/cyclotomic integral RingHom

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-032.md`, `report-032.md`, `source-inventory-032.md` and `frontier-032.md`.
**Scope: Step 033 only.** Formally decide whether a **direct unital ring homomorphism** can exist between the **actual** two integral carriers from Steps012–032. Prefer precise nonexistence proofs using real existing residue RingHoms at characteristic 29 and 13. Do not construct a fictitious E→R map, infer FLT7 descent, generalize to all possible common extensions, add K^5 or an all-k valuation hierarchy.

## Why this is a genuine new type check

Step032 proved the exact global balance is equivalent to Fermat7Equation under additive focus; a strong q43 local-compatible native tuple still fails it. The existing paired finite-field residues only share `ZMod q` as a **codomain**:

```text
E := DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)
R := DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.Ring

E →+* ZMod q     -- when supplied t²-t+1=0
R →+* ZMod q     -- when supplied a nontrivial r⁷=1
```

The older code correctly refrained from inventing `E →+* R`. This step tests whether such a direct map is **not merely missing but mathematically impossible**, using two primes where the required scalar residue roots are incompatible.

The named rings are *not* interchangeable:
- E has the integral generator `τ := TraceOneQuadratic.tau (-1)` with the exact checked relation `τ²=τ−1`, equivalently `τ²−τ+1=0`. Its discriminant is −3.
- R has the actual integral generator `ζ := SevenCyclotomicDegreeSixInt.zeta` and the exact checked geometric relation
  `1+ζ+ζ²+ζ³+ζ⁴+ζ⁵+ζ⁶=0` (Step023 \`zeta_geom_sum\`). Its seventh-root evaluations exist at every **supplied nontrivial** seventh root in a prime field.
- The old `QuadraticBridge.cyclotomicSevenToTraceOne` targets `TraceOneInt (-2)` (discriminant −7), **not** E=\`TraceOneInt (-1)\` (discriminant −3). Do not claim this old norm map is an E↔R unital ring hom or infer an Eisenstein subring from a degree-divisibility heuristic.

## Gate 0 — source owner and Mathlib API inventory

Source-inspect exact signatures in:
- `DkMath.NumberTheory.TraceOneQuadratic`: `TraceOneInt`, `tau`, `traceOne_tau_sq`, \`ofInt\`, integer casts and CommRing instance;
- `DkMath.Lib.NumberTheory.GTailSevenResidueIdeal`: \`eisensteinResidueRingHom\` at supplied root `t:ZMod q` satisfying `t²−t+1=0`, and \`eisensteinResidueRingHom_tau\`;
- `DkMath.FLT.Seven.GTailCyclotomicLocalEval`: actual \`evalCyclotomicFromSeventhRoot\` RingHom `R →+* ZMod q` and the theorem mapping ζ to the supplied root;
- `DkMath.FLT.Seven.GTailCyclotomicTailFactorProduct.zeta_geom_sum` and checked actual R / zeta;
- `DkMath.FLT.Seven.GTailGlobalBalanceFirewall`, Step032's exact-balance iff (context only, do not use the Fermat premise in obstruction proofs);
- `DkMath.FLT.Seven.QuadraticBridge` and old `CyclotomicQRTraceOneBridge` for overlap/type diagnostics only;
- verified Mathlib \`RingHom.comp\`, \`map_pow\`, \`map_sub\`, \`map_add\`, \`map_one\`, \`map_intCast\`, finite Fintype \`decide\`, and ring arithmetic APIs; check exact names against actual sources / \`#check\`.

Create `source-inventory-033.md` comparing source/target types and **unital RingHom** premise, plus the exact q29/q13 residue-field proof obligations. The result is a **carrier-feasibility decision**, not a new FLT7 contradiction or provider construction.

Suggested small owner:
`DkMath/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean`
with direct import of Step032 and targeted earlier root RingHom owner **only if genuinely missing from transitive closure**. Its test:
`DkMathTest/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean`.

No changes to actual E/R definitions, old signed packet/ideal owners, shared neutral Lib APIs or facades.

## Gate 1 — finite-field elementary obstructions, independently kernel checked

First prove four explicit **small numeric facts** with Lean, not only from outside-theorem reasoning.

### q=29: R can be evaluated, E cannot

```text
(7 : ZMod 29)^7 = 1
(7 : ZMod 29) ≠ 1
(7 : ZMod 29) ≠ 0
∀ x : ZMod 29, x² - x + 1 ≠ 0
```

The first three enable the existing \`evalCyclotomicFromSeventhRoot (q:=29) 7 ... : R →+* ZMod29\`; the last means the **Eisenstein quadratic generator relation cannot hold in ZMod29**. Check \`29.Prime\` and every finite residue using \`by decide\`. It is not necessary to assume or construct a Tail tuple c,g divisible by 29.

### q=13: E can be evaluated, R cannot

```text
(4 : ZMod 13)^2 - 4 + 1 = 0
∀ x : ZMod 13,
   1+x+x²+x³+x⁴+x⁵+x⁶ ≠ 0
```

The first fact enables the **actual** \`eisensteinResidueRingHom (q:=13) 4 ... : E →+* ZMod13\`; the second means the actual cyclotomic relation Φ₇ cannot hold in ZMod13. Use \`by decide\` on this finite type, or a verified algebraic proof if faster. The prime q13 Gap-side example from Step013 is **unrelated**: this finite-field evaluation is about **arbitrary integral generators**, not a supposed q13 Tail support instance.

These proposed facts were independently checked by finite integer arithmetic, **not by Lean yet**:
- ZMod29 has six nontrivial seventh roots [7,16,20,23,24,25], including 7, and **no** root of x²−x+1.
- ZMod13 has Eisenstein polynomial roots 4 and 10, and **no** root of 1+x+...+x⁶.

If \`decide\` fails because of an unexpected ZMod decidability/performance API, use a small explicit \`fin_cases\` proof or \`decide +kernel-certificate\`, not \`native_decide\` or a new axiom. Do not falsify a premise just to close the goal.

## Gate 2 — NO unital RingHom E → R (mandatory)

Proposed theorem (name may adapt):

```text
theorem not_exists_eisenstein_to_seven_cyclotomic :
  ¬ ∃ f : TraceOneInt (-1) →+* SevenCyclotomicDegreeSixInt.Ring, True
```

Prefer a more idiomatic:
```text
¬ Nonempty (TraceOneInt (-1) →+* SevenCyclotomicDegreeSixInt.Ring)
```

or `∀ f : E →+* R, False`.

Proof:
1. Suppose unital `f:E→+*R`. Take the actual τ from `TraceOneQuadratic.tau (-1)` and the checked relation `τ²−τ+1=0`, derived from \`traceOne_tau_sq\` and integer cast / \`ofInt\` normalization.
2. Apply `f` to the relation. Because f is an actual **unital** \`RingHom\`, the image `f τ∈R` obeys the same quadratic equation.
3. Apply the existing *real* residue evaluation `ev29 := evalCyclotomicFromSeventhRoot (q:=29) 7 ... : R→+*ZMod29`.
4. The composite sends f τ to some x:ZMod29 with x²−x+1=0, contradicting the checked finite no-root lemma.
5. Do not make claims about additive-group homomorphisms, \`ℤ\`-linear maps, nonunital multiplicative semigroup morphisms or ring maps into **different** coefficient extension rings. The obstruction is for **unital E→R RingHom** of these exact rings.

A short generic helper \`(∀ x:B, x²−x+1≠0) → ¬ Nonempty (E→+*B)\` is optional, but test it carefully; avoid growing an abstraction layer not needed for the two real carriers.

**Build Gate2 before starting the reverse-direction theorem.**

## Gate 3 — NO unital RingHom R → E (strong secondary target)

Proposed endpoint:

```text
¬ Nonempty (SevenCyclotomicDegreeSixInt.Ring →+* TraceOneInt (-1)).
```

Proof:
1. Suppose actual unital `f:R→+*E`.
2. \`zeta_geom_sum\` gives an **integral relation inside R** with seven terms. Apply f using \`map_add\`, \`map_pow\`, \`map_one\` to obtain Φ₇(f ζ)=0 in E. Import or rewrite the exact sum order only as checked.
3. Apply the actual E residue RingHom `ev13 := eisensteinResidueRingHom (q:=13) (4:ZMod13) (by decide)`. Obtain x:ZMod13 with `1+x+...+x⁶=0`.
4. Contradict the checked \`∀ x:ZMod13, 1+x+...+x⁶≠0\`.
5. This proof does **not** assume f ζ remains nontrivial after applying f. The *complete* seven-term integral relation handles any image, including 1. Merely transporting ζ⁷=1 would be too weak (1 is always a seventh root in ZMod13).

If an actual integer zeta relation or named hom is missing from the import closure, inspect Step023/Step013 owners. Record the missing exact reference and stop at the proven direction rather than importing a huge facade or postulating a field embedding.

If both directions compile, provide two separate named theorems (do not collapse to an ambiguous notion of \`RingEquiv\`). As a trivial corollary there is no ring equivalence E ≃+* R, but avoid a redundant extra theorem unless the two directions are already kernel checked.

## Gate 4 — interpret exactly, compare genuine positive alternatives

Create `frontier-033.md` or a dedicated section in \`report-033.md\` with a precise distinction:

| Claim | Mathematical status after successful Gate2+3 |
| --- | --- |
| Unital direct RingHom E→R | **Impossible**, with q29 finite-field witness |
| Unital direct RingHom R→E | **Impossible**, with q13 finite-field witness |
| Shared \`ZMod43\` residue field evaluations | **Already possible**, from actual separate RingHoms |
| Shared scalar norm/readout E→ℤ and R's GTail scalar product | **Already proved**, Steps012–032 |
| Embedding E and R into **some larger common ring** | **NOT ruled out** by these two nonexistence theorems |
| An \`ℤ\`-module map / bilinear pairing / tensor-compositum bridge | **NOT ruled out**; also not constructed by this task |
| Reconstruction of signed-depth provider / Fermat7 descent | **Not supplied** by nonexistence |

A possible later mathematical construction is a compositum or tensor-product **receiving both source rings as maps into a third ring**, not a direct E→R hom. Do not claim such a receiving ring automatically preserves ideal powers or solves the global Fermat equation.

Also source-review the existing discriminant −7 quadratic companion `TraceOneInt (-2)`: its norm map for seventh powers does not contradict the new impossibility for discriminant −3 Eisenstein E. This sign/parameter distinction is central.

After the two no-hom lemmas, write which genuinely new typed algebraic input would be needed next:
- a third target ring C with explicit maps E→C and R→C, generator images and checked defining relations;
- a *mathematically stated* common element/scalar identity that goes beyond an arbitrary image pair;
- if a prime ideal is to be transported, a proved ring map and proper \`Ideal.map\`/comap statement with norms, contraction and nonzero kernel/power checks;
- if FLT descent is desired, an actual new primitive \`CounterexamplePack\`, an away route and exact \`carrier_match\`.

The no-direct-hom results are potentially a **new DkMath structural theorem about these two orders**, but they do NOT resolve FLT7 or prohibit richer bridges.

## Tests, documentation and STOP

Required:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean`;
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicNoDirectHom.lean`;
- `source-inventory-033.md`, `report-033.md`;
- truthful post-032 `ROADMAP.md` append, preserving historical Step032 correction and old instruction/source reports;
- optional `frontier-033.md` if the comparison deserves a separate artifact.

Minimum tests:
- ZMod29 root r7 and absence of quadratic root;
- ZMod13 quadratic root t4 and absence of seventh-cyclotomic root;
- new actual unital no-hom theorem(s), full public \`#print axioms\`;
- the existing q43 simultaneous E/R residue roots **are not contradicted** by the unital no-hom theorem;
- Step032 arithmetic equivalence and q43 local-compatible non-Fermat counterexample still compile;
- q7 / q3 ramified and q13 Gap boundaries retained only as contrasts; do not fabricate a Tail tuple for q29/q13.
- A small test should explicitly disallow misreading `TraceOneInt (-2)` as E=\`TraceOneInt (-1)\`; use source comments/type annotations, not false claims.

Build new source and test, then Step032 and Step031 focused regressions sequentially with process-local `LEAN_NUM_THREADS=2`. Log all actual compilation exit codes/warnings, changed direct import graph, all public axiom printouts, no new \`sorry\`/\`admit\`/\`axiom\`/\`unsafe\`/\`native_decide\`/\`False.elim\`, source-lint and whitespace. No full clean suite, global resource-limit hacks, old carrier code edit, façade promotion, PR/rebase/merge.

**Outcome B expected:** genuine kernel-checked algebraic **nonexistence of direct unital maps** in the two stated directions, with exact finite-field obstructions. This is a high-value mathematical **negative transfer frontier**; no Fermat descent follows.
**Outcome C / partial:** a failed genuine relation/cast/RingHom API gate — report precisely and retain whichever direction is checked; do not fill a type hole with an assumption or a not-actually-unital map.
**Outcome A:** only a separately source-compared, noncircular FLT7 arithmetic obstruction beyond those type-theoretic facts. The no-hom result alone remains B.

**STOP after Step033.** Do not build a compositum, tensor product, 21st-cyclotomic ring, ideal-class theory, new signed packet, primitive Fermat descent or unconditional FLT7 conclusion without a separate instruction.
