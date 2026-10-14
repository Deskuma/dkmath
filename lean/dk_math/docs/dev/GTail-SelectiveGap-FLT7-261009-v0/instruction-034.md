# Instruction 034 — an actual common receiving ring for Eisenstein and seventh-cyclotomic orders

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-033.md`, `report-033.md`, `source-inventory-033.md` and `frontier-033.md`.
**Scope: Step 034 only.** Following the proved impossibility of **direct** unital homs E→R and R→E, implement a small **third ring C with genuine separate unital maps E→C and R→C**, and test a shared finite-field receiving map at q43. If successful, prove that the shared kernel's **ideal contractions** return the two old typed q43 residue ideals. No all-k ideal-depth transfer, integral E→R map, fake Fermat solution, class/unit extraction, compositum field claim or FLT7 descent.

## Existing source contracts and chosen construction

Current actual integral orders:

```text
E := DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)
R := DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.Ring
τ := DkMath.NumberTheory.TraceOneQuadratic.tau (-1) : E
ζ := DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt.zeta : R
```

E's generator satisfies `τ²−τ+1=0` from \`traceOne_tau_sq\`; R's generator satisfies `1+ζ+...+ζ⁶=0` from \`zeta_geom_sum\`. Step033 proves **no** unital RingHom E→R or R→E, using q29/q13 evaluations. Yet Step033 checks simultaneous *separate* residue maps into ZMod43 at t=37 and r=11.

**Concrete receiving ring candidate**:

```text
C := QuadraticAlgebra R (-1 : R) (1 : R)
ω := QuadraticAlgebra.omega : C
ω² = -1 + ω   -- check the actual QuadraticAlgebra multiplication parameters
ιR : R →+* C := algebraMap R C
ιE : E →+* C := coordinate map (a,b) ↦ (a:R) + (b:R)*ω.
```

The choice `QuadraticAlgebra R (-1) 1` is important: Mathlib's convention is `ω²=a+b*ω`, so these parameters represent **discriminant −3 / τ²−τ+1=0**, not the other DkMath order `TraceOneInt (-2)` with discriminant −7. Check that convention in actual Mathlib source before coding.

A workable implementation is \`ιE x := (⟨(x.fst:R),(x.snd:R)⟩ : QuadraticAlgebra R (-1) 1)\`, with actual \`RingHom\` obligations proved using `QuadraticAlgebra.re_mul` / `im_mul`, the actual \`TraceOneInt (-1)\` coordinate multiplication and integer cast identities. This is a proposed implementation sketch, not yet a checked theorem. The result C is a quadratic algebra **over the existing R**, not automatically a field, a domain, or an identified compositum. It may be described informally as a 12-coordinate candidate, but do not claim a checked ℤ-rank-12 basis unless explicitly constructed.

## Phase 0 — source/API preflight and overlap inventory

Inspect **actual** source and relevant Mathlib signatures:
- `DkMath.NumberTheory.TraceOneQuadratic`: \`TraceOneInt\`, \`tau\`, \`traceOne_tau_sq\`, fst/snd arithmetic, coordinate cast and multiplication;
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier`: actual R, \`zeta\`, its signed integral coordinates/injections and \`ofReal\`;
- `DkMath.FLT.Seven.GTailEisensteinCyclotomicNoDirectHom` (Step033): both no-direct-map theorems and q29/q13 obstruction facts; these **remain true**;
- `DkMath.Lib.NumberTheory.GTailSevenResidueIdeal`: actual \`eisensteinResidueRingHom t ht : E→+*ZMod q\` and E-ideal \`eisensteinResidueIdeal t ht\`;
- `GTailCyclotomicLocalEval` and `GTailCyclotomicPrimeAddress`: actual \`evalCyclotomicFromSeventhRoot r ... : R→+*ZMod q\` and \`seventhRootKernel r ...\`;
- Mathlib `QuadraticAlgebra R a b`, \`omega\`, \`re\`, \`im\`, \`algebraMap\`, \`algebraMap_injective\`, \`re_mul\`, \`im_mul\`, \`Algebra\` instances; \`RingHom.comp\`, \`RingHom.ker\`, \`Ideal.comap\`, \`Ideal.mem_comap\` and \`Ideal.ext\`.

Source-check potential *existing* DkMath common-base-change or quadratic-coordinate ring hom before implementing; avoid duplicate broad infrastructure. A generic tensor product or universal compositum theorem is **not** required.

Write `source-inventory-034.md` with:
- E, R, C source/target types and generator relations;
- exact two unital maps' obligations and, if attempting, injectivity proof gates;
- actual paired t37/r11 residue evaluations and kernel ideals;
- what the common receiving ring **does not** do (no global Fermat balance, no norm/product identity across two independent elements, no power transport).

Suggested owner:
`DkMath/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean`,
with direct import Step033 and a **targeted** Mathlib QuadraticAlgebra module only if needed. Test:
`DkMathTest/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean`.
Do not edit prior E/R ring definitions, private old packet owners, neutral Lib, previous Steps or facades.

## Phase 1 — actual common receiving ring and two unital maps (mandatory)

Define an abbreviation for the **actual** C, and genuine bundled RingHoms:

```text
ιR : R →+* C
ιE : E →+* C.
```

Verify:
1. `ιR(ζ)` is the actual scalar embedding of ζ, and \`ιR\` maps integer casts, sums and products correctly because it is a real RingHom.
2. `ιE(τ)=ω`, `ιE((n:E))=(n:C)` for every n:ℤ, and E's generator relation is preserved by actual image arithmetic in C.
3. \`ιE\` is verified to preserve zero, one, addition and **multiplication** by explicit signed coordinates using the **actual** E multiplication law s=−1 and C quadratic law a=−1,b=1.
4. Cross-source integer scalars coincide in C: \`ιE (n:E)=ιR (n:R)\` for every n:ℤ. This is meaningful and is not a claim that unrelated E/R elements equal one another.
5. `ιR` is injective, if inexpensive, via \`QuadraticAlgebra.algebraMap_injective\` (verify exact checked API). `ιE` may also be injective if the original integer scalar casting `ℤ→R` is proved injective via R's actual six-coordinate chart; do **not** assert this merely because E/C are called integral orders. The **two actual unital maps are mandatory**; injections are valuable but secondary if real source API work is required.

**Gate1 must compile before proceeding to the residue comparison.** If C's coefficients or RingHom multiplication are wrong, correct the parameters or stop with an honest report; do not convert a \`RingHom\` goal into an additive map just to evade the defining relation.

## Phase 2 — q43 shared evaluation from C to its residue field

Use the **real** existing q43 root pair:

```text
t := (37 : ZMod 43);  t²−t+1 = 0
r := (11 : ZMod 43);  r≠0, r⁷=1, r≠1.
evE := eisensteinResidueRingHom t ht : E→+*ZMod43
evR := evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 : R→+*ZMod43.
```

Build a genuine bundled RingHom

```text
evC : C →+* ZMod 43
evC (x.re + x.im*ω) := evR x.re + t*evR x.im.
```

The \`QuadraticAlgebra\` coefficients re/im live in **R**, while the target coefficients live in **ZMod43**. Prove the multiplication law under the checked root condition t²−t+1=0. Use a verified QuadraticAlgebra evaluation/lift API if present and source-checked; a direct coordinate construction is acceptable. Do not silently assume \`evR\` is injective or that t has an integral preimage in R.

**Mandatory commuting triangles:**

```text
evC.comp ιR = evR       : R→+*ZMod43
evC.comp ιE = evE       : E→+*ZMod43.
```

Either actual RingHom equalities (via \`RingHom.ext\`) or equivalent fully quantified \`∀x, ...\` source checks suffice. Verify the generator images:

```text
evC (ιR ζ) = 11
evC (ιE τ) = 37
evC (ιR(n:R)) = evC(ιE(n:E)) = (n:ZMod43).
```

A useful generic strengthening is a common evaluation constructor for arbitrary prime q **only when both supplied roots t and r exist in the same ZMod q**. Keep q43 as the minimum acceptance target; do not add arbitrary q29/q13 root assumptions which are impossible there. The q29/q13 no-direct-map facts remain intact and, indeed, C need not admit evaluations at those primes.

## Phase 3 — one genuine common prime kernel and its two different contractions

Once `evC` and both commuting triangles compile, define

```text
M43 : Ideal C := RingHom.ker evC
```

and prove the actual typed contractions:

```text
Ideal.comap ιE M43 = eisensteinResidueIdeal (37:ZMod43) ht
  : Ideal E

Ideal.comap ιR M43 = seventhRootKernel (11:ZMod43) hr0 hr7 hr1
  : Ideal R.
```

The strongest uncomplicated proof is directly from `Ideal.mem_comap`, \`RingHom.mem_ker\` and the proved commuting triangles. This is a **new precise source-typed correspondence of two local addresses in a third ring**, not an E↔R RingHom and not equality between P37 and K0 (they are ideals of different rings).

If useful, specialize the R contraction to \`sixRootKernel r ... 0\` using the actual checked Step021 equality, and prove `M43.IsMaximal` from the surjectivity of evC onto ZMod43 (already evR/evE reach embedded scalars). Maximality is **optional**, provided the two actual ideal contractions have compiled.

**Do not infer** \`Ideal.map ιE P37 = Ideal.map ιR K0\`, powers of these extended ideals equal one another, \`α² = F_0\` in C, or a global norm equality: contraction of the same M need not give any of these. If source API budget prevents a contraction proof, report exact missing typed lemma and retain compiled commuting maps.

## Phase 4 — meaningful actual GTail regression without fictitious FLT solutions

Use q43 data from Steps032/033:
- E: `α := gtailSevenNormCoord 1166 1857 : E`, \`evE α=0\`, and actual E-ideal support at P37 from Step017;
- R: `F_0 := gtailCyclotomicFactor 1858 1165 0 : R`, \`evR F_0=0\` at r11, and existing Step025 K² membership. Both have a common **residue zero** after mapping separately into C and applying evC:
  `evC (ιE α)=0` and `evC (ιR F_0)=0`.
- Use the checked commuting triangles rather than reconstructing unrelated polynomial coordinate evaluations numerically.
- From these, \`ιE α∈M43\` and \`ιR F_0∈M43\` are legitimate. Their **equality in C** does not follow and must not be stated.
- Both source residue evaluations exist, despite the Step033 no-direct-map theorems. Preserve q29/q13 finite-field tests and Step032 local-budget non-Fermat countermodel; no invented hEq or exact global balance is used.
- The old \`QuadraticBridge.cyclotomicSevenToTraceOne\` norm target \`TraceOneInt(-2)\` remains **a different ring** and is not substituted for the discriminant −3 E used in C.

If all maps and contractions succeed but detailed selected-factor q43 proof-rewriting is heavy, prioritize the genuine algebraic contracts over extra numeric tests. Record which optional cases were skipped and why.

## Phase 5 — truthful mathematical interpretation and stopping

In `report-034.md` / optional `frontier-034.md`, separate these statuses:

1. Actual unital direct E→R and R→E: **impossible**, as proved Step033.
2. Actual unital E→C and R→C: **now constructed** only if Gate1 kernel checks; injective status requires its own proof.
3. Actual evC:C→ZMod43 with its two commutative triangles: **verified** only after Gate2.
4. Same M43 contracted to P37 in E and K0 in R: **verified** only after Gate3; **not** ideal equality across rings.
5. Norm, selected natural factors and total GTail global balance: prior typed separate scalar statements only; no new common-element equation.
6. New signed-root packet, ideal class/unit lift, away-descent provider and actual FLT7 contradiction: **not constructed**.

No claim that C is the **unique/minimal** compositum, the degree-12 field, a domain, flat extension, tensor product isomorphism, or its ideals have a known valuation theory without verifying those extra algebraic properties. Quadratic algebra over R alone does not supply all such properties.

## Deliverables / focused builds / STOP

Required:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean`;
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean`;
- `source-inventory-034.md` and `report-034.md`;
- truthful append after Step033 in `ROADMAP.md`, preserving prior source and historical correction intact.
- Optional `frontier-034.md` if separate verified contract table improves clarity.

Run **sequential** focused new production/test builds, then Step033 and Step032 test regressions using process-local `LEAN_NUM_THREADS=2`. Log every gate's signatures, compiler repairs, exact final command/exit/warnings, all new public \`#print axioms\` outputs, import closure (especially neutral Lib→FLT), forbidden token and whitespace/style checks. No \`sorry\`, \`admit\`, new \`axiom\`, \`unsafe\`, \`native_decide\`, \`False.elim\`, global resource-limit workaround, clean all-suite build, edits to existing E/R owners or old signed providers, facade promotion, PR, rebase or merge.

**Outcome B expected:** construction of an actual **third common quadratic receiver** with two typed unital maps, q43 shared evaluation, and **separately typed** q43 prime ideal contractions. This is a mathematically genuine positive compatibility theorem after Step033's negative direct-map theorem, but **does not itself advance FLT7 descent**.
**Outcome C/partial:** a false QuadraticAlgebra parameter/API assumption, missing ring multiplication proof, incompatible residue-evaluation lift or unproved contraction. Preserve the strongest compiled maps and state the precise blocker; do not postulate unitality/injectivity.
**Outcome A:** only if an independently new **noncircular** restriction on hypothetical positive primitive Fermat7 solutions is proved beyond the receiver construction; sharing an integral target and one finite residue field is not that.

**STOP after Step034.** Do not automatically promote the receiver into a 21st-cyclotomic field, tensor universal property, equal extension ideals/powers, K-adic all-depth theorem, reconstructed signed packet, a smaller primitive Fermat solution, or unconditional FLT7 closure.
