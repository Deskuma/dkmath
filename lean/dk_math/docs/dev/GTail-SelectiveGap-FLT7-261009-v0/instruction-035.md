# Instruction 035 — the q43 two-by-six common-prime address grid

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-034.md`, `report-034.md`, `source-inventory-034.md` and `frontier-034.md`.
**Scope: Step 035 only.** Reuse the actual **third quadratic receiver** constructed in Step034 and its two injective source RingHoms to prove a finite **2×6 grid of distinct q43 prime kernels**, including each kernel's **separately typed contractions** to Eisenstein and seventh-cyclotomic source ideals. Explore a strictly bounded *proper-extension* firewall and the actual row/column incidence of the two prior native test elements. No claim that the grid is the full spectrum, no generalized ideal-power transport, no all-k valuations or FLT7 descent.

## Checked input, not to be rebuilt

Actual source types:
```text
E := DkMath.NumberTheory.TraceOneQuadratic.TraceOneInt (-1)
R := SevenCyclotomicDegreeSixInt.Ring
C := DkMath.FLT.Seven.GTailCommonReceiver.Carrier
   = QuadraticAlgebra R (-1) 1
ιE := GTailCommonReceiver.fromEisenstein : E→+*C
ιR := GTailCommonReceiver.fromCyclotomic : R→+*C
```

Step034 **proved** that ιE and ιR are individually injective, agree on embedded integers, and that the q43 evaluation `eval43:C→+*ZMod43` sends the independent C quadratic generator ω (image of E generator τ) to 37 and the R generator ζ to 11. Its maximal kernel `M43` contracts back to `P37 : Ideal E` and `K0 : Ideal R`. A concrete `ιE α≠ιR F0` despite both being in M43 was also tested.

Step033 proved no direct unital RingHom E→R nor R→E. All proposed paired evaluations go from **C to ZMod43**, not from one source to the other. Neither new maps nor contractions imply `α=F_i` in C.

Other existing facts:
- `(37:ZMod43)²−37+1=0` and `(7:ZMod43)²−7+1=0`. These are the **two distinct Eisenstein residue roots**, conjugate since 1−37=7 in ZMod43;
- `(11:ZMod43)^7=1`, `11≠0,1`, and `sixSlotRoot (11:ZMod43) j=11^(j.val+1)` for `j:Fin6`. The six distinct values are `11,35,41,21,16,4`; Step021 already has \`sixSlotRoot_injective\`, \`sixRootKernel_ne\`, and each root's kernel is maximal;
- `eisensteinResidueRingHom t ht : E→+*ZMod43` and `eisensteinResidueIdeal t ht : Ideal E` are existing checked owners; distinct t37/t7 give distinct E kernels;
- Step034's `eval43` is the `t37, s11` case.

The **bounded target** is a map from `Fin 2 × Fin 6` to twelve pairwise distinct **maximal ideals in C**. This is a *proved collection of twelve addresses*, **not** a complete classification of all prime ideals in C above (43), nor a demonstration of a global degree/rank 12 field.

## Phase 0 — source/API inventory

Read exact declarations and direct imports:
- `GTailEisensteinCyclotomicCommonReceiver`: C, ιE/ιR, eval43, commuting RingHom triangles, M43 and contractions/maximality;
- `GTailEisensteinCyclotomicNoDirectHom`: both direct-no-hom theorems;
- `GTailCyclotomicSixRootOrbit`: `sixSlotRoot`, its 6 injective powers, `sixRootKernel` and six-root ideal inequality;
- `GTailCyclotomicPrimeAddress`: \`seventhRootKernel\`, evaluation kernel contraction and maximality;
- `GTailSevenResidueIdeal`: E residues and E-ideal membership, especially \`eisensteinResidueRingHom_tau\`;
- `GTailCyclotomicTailFactorProduct`: factor/kernel inverse-slot incidence, and `GTailCyclotomicTailDepthTwo`: F0 q43 K0² support;
- `GTailSevenIdealSquareAddress`: α's P37 square and conjugate exclusion; Step032 numerical non-Fermat countermodel;
- Mathlib \`RingHom.comp\`, \`RingHom.ker\`, \`Ideal.comap\`, \`Ideal.map\`, \`Ideal.map_le_iff_le_comap\` (verify exact API), \`Ideal.IsMaximal\`, \`Ideal.ext\` and \`QuadraticAlgebra.re_mul/im_mul\`.

Write `source-inventory-035.md` identifying exact types at each gate, current q43 root data, the already proved **Step034 special case**, any old overlap, and what ideal extensions/powers would require additionally.

Suggested new owner:
`DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean`,
directly importing Step034 and **only** narrow targeted extra imports if needed. Test:
`DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean`.
Keep the previous implementation and its old q43 M43 unchanged.

## Phase 1 — actual two-root/six-root parameterization and RingHoms

Create a total finite root selector:

```text
eisenstein43Root : Fin 2 → ZMod 43 := ![37,7]
seven43Root (j:Fin6) := sixSlotRoot (11:ZMod43) j
```

Prove root and injectivity properties:
- for all e, `t=eisenstein43Root e` satisfies `t²−t+1=0`;
- the t selector is injective, 37≠7;
- for all j, `s=seven43Root j` satisfies `s⁷=1, s≠0, s≠1`;
- the s selector is injective, reusing the actual seventh-order lemma, not a new finite proof for every slot;
- document the exact six values only in tests if the universal prior source lemma suffices.

Define genuine source RingHom at each j
```text
evR43(j) : R→+*ZMod43 :=
  evalCyclotomicFromSeventhRoot (seven43Root j) ...
```
and for each e,j define **a bundled, unital**
```text
evGrid(e,j) : C→+*ZMod43
evGrid(e,j) x := evR43(j) x.re + eisenstein43Root(e)*evR43(j) x.im.
```

Prove addition/one/multiplication from actual quadratic coordinate laws and the checked t quadratic relation, as in Step034's eval43 (but **do not edit** the earlier owner or assume a nonexistent universal evaluation map). A compact local generic helper for quadratic algebra over R is fine if it reduces duplicate logic.

Prove **both** commuting triangles for arbitrary e,j, as actual RingHom equalities or quantified equalities:

```text
evGrid(e,j).comp ιE = eisensteinResidueRingHom (eisenstein43Root e) ...
evGrid(e,j).comp ιR = evR43(j).
```

Verify \`evGrid e j (ιE τ)=t_e\`, \`evGrid e j (ιR ζ)=s_j\`, and all integer scalars reduce canonically. Reuse source-level map/evaluation APIs rather than trusting two unrelated bare equality proofs.

**Mandatory Gate1:** the 12 actual unital homs and two compatible restrictions compile.

## Phase 2 — twelve maximal kernels and separately typed source contractions

Define

```text
M(e,j) : Ideal C := RingHom.ker (evGrid e j).
```

For every e,j prove:
- \`evGrid e j\` surjective, using \`evR43(j)\` surjective and the ιR commuting triangle, as Step034 did;
- \`M(e,j).IsMaximal\` and hence \`IsPrime\` from its actual ZMod43 field quotient;
- **actual separately typed E contraction**:
  `Ideal.comap ιE (M(e,j)) = eisensteinResidueIdeal (eisenstein43Root e) ... : Ideal E`;
- **actual separately typed R contraction**:
  `Ideal.comap ιR (M(e,j)) = sixRootKernel (11:ZMod43) ... j : Ideal R`;
- at e=0,j=0, `evGrid 0 0 = eval43` and `M 0 0 = M43`. This exact compatibility is strongly recommended but secondary if dependent \`by decide\` proof terms require an explicit `RingHom.ext` and normalization.

The **E contraction does not depend on j**; the **R contraction does not depend on e**. This is the structural meaning of the 2×6 product of residue choices. Never write `P_e=K_j`: those ideals belong to **different rings**.

## Phase 3 — injectivity of the paired kernel address

Prove a theorem with the precise type

```text
Function.Injective (fun x : Fin 2 × Fin 6 => M x.1 x.2).
```

Recommended proof using **actual source contractions**:
1. Assume \`M(e,j)=M(e',j')\`. Applying the same \`Ideal.comap ιR\` and the checked R contraction gives equality of `K_j=K_j'`. Existing `sixRootKernel_ne` and `sixSlotRoot_injective` imply j=j'.
2. Similarly, E contractions give equality `P_(t_e)=P_(t_e')`. Prove distinctness for t37 and t7 using the genuine source element `τ−(t_e.val:E)` (or explicitly `τ−37:E`) which evaluates to zero at one root and nonzero at the other. Beware of integer vs representative casts in E. Alternatively apply both evaluations to a generator-value/kernel-separating element. Then injectivity of `eisenstein43Root` yields e=e'.
3. Combine with `Prod.ext`. The proof must distinguish **all 12** pairs, not just two sample ideals.

An independent direct separation route via the two C generator images ω and ιRζ is permissible, provided ideal equality is contradicted by a genuine member/nonmember witness. Do not appeal to different homs alone as proof that their kernels differ.

Test:
- all 12 pairs exist and are pairwise distinct;
- same E address across six columns; same R address across both rows;
- \`M 0 0=M43\` if proven;
- any two distinct grid addresses are distinct **maximal** ideals, so they are comaximal if a checked Mathlib \`Ideal.isCoprime_of_isMaximal\` API is convenient (optional). Do not assert the 12-way product equals `(43:C)` without a separate, nontrivial factorization/index/rank argument.

**Mandatory Gate3:** a fully proved 2×6 injective maximal-ideal grid.

## Phase 4 — proper extension firewall (valuable, bounded optional gate)

This is a **strictly stronger** statement than Step034's contraction equalities and should be attempted only after the kernel grid works.

Let `M₀₀:=M(0,0)` and let `P37:Ideal E`, `K0:Ideal R` be the original contracted ideals.

Using \`Ideal.map\` and the two contraction identities, prove inclusions

```text
Ideal.map ιE P37 ≤ M₀₀
Ideal.map ιR K0  ≤ M₀₀.
```

Then establish **both are strict** via the verified independent root choices.

- **R-extension side**: `ω−37:C` is in M(0,0), but **not** in M(1,0) since the second Eisenstein residue sends ω to 7. Yet `Ideal.map ιR K0 ≤ M(1,0)` because M(1,0) has the same R contraction K0. Hence `ω−37∉Ideal.map ιR K0` and `Ideal.map ιR K0 ≠ M₀₀`.
- **E-extension side**: `ιRζ−11:C` is in M(0,0), but **not** in M(0,1) since the second seventh root `11²=35`. Yet `Ideal.map ιE P37 ≤ M(0,1)` because this kernel has the same E contraction P37. Hence `ιRζ−11∉Ideal.map ιE P37` and the extension differs from M₀₀.

When possible state the strong proper inequalities `Ideal.map ιR K0 < M₀₀` and `Ideal.map ιE P37 < M₀₀`. Verify actual \`Ideal.map_le_iff_le_comap\` or corresponding APIs before coding. **Do not replace strict inclusion with the false claim that \`Ideal.map\` commutes with powers, or that \`M₀₀\` equals one of the two extended ideals**.

These two proofs would explain precisely why a **single common maximal kernel** cannot be recovered by extending only one of the two source ideals: a second independent generator-root choice remains.

If the actual ideal-extension API is cumbersome, retain the kernel grid (Outcome B), document the exact missing API/membership argument, and leave strictness as a later task. Avoid resource-limit hacks.

## Phase 5 — actual natural GTail/Eisenstein row-vs-column incidence

Use **only** the verified Step032 q43 **non-Fermat** tuple:

```text
(a,b,c,g)=(1166,1857,1858,1165)
α := gtailSevenNormCoord a b : E
F0 := gtailCyclotomicFactor c g 0 : R
```

Existing results: E α has zero residue at t37 but **nonzero** at the conjugate t7, and R F0 vanishes at the selected seventh root s11 but **not** at the other five roots. Prove, ideally as generic grid examples,

```text
fromEisenstein α ∈ M(e,j) ↔ e=0          -- all 6 j
fromCyclotomic F0 ∈ M(e,j) ↔ j=0        -- both e.
```

This is a particularly useful **orthogonal prime-support readout**: the E-coordinate selects a row while the R-coordinate selects a column. Their common membership occurs at the single address (0,0), but `ιEα≠ιRF0` in C remains true from Step034.

This is a *local compatibility witness*, not a positive Fermat7 solution or an identification of oriented signed packet carriers. Do not claim E α and R F0 generate equal ideals or have identical prime-power depth in C.

The row/column theorem is a strong optional enrichment. If it is expensive, preserve the checked 2×6 grid and provide a few concrete positive/negative examples, accurately recording what remained unproved.

## Deliverables, audit and STOP

Required:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean`;
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean`;
- `source-inventory-035.md` and `report-035.md`;
- truthful **post-034** `ROADMAP.md` append, preserving all historical review/report and correction records.
- Optional `frontier-035.md` if the ideal-map strictness and row/column distinction deserve an independent contract table.

Sequential local focused builds using process-local `LEAN_NUM_THREADS=2`: (1) root selectors and twelve compatible RingHoms; (2) maximality, contractions and `M 0 0` comparison; (3) full 12-pair injectivity; (4) bounded ideal-extension strictness and selected row/column tests where feasible; (5) final source/test plus Step034/033 regressions, all public \`#print axioms\`, import DAG/neutral→FLT, source placeholder/unsafe/decide audit and whitespace/lint checks.

Log exact command/exit/warning per phase and any failed proof or repairs. No full clean all-suite build, global resource-limit workarounds, earlier owner edits, facade promotion, signed packet construction, class/unit-principalization, PR/rebase/merge.

**Expected Outcome B:** a kernel-checked **twelve-point prime-address grid** in the existing C, with correct typed contractions; optionally two proved strict-ideal-extension firewalls and the row/column incidence of actual test factors. Such a result establishes finite-field local branching, not a complete spectrum, ideal-class decomposition, Hensel convergence or new FLT7 descent.
**Outcome C/partial:** a concrete broken root selector, RingHom relation, contraction or injectivity proof; report it with the strongest verified partial theorem instead of conjectural labels.
**Outcome A:** only for an independently new noncircular condition on hypothetical primitive positive FLT7 solutions beyond local address branching; do not call a finite grid a Fermat obstruction.

**STOP after Step035.** No \`C\` field/domain/rank-12 certification, generalized discriminant splitting theorem, general-prime 2×6 product classification, all-k ideal extension-power equality, \`E→R\` map, signed-root reconstruction, next primitive packet, away descent or unconditional FLT7 conclusion. Reassess after Step035 whether the now-verified multiplicity of possible common primes leaves any canonical source-linked pairing in the original focused Fermat7 data.
