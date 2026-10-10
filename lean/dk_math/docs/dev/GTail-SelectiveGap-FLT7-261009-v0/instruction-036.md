# Instruction 036 — joint generation of the two-source q43 prime address, and bounded mixed-power support

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-035.md`, `report-035.md`, `source-inventory-035.md`, `frontier-035.md`.
**Scope: Step 036 only.** Within the **existing** common quadratic receiving ring C and Step035's finite q43 grid, prove that each maximal kernel is generated **jointly** by the two extended source prime ideals. Then obtain a small, source-typed lower bound on the common-kernel power of actual mixed products, using the CORRECT Mathlib \`Ideal.map_pow\`. No entire spectrum classification, equal source-depth assertion, scalar global balance, general-prime construction, all-k tower, new packet or FLT7 descent.

## Previously checked input — must not be rebuilt

The actual source rings, targets and maps:

```text
E := TraceOneInt (-1)
R := SevenCyclotomicDegreeSixInt.Ring
C := GTailCommonReceiver.Carrier = QuadraticAlgebra R (-1) 1

iE := GTailCommonReceiver.fromEisenstein : E →+* C
iR := GTailCommonReceiver.fromCyclotomic : R →+* C
t_e := GTailPrimeGrid.eisenstein43Root e : ZMod 43   -- e:Fin2, roots [37,7]
s_j := GTailPrimeGrid.seven43Root j : ZMod 43        -- j:Fin6, roots [11,35,41,21,16,4]

P_e := eisensteinResidueIdeal t_e (...) : Ideal E
K_j := sixRootKernel (11:ZMod43) ... j : Ideal R
M_ej := GTailPrimeGrid.M e j : Ideal C = ker (evGrid e j)
A_e := Ideal.map iE P_e : Ideal C
B_j := Ideal.map iR K_j : Ideal C
```

Step035 already proves for all e,j:
```text
A_e ≤ M_ej                        -- map_eisenstein_le
B_j ≤ M_ej                        -- map_cyclotomic_le
iE⁻¹(M_ej)=P_e                   -- M_comap_eisenstein
iR⁻¹(M_ej)=K_j                   -- M_comap_cyclotomic
M_ej.IsMaximal
Function.Injective (fun (e,j):Fin2×Fin6 => M_ej)
```

At (0,0) **both** inclusions above are strict; these facts remain true:
```text
A_0 < M_00
B_0 < M_00
```

The actual E generator τ has image ω under iE, and the actual R generator ζ maps to the coefficient inclusion under iR. The C coordinate projections \`QuadraticAlgebra.re/im\` and source ring evaluation are already kernel checked. **Do not** prove A_e=M_ej or B_j=M_ej: those statements are false at (0,0).

The first genuinely missing combination theorem is the IDEAL SUM:

```text
M_ej = A_e ⊔ B_j
```

This has not yet been kernel checked. It is stronger than individual extensions/individual contractions, and weaker than a global spectrum or source ideal-adic valuation theorem.

## Phase 0 — actual API and carrier inventory

Read exactly:
- `DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` (Step035): P_e/K_j embeddings, \`M\`, two commuting triangles, \`map_eisenstein_le\`, \`map_cyclotomic_le\`, \`M_injective\` and strictness;
- `GTailEisensteinCyclotomicCommonReceiver` (Step034): C's \`QuadraticAlgebra\` coordinates, iE/iR injectivity, their integer scalar equality and quadratic generator;
- `DkMath.Lib.NumberTheory.GTailSevenResidueIdeal`: actual E residue RingHom, its τ image, source \`Ideal.ker\`;
- `GTailCyclotomicSixRootOrbit`: \`mem_sixRootKernel_iff\`, actual s_j evaluation and root-slot contracts;
- `GTailCyclotomicTailDepthTwo` and Step017 \`GTailSevenIdealSquareAddress\`: selected native \`F0∈K0²\`, \`α²∈P37²\` and \`α∈P37\`; these are DIFFERENT source rings;
- Mathlib: \`Ideal.map_le_iff_le_comap\`, \`Ideal.mem_map_of_mem\` or a real substitute, \`Ideal.map_pow\`, \`Ideal.mul_mem_mul\`, \`Ideal.pow_mono\`, \`Ideal.pow_mem_pow\`, \`Ideal.mem_sup\` or \`Submodule.add_mem\`, \`QuadraticAlgebra.algebraMap_eq\`, \`QuadraticAlgebra.re_mul/im_mul\`, \`QuadraticAlgebra.ext\`, \`map_natCast\`, \`ZMod.natCast_zmod_val\`. **Check exact names with source/#check**, do not invent.

Create `source-inventory-036.md` recording direct owner/import APIs, source-vs-target ideal types, exact map_pow contract, proposed decomposition identity and what is STILL UNPROVED concerning transported valuations, global Fermat7 balance and old signed carrier.

Suggested owner:
`DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean`
direct import of Step035 only, plus small Mathlib modules only if the existing closure lacks their source-checked APIs; tests:
`DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean`.

No edits of Steps 010–035, existing ring owners/definitions, signed packet providers, façade/ledger or neutral Lib owners.

## Phase 1 — the explicit quadratic coordinate decomposition (first compile gate)

For arbitrary e:Fin2 and x:C, let the integer representative of the chosen row residue be

```text
n_e := (eisenstein43Root e).val : ℕ;
tLift := ((n_e:ℕ):R);
y_e(x) := x.re + tLift*x.im : R.
d_e := tau (-1) - (n_e : E) : E.
```

Prove the actual **source-typed decomposition identity**

```text
x = fromCyclotomic (y_e(x)) +
    fromEisenstein d_e * fromCyclotomic x.im.
```

This is elementary but important: using iEτ=ω, iR(y)=⟨y,0⟩ and ω²=−1+ω, the right side has C-coordinates

```text
re: y + (−n_e)*x.im = x.re,
im: x.im.
```

Use explicit \`QuadraticAlgebra.ext\` and actual source coordinate laws, not deep nested ext which reopens the old carrier. Integer/natural cast t_e.val should be visibly converted from E to R to C via the proven scalar compatibility. This identity is true for **every x:C**, with no membership premises. The index e enters only through the chosen integer lift.

Additionally prove **the row kernel generator membership**:

```text
d_e = τ − (n_e:E) ∈ P_e.
```

Actual E residue evaluation sends τ to t_e and the embedded integer n_e to (n_e:ZMod43)=t_e; use the checked root evaluation RingHom and \`ZMod.natCast_zmod_val\`. Do NOT infer an integral equality t_e=n_e in E (t_e lives in a field).

Finally, for x∈M(e,j) prove

```text
y_e(x) ∈ K_j
```

because \`evR43 j(y_e(x)) = evGrid e j x=0\`, using the exact formula for evGrid and the separate input \`s_j\`. The proof is in the actual R kernel, not a claim x itself lies in B_j.

**Build Gate1 independently** before writing the ideal equality. If a n_e value/cast or \`im\` sign is wrong, show exact failing Lean goal and repair it without adding unsupported ring hypotheses.

## Phase 2 — prove the full joint-generation ideal equation (mandatory)

Define (local or public if useful):

```text
A (e:Fin2) : Ideal C :=
    Ideal.map fromEisenstein (eisensteinResidueIdeal (eisenstein43Root e) ...)

B (j:Fin6) : Ideal C :=
    Ideal.map fromCyclotomic (sixRootKernel 11 ... j).
```

A and B **do not** depend on the other coordinate. Reuse Step035's \`map_eisenstein_le\` and \`map_cyclotomic_le\` to prove

```text
A e ⊔ B j ≤ M e j.
```

The hard direction is

```text
M e j ≤ A e ⊔ B j.
```

Take any x∈M e j. The Phase1 source-typed split says

`x = fromCyclotomic(y_e(x)) + fromEisenstein(d_e) * fromCyclotomic(x.im)`

with `y_e(x)∈K_j` and `d_e∈P_e`.
- The first term is in B_j by the **actual** \`Ideal.map\` membership of the mapped element.
- The second term is in A_e: its generator image \`fromEisenstein d_e\` is in the ideal extension, and multiplying by an arbitrary C element preserves membership.
- Both B_j and A_e lie under their join; closure under addition puts x in the join.

Deduce for every e,j:

```text
theorem M_eq_map_eisenstein_sup_map_cyclotomic (e:Fin2) (j:Fin6) :
  M e j = A e ⊔ B j.
```

This is the primary **Outcome B acceptance theorem**. At (0,0), also verify that this agrees with old \`M43\` through Step035's \`M_zero_zero\`, while **both individual** `A0<M00` and `B0<M00` are retained.

Do not use \`Ideal.map_pow\` here: the ideal sum is an exponent-one construction and must be established directly from the coordinate decomposition. Do not claim \`A_e⊔B_j\` is prime from arbitrary source ideals; its maximality follows *after* proving equality with M_ej already checked maximal.

## Phase 3 — the correct map_pow and bounded mixed-ideal support (valuable secondary gate)

The source report-035 explicitly corrected the nuance: Mathlib **does prove**
```text
Ideal.map f (I^n) = (Ideal.map f I)^n.
```
There is no problem with \`Ideal.map_pow\` itself. The invalid reasoning would replace \`Ideal.map f I\` with the **strictly larger** M(e,j) before asserting equality of powers.

Prove a small truthful source-typed transport, either generally for the two actual source ideals at all n or for the **bounded n=1,2** cases:

```text
z∈P_e^n  → fromEisenstein z ∈ (A e)^n → fromEisenstein z ∈ (M e j)^n
u∈K_j^n → fromCyclotomic u ∈ (B j)^n → fromCyclotomic u ∈ (M e j)^n
```

Use actual \`Ideal.map_pow\`, \`Ideal.pow_mono\` and proven `A_e,B_j≤M_ej`. The implication into M^n is safe because inclusion is preserved by powers. **NO converse is authorized**; the individual strict inclusions at n=1 already defeat equality in general.

Then test a genuinely **mixed C element**, using the true non-Fermat Step032 input:

```text
α := gtailSevenNormCoord 1166 1857 : E
F0 := gtailCyclotomicFactor 1858 1165 0 : R

α∈P37 (Step034 checked)
α²∈P37² (Step017 checked)
F0∈K0² (Step025 checked)
```

From the new power transport at (0,0), establish:

```text
fromEisenstein α ∈ M00,
fromEisenstein (α²) ∈ M00²,
fromCyclotomic F0 ∈ M00²,
(fromEisenstein α) * (fromCyclotomic F0) ∈ M00³,
(fromEisenstein (α²)) * (fromCyclotomic F0) ∈ M00⁴.
```

These are **lower bounds on common-kernel powers** from actual distinct source factors. The product belongs to C and is meaningful; no equality of embedded source elements is assumed. Do NOT claim either product is outside the next power, no exact M-adic valuation, and no common element equality/norm identity across E/R. The two products' membership is compatible with the fact that the chosen numerical tuple is **not** a Fermat7 solution.

If proving a general map-power lemma would invite a large abstraction, keep the bounded powers 1,2 and two tested mixed products. If this optional gate is expensive, the compiled joint-sum theorem is sufficient for Outcome B; accurately note any omitted test.

**Avoid unproved algebraic shortcuts:** \`(A⊔B)^n\` contains mixed products, but is NOT generally \`A^n⊔B^n\`. If explicitly expanding \`(A⊔B)^2\`, include AB mixed terms and source-check the precise Mathlib ideal identity; expansion is optional.

## Phase 4 — exact grid regressions and failure controls

Mandatory tests for every e:Fin2, j:Fin6:
- exact \`M e j = A e ⊔ B j\`;
- the 12 M values are pairwise distinct and maximal from Step035, even though row-only/column-only extensions are reused;
- both A0 and B0 are strictly contained in M00; the new equality does not contradict strictness;
- unchanged E and R typed contractions and commuting evaluation triangles;
- q43 t37/s11 (0,0) equality with Step034 M43;
- α/F0's Step035 orthogonal row/column incidence, non-Fermat equation and inequality of the two images;
- if Phase3 succeeds, the two specific mixed-product lower-bound memberships, not exact depth.

Optional stress test at (1,0) or (0,1) with a different row or column to ensure the coordinate decomposition works generically, not only at t=37. No q29/q13 common receiver evaluation should be fabricated, since Step033's negative finite-field obstructions remain.

Maintain these boundaries:
- no source-to-source E→R/R→E map (Step033 remains valid);
- no universal statement about **all** maximal ideals of C above43 (only the constructed grid is proved);
- no equality of A_e with M_ej or B_j with M_ej;
- no \`Ideal.map_pow\` denial; no replacement of mapped power by M-power **equality**;
- no FLT7 equation/global balance from joint-generation alone, no old signed packet, no away descent.

## Deliverables, focused builds, audit, STOP

Required:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean`;
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean`;
- `source-inventory-036.md` and `report-036.md`;
- truthful post-035 `ROADMAP.md` append, preserving all old reviews/inventories/frontier and corrections.
- Optional `frontier-036.md` with a concise lattice diagram/contract table if the new equalities warrant it.

Build sequential focused:
1. actual R-coordinate decomposition / E source generator in P_e / y_e(x) in K_j when x∈M;
2. two-sided ideal inclusion and **joint sum equality** for all 2×6 pairs;
3. bounded proper-extension and Step035 row/column regression;
4. optional source-mapped powers and mixed C products;
5. final new production/test plus Step035/034 direct regressions, all public \`#print axioms\`, import DAG/neutral→FLT and forbidden-token/whitespace/style checks.

Use process-local `LEAN_NUM_THREADS=2`, no full clean all-suite build and no global resource-limit override. Log actual source/test build commands and exit/warnings, intermediate Lean API/sign/cast failures and corrected proof routes, exact theorem signatures, all public axiom outputs, source/import audit. Do not edit old owners, neutral rings, signed providers, facades, historical ledgers/reviews or repository status; no PR, merge, rebase.

**Expected Outcome B:** exact q43 paired-source **prime join** equality for all twelve addresses, ideally accompanied by **true bounded cross-source M-power lower bounds** on actual α and F0 images. A genuine new local algebra structure theorem; it is NOT FLT7 descent or general prime-depth synchronization.
**Outcome C/partial:** an actual failure of the algebra coordinate identity, ideal-map membership extraction or another mathematically necessary hypothesis; preserve the checked partial sources and report precisely which gate failed.
**Outcome A:** only a separately source-compared noncircular obstruction to a hypothetical primitive positive FLT7 counterexample, beyond this ideal-join arithmetic.

**STOP after Step036.** No complete spectrum, rank-12 field/domain/flatness certificate, generalized q-adic powers, unconditional equality of extension powers with M-powers, reconstructed signed packet, class/unit principalization, primitive Fermat descent provider or unconditional FLT7 closure. After this local paired-prime join is established, reassess the **original FLT7 global balance and packet reconstruction frontier**, rather than growing indefinitely in the finite-field grid.
