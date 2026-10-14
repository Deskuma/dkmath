# Instruction 022 — six-root interpolation and exact scalar ideal recovery

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-021.md`, `report-021.md`, `source-inventory-021.md`.
**Scope: Step 022 only — a source-checked finite interpolation theorem and exact intersection of the six bare-root kernels.** A product formula is a separate optional gate *only after* the intersection equality compiles. No cyclotomic class/unit theory, Eisenstein-to-cyclotomic ring map, signed-packet fabrication or FLT7 descent.

## Mission and high-risk boundary

Step 021 proved for a supplied prime q and a supplied nontrivial seventh root r in `ZMod q` that the six kernels

```text
K_i := sixRootKernel r hr0 hr7 hr1 i : Ideal SevenCyclotomicDegreeSixInt.Ring
i : Fin 6    (roots r^(i.val+1))
```

are pairwise distinct **maximal** ideals, hence pairwise comaximal. The Tail factor `F(c,g)=(c+g)-ζ*c` lies in exactly the first of these six kernels when r is the canonical natural Tail ratio.

**NOT YET PROVED:** the intersection of all six kernels equals the scalar principal ideal `(q)`. Pairwise comaximality cannot by itself establish this equality: one needs to reconstruct **all six integral coordinates** of an arbitrary degree-six element from its six distinct residue evaluations.

This step should construct precisely that missing reconstruction, exploiting the existing integral coordinate equivalence

```text
SevenCyclotomicDegreeSixInt.coordinates :
  Ring ≃+ (Fin 6 → ℤ)
```

and `ofReal_alpha : ofReal alpha = 1+zeta+zetaInv`, `zeta_pow_seven=1`, `zeta_ne_one` and the Step 018 seven-term geometric sum lemma **in the residue field**. No arbitrary real-cubic/degree-six algebra hom is assumed beyond Steps 019–021.

Expected correct mathematical endpoint (under the explicit supplied nontrivial root):

```text
(⨅ i : Fin 6, K_i)
  = Ideal.span ({((q:ℕ) : SevenCyclotomicDegreeSixInt.Ring)} : Set R).
```

**Optional** following this proof and the checked pairwise comaximality:

```text
(∏ i : Fin 6, K_i) = (q).
```

Do not publish the product formula without proving the intersection **and** using a genuine finite-family coprime-product theorem, with exact Mathlib API checked locally. Even when the product is proved, it is a **conditional splitting theorem in this actual degree-six ring**, not a statement about primitive FLT7 solutions, cyclotomic unit powers or descent.

## Phase 0 — exhaustive source/Mathlib overlap check

Read:
- `DkMath.FLT.Seven.GTailCyclotomicSixRootOrbit`, its actual power roots and maximal/comaximal kernel APIs;
- `DkMath.FLT.Seven.GTailCyclotomicPrimeAddress` and `GTailCyclotomicLocalEval`, especially the **coordinate evaluation** on `re/im` of `SevenRealCubicInt`;
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier`, `coordinates`, `ofReal_alpha`, `zeta_mul_zetaInv`, `zeta_pow_seven` and the defining quadratic relation;
- `DkMath.FLT.Seven.SevenRealCubicInt` (signed triple structure, coordinate maps);
- `SevenRamifiedFusionGlobalOrientedPrimeFactorization` and existing split-prime factorization owners for overlapping theorems **under signed-packet hypotheses only**;
- current Mathlib polynomial evaluation, root count/degree bound, ZMod integer casts, invertible integer matrices or Fin6 linear algebra, `Ideal.iInf`, `Ideal.mem_span_singleton` and pairwise-coprime Finset product/inf; inspect actual lemma names with source/`#check`, not guesses.

Write `source-inventory-022.md` with the original six-coordinate carrier, actual evaluation formula, missing lemma, matrix verification plan, proof budget and source dependency restrictions.

## Phase 1 — carrier-correct six coefficients and evaluation polynomial

Define a transparent helper, preferably **without a new ring or algebraic equivalence**, extracting the six signed coordinates of an arbitrary `z : SevenCyclotomicDegreeSixInt.Ring`:

```text
v := coordinates z : Fin 6 → ℤ
v = (z.re.fst, z.re.snd, z.re.thd,
     z.im.fst, z.im.snd, z.im.thd)
```

For any scalar `s : ZMod q` with `s^7=1`, `s≠0` and `s≠1`, the existing Step 019 evaluation is

```text
eval_s z = (x0+x1*β+x2*β²)+s*(y0+y1*β+y2*β²)
β = 1+s+s⁻¹.
```

The nontrivial seventh-root geometric sum gives `1+s+...+s^6=0` and `s⁻¹=s^6`. Reduce the result to a **polynomial in s of degree at most 5** with six coefficients `w0,...,w5` that are **integer linear combinations** of x0,x1,x2,y0,y1,y2. Prove the resulting value identity in Lean **for arbitrary signed coordinates**, not only the q43 numeric tuple.

A candidate integer change-of-basis matrix M with rows w0,...,w5 and columns (x0,x1,x2,y0,y1,y2) is:

```text
M =
[ 1  0  1  0  1  1 ]
[ 0  0  0  1  1  2 ]
[ 0 -1 -1  0  1  1 ]
[ 0 -1 -2  0  0  0 ]
[ 0 -1 -2  0  0 -1 ]
[ 0 -1 -1  0  0 -1 ].
```

**Important:** M and its determinant −1 were calculated **symbolically outside Lean** using `alpha=1+s+s^6`, the seventh geometric sum, and the power basis 1,s,...,s^5. They are **unproved target data**, not authorized Lean lemmas. Check every row against the actual source algebra and the six evaluation formulas before using this matrix as a public statement; correct it if the implementation reveals a sign or ordering discrepancy.

Choose the simplest Lean carrier:
- a vector `Fin 6 → ℤ` and an explicit `Fin 6 → ℤ` map for coefficients;
- a polynomial `Polynomial (ZMod q)` of degree ≤5;
- or the six scalar coefficient equations.

Do not force an unwieldy Matrix framework where a six-equation linear-combination proof suffices. If a genuine linear equivalence over ℤ with determinant ±1 is useful, prove it, do not postulate it.

### Reversibility of coordinate change

The required next lemma is that **if every w_j casts to zero in ZMod q, then every original coordinate v_i casts to zero**. For example, exhibit an *integral inverse matrix* N with N*M=1 by explicit `norm_num`/`decide` and derive coordinate equations; this proof works uniformly in every characteristic, not merely for q43.

The symbolic inverse candidate to source-check is

```text
N =
[ 1  0 -1  1  0  0 ]
[ 0  0  0 -1  2 -2 ]
[ 0  0  0  0 -1  1 ]
[ 0  1 -1  0  0  1 ]
[ 0  0  1 -2  2 -1 ]
[ 0  0  0  1 -1  0 ].
```

Again, the identity N*M=1 must be **verified in Lean** if adopted; do not trust this instruction as a proof.

## Phase 2 — six distinct evaluations force all coefficients zero

Take the six Step 021 roots `sixSlotRoot r i`. They are pairwise distinct and are legitimate nonidentity seventh roots, already kernel checked.

Define the degree≤5 polynomial `p_z(X)=Σ_{j=0}^5 (w_j:ZMod q)*X^j` and prove for each slot i:

```text
evalCyclotomicFromSeventhRoot (sixSlotRoot r i) ... z
  = Polynomial.eval (sixSlotRoot r i) p_z.
```

If `z∈K_i` for **all** `i:Fin 6`, the polynomial vanishes at six *distinct* roots. By a legitimate field polynomial root-count theorem (checked names and prerequisites), a nonzero polynomial of degree≤5 cannot have six distinct roots. Conclude `p_z=0`, hence all six coefficients `w_j` vanish in ZMod q, then Phase 1's **proved** inverse change-of-basis forces every integral coordinate `v_i` to vanish in ZMod q.

The precise output target is an arbitrary-element iff, not only membership for a chosen Tail factor:

```text
(∀ i : Fin 6, z ∈ K_i)
  ↔ (∀ j : Fin 6, (coordinates z j : ZMod q) = 0).
```

The reverse implication uses only the actual RingHom evaluation formula/linear coefficient map. It is **not** contingent on q43 finite calculation.

As an alternative to polynomial root counting, an explicit 6×6 Vandermonde invertibility argument at six distinct roots is acceptable if this is smaller and verified in the real Mathlib environment. Do not assume six roots span the source as a ring; prove the actual linear-algebra conclusion.

## Phase 3 — principal scalar ideal and exact intersection

Define a narrow scalar principal ideal in the *degree-six ring*:

```text
I_q := Ideal.span ({((q:ℕ):R)} : Set R)
```

and prove an arbitrary signed-coordinate iff:

```text
z ∈ I_q
  ↔ (∀ j : Fin 6, (q:ℤ) ∣ (coordinates z j)).
```

Use `Ideal.mem_span_singleton` and the existing additive equivalence `coordinates`, or a directly checked coordinate-wise quotient witness. If needed, show `coordinates (q*z) j = q*(coordinates z j)` by ring arithmetic; `coordinates` is an additive equivalence, so multiplicative compatibility **must be checked**, not assumed. To prove the reverse direction, construct an actual ring element from the six integer quotient coordinates with `coordinates.symm` and show its scalar q-multiple equals z by coordinate extensionality.

Connect coordinate cast-zero in ZMod q with integer divisibility by q. Use Phase 2's iff and ideal extensionality to prove

```text
(⨅ i : Fin 6, K_i) = I_q.
```

The scalar principal ideal is defined **inside the same degree-six carrier**. Do not confuse it with the degree-two Eisenstein `eisensteinScalarIdeal q` or the ideal (q) in ℤ; these are three different types.

This is the **mandatory main proof gate**. If the polynomial/basis or lattice iff fails in the available build budget, stop with the strongest verified intermediate theorem and a detailed missing-lemma report. Do not substitute a q43 finite equality for a universally quantified theorem.

## Phase 4 — optional product equality from already proved comaximality

**Only after** the exact intersection equality is kernel checked, use Step 021's actual pairwise

```text
K_i ⊔ K_j = ⊤  (i ≠ j)
```

and a verified Mathlib theorem for a finite family of pairwise comaximal ideals to deduce

```text
(∏ i : Fin 6, K_i) = (⨅ i : Fin 6, K_i) = I_q.
```

Do not infer this from pointwise maximality without actually constructing the required IsCoprime family and using a *finite* product-vs-inf theorem. If \`Finset.univ.prod\` and \`iInf\` APIs need an explicit finite bridge, prove it.

This is an **optional gate**, not a prerequisite for approving a successfully checked intersection. If it is blocked solely by API discovery, report the exact name/signature mismatch and stop rather than adding a new axiom.

## Phase 5 — mandatory numeric and negative checks

With q=43,r=11, the six root slots are `[11,35,41,21,16,4]`. Check:
- an arbitrary signed coordinate example (not only F(9,4)) using the new polynomial evaluation identity;
- its six polynomial root evaluations agree with the six actual RingHoms;
- explicit M, N inverses and coefficient/cast relations if Phase 1 uses matrices;
- scalar embedded 43 belongs to every K_i and to I_43;
- a signed element such as `z = ofReal(-43)+zeta*ofReal(86)` has all its integer coordinates divisible by 43 and belongs to all six kernels;
- `F(9,4)` belongs to K_0 but not the other five; hence F is **not** in I_43 and not in the all-six intersection/product, consistent with selective support;
- any established intersection/product theorem must be applied to q43 as an instance of the generic theorem, not silently proved only by `decide`;
- q=13 Gap ratio1 does not meet hr1, and q=7 lacks a nontrivial seventh root in ZMod7; no root-free factorization is claimed;
- the old packet-indexed ideal product theorems are **not** passed off as a proof for bare root inputs.

## Deliverables, validation and STOP

Suggested owner/test:
- `DkMath/FLT/Seven/GTailCyclotomicSixRootInterpolation.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicSixRootInterpolation.lean`;
- `source-inventory-022.md`, `report-022.md` and truthful post-021 `ROADMAP.md` entry.

Avoid edits to the source degree-six ring, old signed-root owners, root drivers, FLT facades or historic ledgers. Keep direct imports narrow, although the existing degree-six owner has a large transitive closure.

Build sequential incremental focused targets with process-local `LEAN_NUM_THREADS=2`, then Step 021/020 regressions when affordable. Record each gate's exact public theorem signatures, source Mathlib API names, numerical verification, all `#print axioms` outputs, exit codes, any failed proof attempts, import cycle check and no `sorry`/`admit`/new `axiom`/`unsafe`/`False.elim` placeholders. Do not mask a missing interpolation proof with an assumption or a large linter/recursion-limit workaround.

Expected classification:
- **Outcome B** for genuine integral coordinate interpolation, the exact all-six ideal intersection and (if independently proved) the comaximal ideal product formula; this is a classical split-prime decomposition in the exact degree-six carrier, **not** an FLT7 descent.
- **Outcome C / partial** for an incorrect matrix, missing q-unit/root or a blocked generic ideal-equality inference; retain and document correct partial results.
- **Outcome A** only if a further independent, noncircular FLT7 arithmetic obstruction is actually proved and compared with preexisting owners; a classical six-ideal factorization by itself is B.

**STOP after Step 022.** No generic prime ideal classification, Eisenstein→degree-six integer ring map, cyclotomic unit-power extraction, signed-depth packet construction, valuation-based descent or unconditional FLT7 closure.
