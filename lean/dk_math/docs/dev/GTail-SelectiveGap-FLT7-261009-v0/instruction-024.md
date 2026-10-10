# Instruction 024 — first-order prime-ideal depth firewall for native GTail factors

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-023.md`, `report-023.md`, `source-inventory-023.md`.
**Scope: Step 024 only.** Derive a *guarded* q-local multiplicity-one result for the actual six GTail linear factors when `q|GTail` but `q²∤GTail`. Reuse Step022's six-prime ideal splitting and Step023's **element-level** six-factor product. No unguarded exact valuations, Eisenstein-to-cyclotomic carrier map, signed-root packet manufacture, unit/class group or FLT7 descent.

## Why this is the next narrow arithmetic gate

Step023 now proves unconditionally (as source elements):

```text
∏ i:Fin6, F_i(c,g) = (GTail 7 1 g c : R)
F_i(c,g) := (c+g:R) - zeta^(i.val+1)*(c:R).
```

For a prime q and a canonical nontrivial Tail root r under q∤c,g and q|GTail, it also proves:

```text
F_i(c,g) ∈ K_j ↔ j = sixInverseSlot i
sixInverseSlot = [0,3,4,1,2,5].
```

Step022 proves for these six distinct packet-free prime ideals:

```text
∏ j:Fin6, K_j = cyclotomicScalarIdeal q = (q:R).
```

None of this, **without further input**, shows `F_i∉K_(sixInverseSlot i)^2`. A factor may have larger local multiplicity, even when it belongs to only one q-prime at first order.

The intended **satisfiable guarded theorem** requires the extra arithmetic premise `¬(q²∣GTail 7 1 g c)`:

```text
Nat.Prime q, q∤c, q∤g, q|GTail, q²∤GTail
→ ∀ i:Fin6,
    F_i(c,g)∈K_(sixInverseSlot i)
    ∧ F_i(c,g)∉(K_(sixInverseSlot i))².
```

This result would prove that the **local membership cutoff at power two** is reached under a scalar squarefree-at-q guard. It does NOT supply a general valuation function, or assert q² never divides GTail, or prove FLT7.

## Phase 0 — inventory and mathematical preflight

Read exact source:
- `GTailCyclotomicTailFactorProduct` (Step023 factor product, inverse-index kernel membership);
- `GTailCyclotomicSixRootInterpolation` (Step022 product ideal equality, scalar coordinate criterion);
- `GTailCyclotomicSixRootOrbit` and `GTailCyclotomicPrimeAddress` (maximal kernel, integer contraction);
- `SevenRamifiedFusionCyclotomicDegreeSixCarrier` (signed six-coordinate additive equivalence);
- `DkMath.Lib.Cosmic.GTailCyclotomic` (native natural scalar output);
- Mathlib checked `Ideal.mul_mem_mul`, `Ideal.span_singleton_mul`, `Ideal.mul_le`, Finset product reindex, ideal powers, finite family products, multiplication by a principal ideal and integer cast divisisibility APIs; **do not guess names, inspect source or #check**;
- `SevenRamifiedFusionOrientedCarrierValuationOwnership` and the July 2026 U1.2 oriented valuation report. These contain already-proved **signed-packet-indexed** exact local-power cutoffs. This Step024 is *not* the first local valuation theorem in the repository: it tests what can be proved from the **bare natural GTail Tail** and its scalar first-order guard without constructing the old packet.

Write `source-inventory-024.md` comparing the bare-root input contract with the old signed-depth owner, including exactly why the old \`carrier ∈ K^k ↔ k≤padicValNat...\` cannot simply be applied to natural F_i(c,g) without a typed identification.

Before adding code, validate the following elementary mathematical route on paper and in a minimal Lean sandbox:
- If `F_i∈K_assigned²`, while all six factors are in their respective **distinct** K slots, then
  `(GTail:R) ∈ (∏_j K_j)*K_assigned = (q:R)*K_assigned`.
- If `(n:R)∈(q:R)*K_j` for an integer/natural scalar n, prove **q²|n** using the actual principal-ideal-multiplication law, q-torsionfree signed integral coordinates and `K_j∩ℤ=(q:ℤ)`.
- Therefore `q²∤GTail` excludes the selected factor from its squared prime kernel.

**Do not assume** `(q)*K_j=(q²)` as ideals; this is generally false. The only permissible scalar relation here is the correct *integer contraction* of the product `(q)*K_j` (or the forward implication on scalar elements). A finite q43 example alone does not prove this universal contraction.

If any route turns out false or needs a missing q-nonzero/torsionfree/regularity premise, correct the contract or record a precise mathematical blocker before implementation.

## Phase 1 — primitive scalar cancellation at one degree-six ideal

Suggested new owner:
`DkMath/FLT/Seven/GTailCyclotomicTailDepthOne.lean`,
direct import of Step023 plus minimal Mathlib; **no** full FLT facade or signed packet owner import.

Prove for prime q and each of the six actual root kernels K_j, a tight *scalar membership* lemma:

```text
(n : R) ∈ (cyclotomicScalarIdeal q) * K_j
  → q² ∣ n
```

for all natural n (or signed ℤ if simpler), with K_j defined from a supplied nontrivial seventh root and j:Fin6.

A justified strategy:
1. The principal ideal (q) times K_j should be expressed as **multiples of the embedded scalar q by elements of K_j**. Source-check an ideal product/singleton span lemma and prove both needed directions, rather than treating an arbitrary \`Ideal.mul\` membership as a *single product* without proof.
2. The displayed n is an *integer scalar*. From membership in (q)*K_j, infer q|n via the Step022 \`mem_cyclotomicScalarIdeal_iff\` coordinate criterion; since q prime, q>0.
3. Let m=n/q in naturals or integers. `(n:R)=(q:R)*(m:R)` by the actual integer natural casting arithmetic.
4. From `(n:R)=(q:R)*y` with y∈K_j, and separately `(n:R)=(q:R)*(m:R)`, cancel scalar q in the **actual degree-six ring**. Either use an existing verified \`IsDomain\` instance or prove torsionfree integer scalar multiplication from \`coordinates_natCast_mul\`, the additive equivalence, and injectivity of multiplication by q on ℤ. Do **not** assume an arbitrary \`CommRing\` permits cancellation.
5. Conclude m∈K_j. Step020/021 contraction to integers gives q|m. Thus q²|n.
6. If possible, prove the reverse implication `q²|n → (n:R)∈(q)*K_j` since q∈K_j; a full scalar iff is a clean optional strengthening. The **forward implication is mandatory** for the target.

Keep it generic in q and signed six-dimensional source coordinates; q43 numerical reduction is a regression, not a proof substitute. Do not import an unproved PID/UFD/class-group structure.

## Phase 2 — excess one kernel copy forces an extra scalar prime

For prime q, admissible canonical natural Tail data (q∤c,g and q|T), and any i:Fin6, prove the guarded implication:

```text
F_i(c,g) ∈ (K_(sixInverseSlot i))²
  → ((GTail 7 1 g c : ℕ):R)
       ∈ (cyclotomicScalarIdeal q) * K_(sixInverseSlot i).
```

This is an **actual ideal-product membership** theorem. It must:
- use Step023 `∏ F_i = GTail` as an *element* equality;
- use the **actual** Step023 `F_j∈K_(sixInverseSlot j)` for every j;
- use genuine ideal multiplication / product membership lemmas, without deducing a product's membership from the false assertion that an individual factor generates a K_j;
- reindex the finite family by Step023's actual involution `sixInverseSlot` and prove the product of the six oriented kernels is **the same family** as the Step022 `∏ K_j = (q)`;
- isolate the single **extra** K factor supplied by the assumed square membership at index i;
- use only commutativity/associativity of ideal multiplication, and an actually source-checked bounded-family lemma.

A compact intermediate endpoint may state for any ideals J_i and elements x_i∈J_i that one x_i∈J_i² forces `∏ x_j ∈ (∏ J_j)*J_i`. This should be a *proved finite commutative-ring ideal lemma*, not a copied informal multiplication.

The final main theorem combines Phase1 and Phase2:

```text
q² ∤ GTail 7 1 g c
→ F_i(c,g) ∉ (K_(sixInverseSlot i))².
```

Pair it with the existing first-power membership to expose a precise local first-order certificate. An exact nonmembership at power two suffices for a **depth-one cutoff**, but do not introduce an unproved integer-valued ideal valuation \`v_K\`. In particular, do not state that such a cutoff holds for *every* q dividing GTail without the extra scalar squarefree condition.

## Phase 3 — q43 nonvacuous and false-premise tests

At q=43, c=9,g=4, canonical r=11, T=14491387=43*337009:
- `43|T` and `43²∤T`, checking `337009 % 43 = 18` if useful;
- the factor-to-kernel index permutation [0,3,4,1,2,5] is unchanged;
- for **every i:Fin6**, F_i is in its chosen K slot but **not** in the square of that K, via the new generic theorem;
- all five wrong K slots exclude F_i already at the first power (Step023);
- scalar T belongs to (q), and the factor-element product equals it, yet individual factors do **not** have to generate K or have no other prime factors;
- optional scalar contraction example: n=q² belongs to (q)*K_j, while n=q does not (if full scalar iff compiled).

### Necessary negative control

If q²|T in a valid Tail case, the *premise* of the main theorem fails. Do not assert \`F_i∉K_i²\` anyway. A satisfiable numerical sample may be found, but **do not invent one** or construct a Fermat solution. It is acceptable to demonstrate only logically that the theorem does not apply, and document deeper local multiplicity as unresolved.

Zero-gap g=0 and c=0 are excluded from the q-local depth-one receiver by q∤c,g, while Step023's exact source product remains valid for them. Gap-only q13 does not meet q|T. Characteristic q7 has no nontrivial root in ZMod7 and belongs to the separate old ramified source, not this unramified cutoff.

## Phase 4 — optional light alignment with old depth owner / no false FLT claim

Once the generic bare-root depth-one certificate compiles, source-compare it with the old signed packet \`SevenRamifiedFusionOrientedCarrierValuationOwnership\`, which has a **different** element and signed quotient valuation contract. Write the differences in `report-024.md`. No heavy import or equality of packet sources is required or authorized.

A tiny optional FLT7 input reader may be created **only if** an existing owner gives q-prime, q∤c,g and q²∤GTail with its actual hypotheses; do not derive q²∤GTail from the Fermat equation by wishful algebra. If it duplicates a Step010/011 statement or needs a circular primitive counterexample impossibility, skip it.

Do not claim the new local depth-one result alone yields class-group principality, units, seventh power extraction, a smaller Fermat tuple, or contradiction.

## Deliverables / incremental gates / STOP

Required:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthOne.lean`;
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthOne.lean`;
- `source-inventory-024.md` and `report-024.md`;
- truthful post-023 `ROADMAP.md` entry.

Gate order:
1. source/API audit + scalar cancellation/contraction proof;
2. genuine finite ideal-product excess-factor lemma;
3. generic cutoff theorem with scalar q² guard;
4. q43 6-factor regression, absence of fake unconditional cutoff;
5. public axiom and source/import audit.

Build only new focused source/test, then Step023/022 regressions sequentially with process-local `LEAN_NUM_THREADS=2`. Log final exit status, all public `#print axioms` results, attempted but failed API names and mathematical limitations. No \`sorry\`, \`admit\`, new \`axiom\`, \`unsafe\`, \`False.elim\`, cyclic neutral imports, full clean build, public facade promotion, PR or merge.

**Outcome B expected** for a conditional local depth-one theorem under q²∤T, independently of exact FLT7 equation; no new descent. **Outcome C/partial** if q-torsionfree principal ideal product or finite-family excess-factor membership is blocked; report the exact missing lemma and retain only compiled partial endpoints. **Outcome A** only if an additional genuinely independent noncircular FLT7 arithmetic restriction is proved and compared with existing packet depth results, not from rephrasing classical splitting or a forced squarefree-at-q input.

**STOP after Step024.** No universally exact local valuations, q-adic completion, new signed packet, cyclotomic class/unit-power extraction, primitive Fermat descent or unconditional FLT7 closure.
