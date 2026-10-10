# Instruction 020 — packet-free cyclotomic prime kernels and unique Tail root address

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-019.md`, `report-019.md`, `source-inventory-019.md`.
**Scope: Step 020 only — degree-six cyclotomic kernel API and root uniqueness, without a signed-root packet or FLT7 closure.**

## Aim / overlap warning

Step 019 already constructs a bundled RingHom on the *existing* `SevenCyclotomicDegreeSixInt.Ring`:

```text
evalCyclotomicFromSeventhRoot r hr0 hr7 hr1 :
  SevenCyclotomicDegreeSixInt.Ring →+* ZMod q
```

where q is prime, `r:ZMod q`, `r≠0`, `r^7=1` and `r≠1`. It maps `zeta↦r` and the real cubic alpha to `1+r+r⁻¹`. From q∤c, q∤g and q|GTail, the natural ratio `r=(c+g)/c` supplies these conditions and the actual linear factor `F(c,g)=ofReal(c+g)-zeta*ofReal(c)` maps to zero.

**Important prior work:** `SevenRamifiedFusionCyclotomicLinearPrimeAddress` already has signed-packet-indexed `evalKernel`, `eval_surjective`, `evalKernel_isMaximal`, `evalKernel_comap_ofReal`, `evalKernel_comap_intCast` and `evalKernel_cardQuot`. These are NOT available with Step 019's *bare* root without a new proof. Do not rewrite/duplicate old packet theorems with the same premises, invent a `RamifiedSignedRootDepthPacket` from the q43 numeric calibration, or treat equality of finite-field codomains as an embedding from the **different** Eisenstein ring `TraceOneInt(-1)`.

## Phase 0 — source inventory

Inspect exact signatures in:
- `DkMath.FLT.Seven.GTailCyclotomicLocalEval`;
- `DkMath.Lib.NumberTheory.GTailSevenPairedResidue` and its natural Tail-ratio theorems;
- `SevenRamifiedFusionCyclotomicLinearPrimeAddress` and `SevenRamifiedFusionGlobalOrientedPrimeFactorization`;
- `SevenRamifiedFusionCyclotomicDegreeSixCarrier`, actual `zeta` and `ofReal`;
- Mathlib RingHom kernel, surjectivity-to-maximality, ideal contraction and integer-cast zero APIs.
- separate `GTailSevenResidueIdeal` in the Eisenstein degree-two ring only for **contrast**, not ideal transport.

Write `source-inventory-020.md` documenting exact reused names, hypothesis carrier, minimal direct import graph and overlap.

## Phase 1 — generic packet-free maximal ideal address

Suggested new owner `DkMath/FLT/Seven/GTailCyclotomicPrimeAddress.lean` importing directly `GTailCyclotomicLocalEval` plus targeted Mathlib if necessary.

Define, with explicit q-prime Fact and admissible root proofs,

```text
K_r := RingHom.ker (evalCyclotomicFromSeventhRoot r hr0 hr7 hr1)
```

as an **actual Ideal of the existing degree-six ring**.

Prove:
1. `z∈K_r ↔ eval_r z=0`, via the actual RingHom kernel API.
2. `Function.Surjective eval_r` by taking a residue's natural representative and embedding it as `ofReal (x.val : SevenRealCubicInt)`. This is a bare-root variant of the old packet-indexed proof.
3. `K_r.IsMaximal` using field codomain and actual surjectivity; consequently prime.
4. `Ideal.comap (Int.castRingHom SevenCyclotomicDegreeSixInt.Ring) K_r = Ideal.span {(q:ℤ)}`.
5. `Ideal.comap SevenCyclotomicDegreeSixInt.ofReal K_r = RingHom.ker (evalRealFromSeventhRoot r hr0 hr7 hr1)`.

Optional after these succeed: quotient-cardinality `Submodule.cardQuot K_r = q`. Use exact verified Mathlib theorem names, not invented API labels. These are **typed representation improvements** and remain Outcome B absent any new arithmetic obstruction.

## Phase 2 — unique Tail root slot

Let q prime, c,g naturals with `hc:¬q∣c`, and let `s:ZMod q` be any independent *nonzero, nonidentity seventh root* with proof terms hs0/hs7/hs1. Prove the precise neutral statement:

```text
evalCyclotomicFromSeventhRoot s hs0 hs7 hs1
    (gtailCyclotomicLinearFactor c g) = 0
  ↔ s = gtailSevenTailRatio q c g
```

Expand the existing linear factor: its value is `(c+g)-s*c`. Since c is a q-unit, zero ↔ `s=(c+g)/c`. Importantly this iff does **not** require q|GTail or q∤g: those premises are needed to show that **the canonical ratio itself** supplies a nontrivial seventh root, not for cancellation of c.

Then combine with Step 019: when q|GTail, q∤c and q∤g, its canonical ratio r produces K_r with F∈K_r, while every **distinct** admissible root s has F∉K_s. The conclusion only ranges over the already defined nontrivial root kernels, not all possible prime ideals of the degree-six ring.

## Phase 3 — distinct kernels require a witness

For two distinct nontrivial seventh roots r≠s at the same prime q, show `K_r≠K_s` by producing **an actual element**, not merely noting that two RingHoms take different values on zeta.

One candidate is

```text
w := zeta - ofReal (((r.val:ℕ) : SevenRealCubicInt)).
```

Then `eval_r(w)=r-r=0`, while `eval_s(w)=s-r≠0`. Deduce membership in K_r, nonmembership in K_s, and kernel inequality. Use the existing image-of-zeta and cast image theorems; handle root certificate types explicitly. No general ideal-power or six-kernel product theorem is implied.

If possible, make a thin Tail-specialized theorem bundling F∈K_r and F∉K_s for r=gtailSevenTailRatio q c g and independent s≠r. Avoid a new heavy packet hierarchy.

## Phase 4 — optional typed compatibility with old packet evaluation

Only if Phases 1–3 pass easily, and **only when an existing** `CyclotomicLinearPrimeAddress a` and its canonical ratio are supplied, compare old `a.eval` with new `evalCyclotomicFromSeventhRoot ((a.quotientAddress.ratio:ZMod q)) ...` by RingHom extensional equality / the explicit signed-coordinate formulas. Their beta and quadratic signs should match. Do not infer from a q43 *neutral* tuple the existence of any signed-root packet, and do not claim equality of ideals without a checked evaluation equality.

This adapter is optional and may be omitted with an exact dependency or elaboration blocker.

## Phase 5 — numeric and negative calibrations

At q=43, c=9,g=4, use **two real nontrivial seventh roots**:
- r=11; s=35=11² in ZMod43. Verify powers 7, nonzero, nonidentity, and r≠s.
- The new degree-six RingHoms map zeta respectively to 11 and 35.
- F(9,4)=ofReal13−zeta*ofReal9 belongs to K11 but **not** K35; directly check `13-35*9 ≠ 0` in ZMod43.
- Generic K11≠K35 via the Phase 3 kernel witness. Maximality and integer/real contractions via the Phase 1 theorems where available.
- Preserve the original q43 satisfiable calibration q|Q/T, t=37, and **not** an exact `Fermat7Equation 5 8 9`. No fabricated packet.
- q=13 gap branch (q|g, q∤T, canonical ratio=1) does not supply a nontrivial-root RingHom. q=7 uses the distinct existing ramified evaluation at zeta↦1; do not apply a false nontrivial-root premise there.

Optional low-cost lemma: under q-prime and q∤c,g, prove `q∣GTail 7 1 g c ↔ (gtailSevenTailRatio q c g)^7=1`; reverse uses the **exact** seventh-power shell identity and q∤g to cancel, not a guessed converse. Skip if it duplicates a named source theorem or distracts.

## Deliverables and validation

Required: `DkMath/FLT/Seven/GTailCyclotomicPrimeAddress.lean`, matching narrow `DkMathTest/FLT/Seven/GTailCyclotomicPrimeAddress.lean`, `source-inventory-020.md`, `report-020.md`, truthful post-019 `ROADMAP.md` section. Do not modify old packet owners, ring definitions or facade files.

Build only new focused production/test and Step019/018 regressions sequentially with `LEAN_NUM_THREADS=2`. Record actual final exit codes, every new public theorem signature, `#print axioms`, signed-coordinate and root proof coercions, repairs, the source/graph/forbidden-token audit and nonvacuous q43 tests. No all-test clean build, PR, merge or cyclotomic ideal valuation hierarchy.

**Expected Outcome B:** actual packet-free maximal prime address and unique Tail root orientation, but **not** an FLT7 obstruction or descent. **Outcome C:** a target needs a missing c-unit/nontrivial-root hypothesis; expose precise counterexample, do not hide it. **Outcome A:** only independently checked new noncircular FLT7 restriction beyond an alternative representation.

**STOP after Step 020.** No product formula for all six prime ideals, source-ring-to-source-ring embedding, class group, cyclotomic unit extraction, primitive next tuple or unconditional FLT7 closure.
