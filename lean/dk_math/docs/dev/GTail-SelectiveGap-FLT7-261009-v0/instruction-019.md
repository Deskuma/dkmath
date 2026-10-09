# Instruction 019 — packet-free seventh-cyclotomic residue evaluation from the GTail Tail ratio

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-018.md`, `report-018.md`, `source-inventory-018.md`.
**Scope: Step 019 only — a generic seventh-root-to-existing-degree-six-carrier RingHom, with actual finite-field calibration. No Eisenstein-to-cyclotomic ring embedding, ideal transfer, FLT7 contradiction or descent.**

## Mission

Step 018 established a **nontrivial seventh root**
`r := gtailSevenTailRatio q c g : ZMod q` under `[Fact (Nat.Prime q)]`, `q∤c`, `q∤g`, and `q∣GTail 7 1 g c`. It also established an independent Eisenstein quadratic root t in the same residue field under q∣Q and q∤b.

The repository already contains a degree-six **seventh-cyclotomic integral carrier**

```text
SevenCyclotomicDegreeSixInt.Ring
  = QuadraticAlgebra SevenRealCubicInt (-1) (alpha-1)

SevenRealCubicInt.alpha³ = 2*alpha² + alpha - 1
zeta² = (alpha-1)*zeta - 1
zeta^7 = 1
```

and a **packet-indexed** residue RingHom `SevenCyclotomicDegreeSixInt.localEval` from `QuotientPrimeMuSevenAddress`. That indexed address requires a `RamifiedSignedRootDepthPacket` and divisibility of its signed quotient root. Step 018's neutral r supplies neither. Do **not** fabricate that packet or invoke the existing localEval as if it accepted an arbitrary r.

A valid and more general bridge should construct a *new packet-free evaluation of that actual degree-six carrier* from the bare finite-field root r, in three independently checkable gates:

1. `β := 1+r+r⁻¹` satisfies `β³-2β²-β+1=0`.
2. Evaluating the explicit integral **real cubic** basis at β defines `SevenRealCubicInt →+* ZMod q`.
3. Mapping a quadratic pair `x.re+x.im*zeta` to `evalReal(x.re)+r*evalReal(x.im)` defines a **real ring homomorphism from the actual degree-six cyclotomic carrier** into the same `ZMod q`, with `zeta↦r`.

Then for the Step 018 Tail-side r prove the **concrete oriented linear factor**
`ofReal (c+g) - zeta * ofReal c` maps to zero in `ZMod q`. This is an actual kernel membership in the degree-six ring, not an ideal identity with the separate Eisenstein ring. It is a *new typed input receiver*, not an FLT7 descent.

Outcome B is expected: construction of a residue RingHom and chosen zero linear factor does **not** imply factorization into units, an exact ideal valuation, a class-group theorem or a new Fermat solution.

## Phase 0 — exact inventory and dependency order

Read actual source, theorem statements, and proof prerequisites in:

- neutral `DkMath.Lib.NumberTheory.GTailSevenPairedResidue`, `GTailSevenPrimeOrder`, `GTailSevenResidueIdeal` and `GTailSevenIdealSquareAddress`;
- `DkMath.FLT.Seven.SevenRealCubicInt` (explicit three signed coordinates, multiplication, `alpha_cube` and integral casts);
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier`: actual Ring abbreviation, `ofReal`, `zeta`, `zeta_quadratic_relation`, and already existing `localEval`;
- `DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicPrimeAddress`: `QuotientPrimeMuSevenAddress.beta_cubic_relation` and `evalAlphaRoot`, including the exact generic-looking proof scripts that are **still packet-indexed**;
- existing degree-six `ramifiedEval` at q=7, a separate special characteristic with ζ↦1;
- Mathlib relevant `ZMod` field, inverse, quadratic algebra, RingHom and explicit polynomial identities.

Create `source-inventory-019.md` with the four carriers/types (Eisenstein, real cubic, degree-six, ZMod), exact relations, whether a packet-free receiver already exists, likely minimal dependency closure and unsupported maps. Existing packet-indexed code **must not be modified** merely to get a private lemma or force a match. Avoid importing the full `DkMath.FLT.Seven` facade; only source owners required.

## Phase 1 — neutral seventh root to real-cubic polynomial

Create a narrow **neutral** owner, e.g.
`DkMath/Lib/NumberTheory/GTailSevenRealTraceResidue.lean`, importing Step 018 plus only needed Mathlib.

For prime q (Fact), `r:ZMod q`, and hypotheses

```text
hr0 : r≠0
hr7 : r^7=1
hr1 : r≠1
```

define `beta(r)=1+r+r⁻¹` and prove

```text
beta(r)^3 - 2*beta(r)^2 - beta(r) + 1 = 0.
```

Reuse Step 018's `seven_geom_sum_eq_zero_of_pow_eq_one` and the exact algebraic calculation pattern already in `QuotientPrimeMuSevenAddress.beta_cubic_relation`. An algebraic method: expand (after clearing nonzero denominator) and reduce the resulting polynomial via the **seven-term** geometric sum. Do not treat the polynomial relation as an axiom or assume β equals some existing packet's beta.

Consider splitting the proof into generic `CommField` algebra with explicit hr0/hr7/hr1, but use the smaller `ZMod q` statement if it avoids a new general-purpose hierarchy. No FLT owner is imported into `DkMath.Lib`.

**Mandatory numeric calibration:** q=43,r=11, r⁻¹=4, beta=16, and

```text
16^3 - 2*16^2 - 16 + 1 = 0 in ZMod 43.
```

Boundary: r=1 in ZMod43 satisfies r^7=1 but beta=3 and the cubic value equals 7≠0. This protects the nontrivial-root premise. **Do not claim r=1 universally cannot define an evaluation:** q=7 is a distinct ramified characteristic where beta=3 satisfies the cubic modulo 7 and an existing q=7 evaluation is already implemented.

## Phase 2 — actual real-cubic RingHom, no signed packet

Under the same r root hypotheses, define a genuinely bundled

```text
evalRealFromSeventhRoot :
  SevenRealCubicInt →+* ZMod q
```

on arbitrary signed integral triple `x=⟨x0,x1,x2⟩` by

```text
(x0:ZMod q) + (x1:ZMod q)*beta(r) + (x2:ZMod q)*beta(r)^2.
```

Prove all RingHom laws from **actual** `SevenRealCubicInt.fst/snd/thd` addition/multiplication and Phase 1's β cubic relation. The existing `evalAlphaRoot` proof is a usable **source pattern**, but its private packet proof cannot be silently applied to neutral r.

Prove:

```text
evalRealFromSeventhRoot r (...) SevenRealCubicInt.alpha = beta(r)
evalRealFromSeventhRoot r (...) ((n:ℤ):SevenRealCubicInt) = (n:ZMod q)
```

No new theorem stating every seventh root is represented by a signed-depth packet. A failed cubic RingHom proof is an honest gating result: stop before Phase 3 and report the exact missing identity.

## Phase 3 — actual degree-six cyclotomic RingHom and linear factor kernel

In a new **FLT/cyclotomic carrier owner** (not neutral Lib), suggested
`DkMath/FLT/Seven/GTailCyclotomicLocalEval.lean`, import only the narrow existing `SevenRamifiedFusionCyclotomicDegreeSixCarrier` source and the neutral Phase 1 module (plus the Phase 2 real-cubic owner), and build

```text
evalCyclotomicFromSeventhRoot :
  SevenCyclotomicDegreeSixInt.Ring →+* ZMod q
```

via

```text
x ↦ evalReal(x.re) + r*evalReal(x.im).
```

The multiplication proof must use **both** the verified cubic hom and the actual quadratic carrier relation

```text
r² - (beta(r)-1)*r + 1 = 0
```

derived from `beta=1+r+r⁻¹` and r≠0. Verify the precise signs `QuadraticAlgebra R (-1) (alpha-1)`. The existing packet-indexed `localEval` uses the same kind of relation; do not mistake its source packet dependency for an available bare-root proof.

Prove endpoint equations:

```text
evalCyclotomicFromSeventhRoot r (...) zeta = r
evalCyclotomicFromSeventhRoot r (...) (ofReal x) = evalRealFromSeventhRoot r (...) x
evalCyclotomicFromSeventhRoot r (...) (ofReal alpha) = beta(r)
```

If an existing QuadraticAlgebra universal \`lift\` is easier, use it **only with the checked base and quadratic relations**.

For `r=gtailSevenTailRatio q c g` with `q∤c`, `q∤g` and `q∣GTail 7 1 g c`, derive the root hypotheses from Step 018 (q≠7 may be retained if needed to express nontrivial order). Then prove the actual degree-six kernel membership:

```text
F(c,g) := ofReal ((c+g : ℕ) : SevenRealCubicInt)
            - zeta * ofReal ((c : ℕ) : SevenRealCubicInt)

evalCyclotomicFromSeventhRoot r F(c,g) = 0
F(c,g) ∈ RingHom.ker (evalCyclotomicFromSeventhRoot r ...)
```

The root factor is **specifically** `(c+g)-ζ*c` because `r=(c+g)/c`. Do not silently use `a−ζ*b` or a signed-left/right packet variable. This is a legitimate coordinate-specific vanishing factor, **without** claiming it equals one of the existing signed-depth `cyclotomicDegreeSixCarrier` packets.

Optional, only when low cost: prove this kernel maximal from surjectivity (integer residues lift) and the prime-field codomain. This is a separately verified extra result, not required to claim an ideal *kernel*. **Do not** assert the kernel is identical to a previously existing packet-indexed prime ideal without proving the equality of evaluation maps and their inputs.

## Phase 4 — full nonvacuous tests and source comparison

### Actual neutral Tail instance

At q=43, a=5,b=8,c=9,g=4:

- Step 018: t=37, r=11 and both nontrivial roots, q|Q and q|T; exact Fermat7 equation **false**;
- Phase 1: r⁻¹=4, β=16, cubic relation zero;
- Phase 2: real α generator evaluates to 16;
- Phase 3: degree-six ζ evaluates to 11, real α to 16; the actual element
  `ofReal 13 - zeta * ofReal 9` maps to `13-11*9=0 mod43`;
- kernel membership obtained from new `RingHom`, not a finite shortcut;
- existing separate Eisenstein map at t=37 sends `gtailSevenNormCoord 5 8` to zero. The two homs share codomain `ZMod 43` but **do not constitute a map between their source rings**.

### False or missing-premise controls

- r=1 at q=43: r^7=1 but β=3 fails the cubic polynomial. This rules out dropping `r≠1` from the generic receiver.
- q=13,g=13,c=30 Gap branch: r=1, q∤T; no nontrivial seventh-root receiver is licensed by q|Q alone.
- q=3 repeated Eisenstein root and q=5 inert Eisenstein case from previous steps remain separate **degree-two** phenomena.
- q=7 existing ramified ζ↦1 is **not** a counterexample to the new nontrivial-root-only API; a nontrivial seventh root does not exist in `ZMod 7`.

### Existing code compatibility

Compare the new \`evalRealFromSeventhRoot\` and \`evalCyclotomicFromSeventhRoot\` with the **packet-indexed** \`QuotientPrimeMuSevenAddress.evalAlphaRoot\` and \`SevenCyclotomicDegreeSixInt.localEval\` by exact formula/sign and hypothesis differences. An *optional extensional comparison theorem* requires **an actual equality between their scalar roots** on overlapping packet hypotheses. Do **not** construct a \`RamifiedSignedRootDepthPacket\` from the neutral q43 calibration; the source provides no such construction.

## Phase 5 — deliverables, validation and stop

Suggested files and direct tests:
- `DkMath/Lib/NumberTheory/GTailSevenRealTraceResidue.lean` and `DkMathTest/NumberTheory/GTailSevenRealTraceResidue.lean` — **neutral β algebra only**;
- `DkMath/FLT/Seven/GTailCyclotomicLocalEval.lean` and `DkMathTest/FLT/Seven/GTailCyclotomicLocalEval.lean` — **both actual real-cubic and degree-six RingHoms**, because their source carrier is FLT7-specific; adjust owner placements only if neutral import discipline stays intact;
- `source-inventory-019.md`, `report-019.md`, accurate post-018 `ROADMAP.md` update.

Implementation order: **neutral β relation first**, focused build/test; **real-cubic RingHom second**, focused build/test; **degree-six RingHom third**, focused build/test; **kernel receiver fourth**, focused test. If the base RingHom takes longer than intended or the heavy carrier closure cannot build in the local environment, report a PARTIAL gate with the exact blocker rather than adding a surrogate axiom or hiding proofs behind preexisting FLT7 closure.

Run only sequential incremental focused targets with process-local `LEAN_NUM_THREADS=2` and previous Step 018/017 regression when affordable. Record every final exit code, source theorem signatures, signed coordinate conventions, new public `#print axioms` results, forbidden-source placeholder checks and neutral→FLT import-direction scan. No full clean/all-test run, existing packet owner edits, new public facade, PR or branch merge.

Outcomes:
- **B expected:** nonvacuous bare-Tail-root beta cubic and true typed \`RingHom\` into the shared field from the **existing degree-six cyclotomic ring**, with a concrete zero linear factor but no new unit/class/descent obstruction.
- **C:** missing root condition, wrong quadratic sign, missing cubic relation or infeasible compile/import closure; retain the strongest correctly checked earlier gate with a source-indexed counterexample/blocker.
- **A:** a genuinely new independently verified arithmetic FLT7 restriction beyond the already known order-21 or a mere typed residue representation. A RingHom or its kernel **alone** is not A.

**STOP after Step 019.** No Eisenstein→cyclotomic integral RingHom, ideal equality between source rings, principalization, cyclotomic unit-power lifting, positive FLT7 descent or unconditional closure.
