# Instruction 042 — FLT7 proof-direction and branch-specific reconstruction decision audit

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-041.md`, `report-041.md`, `frontier-041.md`.
**This is a RESEARCH / SOURCE-DEPENDENCY AUDIT, not a new Lean implementation phase.** Step041 explicitly stopped additional local/capacity examples, and that stop remains binding. The goal now is to choose **one** genuinely new and mathematically plausible FLT7 obstruction or descent-reconstruction contract for a later instruction. No new proof-code owner, new examples, new q-adic powers, new RingHom, new CRT coordinate packet, new numerical countermodels or fabricated theorem at Step042.

## 1. Why a proof-route reset is necessary

Steps 001–041 built many correct and now reusable tools:
- exact GN/GTail focus and degree-seven integer defect identity;
- local q|Q Gap/Tail routing, primitive endpoint units and valuation budgets;
- source-typed Eisenstein E (discriminant −3), seventh-cyclotomic R and common receiving C, actual q-local kernels and ideal-power LOWER support;
- equation-free q²-defect stability;
- finite prime-square congruence aggregation and a strict Archimedean **conditional** zero certificate;
- **actual strict positive primitive focused non-Fermat** examples showing the collective coverage and magnitude inputs of the certificate are independent.

The last two facts must not be misread:

```text
ALL p²|Δ  +  |Δ|<M_Q  ⟹  Δ=0  ⟺  Fermat7Equation.
```

This theorem **concludes** a Fermat equation for a given tuple, whereas the FLT7 goal is **no** positive primitive Fermat tuple. If hEq is already a hypothesis, Δ=0 is immediate and the support/size conditions hold trivially; turning that direction into a contradiction would be circular. An independent proof of full support and a size bound for one already-Fermat triple would merely reprove hEq, not exclude it.

To prove FLT7 by contradiction or descent, the next theorem must instead:
- from a hypothetical `CounterexamplePack x y z` derive **False**, via a genuinely new invariant or incompatible pair of consequences; or
- from a genuine indexed primitive counterexample construct a **new primitive** counterexample with a strictly smaller well-founded global measure, with every branch (including the terminal branch) handled.

Step042 selects a concrete contract matching one of these proof directions. Do NOT implement it yet.

## 2. Real old owners whose contracts must be examined

Read these **actual source files**, not just doc summaries. Record exact declarations, namespace, implicit/explicit arguments and source types with file:line ranges or verbatim short signatures (no unsupported guesses):

```text
DkMath/FLT/Seven/Basic.lean
DkMath/FLT/Seven/CounterexampleRouting.lean
DkMath/FLT/Seven/AwayValuationTransfer.lean
DkMath/FLT/Seven/DescentClosureAudit.lean
DkMath/FLT/Seven/SevenBaseTerminalDescentProvider.lean
DkMath/FLT/Seven/SevenBaseTerminalDescentSeedExclusion.lean
DkMath/FLT/Seven/SevenBaseTerminalExclusion.lean
DkMath/FLT/Seven/SevenBaseTerminalFermatChartResolution.lean
DkMath/FLT/Seven/SevenRamifiedSignedRootDepth.lean
DkMath/FLT/Seven/SevenRamifiedFusionDirectChartObstruction.lean
DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean
DkMath/FLT/Seven/SevenBaseTerminalLiftedReconstruction.lean
DkMath/FLT/Seven/SevenBaseTerminalCellCarryDependency.lean
DkMath/FLT/Seven/Seven.lean  [only if it exists; otherwise DkMath/FLT/Seven.lean]
DkMath/FLT/Seven/docs/STATUS.md
DkMath/FLT/Seven/docs/ROADMAP.md
docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-041.md
```

Also check the *actual* `TraceOneInt (-2)` seventh-axis recipient (\`QuadraticBridge\` or original owner), against the **different** Step034 E=\`TraceOneInt(-1)\` and C=\`QuadraticAlgebra R (-1) 1\`. A mathematical relation between them is NOT a type equality and no unital ring map has been supplied by Steps012–041.

For the original CRT optional avenue, inspect any exact theorem for the **original four-coordinate** `originalReconstructionDefect` versus just the independently centered `integerWeightedDefect`, and which input would actually give a strict magnitude bound. Do not silently substitute one discrepancy for the other.

## 3. Mandatory terminal/lifted/ramified impossibility ledger

Build `source-inventory-042.md` with a compact explicit truth table for each branch. Include **at least these existing checked facts**:

### Terminal exponent ONE

1. In \`SevenBaseTerminalDescentProvider\`,
   \`AwayDescentReconstructionSeed\` is **already proved equivalent** in \`Nonempty\` to the older \`AwayDescentClosureProvider\`. The seed's true fields are \`nextX,Y,Z\`, \`nextNormal:AwayCoordinateNormalForm\`, and \`target_source:AwayExceptionalCarrierSource nextY nextZ (Int.natAbs old.root.snd)\`.
2. In \`SevenBaseTerminalDescentSeedExclusion\`,
   \`no_descentReconstructionSeed_of_exponent_eq_one\` and
   \`no_descentClosureProvider_of_exponent_eq_one\`
   are already actual theorems. A **terminal depth-one seed is impossible** because any such seed forces the old pivot exponent ≥2. Therefore **DO NOT propose constructing a universal closure seed at terminal exponent one**; that target is false, not merely missing.
3. \`SevenBaseTerminalFermatChartResolution\`:
   - Row-**Y** reaches an actual **swapped natural ramified** coordinate chart;
   - Row-**Sum** is contradictory by source modular/endpoint facts;
   - Row-**Z** retains an actual **signed** Fermat chart plus the checked divisibility of its signed gap by seven, but does **not** have the required ramified seventh-power extraction in the discriminant −7 order.
4. The exact Row-Z open proposition is \`AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation hz\`, requiring a genuine
   `root : TraceOneInt (-2)` satisfying
   `cyclotomicSevenToTraceOne (x:ℤ) (-(y:ℤ)) = sevenAxis * root^7`
   under an actual source packet and the Row-Z terminal profile. A proof of this is a substantial arithmetic theorem, not a routine source-type cast. If the extracted root is impossible, a **proved** Row-Z exclusion would be a different legitimate route. Do not assume a root exists or claim its nonexistence without a proof.
5. The Ramified source pathway itself still has its own open global terminal/primitive-descent obligations. “Row-Y reaches ramified” does **not** close FLT7 by itself.

### Lifted exponent TWO OR MORE

6. \`AwayDescentReconstructionSeed.two_le_pivotExponent\` provides **a necessary condition** \`2≤p.exponent\`, not a guarantee of an inhabited seed when the exponent is ≥2.
7. From an inhabited seed, the previously checked \`seed.toClosureProvider\` and \`away_depth_descent_of_reconstructionSeed\` give a genuine **smaller seven-adic carrier**. But the seed still needs an **actual new primitive next triple**, the new away normal form and a source match at the *old* root-second-coordinate carrier; the CRT model and local ideals do not make these fields automatically exist.
8. Determine whether existing stronger \`SevenBaseTerminal...LiftedReconstruction\` and \`...Exclusion\` actually eliminate part of this lifted branch or require still extra integer constraints; never confuse the terminal exponent-one theorem with a lifted-branch contradiction.

### Ramified FUSION

9. \`SevenRamifiedFusionDirectChartObstruction\` already proves the signed extracted-root seventh-power difference has **exact** seven-depth five and **cannot** be a seventh power, so \`SignedFermatSevenChart signedRightRoot (-signedLeftRoot) c\` is impossible. This **rules out a shortcut** using those visible signed roots as a new chart, not the original hypothetical Fermat chart.
10. \`SevenRamifiedFusionStrictDescentFailureBoundary\` proves an internal 7-adic depth drop 5→4, but its \`InternalDepthFourCounterexampleReconstructionObligation\` is **not inhabited** and is explicitly required to turn the internal coordinate into a genuine away primitive counterexample carrier. A numeric depth drop alone is not counterexample descent.

### CRT global residual

11. \`SevenBaseTerminalLiftedReconstruction\` already proves the **original integer** residual coordinates are multiples of \`family.combinedModulus\`. Which original-coordinate bounds, not just independently centered representatives, would make those residuals zero? Verify exact owner and note the independent information needed.
12. \`SevenBaseTerminalCellCarryDependency.fixedFirstResidual_decomposition\` gives a **dependent** expression of each fixed first-coordinate residual in terms of universal and other residuals. Thus another proof of those same nine relations cannot independently force zero unless some new constraint is supplied.
13. Check which existing ROW-\`Y/Z/Sum\` congruences, sign normal forms and “winding” records are already proved; the fact that a packet has a field named \`reconstructionObligation\` is **not** a proof of its inhabitance.

## 4. Rank concrete future proof candidates; no implementation this step

Produce `research-decision-042.md` with **three** clearly distinguished candidates and select ONE for a later Step043 proof attempt, or recommend stopping if none has a plausible independent proof route:

**Candidate I — terminal Row-Z signed arithmetic closure (preferred first to assess):**
- exact input: \`source:CounterexamplePack x y z\` plus \`terminal\` and \`hz:AwaySevenBaseTerminalRowZProfile terminal\`;
- exact missing *number-theoretic* fact: the signed discriminant−7 root extraction **or a contradictory obstruction** to such a signed Row-Z packet;
- check existing signed \`TraceOneInt(-2)\` prime/unit/ideal-power lemmas and precise interaction with \`cyclotomicSevenToTraceOne x (-y)\`; avoid recycling the degree−3 Eisenstein E result;
- a proof that the extraction “follows” from hEq must identify the source factorization and integral integrality/unit conditions, not just use an assumption equivalent to the target.

**Candidate II — lifted-away primitive reconstruction:**
- exact input \`r,p\` with proven 2≤pivot exponent and real \`AwayCubicRoutingPacket\`;
- exact missing nextX/Y/Z, a **new** \`AwayCoordinateNormalForm\` and target source equal to \`Int.natAbs old.root.snd\`;
- identify a proposed explicit algebraic triple map or descending invariant. A smaller natural norm/gap alone is insufficient;
- the theorem must exclude exponent-one terminal from its statement and address how the old and new routes sit in one global well-founded descent system.

**Candidate III — actual CRT original-integer bound leading to a nontrivial terminal contradiction:**
- exact \`originalReconstructionDefect\` or \`integerWeightedDefect\` source, already verified finite modulus M, and true signed original coordinates;
- explicit separate inequality \`abs(residual)<M\` or another new ingredient, not just two centered representatives in unrelated coordinates;
- identify exactly what **contradiction** or reconstruction would follow after residual=0, including Row-Z vs Row-Y. An equality of old coordinates alone is not FLT7 closure.

For each option give:
(a) actual theorem owner/signature;
(b) source ring and target;
(c) what is already proved;
(d) which missing premise is **not** a reformulation of hEq or a false universal seed;
(e) possible new arithmetic technique in precise terms (not “use GN” without an equation);
(f) first falsifiable local lemma for a later Lean step;
(g) how success would feed into **False or genuine counterexample descent**;
(h) why the proposed result is not already proved or ruled out by old owners;
(i) expected difficulty, import cost, focused verification strategy and possible Outcome C.

Do not rank generic “more K^n”, “more shared q43 rows”, “more defect capacity examples” or \`full support+size→hEq\` as candidate global obstructions.

## 5. Deliverables, acceptance and STOP

Produce DOCUMENTATION ONLY under
`docs/dev/GTail-SelectiveGap-FLT7-261009-v0/`:

- `source-inventory-042.md`: actual source-level signatures and branch truth table;
- `research-decision-042.md`: 3 candidates, precise ranking and single chosen Step043 theorem-sized proof target if justified;
- `report-042.md`: results, any false assumptions corrected, exact source links/paths, unresolved premises and why this step adds no Lean theorem;
- `ROADMAP.md`: append one honest post-041 research-decision checkpoint (Outcome B research audit or Outcome C if no plausible target).

There should be **no new production/test Lean module**, no numerical-example catalogue, no source owner/facade edit and no claim of a new public axiom/build. Read source signatures with GitHub and optional scratch \`#check\`/\`#print\` if needed; record command/exit if any actual scratch Lean invocation is made, but do **not** run or claim new full build, suite success or axiom audit for nonexistent new declarations.

The output's essential accepted content is an exact **terminal-impossible versus lifted-open versus Row-Z-signed-open** decision that is correct in source types. Use previously proved Step033 no-E↔R RingHom only to prevent misuse; it is **not** an obstruction to a different discriminant−7 quadratic order.

**Expected Outcome B (research audit):** factual, source-backed selection of an honest global FLT7 proof target with a small noncircular first lemma, or an explicit well-supported finding that no implementable target can yet be chosen. An audit is NOT an Outcome A proof.
**Outcome C:** the first attempted claim is mathematically false or source owners already disprove it; identify it and decline to generate proof code.

**STOP after Step042.** Do not automatically implement the chosen Step043 theorem, construct an impossible terminal seed, assert the signed Row-Z extractor, fill a nonempty old packet by fiat, build another local C-grid or represent the conditional zero certificate as FLT7 impossibility. Further implementation requires a separately scoped post-audit instruction based on the actual research decision.
