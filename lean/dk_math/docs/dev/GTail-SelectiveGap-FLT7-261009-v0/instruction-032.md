# Instruction 032 — GTail global-balance equivalence and a strong local-compatibility countermodel

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-031.md`, `report-031.md` and `source-inventory-031.md`.
**Scope: Step 032 only — identify the precise missing GLOBAL equality between native focused GTail and an exact FLT7 equation, and prove that the currently checked local Eisenstein/cyclotomic/norm/valuation readouts, even with focused geometry, need not recover that equality.** No attempt to construct a new Fermat solution, no misleading false impossibility, no E→R integral RingHom, signed-depth packet, or K⁵/all-k extension.

## Motivation: what Steps 010–031 actually delivered

Actual native natural notation:
```text
Q(a,b) := a^2+a*b+b^2
T(c,g) := DkMath.CosmicFormula.GTail 7 1 g c
hfocus : a+b=c+g
hEq : Fermat7Equation a b c
```

Checked source facts:
- `GTailBridge.gtail_seven_shell`: under **hfocus alone**, `g*T+c^7=(a^7+b^7)+7*a*b*(a+b)*Q^2` in ℕ.
- `GTailBridge.gtail_seven_eq_of_fermat7Equation`: under **hfocus+hEq**, the exact scalar balance `g*T=7*a*b*(a+b)*Q²`.
- `GTailPrimeAllocationAudit` Step010: positive primitive hEq/hfocus and prime q≠7 dividing Q yield the exclusive gap/Tail support and doubled local valuation budget.
- `GTailFocusedNormCyclotomicDepthBridge` Step031: on the q-Tail branch, q∤g gives even scalar q-depth; \`F_i∈K³ ↔ F_i∈K⁴\` follows via Steps029–030. The true integral carriers remain distinct:
  `E=TraceOneInt (-1)` with `α=gtailSevenNormCoord a b` and prime ideals P_t,
  versus `R=SevenCyclotomicDegreeSixInt.Ring` with six factors F_i and K_j.
- A shared `ZMod q` and the scalar Q,T do not supply an E→R map, an ideal equality P=K, or a signed seventh-root depth packet.
- \`DescentClosureAudit.AwayDescentClosureProvider\` requires a **new primitive CounterexamplePack, its away valuation route, and a precise carrier_match** to make descent. A smaller scalar or a locally constrained sixth-degree prime factor is not the provider.

The key logical question at the next frontier is **what additional exact information would let the local necessary conditions imply the original global equality?** Do not simply add more local K^k theorems: finite congruence and q-adic depth conditions can be fully compatible without a positive Fermat solution.

## Phase 0 — source and hypotheses audit before coding

Inspect:
- `DkMath.FLT.Seven.GTailBridge`, exact type and proof of `gtail_seven_shell`, `gtail_seven_eq_of_fermat7Equation` and `Fermat7Equation`.
- `DkMath.FLT.Seven.GTailNormReadoutAudit.focused_gtail_eq_norm_square` and \`DkMath.Lib.NumberTheory.GTailSevenNormReadout.norm_gtailSevenNormCoord_sq\`. Compare the NAT scalar balance to the INT norm balance; correct casts are essential.
- `DkMath.FLT.Seven.GTailConstraintAudit.fermat7_focused_bounds` and `focused_gap_lt_coordinates` (the original strict focus inequalities use positive a,b AND hEq; a numeric witness can satisfy their **conclusions** without hEq).
- `GTailPrimeAllocationAudit` and `GTailFocusedNormCyclotomicDepthBridge` for exact scalar budget and all derived units.
- Step017 neutral Eisenstein `gtailSevenNormCoord_split_square_address`, Step025 selected K² iff, Step029 K³ iff and Step030 K⁴ iff; check concrete q43 root/slot access without dependent-proof-term rewriting.
- \`DkMath.Lib.NumberTheory.GTailSevenPairedResidue\`: coexistence of distinct cubic and seventh roots in ZMod q never gives an integral E→R hom.
- \`DkMath.FLT.Seven.DescentClosureAudit.AwayDescentClosureProvider\`, \`SevenRamifiedSignedRootDepth.RamifiedSignedRootDepthPacket\`, \`SevenRamifiedFusionOrientedCarrierValuationOwnership\` and \`docs/STATUS.md\`: **read signatures/source only**, do not import/inhabit/modify the old packet. Record exact required reconstruction data and differences from the present natural focused tuple.

Write `source-inventory-032.md` including a **necessary-vs-sufficient contract table**:
  (A) original exact FLT7 equation,
  (B) focused addition/inequalities/primitive geometry,
  (C) prime q and residue roots/orders,
  (D) scalar budget/evenness,
  (E) Eisenstein E-ideal square and cyclotomic R-ideal powers,
  (F) exact scalar balance,
  (G) old signed-depth/descent packet.

For each row identify source carrier/type, actual theorem name, premises, data lost, and whether it is sufficient for Fermat7Equation (under hfocus). The intended source finding is **F is equivalent to A under B's additive relation**, whereas B/C/D/E do not by themselves supply F. Do NOT rewrite one row as a stronger theorem based on intuition.

Suggested small new FLT owner:
`DkMath/FLT/Seven/GTailGlobalBalanceFirewall.lean`
with direct import of Step031 and only targeted extra exact owners not already in its closure. Tests:
`DkMathTest/FLT/Seven/GTailGlobalBalanceFirewall.lean`.

No broad FLT facade, old signed packet/valuation import, ring definition edits, new universal impossibility lemma or public repository status change.

## Phase 1 — prove exact natural scalar balance IFF the actual Fermat equation

**Main proof gate:** for *arbitrary* natural a,b,c,g and ONLY the additive focus assumption `a+b=c+g`, prove

```text
Fermat7Equation a b c
  ↔ g * GTail 7 1 g c
     = 7*a*b*(a+b)*(a^2+a*b+b^2)^2.
```

Suggested name: `fermat7Equation_iff_focused_scalar_balance`.

Forward is the preexisting public \`gtail_seven_eq_of_fermat7Equation\`.
Reverse uses the **actual NAT semiring** \`gtail_seven_shell\` (whose equality is unconditional in Fermat); rewrite the scalar equality to obtain \`I+c^7=(a^7+b^7)+I\`, then use valid natural addition cancellation or \`omega\`, respecting the exact side/order of the summands. No signed subtraction or hidden positivity requirement is necessary.

This is an exact **equivalence/circularity firewall**, not a new FLT theorem: reconstructing the balance from only prior q-local necessary conditions would be as hard as reconstructing the original Fermat equation under focus. Do NOT present the reverse direction as a contradiction or independently new obstruction.

Additional typed IFF target, if Lean checks with short cast normalization:
```text
Fermat7Equation a b c
  ↔ (g:ℤ) * ((GTail 7 1 g c:ℕ):ℤ)
       = 7*(a:ℤ)*(b:ℤ)*((a+b:ℕ):ℤ)*
           norm ((gtailSevenNormCoord a b : TraceOneInt (-1))^2)
```
under the **same hfocus and no extra premises**.

Forward reuses `focused_gtail_eq_norm_square`, reverse reduces the typed norm to the original Q² natural cast via `norm_gtailSevenNormCoord_sq` and injectivity of \`Nat.cast : ℕ→ℤ\`, then applies the new NAT iff. Do NOT equate the norm-carrying E element α² with any degree-six R factor F_i.

If this optional typed equivalence is awkward for theorem inference, keep it as a proved standalone lemma with exact casts, or report the limited transport problem. The NAT iff is mandatory.

## Phase 2 — satisfiable *strong* q43 local-compatibility witness

A deliberately selected independently calculated candidate, **NOT YET Lean evidence**:

```text
q = 43
(a,b,c,g) = (1166, 1857, 1858, 1165)
a+b = c+g = 3023
gcd(a,b) = 1
0 < g < a,b < c < a+b
Q = a²+ab+b² = 6,973,267
T = GTail 7 1 g c = 1,914,732,507,483,487,090,603
43 | Q,       43² ∤ Q
43² | T,      43³ ∤ T
43 ∤ a,b,a+b,c,g
v43(g)=0, v43(Q)=1, v43(T)=2
v43(g)+v43(T)=2*v43(Q)
3|42, 7|42, 21|42
Eisenstein root t = 37 (same mod43 residues as a=5,b=8)
Cyclotomic Tail root r = 11 (same mod43 residues as c=9,g=1165)
BUT:
  ¬ Fermat7Equation a b c
  ¬ (g*T = 7*a*b*(a+b)*Q²).
```

Numbers here were checked by independent external integer arithmetic, not by the reviewer running Lean. **Codex must verify every number, divisibility, coprimality, strict inequality, scalar budget and negative statement in Lean.** If any candidate is false, find and report a corrected genuinely satisfying tuple, rather than using a fictional Fermat input.

This is a stronger negative control than Step031's (5,8,9,4): it satisfies **the complete additive focus relation and strict geometric bounds**, in addition to primitive positivity, prime/unit guards, quadratic/Tail support and *the exact same doubled scalar valuation budget*. It is NOT a Fermat counterexample; it fails the Fermat equation and (equivalently by Phase1) the global scalar balance.

Prove in a manageable compact numeric test:
- positive a,b, c>max(a,b), c<a+b, 0<g<min(a,b), a+b=c+g, Nat.Coprime a b;
- q43 units a,b,a+b,c,g and q43 support for Q and T, exact q-valuations 1 and 2, natural doubled budget;
- if practical a bundled `∃ a b c g, ... ∧ ¬Fermat7Equation ...`, otherwise keep a small suite of individual direct examples and one top-level implication counterexample with only the premises you truly verified;
- use the new generic Phase1 iff to derive balance **failure** from \`¬Fermat7Equation\`, and separately check the concrete integer inequality if reasonable;
- the equality `g*T=7ab(a+b)Q²` and Fermat input must not be marked as simultaneously satisfying. This is the **precise missing global equation**, not a failed q-local congruence.

### Actual source-typed ideal regressions on the same tuple

Check if inexpensive using the existing generic theorems:
- `t = gtailSevenResidueRoot 43 1166 1857 = 37`;
- `α=gtailSevenNormCoord 1166 1857 : TraceOneInt (-1)` and the Step017 *actual* Eisenstein ideal result \`α²∈P_37²\`, excluding conjugate P_7 and the scalar Eisenstein ideal;
- `r = gtailSevenTailRatio 43 1858 1165 = 11`;
- for **all** i:Fin6, `F_i(1858,1165) ∈ K_(sixInverseSlot i)^2` and **not** in `K_(sixInverseSlot i)^3` by Step025/029 exact generic iff and q²|T, q³∤T;
- six chosen root indices remain [0,3,4,1,2,5], with all wrong slots excluded at first power;
- q43’s two roots coexist in **the same ZMod43**, but `P_t : Ideal E` and `K_j : Ideal R` remain separate types.
- the Step031 full Fermat-facing theorems do **not** apply to this numeric witness, precisely because hEq is false, even though **their local scalar conclusions happen to be satisfied**.

If dependent RingHom root-certificates or large natural \`decide\` runs threaten build budget, split checks into typed local sublemmas and prioritize the mandatory Phase1 iff and core scalar/geometry witness. Record any numerically expensive test and leave irrelevant checks optional; do not override global heartbeats or run a full-suite build.

## Phase 3 — exact FLT7 descent reconstruction ownership audit

After the Lean-positive local compatibility witness is built, source-trace the **actual missing downstream reconstruction statement** rather than predicting an impossible ring map. Write `frontier-032.md` (or a section in `report-032.md`) with at least:

1. \`AwayDescentClosureProvider x y z p\` **requires** nextX,nextY,nextZ naturals, a new `CounterexamplePack nextX nextY nextZ`, `AwayValuationTransferPacket nextX nextY nextZ` and the actual signed carrier equality. A strict fall of a scalar valuation alone is not enough.
2. \`RamifiedSignedRootDepthPacket\` requires the whole balanced real-cubic split, exact signed root identities, signed coprimality, specialized gap/quotient roots and their 7-adic unit conditions, and the actual normalized equation. Nothing in Steps 018–031 constructs this packet from a bare q≠7 natural Tail root.
3. \`SevenRamifiedFusionOrientedCarrierValuationOwnership\` owns conditional oriented local exponents **for that old signed packet carrier**, not the new F_i from an arbitrary natural focused tuple. Do not identify the two elements, roots, prime ideals or integer valuation budgets by shared names/codomains.
4. Explicitly tabulate all maps and equalities currently **proved**: natural/ℤ focused balance, E norm and E→ZMod43 evaluation, R factor product and R→ZMod43 evaluation. Underline the data discarded by scalar norms, by finite-field reduction and by the loss of source ring type.
5. A negative information finding **is not a proof of impossibility** to ever build a carrier bridge. It is a precise statement that the *current source contracts do not inhabit the missing provider*. If a new algebraic construction is proposed, list its exact source type, target type, image of generators, preserved relations, integrality and which existing owner would consume it; **do not implement** it in Step032 without separate authorization.

Optional narrow contract table in `frontier-032.md`:
`[current premise], [typed conclusion], [countermodel sensitivity], [extra proof needed], [owner]`.
No unsupported equality of q-local root kernels, and no claim that a root of degree three in ZMod q has a canonical expression in the selected seventh root.

## Phase 4 — tests and protective boundaries

Include:
- Phase1 universal theorem signature tests for the natural iff and, if compiled, typed integer norm iff; no fictional Fermat example.
- The **actual** positive primitive focused q43 non-Fermat witness, visibly satisfying *local* hypotheses but not the exact global balance.
- Old (5,8,9,4) q43 sample, which has both roots but even fails additive focus; show the new witness really strengthens it.
- q43 c9,g32598 exact K³\\K⁴ example still fails the focused sum with a5,b8; never use it as a contradiction to the Step031 conditional theorem.
- q3 Eisenstein repeated-root, q7 no nonidentity scalar root, q13 Gap-only, zero-coordinate Fermat equation, each with the exact premise it violates.
- Verify that when hEq is assumed in the universal theorem, the full exact scalar balance returns immediately, while from the **weaker local** hypotheses the numerical countermodel blocks the reverse implication.
- Maintain integer norm distinct from element-level divisibility and the two distinct ideals.

## Deliverables, builds, classification, STOP

Expected:
- `DkMath/FLT/Seven/GTailGlobalBalanceFirewall.lean`;
- `DkMathTest/FLT/Seven/GTailGlobalBalanceFirewall.lean`;
- `source-inventory-032.md`, `report-032.md`, optional `frontier-032.md`;
- truthful post-031 `ROADMAP.md` append, with previous historical checkpoints unchanged.

Gates:
1. source-overlap audit and **mandatory exact natural balance iff**;
2. optional typed integer norm balance iff;
3. positive primitive focused q43 local compatibility witness, its q-adic budget and non-Fermat negative control;
4. actual two-ring ideal readout examples under the witness if computationally feasible;
5. old descent-provider required-field frontier ledger and focused regression tests.

Build sequential focused new source/test and Step031/030 plus GTailBridge direct regressions using process-local `LEAN_NUM_THREADS=2`. Record exact source/test/selected regression commands and exits, any intermediate elaboration fixes, all new public \`#print axioms\`, import DAG/neutral→FLT audit, forbidden token and whitespace/style checks. No all-suite rebuild, proof-resource-limit hacks, old packet/owner edits, new facades, PR, rebase or merge.

**Outcome B expected:** a correct NAT (and ideally typed INT norm) Fermat-balance iff plus a genuinely **satisfiable positive primitive q43 local-but-non-Fermat countermodel** demonstrating the precise logical insufficiency of previously built local readouts. This is an information/circularity firewall, not an FLT7 descent.
**Outcome C/partial:** wrong numeric candidate, unexpected hidden hypotheses, inaccessible old APIs or a mistaken reverse direction: keep the strongest compiled lemmas, produce an actual counterexample or missing-lemma report; never invent a Fermat tuple or infer contradiction.
**Outcome A:** only a noncircular new restriction on hypothetical positive primitive FLT7 solutions beyond source-checked Step010/011/old signed packets. A tautological restatement of hEq as a balance, or a local satisfiability witness, remains B.

**STOP after Step032.** Do not automatically create a new FLT7 descent provider, all-k valuation, Eisenstein→cyclotomic RingHom, class/unit/principalization theory, signed-root packet or contradiction. The subsequent plan should be chosen **after** comparing the actual missing global equality and the old descent-provider reconstruction fields to any proposed genuinely new algebraic input.
