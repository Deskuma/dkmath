# Review 041 — genuine focused capacity-premise separation and second native grid address

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 041 COMPLETE / Outcome B / STOP041 honored**

## Scope and verification

Statically inspected the actual pushed GitHub source and test:
- `DkMath/FLT/Seven/GTailFocusedCapacityIndependence.lean` (77 lines);
- `DkMathTest/FLT/Seven/GTailFocusedCapacityIndependence.lean` (231 lines);
- `report-041.md`, `source-inventory-041.md`, `frontier-041.md`;
- previous Step040 full-support conditional zero certificate, Step039 signed defect, Step032 focus balance iff and Step035/037 actual common C kernel APIs.

**This is GitHub static source/proof-route inspection, not an independently executed Lean build.** Codex reports final source05/test07 and Step040/039 direct regression08/09 exit0/warning0, 40 examples, public theorem `#print axioms` each within standard `[propext,Classical.choice,Quot.sound]`; no full clean suite, new axiom or global resource workaround is claimed. Intermediate source01 duplicated primeFactors rewrite and test03 metavariable inference failures were fixed by narrowing rewrites and explicit q/a/b arguments. The old files and historical reports were reportedly unchanged; ROADMAP append only.

## Mathematical check of the public theorems

1. `exists_full_support_without_size` is a genuine existential of a **positive primitive, coprime, strict focused natural tuple** with **all** actual prime factors p of Q satisfying `(p:ℤ)²|Δ`, but **without** `Δ.natAbs<M_Q`, and also `¬Fermat7Equation`. Actual witness (a,b,c,g)=(13,35,46,2) and signed Δ=−371,415,611,824; Q=1849=43²; `Nat.primeFactors Q={43}` with actual primality certificate, M_Q=1849. Its positive primitive geometry and non-Fermat status are checked in the source/test. This Q is **not squarefree**, so `M_Q<Q²` and the modulus is the square of the *radical* rather than Q².
2. `exists_size_without_full_support` is a separate genuine existential with the **same strong focused geometry** and `Δ.natAbs<M_Q`, but **without** collective q-square support and with `¬Fermat7Equation`. Actual witness (a,b,c,g)=(1497,2797,2802,1492); Q=14,251,327=37·385171 with both factors certified prime, M_Q=203,100,321,260,929, Δ=−179,820,312,066,002. Both 37 and 385171 fail even first-power divisibility of Δ. The proof of `¬hsupport` displays an actual missing prime, not a spurious negation of the combined zero certificate.
3. The test proves negative signed defect values and absolute bounds with `Int.natAbs`, retains the true exact balance iff under additive focus, and shows all four relevant truth-table patterns: old Tail/Gap non-Fermat examples fail both support and size; new A has support only; new B has size only; support+size with a non-Fermat tuple is ruled out by Step040's **previously conditional** theorem.
4. New A has actual natural Q/T native roots t=7 and r=16 in ZMod43, with q43²|T and b,c,g units; `nativeKernel 13 35 46 2 = GTailPrimeGrid.M 1 4` is a real equality of ideals in **the unchanged common C**, proven by reducing both bundled evaluation RingHoms on arbitrary C coordinates and applying `congrArg RingHom.ker`. This genuinely differs from older selected pair (37,11). It does not equate the embedded E/R source elements or their prime ideals across ring types.
5. A's `v43(Q)=2,v43(T)=2,v43(g)=0` explicitly **violates** the Step031 equation-conditioned exact budget `v_q(g)+v_q(T)=2v_q(Q)`; Step039's weaker q²-defect route is applicable, but the hEq-conditioned Step031 valuation theorem is correctly not invoked. B's magnitude alone gives no q-square defect support or canonical Tail kernel.
6. The production module exports exactly **two** theorems, uses private support certificates and only direct-imports Step040. The test has 40 examples; its arithmetic identities, primeFactors factorization, new grid equality and old controls have report-recorded successful focused elaboration and two public standard axiom audits. No forbidden proof shortcut, neutral Lib→FLT cycle, broad ABC owner or signed-descent packet is added.

## Essential proof-direction boundary

**APPROVED — Outcome B.** The Step040 `full_quadratic_defect_zero_certificate` is an implication from **all prime-square support plus a strict global size bound to `Fermat7Equation`**, *not* to `¬Fermat7Equation`. Even if those inputs were independently proved for a positive primitive focused tuple, the result would **certify a Fermat solution for that tuple**, not by itself rule one out. Proving the two inputs as consequences of an already assumed Fermat equation would be vacuous, since `Δ=0` from hEq already gives all congruences and the size bound for positive M. This directionality must be preserved before selecting further FLT7 work.

The existential witnesses prove these assumptions do not follow **separately from basic positivity+primitivity+focus alone**. They do not rule out a stronger source theorem conditioned on other genuinely new arithmetic properties.

## New source-checked post-041 reconstruction assessment

Reviewing actual older FLT7 owners revealed **more specific frontiers** than the repeated reference to the original `AwayDescentClosureProvider` alone:

- `SevenBaseTerminalDescentProvider.AwayDescentReconstructionSeed` already reduces the old provider to nextX/Y/Z, `nextNormal : AwayCoordinateNormalForm`, and an exact `AwayExceptionalCarrierSource` matching `Int.natAbs old.root.snd`. The source proves `Nonempty seed ↔ Nonempty AwayDescentClosureProvider`; there is no need to reinvent those type fields.
- Crucially, `SevenBaseTerminalDescentSeedExclusion.no_descentReconstructionSeed_of_exponent_eq_one` **proves that no such seed or closure provider exists on an exponent-one terminal packet**. Demanding a universal seed or terminal-route descent theorem is **mathematically false** on that branch. It remains a possible construction target only in branches for which its actual necessary pivot-depth premises hold, not an automatically available closure.
- `SevenBaseTerminalFermatChartResolution` already has a **terminal chart decision**: Row-Y goes to the existing natural ramified chart after swapping summands, Row-Sum is contradictory, while Row-Z has a **specific outstanding signed quadratic-root extraction** `AwaySevenBaseTerminalRowZSignedRamifiedArithmeticObligation` in `TraceOneInt (-2)` (the discriminant −7 order), not the Eisenstein `TraceOneInt (-1)` order used in Steps012–041.
- `SevenRamifiedFusionDirectChartObstruction` proves the visible signed extracted-root difference has exact 7-adic depth five and **is not a seventh power**; thus the tempting direct `SignedFermatSevenChart signedRightRoot (-signedLeftRoot) c` is already impossible. This obstruction must not be misinterpreted as a contradiction to the *original* hypothetical Fermat tuple.
- `SevenRamifiedFusionStrictDescentFailureBoundary` has an internal 7-adic depth drop from five to four but *explicitly lacks reconstruction* of a new primitive away route. The associated named obligation is not inhabited.
- `SevenBaseTerminalLiftedReconstruction` already proves its true original-integer-coordinate CRT reconstruction defect is divisible by a combined modulus. It does **not** furnish an independent strict absolute bound for all four unbounded original coordinates; centered *representatives* by themselves do not imply this.
- `SevenBaseTerminalCellCarryDependency.fixedFirstResidual_decomposition` proves the nine fixed first-coordinate equations algebraically depend on the universal/endpoint/root residuals, so recycling those equations alone cannot create a new independent global obstruction.

These findings suggest a **source-first research selection** after STOP041. Do not automatically extend Step040's support/capacity calculations into another local q-depth or repeat impossible terminal-seed construction.

## Suggested Step042

**Docs-only, no new Lean theorem or example catalogue:** rigorously inventory the real branch-specific old terminal/lifted/ramified reconstruction obligations, prove-path dependency overlap, and select **one** honest, noncircular and mathematically viable Step043 proof target. Especially assess the Row-Z `TraceOneInt(-2)` signed seventh-root extraction, the lifted-pivot seed conditioned on exponent≥2, and the original CRT integer-defect global-bound path with its actual magnitude premises.

Record, for each option: exact source theorem/signature, active source ring, whether already proved or refuted, minimal missing premise, false shortcuts and whether a proposed theorem could ever conclude `False` or a genuinely smaller primitive counterexample rather than simply hEq. Do not supply a `nonempty` packet as an assumption or use the existence of a signed chart as its own proof of a contradiction.

No PR/rebase/merge, façade promotion, new ideal grid, signed-root packet construction, automatic FLT7 closure or new repetitive capacity witness work authorized.
