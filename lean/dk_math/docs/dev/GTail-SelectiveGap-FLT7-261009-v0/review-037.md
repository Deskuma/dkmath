# Review 037 — generic-prime actual native Q/T common receiver

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 037 COMPLETE / Outcome B**

## Source and verification limit

Statically inspected on the pushed feature branch:
- `DkMath/FLT/Seven/GTailFocusedGenericPrimeReceiver.lean` (302 lines);
- `DkMathTest/FLT/Seven/GTailFocusedGenericPrimeReceiver.lean` (269 lines);
- `report-037.md`, `source-inventory-037.md`, `frontier-037.md`;
- actual Step034–036 E/R injections into C and prime join, Step013/023 source root and cyclotomic factor APIs, Step017 Eisenstein square, Step025 R square, Step010/031 conditional valuation budget, Step032 exact global balance and `DescentClosureAudit.AwayDescentClosureProvider` (for scope comparison).

**Static GitHub proof-route review, not an independently executed Lean build.** Codex reports final focused source07 and test08 both exit0/warning0, direct Step036/035 regression09/10 exit0/warning0, 59 examples and all 24 public declarations' `#print axioms` within `[propext, Classical.choice, Quot.sound]`. Intermediate source03 failed at an underspecified `Even` witness and test05 failed from local notation/implicit certificate elaboration; exact proof-independent repairs are documented. No full clean repository build or all-suite regression is asserted.

## Mathematical proof and ownership audit

1. `evPair` is a **genuine unital** `Carrier→+*ZMod q` for prime q with *supplied* quadratic root t and nonzero, nonidentity seventh root r, retaining the same actual quadratic coefficient carrier C as Step034. Multiplicativity is checked from `QuadraticAlgebra.re_mul/im_mul` and t²−t+1=0, not an assumed R-valued t or a fictional E→R map.
2. `evPair_comp_eisenstein` and `evPair_comp_cyclotomic` are genuine RingHom equalities to the **existing** source evaluations. Surjectivity is inherited from the actual R coefficient evaluation. The kernel is maximal/prime; its `Ideal.comap` to E is the Eisenstein residue ideal and to R is the distinct typed seventh-root kernel.
3. `pairedKernel_eq_sup` directly generalizes Step036's **single-pair coordinate split** at the natural residue representative `t.val`, showing exact sum of the two separately extended source ideals for arbitrary *supplied* roots. It does not create a generic Fin2×Fin6 grid, a full spectrum classification or any power equality.
4. `evPair_43` and `pairedKernel_43` identify the symbolic construction with the **exact unchanged** Step034 eval43 and M43, not merely with isomorphic structures. Tests independently check q127: t=20 satisfies t²−t+1=0 modulo 127 and r=2 has seventh power 1 and is nonidentity; these are input *roots*, not invented FLT7 coordinates.
5. `nativeEval` and `nativeKernel` use **actual natural** Q(a,b) and T(c,g) support and the explicit q-unit hypotheses q∤b,c,g to derive t=−a/b and r=(c+g)/c via existing root/guard owners. Neither `Fermat7Equation` nor additive focus is assumed in these definitions and their direct E/R contraction and image-membership endpoints.
6. `native_eisenstein_source_mem` and `native_factor_source_mem` use actual typed E norm-coordinate and native selected R slot-0 factor, respectively; `native_eisenstein_mem`, `native_factor_mem` and `native_residue_zeros` transport them into the **same** C kernel. Their residues are both zero but the embedded elements are not identified, even in the existing q43 sample.
7. `native_square_support` adds q≠3 and q²|T, clearly distinguishing higher support from mere q|Q,T. It reuses Step017's E ideal-square certificate, Step025's selected R square iff, correct `Ideal.map_pow` into separate extension powers, one-way `pow_le_pow_left'` into the common kernel square, and true ideal-product multiplication for mixed M³/M⁴ **lower bounds**. No equality or reverse transport of depths is claimed.
8. `focused_receiver` is **explicitly conditional** on positive a,b, primitive coprime a,b, an actual hypothetical `Fermat7Equation`, additive focus, prime q≠7 and q|Q,T. It derives q∤b,c,g and q≠3 from Step031, then invokes the native receiver; its scalar depth equality, evenness, q² support and q³↔q⁴ parity are read from **preexisting Step010/031**, not inferred from `pairedKernel` alone. The proof contains a real explicit evenness witness `padicValNat q Q`.
9. Numeric q43 witnesses `(1166,1857,1858,1165)` and `(5,8,9,4)` select the **same** M43. The former has q² Tail support and a compatible abstract doubled budget, while the latter has only q-first-power Tail support and fails the doubled budget; **both** satisfy additive focus and **neither** is Fermat7. Thus mere source-linked kernel existence does not force valuation depth or the exact global balance. This deliberately retains the Step032 historical correction.
10. The report checks q7/q3/q13 root-contract exclusions and q13 Gap-only support, without claiming any of these primes yields a native Tail-side kernel. The old signed packet needs balanced signed roots, coprimality, gap/quotient roots and normalized equation; `AwayDescentClosureProvider` still needs newX/Y/Z, a new primitive CounterexamplePack, a new AwayValuationTransferPacket and exact `carrier_match`. The new `Ideal C` endpoints inhabit none of those construction fields.
11. All twenty new theorem and four definition declarations have reported standard-only axioms, no sorry/admit/new axioms/unsafe/native_decide/global resource options. Direct new production import is Step036 only, local owner graph remains acyclic with no neutral Lib→FLT edge. Prior rings, old providers, facades and historical reports were untouched. The transitive closure still contains certain old signed modules as preexisting imports; the report correctly does not claim they vanished.

## Outcome and next research target

**APPROVED — Outcome B.** The reusable generic paired-kernel interface is kernel checked according to Codex's logs, and is no longer locked to q43. But its source conditions are still just **necessary local conditions**, and it cannot generate the global balance or a signed primitive descent packet.

The next proof should not automatically enlarge M-adic powers or rebuild another generic root grid. **Recommended Step038: a typed two-branch *total q|Q routing contract* for hypothetical positive primitive FLT7**, distinguishing the **Gap support** q|g versus **Tail support** q|T using the already checked Step010 `prime_square_focused_allocation`, with an actual source-derived common kernel only on the Tail branch. This matters because Step037's generic receiver consumes q|T and q∤g; it cannot, without additional conditions, accept every prime q|Q.

On the Gap branch, derive the actual canonical ratio `gtailSevenTailRatio q c g = 1` from q|g and q∤c; this **violates** the nonidentity seventh-root guard and explains why no Tail-side receiver is available from those data. On the Tail branch, derive q∤g, q²|T and the full Step037 `focused_receiver` endpoints, including the common maximal ideal and bounded mixed products. This should give a total, honest **case routing theorem**, not a contradiction or descent.

A modest separate source-typed inequality theorem `fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic u` under q∤b, for arbitrary u:R, may also be worthwhile as a carrier equality firewall: the former has imaginary coordinate (b:R), the latter imaginary coordinate zero. Use the genuine R evaluation to show (b:R)≠0; do not infer that unequal source elements obstruct the Fermat equation.

The genuine unsupplied step remains **global**: under focus, Step032 proves exact balance iff Fermat7Equation, and Step010's dichotomy plus a common kernel is not enough to derive this balance. A future noncircular proof would have to constrain/close one or both branches beyond already checked consequences, or actually construct a new signed primitive packet with exact carrier match. Neither result is contained in Steps018–037.

No PR/rebase/merge, public facade, all-k valuation, full spectrum, global FLT7 claim or new signed packet is authorized.
