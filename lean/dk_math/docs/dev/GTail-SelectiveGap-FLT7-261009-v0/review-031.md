# Review 031 — typed Eisenstein norm and cyclotomic depth synchronization

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 031 COMPLETE / Outcome B**

## Reviewed evidence and verification scope

Statically inspected the actual pushed GitHub source:
- `DkMath/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean` (146 lines);
- `DkMathTest/FLT/Seven/GTailFocusedNormCyclotomicDepthBridge.lean` (177 lines);
- `report-031.md` and `source-inventory-031.md`;
- prior Step010 `GTailPrimeAllocationAudit`, Step011 order and paired-residue owners, Step012 Eisenstein norm and `GTailNormReadoutAudit`, Step017 Eisenstein ideal square address, and Steps025/029/030 genuine cyclotomic ideal-power endpoints;
- original `GTailBridge.gtail_seven_shell`, `gtail_seven_eq_of_fermat7Equation`, and the old explicit `AwayDescentClosureProvider` and signed-depth packets **for scope comparison only**.

This is **GitHub static proof-route inspection**, NOT a separate Lean build. Codex's report records focused source/test builds and five targeted regression modules passing, 26 examples, and seven public declaration axiom audits each with only `[propext, Classical.choice, Quot.sound]`. One transient test-local notation clash was repaired without modifying a theorem statement. Final source/test exit codes 0, warning counts 0; no all-suite clean build was claimed.

## Mathematical audit

1. `scalar_budget_tail_double` is a correct abstract consequence of `v_q(g)+v_q(T)=2v_q(Q)` and q∤g, using `padicValNat.eq_zero_of_not_dvd`; no prime or nonzero premises are needed for this *equality-only* lemma.
2. `scalar_budget_depth_readouts` explicitly requires prime q, T≠0 and Q≠0 for `padicValNat_le_iff_dvd` and converts doubled valuations into `q²|T ↔ q|Q`, `q⁴|T ↔ q²|Q`, `q³|T ↔ q⁴|T`, and absence of exact scalar q-depth three. The tests provide real counterexamples if T=0, Q=0 or the gap q-unit premise is removed. The zero-value convention is not quietly ignored.
3. `focused_norm_depth_guards` derives q∤a,b,a+b from the checked primitive-pair product-unit result, q∤c from the actual Fermat equation/endpoint unit, and q∤g from the Step010 support-exclusion dichotomy plus q|T. It derives q≠3 from the actual nontrivial seventh-tail root, rather than adding it as an undocumented premise.
4. The private `focused_positive_nonzero` obtains g≠0 and T≠0 from the **exact focused product** and positive a,b, and Q≠0 directly by positivity; it does not refer to unavailable previous private declaration names.
5. `focused_norm_scalar_depth_readouts` **reuses**, rather than re-proves, the existing Step010 `padicValNat_focused_quadratic_budget` and `prime_square_focused_allocation`. It establishes `v_q(T)=2v_q(Q)`, q²|T, q⁴|T iff q²|Q and q³|T iff q⁴|T under explicit hypothetical positive primitive Fermat7 conditions. This parity restriction was already *implicit in Step010*; it must not be counted as an independent new FLT7 obstruction.
6. `focused_eisenstein_norm_square_endpoint` has a genuine source-typed `TraceOneInt (-1)` element `gtailSevenNormCoord a b`, norm readout, and actual oriented split `α²∈P_t²` with conjugate/scalar exclusions. It invokes Step017 with the **derived** q≠3, q|Q and q∤b premises and Step012's integer norm-square balance under hEq+hsum. It does NOT send this element or its ideal to the cyclotomic ring.
7. `focused_cyclotomic_depth_endpoint` separately constructs the actual canonical natural Tail root and actual selected degree-six ideal, proves `F_i∈K²` from the checked Step010 q² allocation and Step025 square iff, and proves `F_i∈K³ ↔ F_i∈K⁴` using the scalar parity result plus the checked Step029/030 genuine ideal power iff endpoints. The proposition `¬(F_i∈K³ ∧ F_i∉K⁴)` is a direct consequence, not a new standalone impossibility theorem.
8. `focused_tail_fourth_iff_norm_square_dvd` is precisely the cross-carrier **integer scalar value** iff `q⁴|T ↔ (q:ℤ)²|norm α`. It uses the existing norm equality and proper nat/int divisibility transfer. It does not assert `P_t=K_j`, `α²=F_i`, a RingHom E→R, or any class/unit-power correspondence.
9. Numeric q43,a5,b8,c9,g4 checks the coexistence of the genuine Eisenstein split square address at root37 and cyclotomic selected root11, while the exact Fermat7 equation and scalar product balance **both fail**. At q43,c9,g32598 the genuine K³\K⁴ example is outside the focused coordinate-sum relation. Correctly, neither is passed off as a counterexample to the hypothetical FLT7-conditioned parity conclusion. Separate satisfiable *abstract scalar* budgets, gap-unit failures and zero-valued counterexamples are retained.
10. All seven declarations have report-recorded standard axiom lists. Source tests preserve exact conditional signatures rather than supplying fictional positive Fermat solutions. The direct imports are Step030, Step010, Step012 conditional norm, Step017 Eisenstein square; no new neutral→FLT import cycle or edits to old rings/facades/packet owners. A broad existing transitive closure does not imply proof use of an unrelated unconditional FLT7 result.
11. The report explicitly stops at Step031; no K⁵/all-k, typed integral carrier transfer, signed-depth packet, recurrence to a new primitive Fermat tuple, or FLT7 descent is implemented. The existing `AwayDescentClosureProvider` still requires a **new primitive counterexample packet and carrier match**, not merely a smaller scalar or a new local ideal-address theorem.

## Precise frontier and next recommendation

**APPROVED — Outcome B.** We now have a truthful *jointly typed readout*, not an integral-algebraic map. The next step should identify the logical information missing from the joint readouts, not add another ideal power or assume that both source rings are secretly the same.

A useful overlooked cheap theorem is **the exact Fermat-balance equivalence**:
`a+b=c+g → (Fermat7Equation a b c ↔ g*GTail 7 1 g c = 7*a*b*(a+b)*(a²+a*b+b²)^2)`.
The original `GTailBridge.gtail_seven_shell` supplies the reverse directly by natural-addition cancellation. This is an **arithmetic equivalence/circularity firewall**, not a proof of FLT7. Any attempt to obtain the exact balance from q-local readouts would have to supply genuinely new global information.

Independently calculated **proposal for a satisfiable local compatibility countermodel**, NOT a Step031 Lean example:
```text
q=43, (a,b,c,g)=(1166,1857,1858,1165).
a+b=c+g=3023; gcd(a,b)=1; 0<g<a,b<c<a+b.
Q=6,973,267; 43|Q, 43²∤Q.
T=GTail 7 1 1165 1858 = 1,914,732,507,483,487,090,603;
43²|T, 43³∤T; 43∤a,b,c,g,a+b.
v43(g)=0, v43(T)=2=2*v43(Q).
The Eisenstein split root is 37 and Tail root is 11.
BUT the exact focused scalar product equality and Fermat7Equation both FAIL.
```
These values were independently calculated outside Lean. Source-check and re-evaluate **all** values in Lean before accepting as a regression. This stronger witness preserves not only shared q-orders, parity and local support, but even the additive focus and strict geometric bounds. It is a **countermodel to the sufficiency of that explicitly listed set of local conditions**, not evidence against any actual Fermat solution or impossibility of a stronger future obstruction. It pinpoints the *exact scalar equality* as still missing.

**Recommended Step032:** source-trace the original Fermat7 balance equivalence, exhibit a kernel-checked positive primitive local-compatible but non-Fermat witness, and publish a **necessary-vs-sufficient contract frontier** for existing source typed E/R readouts. Audit the old `AwayDescentClosureProvider` input contract so the same missing global equality is not silently replaced by a seventh-power/signed packet. The best result is a carefully delimited negative-information barrier and an explicit list of what a genuinely new FLT7 theorem would need, not a fabricated E→R RingHom.

No PR, branch merge or façade promotion is authorized.
