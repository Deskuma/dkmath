# Review 036 — joint generation of paired q43 primes and bounded mixed powers

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 036 COMPLETE / Outcome B**

## Inspected sources and verification boundary

Statically reviewed:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean` (125 lines);
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeJoin.lean` (162 lines);
- `report-036.md`, `source-inventory-036.md`, `frontier-036.md`;
- Step035's actual twelve maximal kernels and strict source extensions, Step034 common quadratic algebra and embeddings, source Eisenstein and cyclotomic square support, Step031's Fermat-conditioned valuation budget, Step032 global-balance iff and `DescentClosureAudit.AwayDescentClosureProvider`.

**Static GitHub source/proof-route review only: reviewer did not independently run Lean.** Codex records final source build 07, test build 09 and Step035/034 regression builds 10/11 exit 0, warning 0, 34 checked examples, fifteen public declarations' axiom lists each restricted to `propext`, `Classical.choice` and `Quot.sound`. Intermediate compilation failures 01,02,04,08 and their repairs are disclosed, as is the early unused simp warning. No full clean DkMathTest build claimed.

## Mathematical proof audit

1. `rowRemainder e x := x.re + (eisenstein43Root e).val*x.im : R` and `rowDifference e := tau (-1) − (eisenstein43Root e).val : E` have the correct, **separately typed** source and integer-lift carriers. `coordinate_decomposition` proves in the **actual C=QuadraticAlgebra R (-1) 1** the equality
   `x = iR(rowRemainder e x) + iE(rowDifference e)*iR(x.im)` for arbitrary x, not only kernel elements. It first rewrites `iE(rowDifference e)=omega−n_e` and checks actual re/im coordinates with `QuadraticAlgebra.ext`, narrowly controlled casts and `ring`; no domain or DVR premise.
2. `rowDifference_mem` transports the correct finite-field generator residue to the actual E ideal `P_e`. `rowRemainder_mem` uses x∈M(e,j) and the **actual** `evGrid` equality to obtain the separately typed R kernel membership y∈K_j. Neither is assumed from a generic shared prime.
3. The extensions `A e := Ideal.map iE P_e : Ideal C`, `B j := Ideal.map iR K_j : Ideal C` do not depend on the other coordinate. `sup_le_M` reuses the checked Step035 individual inclusions. `M_le_sup` applies the genuine decomposition, `Ideal.mem_map_of_mem`, ideal multiplication closure and ideal addition closure for the reverse containment. Therefore
   **`M_eq_map_eisenstein_sup_map_cyclotomic : ∀ e j, M e j=A e⊔B j`**
   is a proof about the **whole ideal C**, not merely about finite field zero values.
4. `M43_eq_sup` agrees with Step034's unchanged actual M43. Test regressions also check that at (0,0) **both** `A0<M00` and `B0<M00` hold even though `A0⊔B0=M00`; there is no false equality of either individual extension with the common prime. The twelve joined ideals remain pairwise distinct and maximal by already checked Step035 results.
5. The four `eisenstein_mem_A_pow` / `eisenstein_mem_M_pow` and `cyclotomic_mem_B_pow` / `cyclotomic_mem_M_pow` theorems restrict n to `Fin 3`, i.e. powers **0,1,2**. They correctly use Mathlib **`Ideal.map_pow`** to enter the powers of source extensions and **`pow_le_pow_left'`** with `A,B≤M` for a **one-way membership implication** into M-power. There is **no inverse implication** or identification of extension powers with M powers.
6. Actual `α=gtailSevenNormCoord 1166 1857 : E` has `α∈P37` and `α²∈P37²` by the prior source; actual `F0=gtailCyclotomicFactor 1858 1165 0:R` has `F0∈K0²` by Step025. The test transports source membership to `iEα∈M00`, `iE(α²)∈M00²` and `iRF0∈M00²`. Actual `Ideal.mul_mem_mul` and `pow_add` give
   `iEα * iRF0 ∈ M00³` and `iE(α²)*iRF0 ∈ M00⁴`. No next-power nonmembership, exact M valuation or equality of the two embedded elements is claimed.
7. The numerical tuple is still **not** a Fermat7 solution. The valid mixed products and joint ideal sum **do not supply** `g*T=7ab(a+b)Q²`. Step032's `fermat7Equation_iff_focused_scalar_balance` makes that exact equality equivalent to hEq under focus. This is an essential noncircularity boundary.
8. `AwayDescentClosureProvider` (actual source read) still demands nextX/Y/Z, a new `CounterexamplePack`, a new `AwayValuationTransferPacket` and `carrier_match : nextRoute.carrier=Int.natAbs p.normal.root.snd`. An `Ideal C` membership/sum does not inhabit any of these fields or identify with the older signed packet's carrier. Neither a closure theorem nor nonexistence of a future closure provider is proved.
9. Production directly imports Step035 only; test imports new production. The report's 15 public axiom checks and local source/import audits record no nonstandard axioms, unsafe shortcuts, placeholders, neutral Lib→FLT import cycles, old owner changes or broad facade imports.

## Scientific classification and next frontier

**APPROVED / Outcome B.** The project has now constructed an explicit q43 **two-source prime generator equation** with bounded mixed-power lower bounds. This is an actual algebraic fact about the third ring C, not an E→R RingHom, proof of whole-spectrum splitting or FLT7 descent.

Do **not** continue with an arbitrary `M^5,M^6` ladder or claim `(A⊔B)^n=A^n⊔B^n`; mixed terms matter. Re-evaluate the original FLT7 reconstruction problem instead.

**Proposed Step037: a prime-variable, actual-source paired-kernel *receiver for hypothetical focused Fermat data***. The 43-fixed q43 grid was an informative test but cannot, alone, ingest the generic prime q demanded by the old local valuations or any hypothetical Fermat equation. Build a **single paired local evaluation** in the unchanged C at arbitrary prime q when supplied (i) an E quadratic root `t:ZMod q` and (ii) an R nontrivial seventh root `r:ZMod q`, and prove separately typed E/R contractions and maximality. Do not rebuild a generic 2×6 grid. Crucially specialize this construction to **actual natural focused inputs** `a,b,c,g` with `q|Q`, `q|T`, `q∤b,c,g`, using checked `gtailSevenResidueRoot`, `gtailSevenTailRatio`, E source-coordinate membership and R selected factor membership. Then add one clearly conditional Fermat-facing adapter deriving the q-unit guards from Step031 given hypothetical hEq, hfocus, primitivity and q≠7, without fabricating a Fermat tuple or claiming a descent.

The new **usable contract** should concern a common ideal and source images **for symbolic q and actual natural source coordinates**, not just q43, and should report precisely that the same contract is satisfiable for q43 non-Fermat data; hence no global balance, signed packet or reduction of a primitive counterexample is forced. An optional source-side square-power **one-way** transport to M² can be proved from existing split-E ideal square and Step025 factor square only if the source q hypotheses already satisfy them.

This is a strictly narrower proof target than general-prime full grid, flatness, class groups, ideal-power equality or a direct E→R hom. It is also a meaningful local algebra interface a future noncircular Fermat obstruction could consume—but not that obstruction itself.

No PR, merge/rebase, facades or signed packet reconstruction is authorized.
