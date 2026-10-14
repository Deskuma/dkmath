# Review 035 — q43 twelve-prime grid, strict extensions and orthogonal source membership

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 035 COMPLETE / Outcome B**

## Evidence and scope of review

Source-level GitHub audit of:
- `DkMath/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean` (242 lines);
- `DkMathTest/FLT/Seven/GTailEisensteinCyclotomicPrimeGrid.lean` (117 lines);
- `report-035.md`, `source-inventory-035.md`, `frontier-035.md`;
- Step034 actual common quadratic algebra `GTailCommonReceiver.Carrier`, source embeddings and q43 evaluation; Step033 no-direct-hom endpoints; actual Step021 seven-root kernels, Eisenstein residue ideals and natural Tail source factor ownership.

**Static GitHub source/proof-route review only:** the reviewer did not independently run Lean. Codex reports final focused source build 08 and test build 09 passing exit0, warning0; direct Step034 and Step033 regressions 10/11 exit0, warning0; 30 examples and all 32 public declarations' axiom checks restricted to `propext`, `Classical.choice`, `Quot.sound`. Intermediate build 03 failed at ideal-equality transport and 05 failed at optional normalization; corrected and retested; two initial linter warnings were removed. No full clean repository suite is claimed.

## Mathematical audit

1. `eisenstein43Root : Fin2→ZMod43` selects the **actual** roots 37 and 7 of t²−t+1. `seven43Root : Fin6→ZMod43` reuses `sixSlotRoot 11`, so all six roots are seventh powers with order 7, nonzero and nonidentity. Root-choice injectivity is proved for both coordinates; six values [11,35,41,21,16,4] are only enumerated in tests.
2. `evR43 j : R→+*ZMod43` is the preexisting actual cyclotomic evaluation. `evGrid e j : C→+*ZMod43` is a genuine unital RingHom via `evR43 j x.re + t_e*evR43 j x.im`, with multiplicativity obtained from actual `QuadraticAlgebra.re_mul/im_mul` and the checked relation on t_e, not from any E→R map.
3. Both **bundled RingHom commuting triangles** are proved: `evGrid.comp fromEisenstein` equals the E residue evaluation at row root t_e, and `evGrid.comp fromCyclotomic` equals the R residue evaluation at column root s_j. Images of τ and ζ and all integer scalar casts are checked.
4. `M e j := ker (evGrid e j) : Ideal C`. For **every** e,j, `evGrid` is surjective onto field ZMod43, hence M is maximal and prime. The E contraction of M is the actual `eisensteinResidueIdeal t_e` and the R contraction is the actual `sixRootKernel 11 j`, each as an equality in its **own** ideal type.
5. The source checks `evGrid 0 0=eval43` and `M 0 0=M43` literally; the Step034 q43 kernel has not been silently replaced by an isomorphic copy.
6. `M_injective : Function.Injective (fun x:Fin2×Fin6 => M x.1 x.2)` is proved by actual ideal contraction, not merely unequal RingHoms. R contractions and `sixRootKernel_ne` force matching column j; the E generator separator `fromEisenstein τ − t_e.val` and distinct row roots force matching e. Thus **twelve different maximal ideals** in C are constructed. This is not a complete prime spectrum classification.
7. `map_eisenstein_le` and `map_cyclotomic_le` use the **real** `Ideal.map_le_iff_le_comap` adjunction. The two strict inequalities at (0,0) hold:
   `Ideal.map fromEisenstein P37 < M00` and `Ideal.map fromCyclotomic K0 < M00`.
   The first is witnessed using the **other column** j=1 where the cyclotomic generator has residue35 instead of11; the second uses the **other row** e=1 where τ has residue7 instead of37. Actual membership/nonmembership arguments verify strictness, rather than unsupported intuition that a proper ideal extension must be proper in C.
8. `normCoord_mem_iff` proves the *native non-Fermat witness* `fromEisenstein (gtailSevenNormCoord 1166 1857) ∈ M e j ↔ e=0`. `factor_mem_iff` independently proves `fromCyclotomic (gtailCyclotomicFactor 1858 1165 0) ∈ M e j ↔ j=0`. The test checks intersection iff `e=0∧j=0`, nonmembership in a wrong row/column and **inequality** of the embedded source elements. No Fermat7 solution or identification of source elements is claimed.
9. Important correction to the previous instruction's caution: Mathlib **does prove** `Ideal.map f (I^n) = (Ideal.map f I)^n` via `Ideal.map_pow`. The invalid inference is to *replace* `Ideal.map f I` by a strictly larger selected maximal ideal M before taking powers; Step035's strict inequality already refutes that at n=1. The source inventory and report state this distinction accurately.
10. Definitions/theorems total **5 + 27 = 32 public declarations**. The report shows standard logical axioms only, no sorry/admit/new axiom/unsafe/native_decide/global resource option and no neutral Lib→FLT import cycle. The new owner imports Step034 only and did not edit earlier ring, signed-packet, façade, review or FLT7 closure owners.

## Interpretation and candidate Step 036

**APPROVED — Outcome B.** The 2×6 grid is a genuine **local branching** theorem in the common receiving algebra. Fixing only an E prime leaves six possible grid primes; fixing only an R prime leaves two. Both source prime addresses together determine exactly **one within this constructed grid**. This is not proof that the original Fermat7 input produces a canonical global pairing, that all primes of C above 43 are in the grid, or that the common kernel realizes identical source ideal-adic valuations.

**Recommended Step036: the missing *joint-generation* theorem**, not merely another numerical root grid or power cutoff. For each e:Fin2 and j:Fin6, let
`A_e := Ideal.map fromEisenstein (eisensteinResidueIdeal t_e)`
and
`B_j := Ideal.map fromCyclotomic (sixRootKernel 11 j)`.
Step035 already proved **separate** proper inclusions (and `A_e⊔B_j≤M(e,j)` from the two inclusions). A new **exact ideal equation**
```text
M(e,j) = A_e ⊔ B_j
```
is mathematically plausible and is **not yet proven**. It is stronger than contractions and strictly weaker than `A_e=M` or `B_j=M`.

Suggested correct proof method: for x:C in M(e,j), let t=t_e and
`y := x.re + ((t.val:ℕ):R)*x.im : R`.
Because `evGrid e j x=0`, the actual cyclotomic evaluation of y vanishes, so y∈K_j. Also the Eisenstein source element `τ−t.val` lies in P_e by its actual generator residue evaluation. In the real two-coordinate quadratic algebra prove:
```text
x = fromCyclotomic(y)
    + fromEisenstein(τ−t.val)*fromCyclotomic(x.im).
```
The first term belongs to B_j, the second to A_e; hence x∈A_e⊔B_j. Conversely both included in M(e,j) are already Step035 theorems. This is a **bounded q43 double-address joint generation theorem**, not automatic `Ideal.map_pow` or a field/compositum result.

After that, compare `A_e^n`, `B_j^n`, `M(e,j)^n` **only where supported by direct theorem statements**, and observe `(A_e⊔B_j)^n` generally contains mixed products. Do not assert arbitrary cross-ring depth equality or generate another Hensel/valuation tower. A small symbolic mixed-term witness/readout could be worthwhile, but is optional.

This proposed joint-sum identity would provide a fully typed **prime-address pairing** in C, perhaps useful as a later local infrastructure contract for an actual signed carrier—still not a reconstruction of an FLT7 primitive counterexample, global balance or away descent.

No PR, merge/rebase, façade promotion, all-spectrum statement or global FLT7 theorem authorized.
