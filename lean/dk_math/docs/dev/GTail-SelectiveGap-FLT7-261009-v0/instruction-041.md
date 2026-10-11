# Instruction 041 — genuine focused inputs separating global coverage and magnitude

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-040.md`, `report-040.md`, `source-inventory-040.md`, `frontier-040.md`.

**Scope: Step 041 only.** Test the two **still-unproved, independent inputs** of Step040's exact global zero certificate on genuine, positive, primitive, strictly focused **non-Fermat** integer tuples. Prove by kernel-checked certificates that (A) full prime-square support of the actual quadratic Q may hold while the strict magnitude bound fails, and (B) the strict magnitude bound may hold while full prime-square support fails. This gives a meaningful two-direction **independence / falsification firewall** for the current capacity strategy. Optionally link a new naturally selected q43 Eisenstein/cyclotomic root pair to an already constructed *different* q43 grid cell. No global FLT7 proof, no q³/q⁴ hierarchy, no generated FLT counterexample, no new signed packet or away descent.

## 0. Exact source contracts and the mathematical gap

Source owners already kernel checked:

```lean
open DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall
open DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity

Δ(a,b,c) := focusedFermatDefect a b c : ℤ
Q(a,b) := a^2+a*b+b^2 : ℕ
S_Q := Nat.primeFactors Q : Finset ℕ
M_Q := squarePrimeSupportModulus S_Q : ℕ
```

Step040's true theorem has **both** arguments:

```lean
(hsupport : ∀ p ∈ Nat.primeFactors Q, (p:ℤ)^2 ∣ Δ)
(hsize : Δ.natAbs < M_Q)
---------------------------------
Fermat7Equation a b c.
```

Under Q≠0 it also proves `M_Q=(∏p∈S_Q,p)²≤Q²`; the mathematical expression is `rad(Q)^2`, where `DkMath.ABC.Rad.rad` already exists but is intentionally not imported into this FLT chain.

Step039 separately proved `Δ=0 ↔ Fermat7Equation` even without focus, and an hEq-free **single selected q²** Gap/Tail route. Step032 proved that under `a+b=c+g` the exact scalar global balance and the Fermat equation are equivalent. None of these gives the collective hsupport or strict hsize for a nonzero defect.

The two old Step040 true positive/negative numerical controls fail **both** hsupport and hsize. The reviewer has now independently calculated two **new candidates**, one satisfying **exactly one** missing premise in each direction. The following numbers are **not yet Lean certificates**; Codex must check ALL of them in Lean.

The intended scientific result is **independence within actual strict positive primitive focused geometry**, not mere formal independence of arbitrary signed z or a restatement of a disjunction.

## Gate 0 — source/owner audit and numerical verification before theorem design

Source-inspect actual:
- `DkMath.FLT.Seven.GTailFocusedDefectGlobalCapacity`: \`squarePrimeSupportModulus\`, \`squarePrimeSupportModulus_dvd_iff\`, \`finite_defect_zero_certificate\`, \`quadratic_prime_support\`, \`quadratic_modulus_le_square\`, \`full_quadratic_defect_zero_certificate\`;
- `DkMath.FLT.Seven.GTailFocusedDefectSquareFirewall`: actual signed `focusedFermatDefect`, `defect_square_prime_route`, `focusedFermatDefect_zero_iff`, source q-unit endpoint;
- `DkMath.FLT.Seven.GTailGlobalBalanceFirewall.fermat7Equation_iff_focused_scalar_balance`;
- `DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` (Step037): actual source-root \`nativeKernel\` when q|Q,T and q∤b,c,g;
- `DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid` (Step035): q43 row roots [37,7], column roots [11,35,41,21,16,4], actual \`M\`, \`evGrid\`, and their two typed contractions;
- `DkMath.FLT.Seven.GTailEisensteinCyclotomicCommonReceiver` (Step034): C source injections, generator evaluations;
- \`Nat.primeFactors_mul\`, \`Nat.Prime.primeFactors\`, \`Nat.mem_primeFactors_of_ne_zero\`, \`Finset\` membership and Int signed comparisons; verify actual APIs with \`#check\`, avoid naive \`decide\` on large factorizations.
- read-only \`AwayDescentClosureProvider\` and \`RamifiedSignedRootDepthPacket\` fields to maintain the existing FLT7 frontier, not to import or construct them.

Write `source-inventory-041.md` identifying exact q/number witnesses, proof requirements, source ideal/carrier types if optional receiver, and **what is not implied**. Suggested owner:
`DkMath/FLT/Seven/GTailFocusedCapacityIndependence.lean`
importing Step040 directly. Test:
`DkMathTest/FLT/Seven/GTailFocusedCapacityIndependence.lean`.
A **test-only** numerical witness is acceptable if accompanied by a reusable, precise named existential in production or a small theorem documenting the actual first-order logical countermodel; avoid 100 redundant numeric aliases. No changes to Steps010–040 or generic norm, radical, ideal, packet and facade owners.

## Gate 1 — FULL prime-square coverage, SIZE FAILS (mandatory)

**Reviewer-calculated candidate A**:

```text
q = 43
(a,b,c,g) = (13,35,46,2)
a+b = c+g = 48
gcd(a,b)=1
0<g<a,b<c<a+b
Q = 13²+13·35+35² = 1849 = 43²
Nat.primeFactors Q = {43}
M_Q = (43)^2 = 1849

Δ = 13⁷+35⁷−46⁷ = −371,415,611,824  (nonzero, NEGATIVE)
Δ.natAbs = 371,415,611,824 > M_Q
(43:ℤ)^2 ∣ Δ
∀ p ∈ Nat.primeFactors Q, (p:ℤ)^2 ∣ Δ  -- TRUE
¬(Δ.natAbs < M_Q)                    -- TRUE

T := GTail 7 1 2 46 = 75,625,342,528
43²∣T; 43∤g; 43∤b,c.
t := gtailSevenResidueRoot 43 13 35 = 7 (mod43)
r := gtailSevenTailRatio 43 46 2 = 16 (mod43)
7²−7+1=0 (mod43); 16^7=1 and 16≠0,1 (mod43).
¬ Fermat7Equation 13 35 46.
```

The **radical** is 43, not 1849: Q is **not squarefree**, unlike old samples. The support modulus is rad(Q)²=1849 even though Q²=1849²=3,418,801. Never substitute Q² for M_Q here. This test is a useful real regression for the inequality `M_Q≤Q²` being possibly STRICT.

**Prove** with actual numeric Lean examples:
1. primality of 43, Q=43², \`Nat.primeFactors Q={43}\` by \`primeFactors_mul\` / checked \`Nat.Prime.primeFactors\` / \`norm_num\`;
2. strict positive primitive focused geometry;
3. exact signed integer Δ value, nonzero and negative, full support \`∀p∈S_Q,(p:ℤ)^2|Δ\`;
4. \`M_Q=1849\` with \`M_Q<Q²\` and \`M_Q<Δ.natAbs\`;
5. \`¬Fermat7Equation\` and \`¬exact global scalar balance\` via Step039/032, not via a fictional hEq argument;
6. actual Tail q-unit/GTail q² support and Step039 equation-free square route, with **no** Fermat premise.
7. compare with full Step040 certificate: its **hsupport is true** but its **hsize is false**, so its conclusion is *not applicable*. Do not assert the theorem itself is false.

**Important additional nuance:** numeric v43(Q)=2, v43(T)=2, v43(g)=0, so `v43(g)+v43(T)≠2v43(Q)`. Do NOT apply Step031's hEq-conditioned exact valuation budget to this non-Fermat witness just because q43² divides Δ. If numerically checked, this gives another true control of the difference between Step039 square support and Step010's exact budget.

### Optional actual q43 grid address: native roots (7,16)

This tuple independently selects the **second** Eisenstein root t=7 and **fifth** seventh-root column r=16, whereas old q43 native data selected (t37,r11). Step035 \`seven43Root (4:Fin6)=16\`, \`eisenstein43Root (1:Fin2)=7\`.

If dependencies and proof-term normalization permit, prove in the test:

```lean
nativeKernel 13 35 46 2 ... = GTailPrimeGrid.M (1:Fin2) (4:Fin6)
```

using actual \`nativeEval\` and \`evGrid\` RingHom equalities or equality of evaluations on all coordinates (with the correct root certificates) and then \`RingHom.ker\`. A weaker checked version is that the same *two typed contractions* yield P7 in E and K16 in R. If source type owner reachability would require a large new import or proof-dependent equality is expensive, **do not block the two mandatory independence witnesses**. Record this optional grid identity as pending with exact imported module/API blocker.

This is a **native** q43 prime pair from actual a,b,c,g, not an invented arbitrary residue assignment. No source image equality or signed-prime packet follows.

## Gate 2 — SIZE bound TRUE, FULL support FAILS (mandatory)

**Reviewer-calculated candidate B**:

```text
(a,b,c,g) = (1497,2797,2802,1492)
a+b = c+g = 4294
gcd(a,b)=1; 0<g<a,b<c<a+b
Q = 14,251,327 = 37 * 385,171
37 and 385171 are BOTH prime
Nat.primeFactors Q = {37,385171}
M_Q = (37*385171)^2 = 203,100,321,260,929 = Q²

Δ = 1497⁷+2797⁷−2802⁷ = −179,820,312,066,002
Δ.natAbs = 179,820,312,066,002
0 < Δ.natAbs < M_Q
Δ ≠ 0, hence ¬ Fermat7Equation a b c.

37²∤Δ; 385171²∤Δ
¬(∀ p ∈ Nat.primeFactors Q, (p:ℤ)^2 ∣ Δ)
```

This is the **opposite** of candidate A: real strict positive primitive focused geometry satisfies the **strong Archimedean inequality**, but the required full-prime-square coverage fails. It is a relatively close seventh-power **near miss**, not an FLT7 solution.

Kernel-check:
1. all geometry, additive focus and coprimality;
2. Q factorization and primality of 37 and 385171; avoid a naive \`decide\` that unfolds primeFactors to enormous recursion; construct \`S_Q\` with exact factorization and proved primality (use `norm_num` if feasible, otherwise check a compact kernel certificate using actual divisibility exclusion);
3. real signed Δ, its exact absolute value and **strict hsize** using actual Step040 modulus;
4. two explicit counter-support residues (checking one missing prime already refutes hsupport; both are useful if cheap);
5. \`¬hEq\` from Δ≠0 and \`¬exact balance\` under focus;
6. exact Step040 certificate hypothesis ledger: **hsize true, hsupport false**. Do not call the conditional certificate under the missing proof.

**Safety against invalid deductions:** do not infer q²∣Δ from a small |Δ|; it is a completely independent arithmetic condition. In this tuple even q|Δ fails at both Q-prime factors; no Step039 selected square route should be instantiated without checking its actual q² defect premise.

## Gate 3 — genuine internal independence theorem (recommended export)

Expose the two countermodels as one or two small **Lean theorem(s) in production** with first-order, satisfiable existential claims, not enormous numbered literals hidden only in tests.

Minimal types:
```text
exists_full_support_without_size :
  ∃ a b c g : ℕ,
    0<a ∧ 0<b ∧ Nat.Coprime a b ∧ a+b=c+g ∧
    0<g ∧ g<a ∧ g<b ∧ a<c ∧ b<c ∧ c<a+b ∧
    (let Q := a^2+a*b+b^2
     let Δ := focusedFermatDefect a b c
     ∀p∈Nat.primeFactors Q, (p:ℤ)^2 ∣ Δ) ∧
    ¬((focusedFermatDefect a b c).natAbs <
       squarePrimeSupportModulus (Nat.primeFactors (a^2+a*b+b^2))) ∧
    ¬ Fermat7Equation a b c

exists_size_without_full_support :
  ∃ a b c g : ℕ,
    analogous positive primitive strict focused geometry ∧
    Δ.natAbs < squarePrimeSupportModulus (Nat.primeFactors Q) ∧
    ¬(∀p∈Nat.primeFactors Q, (p:ℤ)^2∣Δ) ∧
    ¬ Fermat7Equation a b c.
```

This is merely a **proposed theorem shape**; adapt concise LET/casts to actual Lean APIs. The key is exact inclusion of **both** the honest geometry and the logically missing condition. Use concrete witnesses A and B and prior checked numeric helpers. If public existence lemmas make the production module slow or distract from the core, keep them in a small new production owner with tests, and avoid creating a general new geometry structure. Do not state an invalid fully universal independence theorem.

Optionally add the valid **contrapositive diagnosis** of Step040's certificate:

```text
Δ≠0 → ¬hsupport ∨ ¬hsize
```

but label it transparently as a **direct logical contrapositive**, not a new number-theoretic obstruction; the two real witnesses are the real added information.

## Gate 4 — compare actual capacity and root-support facts without losing semantics

Source compare the new witnesses to older Step039/040 ones:

| Witness | Full Q prime-square support | |Δ| < M_Q | Fermat |
| --- | --- | --- | --- |
| Old Tail q43 (1166,1857,1858,1165) | False | False | False |
| Old Gap q13 (196,211,238,169) | False | False | False |
| **New A q43** (13,35,46,2) | **True** | **False** | False |
| **New B near miss** (1497,2797,2802,1492) | **False** | **True** | False |

This is a **three-of-four truth-table** control, with the fourth (True,True) being impossible for a non-Fermat input by the actual Step040 zero certificate. Do not confuse the Boolean status of a hypothesis with the status of its implication theorem.

In A, q43 source-compatible ideals in E/R/C are available because q43|Q,T and q43∤b,c,g; **the actual common kernel can exist even when full prime-square support holds**, so its existence does not solve the missing magnitude bound. In B, the strict magnitude bound alone gives no selected q²-supported native Tail receiver. These are structural lessons grounded in actual tuples, not intuition.

Document this separately from the old signed descent packet:
- AwayDescentClosureProvider still requires nextX/Y/Z, a new CounterexamplePack, new AwayValuationTransferPacket and exact \`carrier_match\`.
- RamifiedSignedRootDepthPacket still requires balanced signed identities, coprimality, gap/quotient roots and 7-unit guards.
- Neither full support alone nor hsize alone constructs an FLT7 contradiction or descent.

## Deliverables, builds and STOP

Required:
- `DkMath/FLT/Seven/GTailFocusedCapacityIndependence.lean`;
- `DkMathTest/FLT/Seven/GTailFocusedCapacityIndependence.lean`;
- `source-inventory-041.md`, `report-041.md` and a concise `frontier-041.md` or clearly separated equivalent in report;
- truthful post-040 `ROADMAP.md` append with all older sources/reviews/corrections unchanged.

Gates: (1) first independently source-check and kernel-certify numeric candidate A with correct **nonsquarefree Q**; (2) candidate B with the actual factorization and near-miss bound; (3) export narrow existential witness theorem(s) and optional new q43 row/column source-match; (4) verify old Step039/040 controls and explicit capacity hypothesis truth table; (5) focused final source/test and Step040/039 direct regressions.

Sequential process-local `LEAN_NUM_THREADS=2`. Record full compiler commands/exits/warnings, any intermediate invalid numeric claim or API failure and corrected value, exact public theorem signatures, all \`#print axioms\`, actual owner import DAG/neutral Lib→FLT/ABC cost, forbidden proof tokens, whitespace/style and unchanged historical records. Avoid unnecessary \`native_decide\`, \`set_option maxRecDepth\` and full all-suite rebuild.

**Outcome B expected:** two real, kernel-checked, **positive primitive strictly focused non-Fermat** countermodels separating full prime-square coverage from the independent Archimedean bound, plus optional native source selection of a different q43 common prime. This is a high-value **capacity strategy limitation**, not a new FLT7 obstruction.

**Outcome C/partial:** a false reviewer arithmetic number, excessive primality reduction, or incompatible ideal-equality certificate; preserve checked truthful witnesses and state the exact blocker, correcting the proposed candidate rather than fabricating a Fermat solution.

**Outcome A:** only a genuinely new noncircular global arithmetic restriction on hypothetical positive primitive Fermat7 data beyond the Step040 conditional certificate and these non-Fermat witnesses.

**STOP after Step041.** Do not iterate an endless capacity-example catalogue, q³/q⁴ defect ladder, generic K-valuation, new ideal grid, ABC conjectural inequality, signed packet, primitive next counterexample, away descent or unconditional FLT7 closure. The next research decision MUST evaluate whether there is a **new independently provable global restriction** or a route to a genuine old-provider reconstruction; if neither is found, record the remaining gap explicitly rather than adding more equivalent local interfaces.
