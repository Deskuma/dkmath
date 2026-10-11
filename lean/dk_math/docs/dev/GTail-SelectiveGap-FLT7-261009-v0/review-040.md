# Review 040 — finite square-support aggregation and global zero-capacity certificate

Date: 2026-10-11
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 040 COMPLETE / Outcome B**

## Evidence and verification limit

Statically inspected actual feature-branch GitHub files:
- `DkMath/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean` (131 lines);
- `DkMathTest/FLT/Seven/GTailFocusedDefectGlobalCapacity.lean` (199 lines);
- `report-040.md`, `source-inventory-040.md`, `frontier-040.md`;
- previous Step039 actual signed defect and zero iff, Step032 exact focused balance, Mathlib Nat.primeFactors/Int.natAbs APIs and the existing `DkMath.ABC.Rad` *definition* (for overlap only).

**Source/proof-route audit on GitHub; reviewer did not independently run Lean.** Codex reports final new production05, test07 and focused Step039/038 regressions08/09 all exit0/warning0 (old regressions include cached replay); 56 checked examples and all 13 public declarations' `#print axioms` limited to standard `propext`, `Classical.choice`, `Quot.sound`. Intermediate test06 recursion and production03/04 prime-support API failures and legitimate fixes are documented. No full clean repository suite, new axioms, unsafe, native_decide or size-resource workarounds are claimed.

## Actual checked mathematical statements

1. `squarePrimeSupportModulus S := ∏ p∈S,p² : ℕ` has the correct empty-support convention `M_∅=1`, strictly positive when each p∈S is prime, and satisfies `M_S=(∏p∈S,p)²`.
2. Private finite induction `square_support_dvd_nat` correctly uses **distinctness AND primality** to derive pairwise coprimality of `p²` and remaining square products, by actual `Nat.coprime_primes`, `Coprime.pow_left/pow_right`, `coprime_prod_right_iff` and `mul_dvd_of_dvd_of_dvd`. It does not use the false general implication that individual overlapping factors dividing n imply their product divides n. The nonprime 4/8 test is a real negative control.
3. `squarePrimeSupportModulus_dvd_iff S z hs` proves the **signed integer** equivalence
   `(M_S:ℤ)|z ↔ ∀p∈S,(p:ℤ)²|z`,
   with the reverse direction through the finite coprime induction and `Int.natCast_dvd`; the forward through `Finset.dvd_prod_of_mem`. Correct for negative z and empty S.
4. `int_zero_of_modulus_size` proves `(m:ℤ)|z → z.natAbs<m → z=0` via the real Mathlib `Int.eq_zero_of_dvd_of_natAbs_lt_natAbs`, with no *extra* explicit positive-m hypothesis needed. `int_nonzero_modulus_bound` proves `(m:ℤ)|z → z≠0 → m≤z.natAbs`. The useful prime-modulus M is independently known positive. Signed -36/+36 examples prevent misreading local congruences alone as sufficient for zero.
5. `finite_support_zero`, `finite_support_nonzero_bound` correctly compose (3) and (4); `finite_defect_zero_certificate` derives `Fermat7Equation` from **two explicit, independently supplied** hypotheses `∀p∈S,p²|Δ` and `|Δ|<M_S`, using Step039's zero-defect iff. Neither `hEq` nor `Δ=0` is a premise. The theorem is conditional; the source does not prove either collective premise from one selected q.
6. `quadratic_prime_support` correctly requires Q≠0 to use the exact `Nat.mem_primeFactors_of_ne_zero` contract. `quadratic_modulus_dvd_square` holds even for zero Q: `M_Q=(∏_{p|Q}p)²|Q²`. `quadratic_modulus_le_square` separately requires Q≠0, since Q=0 has `M_Q=1` and `1≤0` is false. This zero-edge distinction is explicitly regression-tested.
7. `full_quadratic_defect_zero_certificate` under Q≠0 retains **all-prime-square support AND the strict size inequality as literal theorem arguments**, and applies the generic signed certificate. This is a reusable capacity guard, *not* a derivation of a positive primitive Fermat7 solution from currently known hEq-free constraints.
8. The standard radical overlap is accurately handled: `DkMath.ABC.Rad.rad n` is exactly `n.factorization.support.prod id`, and the production uses only `Nat.primeFactors`, `Nat.prod_primeFactors_dvd` and `Finset.prod_pow`. The test proves expression-level equality `M_(primeFactors n)=(n.factorization.support.prod id)²` by `Nat.support_factorization`; no new ABC import or second general radical library is created. `M_Q=rad(Q)²≤Q²` is an **upper capacity bound on M_Q**, NOT any inequality controlling |Δ|.
9. The original actual non-Fermat Tail model `(a,b,c,g)=(1166,1857,1858,1165)` has `Q=7*43*23167`, `M_Q=Q²=48,626,452,653,289`, positive `|Δ|=2,642,627,963,860,178,152,897`, and only `43²|Δ` among those three primes; `7²∤Δ`, `23167²∤Δ`. The old Gap `(196,211,238,169)` has `Q=3*13*3187`, `M_Q=Q²=15,448,749,849`, negative Δ with `|Δ|=13,523,337,259,569,605`, and only `13²|Δ`; the other prime squares fail. **Both** have failed coverage AND failed size; they are not counterexamples to the conditional zero theorem.
10. Generic signed z=±36 with S={2,3}, M=36 verifies full local support with z nonzero when strict size fails. Q=0/1, support empty, modulus1 and the negative-integer absolute threshold are tested. Production direct import remains Step039 only; no direct `DkMath.ABC`, old signed packet, domain/class-group or facade import was added. The report records unchanged old sources, proper import DAG and no forbidden proof steps.

## Research frontier and concrete next source tests

**APPROVED — Outcome B.** This is an honest finite-to-global *conditional* certification and actual proof of the maximum magnitude attainable by the full radical-square modulus of Q. It is not an FLT7 solution: **two separate additional input theorems** would be needed to apply it.

A useful next falsification/independence study is possible with **genuine positive primitive strict additive-focused non-Fermat tuples**, not only abstract signed z=±36.

New reviewer-computed, **NOT YET Lean-certified**, candidates:

**(A) FULL Q-square support, but size FAILS:**
```text
(a,b,c,g) = (13,35,46,2), gcd(a,b)=1, a+b=c+g=48
0<g<min(a,b)<max(a,b)<c<a+b
Q = 1849 = 43², Nat.primeFactors Q = {43}, M_Q = 1849
Δ = 13⁷+35⁷−46⁷ = -371,415,611,824
43²|Δ; Δ≠0; |Δ|=371,415,611,824 >1849.
T=GTail 7 1 2 46 = 75,625,342,528; 43²|T, 43∤g
t=-13/35 mod43=7; r=(46+2)/46 mod43=16=11^5 mod43
```
The native E/R source root pair (7,16) occurs at a DIFFERENT genuine q43 row/column than the older (37,11). A possible optional Step041 test links the actual `nativeKernel` to Step035 `M (1:Fin2) (4:Fin6)` by actual evaluation/ideal equality; do not assume the dependent-certificate normalization will be trivial or infer source images are equal. Note `v43(Q)=2` but `v43(T)=2`: this sample **does not** have the Step031 hypothetical Fermat valuation budget, and is NOT a Fermat solution.

**(B) SIZE condition TRUE, but square support FAILS:**
```text
(a,b,c,g) = (1497,2797,2802,1492), gcd(a,b)=1,
a+b=c+g=4294
0<g<min(a,b)<max(a,b)<c<a+b
Q = 14,251,327 = 37 * 385171 (both prime)
M_Q = Q² = 203,100,321,260,929
Δ = 1497⁷+2797⁷−2802⁷ = -179,820,312,066,002
0<|Δ|=179,820,312,066,002 < M_Q
37²∤Δ and 385171²∤Δ; Δ≠0, ¬Fermat7Equation.
```
These numbers were independently calculated in integer arithmetic and **must be rechecked in Lean**. Neither is a counterexample to the valid combined certificate. They demonstrate that the **two missing obligations are independently satisfiable/failable inside the actual positive primitive focused geometry**:
- all-support without size; and
- size without all-support.
The prior Step040 actual Tail/Gap examples satisfied neither obligation, so these are distinct and more discriminating scientific controls.

**Recommended Step041:** prove the two actual independence witnesses *kernel checked*, plus a narrowly framed diagnostic contract preserving the Step040 theorem's exact hypotheses. If feasible, identify the new q43 source-derived (7,16) kernel with Step035's second-row/fifth-column ideal, demonstrating that the same common-receiver construction is genuinely occupied by a second native arithmetic input, not just arbitrary supplied roots. Explicitly **STOP after this one frontier test** and reassess whether any known source theorem can prove *both* collective prime support and an independent size bound; do not start another arbitrary depth or root grid.
If Step041 merely packages tautological case splits, classify as mathematical diagnostic Outcome B and not a new global obstruction. A next decisive FLT task would need genuinely new hypotheses/proofs distinguishing Δ=0 or the actual signed counterexample recursion, not just a restatement of the conditional zero criterion.

No PR, rebase/merge, facade, new square/adic tower, general-prime grid, global FLT7 impossibility or signed provider construction authorized.
