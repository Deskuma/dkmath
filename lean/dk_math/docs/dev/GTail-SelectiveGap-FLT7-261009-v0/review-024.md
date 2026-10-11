# Review 024 — first-order ideal depth cutoff under scalar q-squarefree guard

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 024 COMPLETE / Outcome B**

## Source basis and verification limitations

Reviewed the actual pushed GitHub files:
- `DkMath/FLT/Seven/GTailCyclotomicTailDepthOne.lean` (127 lines);
- `DkMathTest/FLT/Seven/GTailCyclotomicTailDepthOne.lean` (132 lines);
- `report-024.md`, `source-inventory-024.md`;
- existing Steps 020–023 bare-root prime kernel, six-root splitting, exact GTail element product and inverse-index incidence;
- the preexisting July 2026 `SevenRamifiedFusionOrientedCarrierValuationOwnership` and U1.2 report for comparison only.

This is a **static Lean source/proof-route review**. Codex reports final successful incremental builds of both new targets and the Step 023/022 test regressions, 30 examples, seven new public theorem axiom audits containing only `propext`, `Classical.choice`, `Quot.sound`, and clean direct-import/placeholder audits. No independent Lean build was executed by the reviewer. The failed intermediate elaborations and fixes are logged honestly.

## Verified mathematical scope

1. `cyclotomic_natCast_mul_injective` proves that multiplication by a **nonzero natural integer scalar** is injective on the actual six-coordinate degree-six ring. The proof applies the existing `coordinates_natCast_mul` and coordinate injectivity, then cancels nonzero integer q in each signed coordinate; no new `IsDomain`, UFD, PID or class group is assumed.
2. `natCast_mem_scalar_mul_sixRootKernel_iff` proves, **for a natural scalar n only**, `(n:R)∈cyclotomicScalarIdeal q * K_j ↔ q²∣n`. It uses the genuinely available `Ideal.mem_span_singleton_mul` API, an actual witness `n=q*y` with y∈K, the first signed coordinate to derive q∣n, a genuine source-ring scalar cancellation to identify y with the natural quotient m, then `map_natCast`/integer contraction to infer q∣m. The reverse direction constructs `y=q*k∈K`. It DOES NOT assert the generally false **ideal equality** `(q)*K_j=(q²)`.
3. `prod_mem_prod_mul_of_mem_square` is a generic finite-family CommRing ideal lemma: selected factor in J_i² plus the other first-power memberships forces the element product into `(∏J)*J_i`. The source uses `Finset.prod_erase_mul`, real finite ideal product membership and `Ideal.mul_mem_mul`. No bogus claim that an individual factor generates its receiving ideal is used.
4. `prod_inverseSlot_sixRootKernel_eq_scalarIdeal` reindexes the *actual six kernels* by the Step 023 inverse-slot involution, via an explicit Lean `Equiv`, and reuses the Step 022 product equality. There is no conflation of the factor and ideal finite products.
5. `GTail_mem_scalar_mul_kernel_of_factor_mem_square` combines this generic excess-copy lemma, the actual Step 023 product `∏F_i=GTail` as a ring element, and each factor's already checked unique ideal address. This does imply scalar Tail belongs to `(q)*K_assigned` whenever one selected factor belongs to `K_assigned²`.
6. `gtailCyclotomicFactor_not_mem_square` uses only the **explicit scalar premise** `q²∤GTail` and the preceding scalar iff to reach contradiction. `gtailCyclotomicFactor_depth_one` bundles genuine K membership with K² nonmembership. The proof is nonvacuous and is not presented as an unconditional ideal-adic exponent theorem or a new FLT7 contradiction.
7. For q=43,c=9,g=4, T=14491387=43·337009 with 337009%43=18; all six actual integral factors belong to their uniquely assigned K and not K², via the **generic** theorem. The scalar T belongs to (43) but not (43)*K_j for any slot. Tests include scalar 1849∈(43)*K and 43∉(43)*K.
8. A genuine guard-failure case q=43,c=9,g=1165 has q∤c,g, q|T and **q²|T**, with identical canonical ratio r=11. The report proves only that `q²∤T` cannot be supplied, **not** whether each F_i actually lies in K² in this case. It is a valuable potential next-step witness, not a contradiction.
9. Degenerate c=0 or g=0 and q13 Gap remain excluded from the q-local depth theorem while the Step 023 unconditional source factorization remains intact. Characteristic q7's different ramified evaluation is not falsely identified with this packet-free six-root branch. q43,a5,b8 is explicitly not a Fermat7 solution.
10. Previous July 2026 oriented valuation owner already provides `carrier∈s.orientedKernel^k ↔ k≤s.quotientExponent` **for signed-depth packet-indexed carriers**, distinct from the new natural GTail factors and bare canonical Tail root. No unproved identification of signed carrier, signed quotient-root valuation or prime kernels was used to claim novelty.
11. Axiom/source audits are consistent with the report: 7 theorems, no added axioms/sorryAx/unsafe/new facade/reverse Lib→FLT imports. The report's focused test builds exit 0, and no full repository rebuild was claimed.

## Next research gate: prove or refute the missing reverse square-depth direction

The newly checked forward direction is

```text
F_i(c,g)∈K_(sixInverseSlot i)^2 → q²∣GTail 7 1 g c
```

under the canonical unit/Tail conditions. Step 024 provides a **satisfiable higher-support sample** q43,c9,g1165. The natural next step is to study the converse:

```text
q²∣GTail 7 1 g c → F_i(c,g)∈K_(sixInverseSlot i)^2 .
```

It has a plausible *elementary comaximal saturation* route: q²|T implies scalar T∈K_j² because q∈K_j; the product of the five *other* factors lies outside K_j because K_j is prime and each is excluded at the first power. Since K_j is maximal, an element outside K_j is invertible modulo K_j and modulo K_j². Thus from `T=F_i*(∏_{h≠i}F_h)∈K_j²`, infer `F_i∈K_j²`. This requires **a checked comaximality-with-K² or quotient-unit lemma**; it is NOT a consequence of primality of K_j alone (prime membership only controls K_j, not K_j²).

If proved, this would yield **the exact second-level iff**
`F_i∈K_assigned² ↔ q²|T` for arbitrary natural Tail inputs with the canonical q-local unit hypotheses. It is a genuinely stronger boundary, not an assumption that q²∤T holds. It would positively classify the q43,c9,g1165 witness at depth two.

Source-check Mathlib ideal-powers, coprime ideals and local cofactor cancellation APIs first, keeping no signed-depth packet assumptions. Avoid claiming generic all-k valuations or element principalization on the strength of the k=2 result alone.

**Decision: APPROVED — Outcome B**; next authorize only the bounded second-depth converse/equivalence experiment. No PR, branch merge, facade promotion, cyclotomic class/unit work, primitive Fermat descent or unconditional FLT7 claim.
