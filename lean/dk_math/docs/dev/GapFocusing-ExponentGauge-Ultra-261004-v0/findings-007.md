# Instruction 007 findings

## Initial source audit

- Baseline HEAD `bed7c6d4b`;006 committed as `e18edcd7b`; initial working tree clean.
- Existing candidate/wave/quotient transposes and uncovered balance are reused. No second incidence ledger.
- `ParitySafeReducedResidue` already proves same-wave2q divisibility and exact active-wave/reduced-quotient cardinality.
- `ParitySafeMobiusOddCorrection` already proves the exact odd endpoint cardinal, nonpositive full odd-anchor Möbius correction, and global odd-raw upper bound. A new odd-raw theorem alone would duplicate existing production mathematics.
- The odd-multiple floor-count proof exists privately in that module. Expose the existing proof with an application-owned public name for the one-divisor upper bound rather than duplicate it.
- All eleven requested source modules were located; exact names and their interfaces are recorded in the source inventory probe.

## Initial arithmetic diagnostics (not proof)

For successor shells21..40, uniform2q packing gives602, exact odd endpoints510, and removing the best single odd anchor-prime divisor per wave gives425. A=490 and005's conditional temporal charge38 set the main threshold528.

At N=20, widths20,10,5,4,3,2,1 give single-divisor upper totals425,162,73,55,45,24,7 versus candidate totals490,200,90,70,54,32,12. These require Lean kernel checks through a structural incidence upper theorem, without evaluating actual I.

The smallest possible positive block width1 appears achievable for the explicit shell21. This is not uniform in N and therefore not Legendre.

## Checkpoint: structural upper theorem

- The new production module builds. Existing2q rigidity is converted to an actual-wave packing bound by injecting seat quotient blocks; no exact-adjacency assumption is made.
- Odd quotient endpoints are retained exactly. The existing odd-multiple floor proof is publicly exposed and reused to remove one odd anchor-prime divisor's hits.
- Reduced quotient cardinality is bounded by every valid one-divisor exclusion, hence by their finite minimum. The final wave cap takes the minimum with uniform2q packing.
- The shell and block incidence upper theorems assume no full cover.
- Exact block representation switching and Nat-safe unconditional uncovered-deficit bounds are implemented. The conditional temporal38 is used only by a full-cover contradiction consumer, not as an unconditional excess lower bound.
- A seat-side point-prime-factor subset and incidence bound are implemented for independent comparison; they include large point factors and are not claimed sharper.

## Checkpoint: main block and width reduction

- Kernel-checked structural cap425, odd endpoint510, uniform spacing602. Main threshold490+38=528 gives slack103. No actual-incidence evaluation is used by the structural contradiction.
- The main unconditional uncovered lower bound is65, using excess>=0. It is stronger than what endpoint510 alone supplies without a temporal premise.
- Widths20,10,5,4,3,2,1 all succeed at N=20, with candidate-minus-upper deficits65,38,17,15,9,8,5. Smallest positive width is1, shell21. This is an explicit finite shell, not a theorem uniform in N.
- Shell21 has upper7 and candidates12; the existing prime consumer yields a prime strictly between441 and484. The mature odd endpoint cap already gives10 here, so the new divisor correction strengthens the quantitative deficit rather than uniquely enabling this finite prime example.
- Shell29's cap31 exceeds candidates28, so the zero-excess provider fails. This disproves extending that sufficient condition uniformly, not Legendre itself.

## Checkpoint: computational normalization

The cap minimum is represented by a computable Finset fold with the raw endpoint cap as its initial value. Ordinary elaborator `decide` stops at the irreducible well-founded `Nat.primeFactorsList`; `decide +kernel` unfolds it and checks the same arithmetic in the kernel. No native evaluator or additional axiom is used. The original min' experiment and the unfolding investigation are local elaboration checkpoints, not mathematical failures.

## Checkpoint: precise remaining slack

- The six residual-wave examples account for all seven units between the new cap425 and the old diagnostic incidence418. Their anchor exclusions require more than one odd anchor divisor.
- Low-prime q<=7 capacities total261. Large aggregate low-q incidence and residual cap overcount are distinct issues.
- Point-prime-factor seat upper17 at shell21 is weaker than wave upper7.
- Same-wave n=18,q=5 seats{1,11,31} disprove exact2q adjacency; only divisibility and lower spacing are consumed.
- Next targets are a two-divisor union bound and independent local support-excess certificates. Their exact statements and limits are written in report007.

## Final decision

Outcome A applies to explicit block width shrinking to1 at N=20. No uniform width1 or uniform fixed-width statement is established. Acceptance build, complete declaration axiom coverage and scans are recorded separately in validation007.

Final acceptance checks pass:10374 Lake jobs for the changed counting module, new upper module, regression, facade and root;48/48 source-derived declaration dependency sets use only the standard axioms; forbidden-token, tracked/new-file whitespace and local document-link checks pass. Existing root research warnings do not occur in any new declaration's dependency set.
