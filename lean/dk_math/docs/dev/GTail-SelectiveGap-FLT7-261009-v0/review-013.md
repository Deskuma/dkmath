# Review 013 — oriented Eisenstein residue evaluations

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 013 COMPLETE / Outcome B**

## Evidence reviewed

- `DkMath/Lib/NumberTheory/GTailSevenEisensteinResidue.lean` (162 lines)
- `DkMathTest/NumberTheory/GTailSevenEisensteinResidue.lean` (113 lines)
- `report-013.md`, `source-inventory-013.md`, project `ROADMAP.md`
- Existing `TraceOneQuadratic`, `TraceOneLatticeLanding`, `EisensteinLatticeLanding`, `TraceOneResidueType` and `QuadraticResidueType` APIs, and Step 012 typed norm interface.

Review method: **static inspection of pushed GitHub Lean declarations, proof route and regression content**. Focused builds and axiom results are supplied by Codex's local report and **were not independently rerun** by this reviewer.

## Findings

1. `gtailSevenNormCoord_mul_conj` reuses the existing element equation `traceOne_mul_conj` and the typed natural-input norm result, without replacing an element equality by a scalar value assertion.
2. `scalar_dvd_gtailSevenNormCoord_iff` correctly characterizes divisibility by the embedded integer q: the two integral coordinates must both be divisible by q. It holds even at q=0 and does not falsely conclude embedded q-element divisibility from divisibility of a norm value.
3. `eisensteinResidueEval` carries integer coordinates into `ZMod q`; addition is unconditional, multiplication is proved only with the exact quadratic relation `t²-t+1=0`. These are adequate ingredients for a *future* bundled ring homomorphism. No ring hom was claimed without its laws.
4. The chosen root `t=-(a:ZMod q)/(b:ZMod q)` uses a prime-field instance and the explicit premise q∤b. Its polynomial relation follows from q|Q. The **first zero evaluation** needs only q∤b, not q|Q.
5. `eisensteinResidueEval_conj` proves conjugating the input exchanges t with 1-t. `eisensteinResidueEval_gtailSevenNormCoord_conjugate` computes the second value as 2a+b, with no q≠3 assumption.
6. When q≠3, q|Q and q∤b, the identity `4Q=(2a+b)²+3b²` forces 2a+b nonzero modulo q. Hence the conjugate evaluation is nonzero and the root parameters are distinct. q=3,a=b=1 is a valid repeated-root countercheck.
7. q=43,a=5,b=8 checks t=37, 1-t=7, actual slot values 0 and 18, and the simultaneously true facts 43|norm(alpha) and not (embedded 43)|alpha. The zero first slot says only that a linear residue evaluation vanishes, not that both integer coordinates vanish.
8. The new module imports no FLT owners or cyclotomic/ideal-class closure endpoints. The existing `TraceOneResidueType.residueMap` retains a two-coordinate `QuadraticAlgebra` residue model; the new evaluation is a selected scalar slot, with separate additive and relation-guarded multiplicative proofs. This is a distinct, narrow receiver rather than a duplicate residue carrier.
9. Codex reports final successful targeted builds of both new targets and both Step 012 regressions, 16 kernel-checked examples, all **15 public declarations** with only standard axioms, and clean source/import/whitespace scans. Intermediate elaboration and finite-ratio reduction issues were repaired without weakening theorems.

## Classification and limits

**APPROVED / Outcome B.** A full residue orientation is now checked, but it is not yet a bundled ring homomorphism, an ideal, an element prime, a chosen prime ideal above q, an equality (q)=P*Pbar, a unit-power class, or a descent map.

The next highest-value **neutral** step is to package the proved ring laws as a `RingHom`, expose its `RingHom.ker` as a **typed ideal**, and prove the field-valued norm-product identity:

```text
((norm z : ℤ) : ZMod q) = eval_t(z) * eval_(1-t)(z)
```

for any root t of t²-t+1. For prime q, this makes q|norm z equivalent to membership in at least one of the two evaluation kernels. At q=43 the selected alpha belongs to exactly one kernel; at q=3 the two roots can coincide. Distinguish **constructing two kernels** from proving a prime-ideal factorization of the principal ideal (q), which requires separate ideal-level work.

No FLT7 counterexample, norm-to-square converse, cyclotomic root-depth packet, or global class/unit claim is authorized by Step 013. No merge, PR, or facade promotion.
