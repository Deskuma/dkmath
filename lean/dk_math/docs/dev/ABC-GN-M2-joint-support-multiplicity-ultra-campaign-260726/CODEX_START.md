# Codex Start Entry - ABC-GN M2/M3 Ultra Campaign

作業 branch:

```text
wip/ABC-GN-M2-joint-support-multiplicity-ultra-campaign-260726-v1
```

作戦室:

```text
lean/dk_math/docs/dev/ABC-GN-M2-joint-support-multiplicity-ultra-campaign-260726/
```

## Status

```text
M1  odd-prime exceptional valuation excess      complete / merged / closed Core
M2  exact fresh support identity                 complete
M3  finite layer-cake / deep-prime pincer        complete
Order packet  q ≡ 1 mod p                        complete
Raw-variable endpoint transport                  complete
Legacy tail/counting bridge                      complete
Uniform joint contract                           open / exact ABC-strength frontier
Final target                                     not reached; abc_main_axiom retained
```

Current instruction:

```text
instruction-ultra-001.md
```

## Ultra-001 current frontier

Production modules:

```text
DkMath.ABC.GNJointPressureOddPrime
DkMath.ABC.GNDepthPressure
DkMath.ABC.GNPrimeSupportOrder
DkMath.ABC.GNLegacyTailCountingBridge
```

Completed theorem chain:

```text
exact prime-exponent lift-radical identity
-> exact fresh support-plus-depth channel mass
-> odd-prime joint pressure equivalence
-> direct logarithmic and pointwise ABC bridge
-> positive and zero-coordinate raw-variable endpoint
```

Recovered legacy coordinates and counting entry:

```text
non-exceptional valuation excess
  = log piSqRad(non-exceptional part)
  + log twoTail(non-exceptional part)

finite Hensel residue cover
  -> GN deep-lift interval count
  -> padic depth layer
  -> legacy exp_layer_cake
```

The next arithmetic input on this lane is the construction of a residue cover
of cardinality at most `p - 1`. This is not yet proved by the bridge module.

The remaining input is an unconditional construction of:

```lean
ABCGNOddPrimeJointContract ε
```

for every `ε > 0`. This is not a bookkeeping remainder: under the exact
identities it is the uniform arithmetic inequality that supplies ABC itself.
The deep-lift branch cannot be eliminated from freshness and exact order
alone; the existing kernel-clean counterexample has `GN 3 2 3 = 7^2`.

Therefore `abc_main` and `abc_main_axiom` remain unchanged. Do not emit
`ULTRA_FINAL_REPORT.md` or claim final victory unless this contract is
constructed without a new trust assumption.

## Mission

This is the formal start point of the ABC-GN joint support-multiplicity Ultra campaign.

The final victory theorem is the existing public theorem surface:

```lean
theorem DkMath.ABC.abc_main (ε : ℝ) (hε : 0 < ε) :
  ∃ K : ℝ, (1 : ℝ) ≤ K ∧
    ∀ (a b c : ℕ), a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)
```

At campaign start this theorem is still proved only by:

```lean
abc_main_axiom ε hε
```

The campaign goal is to replace that dependency with a Lean proof assembled from the DkMath ABC-GN theorem chain, then delete `abc_main_axiom` after the replacement theorem and downstream audit are complete.

A contract theorem, reduction theorem, pointwise theorem, or exact obstruction report is not the final victory flag. The victory flag is the public `abc_main` theorem itself with no project axiom dependency.

## Read order

Read current repository source, not remembered theorem names.

```text
1. README.md
2. CODEX_START.md
3. instruction-ultra-001.md
4. ../ABC-GN-M1-odd-p-exp-exceptional-excess-260725/FINAL_REPORT.md
5. DkMath/ABC/GNExceptionalExcessOddPrime.lean
6. DkMath/ABC/GNFinalBudgetBridge.lean
7. DkMath/ABC/GNSupportReturn.lean
8. DkMath/ABC/GNValuationExcess.lean
9. DkMath/ABC/GNHighLift.lean
10. DkMath/ABC/ABCMainTheorem.lean
11. relevant Petal, PrimitiveSet, valuation, order, ZMod, and power-lift modules discovered by search
```

Repository paths in items 5-11 are relative to:

```text
lean/dk_math/
```

## Closed Core from M1

For every ABC triple `T` and odd prime exponent `p`:

```lean
Triple.GNExceptionalValuationExcess_eq_zero_of_oddPrime
Triple.GNExceptionalExcessBudgetAffine_zero_of_oddPrime
Triple.GNValuationExcessBudgetAffine_of_oddPrime_nonExceptional
```

Thus the exceptional affine budget is exactly:

```text
τe = 0
De = 0
```

and the full valuation-excess budget is exactly the non-exceptional budget.

Do not reopen M1 unless a concrete type, dependency, or mathematical defect is found.

## Existing final bridge

The current deterministic bridge already proves:

```text
support affine budget
+
valuation-excess affine budget
+
coefficient margin
->
pointwise ABC bound
```

and packages a uniform contract for positive triples.

The remaining task is not to re-prove this transport. It is to defeat the remaining uniform arithmetic input and connect the completed result to the full raw-variable `abc_main` surface, including zero-coordinate endpoints.

## Ultra operating doctrine

Codex and Wise Wolf are peer reasoning agents over the same Lean-verified program.

```text
not master and subordinate
not planner and transcription engine
two reasoning brains with different search paths
```

A checkpoint is an auditable observation point, not a permission gate.

After each checkpoint:

```text
inspect the theorem and dependency state
identify the strongest remaining Gap
reuse all completed lemmas across attack lanes
choose the next strongest route
continue implementation and verification
record a compact report
```

Do not stop because one planned lemma or interface has been completed. Do not return merely with a proposal when an implementation route remains available.

Repository publication operations remain user-controlled unless separately requested. Keep local changes reviewable and reports current.

## Ultra attack lanes

Run multiple fronts and share results between them:

```text
Lane A  exact odd-prime accounting and joint pressure
Lane B  exact lift-radical / fresh-support identity
Lane C  valuation-excess layer-cake decomposition
Lane D  support-heavy / multiplicity-heavy pincer
Lane E  multiplicative order and q ≡ 1 mod p
Lane F  deep q-adic lift / Hensel / Wieferich-type constraints
Lane G  primitive-divisor, Petal, PrimitiveSet, and repeated-lift interaction
Lane H  uniform joint budget and final abc_main integration
```

Do not isolate these lanes as independent projects. A lemma proved in one lane must immediately be tested as ammunition in the others.

## Final victory conditions

The campaign is complete only when all of the following hold:

```text
1. abc_main has the existing public statement.
2. abc_main is proved without abc_main_axiom.
3. abc_main_axiom is deleted from production source.
4. zero-coordinate and positive-coordinate cases are all closed.
5. #print axioms abc_main shows no DkMath project axiom.
6. no new axiom, sorry, native_decide, or finite enumeration is used.
7. public DkMath.ABC and full DkMath builds succeed.
8. final report records the completed theorem chain and the removed axiom dependency.
```

## Hard boundaries

```text
no new axiom
no sorry
no native_decide
no finite enumeration as a general proof
no weakening or renaming of the public abc_main statement
no hidden replacement axiom or opaque unproved contract
no claim that a conditional contract theorem is abc_main
no ABC -> FLT5 production dependency
no FLT7 WIP dependency
no unrelated refactor
```

`abc_main_axiom` is the target for deletion, not an admissible source for any new theorem.

## Begin

Read `instruction-ultra-001.md`, inspect the current source, and begin the multi-front campaign immediately.
