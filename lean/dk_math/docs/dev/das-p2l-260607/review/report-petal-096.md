# Report Petal 096: Generic Pow-Two Residue Counts

## Checkpoint

This checkpoint follows `__next_implementation-096.md`.

Checkpoint 095 lifted the recursive two-adic Petal transition to actual
orbit-label theorems.  The next task was to count how often a window visits a
given two-adic residue cell, then lift pointwise transitions to count-level
source-to-tail inequalities.

The checkpoint closed with no new Lean `sorry`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

Generic source-window residue count:

```lean
orbitWindowResidueCountPow2
orbitWindowResidueCountPow2_le_window
```

Generic shifted-tail residue count:

```lean
orbitWindowResidueCountPow2Tail
orbitWindowResidueCountPow2Tail_le_window
```

Bridge from a named concrete count:

```lean
orbitWindowResidueCountMod8EqSeven_eq_pow2
```

Count-level recursive Petal transitions:

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
```

## Generic Count API

Source-window count:

```lean
noncomputable def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

Shifted-tail count:

```lean
noncomputable def orbitWindowResidueCountPow2Tail
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
```

Both counts have the expected window-size bound:

```text
source count <= k
tail count <= k
```

The named `7 mod 8` source count is now fixed as a concrete instance:

```lean
theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k =
      orbitWindowResidueCountPow2 n k 3 7
```

## Count-Level Recursive Petal Transition

Recovery sibling:

```lean
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
```

Continuation sibling:

```lean
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
```

Reading:

```text
source-window recovery occupation
  <= shifted-tail outward-retention occupation

source-window continuation occupation
  <= shifted-tail next-retention occupation
```

This is the first count-level version of the recursive two-adic Petal.  The
previous theorem said that a single source address determines a next address.
The new theorem says that the number of visits to a source address is bounded
by the number of visits to the corresponding shifted target address.

## Proof Shape

The proofs use the same induction pattern as the earlier concrete count
bridges:

```text
induct on k
split on whether index k is in the source cell
if yes, pointwise orbit-label theorem gives the tail target cell
if no, the target may or may not occur, but the inequality follows by monotonicity
```

The pointwise input is exactly checkpoint 095:

```lean
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
generic pow-two residue counts
generic shifted-tail pow-two residue counts
named 7 mod 8 count as depth-3 instance
count-level recovery transition
count-level continuation transition
```

## Factor-Layer Note

The odd factor layer remains design-level only in this checkpoint.

The current formal layer is:

```text
TwoAdicPetalCoordinate:
  residue address modulo 2^depth

TwoAdicOccupation:
  how often an orbit window visits a residue address
```

The future layer remains:

```text
OddFactorCarrier:
  odd-prime factor structure of the current or next odd core

NewOddPrimeFactor:
  an odd prime appearing in the next odd core but not in the current label

CoordinateFactorInteraction:
  how two-adic branch occupation interacts with odd-prime carrier changes
```

The reason to wait is now clearer: before studying factor interaction, we need
the coordinate distribution itself.  This checkpoint provides the occupation
API for that distribution.

## Verification

Passed:

```text
lake build DkMath.Collatz.PetalBridge
```

The build still reports the existing upstream warning:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
```

No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.

## What Was Not Done Yet

The full residue partition theorem was not attempted in this checkpoint:

```lean
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

This is the next natural theorem.  It says every orbit-label index in the
window is assigned to exactly one residue cell at the chosen depth.

## Next Implementation Candidates

Candidate A: zero-depth sanity check.

```lean
theorem orbitWindowResidueCountPow2_depth_zero_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k 0 0 = k
```

Candidate B: out-of-range residue count is zero.

```lean
theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
    (n : OddNat) (k depth residue : ℕ)
    (hres : 2 ^ depth ≤ residue) :
    orbitWindowResidueCountPow2 n k depth residue = 0
```

Candidate C: full residue partition.

```lean
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

Candidate D: source-to-tail count theorem as a reusable implication helper.

```lean
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

Candidate D would remove duplicated induction from future count transitions.
It is not necessary yet, but if the next checkpoint adds more source-to-tail
rules, it should be considered.
