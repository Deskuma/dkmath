# Report Petal 095: Orbit-Level Recursive Two-Adic Petal

## Checkpoint

This checkpoint follows `__next_implementation-095.md`.

The target was to move from practical raw residue-cell theorems to orbit-label
theorems.  The missing bridge was:

```text
large residue modulo 2^(r+2)
  -> visible source residue modulo 8
```

The checkpoint closed with no new Lean `sorry`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New residue reduction helper:

```lean
mod_eq_mod_of_dvd_modulus
```

New source-entry bridges:

```lean
mod_eight_eq_seven_of_recovery_residue_of_two_le
mod_eight_eq_seven_of_continuation_residue_of_one_le
```

New orbit-label recursive transition theorems:

```lean
oddOrbitLabel_succ_recovery_residue_of_mod
oddOrbitLabel_succ_continuation_residue_of_mod
```

## Residue Reduction Bridge

The local helper is:

```lean
theorem mod_eq_mod_of_dvd_modulus
    {a M d : ℕ} (hd : d ∣ M) :
    a % d = (a % M) % d
```

It wraps `Nat.mod_mod_of_dvd` in the orientation used by the Collatz Petal
bridge.

Reading:

```text
if a smaller modulus d divides a larger modulus M,
then the M-address determines the d-address
```

This is the general mechanism for projecting a deep two-adic Petal cell down
to its visible `mod 8` entry channel.

## Source Entry

Recovery side:

```lean
theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
    (r m : ℕ) (hr : 2 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    m % 8 = 7
```

Continuation side:

```lean
theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
    (r m : ℕ) (hr : 1 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    m % 8 = 7
```

The lower bounds on `r` are not decoration.  They ensure that the source cell
has enough two-adic depth to project to the exact height-one `7 mod 8` channel.

## Orbit-Level Theorems

Recovery sibling:

```lean
theorem oddOrbitLabel_succ_recovery_residue_of_mod
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
```

Continuation sibling:

```lean
theorem oddOrbitLabel_succ_continuation_residue_of_mod
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
      2 ^ (r + 1) - 1
```

This is the orbit-label version of the recursive two-adic Petal:

```text
recovery sibling:
  exits one level outward

continuation sibling:
  becomes the next retention cell
```

The previous fixed ladder up to `mod 512` is now explained by a general theorem
at the actual accelerated orbit-label layer.

## Proof Shape

Each orbit theorem follows the same four-step pattern:

```text
1. use the large residue hypothesis to prove source mod 8 = 7
2. use the exact height-one theorem for the 7 mod 8 channel
3. rewrite oddOrbitLabel (i+1) as T (iterateT i n)
4. rewrite T as (3m + 1) / 2 and apply the practical raw theorem
```

The important point is that the raw theorem is no longer isolated arithmetic.
It now acts on the actual Collatz orbit label.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
residue reduction through a divisor modulus
large residue -> mod 8 source-entry
general orbit-label recovery transition
general orbit-label continuation transition
```

## Factor-Layer Design Note

This checkpoint also clarifies the next conceptual split.

The Collatz state has at least two visible coordinate systems:

```text
TwoAdicPetalCoordinate:
  the residue address modulo 2^r

OddFactorCarrier:
  the odd-prime factor structure of the current or next odd core
```

After one accelerated step:

```text
3m + 1 = 2^h * nextOdd
```

The two-adic coordinate controls the peeling branch:

```text
height h
recovery sibling
continuation sibling
retention cell
```

The odd factor carrier controls the remaining odd core:

```text
which odd primes divide nextOdd
which were already present in m
which are newly introduced by the step
```

Useful future vocabulary:

```text
NewOddPrimeFactor:
  a prime p such that p | (T n).val and not p | n.val

CoordinateFactorInteraction:
  how a two-adic Petal branch changes, or correlates with,
  the odd-prime carrier of the next odd state
```

This should remain docs/design level for now.  The current Lean bridge has just
stabilized the two-adic coordinate transition; the factor layer should be added
only after the coordinate-count API is ready.

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

The residue-cell occupation count API was not added.

The natural next definition is still:

```lean
def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

This should come after the transition theorem because it can now count actual
orbit-label addresses at arbitrary two-adic depth.

## Next Implementation Candidates

Candidate A: pow-two residue count.

```lean
def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

Candidate B: count bound.

```lean
theorem orbitWindowResidueCountPow2_le_window
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n k depth residue ≤ k
```

Candidate C: bridge existing named counts into the generic count.

```lean
theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k =
      orbitWindowResidueCountPow2 n k 3 7
```

Candidate D: docs-only design for future factor layer.

```text
TwoAdicPetalCoordinate
OddFactorCarrier
NewOddPrimeFactor
CoordinateFactorInteraction
```

The next strong technical direction is to count occupation of arbitrary
two-adic cells, then use the new orbit-level recursive theorem to relate
occupation at depth `r + 2` to occupation at depth `r + 1` in the next shifted
window.
