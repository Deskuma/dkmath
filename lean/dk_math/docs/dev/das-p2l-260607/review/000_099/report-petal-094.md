# Report Petal 094: Practical Residue Form and Source Entry

## Checkpoint

This checkpoint follows `__next_implementation-094.md`.

The goal was to move from the expanded raw theorem to a practical theorem about
an arbitrary label `m` known only by its residue class.

The checkpoint closed with no new Lean `sorry`.

## Implemented Lean Surface

File:

```text
lean/dk_math/DkMath/Collatz/PetalBridge.lean
```

New practical residue-class theorems:

```lean
next_recovery_residue_of_mod
next_continuation_residue_of_mod
```

Fixed anchors rederived from the general theorem:

```lean
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_twohundredfiftyfive_via_general
next_mod_twohundredfiftysix_of_mod_fivehundredtwelve_eq_fivehundredeleven_via_general
```

Source-entry residue checks:

```lean
recovery_residue_mod_eight_eq_seven
continuation_residue_mod_eight_eq_seven
```

## Main Result

Recovery sibling:

```lean
theorem next_recovery_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ r - 1
```

Continuation sibling:

```lean
theorem next_continuation_residue_of_mod
    (r m : ℕ)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    ((3 * m + 1) / 2) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
```

This is the practical form of the recursive two-adic Petal:

```text
parent retention cell
  -> recovery sibling
  -> continuation sibling = next retention cell
```

The theorem now applies directly to any label sitting in the relevant residue
cell, not only to a syntactic expanded expression.

## Proof Reading

The proof is short because checkpoint 093 already did the hard arithmetic.

For `M = 2^(r+2)`, decompose:

```text
m = M * (m / M) + m % M
```

This is obtained from `Nat.mod_add_div` and normalized by `omega`.

After rewriting by the hypothesis on `m % M`, the goal is exactly the expanded
theorem from checkpoint 093:

```lean
next_recovery_residue_expanded r (m / 2 ^ (r + 2))
next_continuation_residue_expanded r (m / 2 ^ (r + 2))
```

## Usability Tests

The old fixed `mod 512` anchors were rederived from the general theorem:

```text
255 mod 512 -> 127 mod 256
511 mod 512 -> 255 mod 256
```

This confirms that the previous numeric ladder is now an instance of the
general recursive theorem.

## Source Entry Condition

The next orbit-label theorem cannot use the raw step unless the source is in
the exact height-one channel.  The needed residue fact is now explicit:

```lean
theorem recovery_residue_mod_eight_eq_seven
    (r : ℕ) (hr : 2 ≤ r) :
    (2 ^ (r + 1) - 1) % 8 = 7

theorem continuation_residue_mod_eight_eq_seven
    (r : ℕ) (hr : 1 ≤ r) :
    (2 ^ (r + 2) - 1) % 8 = 7
```

Reading:

```text
recovery source needs 2 <= r
continuation source needs 1 <= r
both enter the exact height-one 7 mod 8 channel
```

This is why the future orbit-label theorem should carry a lower-bound
hypothesis on `r`.

## Documentation Sync

Updated:

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status note now records:

```text
practical hm form
mod 512 anchors via the general theorem
source-entry mod 8 checks
next orbit-label condition
```

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

The orbit-label generalization itself was not added in this checkpoint.

Reason:

```text
we still need the bridge from a large residue hypothesis on oddOrbitLabel
to oddOrbitLabel % 8 = 7
```

The new residue checks prove the source residue itself is `7 mod 8`, but the
next theorem must transfer this through an arbitrary label hypothesis:

```lean
m % (2 ^ (r + 2)) = residue
  -> m % 8 = 7
```

This is the next small missing bridge.

## Next Implementation Candidates

Candidate A: practical residue-to-`mod 8` bridge.

```lean
theorem mod_eight_eq_seven_of_recovery_residue_of_two_le
    (r m : ℕ) (hr : 2 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    m % 8 = 7
```

Candidate B: continuation counterpart.

```lean
theorem mod_eight_eq_seven_of_continuation_residue_of_one_le
    (r m : ℕ) (hr : 1 ≤ r)
    (hm : m % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    m % 8 = 7
```

Candidate C: orbit-label recovery theorem.

```lean
theorem oddOrbitLabel_succ_recovery_residue_of_mod
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
```

Candidate D: orbit-label continuation theorem.

```lean
theorem oddOrbitLabel_succ_continuation_residue_of_mod
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (i : ℕ)
    (hmod :
      oddOrbitLabel n i % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1) :
    oddOrbitLabel n (i + 1) % (2 ^ (r + 1)) =
      2 ^ (r + 1) - 1
```

The likely proof route for A and B is to use divisibility of moduli:

```text
8 | 2^(r+2)
m % 8 = (m % 2^(r+2)) % 8
```

After that, the source-entry lemmas from this checkpoint should close the
exact-height-one condition needed for C and D.
