# Report: Petal 083

Date: 2026/06/30 15:16 JST

## Scope

Checkpoint `083` implemented the general finite layer-cake stage for
`DkMath.Collatz.PetalBridge`.

The input instruction was:

```text
general finite layer-cake
  -> list / Nat helper
  -> Collatz height profile theorem
  -> prefix theorem
  -> Collatz-specific tail theorem
  -> small experiments and next inference
```

The temporary `__next_implementation-083.md` file was used only as input.  It
was not edited, following the docs filename rule for temporary `__*` files.

## Implemented API

New private helpers:

```lean
range_threshold_count_le
list_sum_ge_sum_countGe_range
```

New public finite layer-cake theorems:

```lean
orbitWindowHeightSeq_sum_ge_sum_countGe_range
orbitWindowHeightPrefix_sum_ge_sum_countGe_range
```

New Collatz-specific tail forms:

```lean
orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
```

New practical observation-to-drift bridges:

```lean
orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
```

New explicit experiment witness:

```lean
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
```

## Main Result

The central theorem is:

```lean
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k
```

Meaning:

```text
CountGe 1 + CountGe 2 + ... + CountGe H <= sumS
```

This upgrades the previous two-layer and three-layer observations into a
general finite layer-cake theorem.

## Proof Shape

The proof was split before touching Collatz-specific vocabulary.

First, a local threshold-count helper:

```lean
private theorem range_threshold_count_le
    (H x : ℕ) :
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
```

Meaning:

```text
Among thresholds 1, ..., H, at most x thresholds are <= x.
```

Then, a Collatz-independent list theorem:

```lean
private theorem list_sum_ge_sum_countGe_range
    (l : List ℕ) (H : ℕ) :
    (Finset.range H).sum
        (fun t => l.countP (fun x => decide (t + 1 ≤ x)))
      ≤ l.sum
```

The list proof is the finite layer-cake engine.  Each head element `x`
contributes to the visible layers `t + 1 <= x`, and
`range_threshold_count_le` bounds that contribution by `x`.

The Collatz theorem then follows by applying the list theorem to
`orbitWindowHeightSeq n k` and rewriting its sum as `sumS n k`.

## Collatz Tail Form

Because Collatz odd-state dynamics already proved:

```text
CountGe 1 = k
```

the more useful form separates the base layer:

```lean
theorem orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
    (n : OddNat) (k H : ℕ) :
    k + (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 2))
      ≤ sumS n k
```

Meaning:

```text
base peeling k
  + CountGe 2
  + CountGe 3
  + ...
  + CountGe (H + 1)
  <= sumS
```

This is the currently most useful drift-budget theorem.

## Prefix Form

The prefix version was also implemented:

```lean
theorem orbitWindowHeightPrefix_sum_ge_sum_countGe_range
    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 1))
      ≤ sumS n r
```

and the Collatz-specific prefix tail:

```lean
theorem orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
    (n : OddNat) {r k H : ℕ} (hr : r ≤ k) :
    r + (Finset.range H).sum
        (fun t => orbitWindowHeightPrefixCountGe n k r (t + 2))
      ≤ sumS n r
```

This keeps local-window diagnostics available without leaving the finite
observation-window setting.

## Experiment

The four-layer theorem was added as an explicit witness:

```lean
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three_add_countGe_four
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
        orbitWindowHeightCountGe n k 3 + orbitWindowHeightCountGe n k 4 ≤
      sumS n k
```

This theorem is not proved by a new hand-written induction.  It is derived from
the general finite layer-cake theorem at `H = 4`.

Result:

```text
The fixed-depth layer theorems are now examples of the general theorem.
```

## Practical Bridge

Two small corollaries turn future occupation estimates directly into drift
lower bounds:

```lean
theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
    (n : OddNat) (k m : ℕ)
    (hm : m ≤ orbitWindowHeightCountGe n k 2) :
    k + m ≤ sumS n k
```

```lean
theorem orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
    (hm : m ≤ orbitWindowHeightPrefixCountGe n k r 2) :
    r + m ≤ sumS n r
```

Meaning:

```text
If a future residue/address theorem proves CountGe 2 >= m,
then the drift lower bound k + m <= sumS follows immediately.
```

This is the bridge from Petal address occupation to Collatz drift.

## Documentation

Updated:

```text
DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

The status document now records:

```text
finite layer-cake
finite tail layer-cake
four-layer experiment witness
external CountGe 2 lower-bound bridge
```

## Verification

The targeted build passed:

```bash
lake build DkMath.Collatz.PetalBridge
```

Existing unrelated warning still appears:

```text
DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses sorry
```

## Next Inference

The next mathematical target is no longer layer-cake itself.  It is now:

```text
CountGe 2 lower bound
```

For Collatz:

```text
height >= 2
  means v2(3n + 1) >= 2
  means 4 divides 3n + 1
```

For odd `n`, this should correspond to a residue class modulo `4`.

Thus the next implementation direction should be:

```text
height >= 2
  -> residue condition modulo 4
  -> address / residue occupation count
  -> CountGe 2 lower bound
  -> k + m <= sumS
```

Concrete next candidates:

```lean
theorem rawHeightLabel_two_le_iff_mod_four
theorem orbitWindowHeight_two_le_iff_mod_four
theorem orbitWindowHeightCountGe_two_eq_residueCount
```

The exact theorem names and statement shape should be adjusted after checking
the existing `V2`, `Shift`, and modular arithmetic API.
