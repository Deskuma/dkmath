# Petal / FloatWindow implementation report - checkpoint 328

## Result

The revised width obstruction is proved.  The former length-one balanced
carry exception is impossible, and the local claim grammar now has a generic
block-core normal form.

## Saturated next-start obstruction

`CanonicalSaturatedBorderBlock.nextStart_stateUpperCarry_eq_one` proves that
the next block starts with own-width carry one.  The proof uses the exact
saturated forms

```text
x = 4*u - 1
y = (9*u - 1)/2
bitWidth y = bitWidth x + 1
```

and derives `3*y + 1 < 4*x`, hence the carry-two threshold cannot hold.

## Deepest claim hole

The general coordinate theorem

```text
canonicalPaymentSourceAtDepth n k (canonicalBlockLength n k)
  = canonicalBlockStartTime n k
```

identifies the deepest source with the block start.  Therefore every successor
of a saturated block misses its deepest claim depth.  Lean derives:

- the successor hole carrier is nonempty;
- successor claim count is at most `length - 1`;
- a length-one successor has claim count zero;
- `CanonicalLengthOneBalancedCarrySuccessor` is empty.

## Nonvacuous residue grammar

`CanonicalLengthOneTerminalOneSuccessor` retains saturation, successor length
one, and terminal valuation one, but drops the impossible claim.  It is
equivalent to predecessor odd-core residue `11 mod 16`.  On this surface Lean
proves:

- successor claim count is zero;
- successor drift is `-1`;
- predecessor and successor drift sum to zero;
- the following start is `(27*u - 1)/8`;
- the residue refines to `11` or `27 mod 32`.

For the alternate length-one residue `3 mod 16`, successor drift is at most
`-2`.

## Generic claim-profile API

For every valid depth `1 <= d <= L`, Lean now proves

```text
iterateT (canonicalPaymentSourceAtDepth n k d) n + 1
  = 2^d * 3^(L-d) * u.
```

Consequently membership in `canonicalPaymentClaimDepths` is equivalent to
carry two at the exact core word

```text
2^d * 3^(L-d) * u - 1.
```

This removes the need for residue-specific claim transport inside one block.

## First genuine obstruction

The local arithmetic obstruction did not survive formalization.  The remaining
boundary is global resource ownership.  Existing width and carry APIs do not
provide a finite initial-root carrier together with subtree assignment,
temporal ownership, and a proved nonreuse or uniform multiplicity bound.

The abstract local embeddings therefore cannot yet be summed globally without
risk of charging the same upper-boundary resource multiple times.  A future
conditional interface may state that such ownership data imply a finite total
demand bound, but existence of that data must not be asserted.

## Verification

The focused modules build without `sorry` or heartbeat overrides.  Final
top-level gates are recorded in the completion response for this checkpoint.
