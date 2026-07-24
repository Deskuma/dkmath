# Report 004: valuation excess and current proof frontier

## Completed theorem surfaces

`ABC-GN-005` is complete in:

```text
DkMath/ABC/GNValuationExcess.lean
```

The module defines finite logarithmic multiplicity excess and its GN,
exceptional, and non-exceptional specializations.  For nonzero `m` it proves
the exact identity

```text
log m = log (rad m) + valuationExcess m
```

and partitions GN excess exactly into the `q ∣ n` and `q ∤ n` sums.

The local part of `ABC-GN-007` is packaged in:

```text
DkMath/ABC/GNHighLift.lean
```

It defines square high-lift primes, splits them into exponent-exceptional and
non-exceptional layers, proves the layers disjoint, and connects `q^2 ∣ GN`
with `2 ≤ padicValNat q GN`.  Absence of a square lift bounds the local GN
valuation by one; on a non-exceptional channel the same bound transfers to
the full power difference.

## ABC-GN-006 deterministic bridge

The proved portion is in:

```text
DkMath/ABC/GNQualityExcessBridge.lean
```

For positive ABC-radical logarithm, `Q < quality T` yields the exact strict
height inequality

```text
Q * log (rad (a*b*c)) < log c.
```

Two named obligations expose the remaining transport:

```text
GNReturnLowerBound
GNSupportBudget
```

Given these estimates, high quality forces the quantitative lower bound

```text
(κ * (1 + ε) - σ) * log (rad (a*b*c))
  < GNValuationExcess n a b.
```

This is not advertised as an unconditional completion of `ABC-GN-006`.
Proving the return and support estimates uniformly is precisely the missing
global mathematics.

## Honest roadmap frontier

```text
ABC-GN-004  complete
ABC-GN-005  complete
ABC-GN-006  deterministic reduction complete; two global estimates open
ABC-GN-007  local obstruction API complete; global rarity/bound open
ABC-GN-008  blocked on a uniform bound for exceptional/nonexceptional excess
ABC-GN-009  blocked on 008
ABC-GN-010  audit result: abc_main still calls abc_main_axiom directly
```

In particular, finite exceptional absorption and a valid `K_ε` cannot be
constructed from the current source merely by finite-sum bookkeeping.  The
existing `ABCMainTheorem.K_eps` is explicitly a placeholder, and
`abc_main` remains exactly an application of `abc_main_axiom`.

## Verification

```text
lake build DkMath.ABC.GNHighLift
Build completed successfully (8321 jobs).

lake build DkMath.ABC.GNQualityExcessBridge
Build completed successfully (8325 jobs).
```

No new `axiom`, `sorry`, or `native_decide` was added.  Existing upstream
warnings, including the pre-existing research `sorry`, were replayed by the
import graph but were not introduced or used as a claimed closure here.
`#print axioms` on the six representative new endpoints reports only
`propext`, `Classical.choice`, and `Quot.sound`; it does not report the
pre-existing research declaration or `abc_main_axiom`.
No commit, push, PR, or CI operation was performed.
