# FLT7-004 implementation report

## Outcome

Outcome A.  The valuation-defined maximal depth, its nonzero divisibility
characterization, attainment and successor obstruction, thickness witness,
terminal residual core, and both optional exact evaluations are complete.

## Files changed

- `DkMath/FLT/Seven/AxisDepth.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenAxisDepth.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-004.md`

## Definition and zero convention

The exact definition is

```lean
sevenAxisDepth x = padicValNat 7 (Int.natAbs (norm x)).
```

The transparent theorem `sevenAxisDepth_zero` proves depth zero at the zero
element.  No power-divisibility characterization is claimed for zero: every
finite axis power divides zero, while the natural-valued valuation assigns
zero to zero.  Zero remains absence of a nonzero core, not an infinitely deep
roll.

## Exact theorem surface

- `sevenAxisDepth`, `sevenAxisDepth_zero`
- `norm_pos_of_ne_zero`, `natAbs_norm_ne_zero_of_ne_zero`
- `pow_seven_dvd_norm_iff_pow_seven_dvd_natAbs_norm`
- `sevenAxis_pow_dvd_iff_le_sevenAxisDepth`
- `sevenAxis_pow_depth_dvd`
- `not_sevenAxis_pow_succ_depth_dvd`
- `le_sevenAxisDepth_of_pow_dvd`
- `sevenAxis_pow_dvd_of_le_depth`
- `pow_seven_depth_le_norm`
- `exists_terminal_sevenAxis_core`
- `sevenAxisDepth_sevenAxis_pow`
- `sevenAxisDepth_cyclotomicSevenToTraceOne`

## Integer-to-natural norm bridge

`pow_seven_dvd_norm_iff_pow_seven_dvd_natAbs_norm` uses
`Int.natAbs_dvd_natAbs` and `Int.natAbs_pow` to prove, for every `x,n`,

```text
(7:ℤ)^n ∣ norm x ↔ 7^n ∣ Int.natAbs (norm x).
```

For nonzero `x`, FLT7-001 supplies `1≤norm x`, hence strict positivity and a
nonzero natural absolute value.  This is the nonzero hypothesis needed by
`padicValNat_dvd_iff_le`.

## Maximality and finite termination

Combining the bridge with FLT7-003 gives the summit characterization

```text
sevenAxis^n ∣ x ↔ n ≤ sevenAxisDepth x     (x≠0).
```

Reflexivity of `≤` proves attainment at the depth; irreflexivity at its
successor proves the successor obstruction.  The attained power fed into the
finite-thickness theorem gives

```text
7^(sevenAxisDepth x) ≤ norm x,
```

which is the explicit finite termination witness.

## Terminal residual core

Attainment provides an existential quotient `y` with
`x=sevenAxis^depth*y`.  It is nonzero because `x` is nonzero.  If another
`sevenAxis` divided `y`, associativity would reconstruct a successor-depth
factorization of `x`, contradicting strict maximality.  FLT7-002 converts this
to `7∤norm y`; FLT7-003 supplies exact norm scaling and `1≤norm y`.

No canonical quotient or public `Classical.choose`-based data was defined.

## Optional evaluations

Both optional results are included:

- `sevenAxisDepth (sevenAxis^n)=n`;
- cyclotomic coordinate depth is exactly
  `padicValNat 7 (Int.natAbs (cyclotomicSeven z y))`.

The latter is only the existing norm identity under the depth definition.  It
does not assert an endpoint-gap valuation formula.

## Scope preserved

No recursive search, infinite-valued valuation, zero characterization,
canonical residual quotient, LTE, exact endpoint-gap comparison, primitive
packet, FLT7 descent, ideal/factorization theory, or general prime abstraction
was added.

## Verification and axiom audit

Focused builds, tests, forbidden-token scan, and `git diff --check` are run at
checkpoint close.  The integer/natural divisibility bridge depends exactly on
`propext`; every other audited theorem depends on the standard set `propext`,
`Classical.choice`, and `Quot.sound`.  No `sorryAx` or DkMath-defined axiom
appears, and the implementation/test use no active `native_decide`, `admit`, or
`sorry`.

## Recommended FLT7-005 boundary

Investigate the exact maximal depth of the seventh cyclotomic kernel under
explicit primitive/coprime endpoint hypotheses.  In particular, first isolate
the hypotheses governing the second trace factor before comparing depth with
`padicValNat 7 (Int.natAbs (z-y))`; do not assume higher gap divisibility alone
produces equal higher cyclotomic depth.
