# ZDI-002 — DkReal common shrinking-interval uniqueness report

Date: 2026-08-19  
Branch: `wip/RH-CFBRC-zeta-dkreal-zero-interval-260819-v0`

## Scope and conclusion

This report implements `0003-ZDI-002-DkReal-common-shrinking-interval-uniqueness-instructions.md`.
The task is an analysis-library interface task only.  It does not add a zeta
statement, a prime statement, an RH provider, or a new definition.

The repository did not already contain the requested two-candidate theorem.
The smallest generic theorem was added to
`DkMath.Analysis.DkReal.Semantic`:

```lean
theorem eq_of_mem_all_intervals
    (x : DkMath.Analysis.DkReal) {r s : ℝ}
    (hr : ∀ n, r ∈ Set.Icc (lowerReal x n) (upperReal x n))
    (hs : ∀ n, s ∈ Set.Icc (lowerReal x n) (upperReal x n)) :
    r = s
```

Its proof is exactly the composition of the existing semantic uniqueness
theorem for `r` and `s`; no new completeness or squeeze argument was added.

## 1. Existing DkReal audit

The audited carrier is the structure in `DkReal.Basic`:

```text
x.interval              : ℕ → GapInterval
x.nested                : later rational interval is contained in the earlier one
x.width_tends_zero      : rational widths tend to zero
```

The semantic module defines:

```text
lowerReal x n := (x.interval n).lo
upperReal x n := (x.interval n).hi
widthReal x n := upperReal x n - lowerReal x n
semanticValue x := ⨆ n, lowerReal x n
```

The dependency path already present before this change is:

```text
DkReal.nested / DkReal.lo_mono / DkReal.hi_antitone
  → lowerReal_le_upperReal
  → bddAbove_range_lowerReal
  → semanticValue
  → semanticValue_mem_interval

DkReal.width_tends_zero
  → tendsto_widthReal_zero

semanticValue_mem_interval + tendsto_widthReal_zero
  → eq_semanticValue_of_mem_all_intervals
```

`eq_of_mem_all_intervals` then uses the last theorem twice:

```text
r = semanticValue x = s
```

Thus the one representation, two all-stage interval membership hypotheses, and
the existing shrinking-width invariant imply the two candidate values are
equal.  Completeness remains encapsulated in `semanticValue`; no additional
assumption is present in the new theorem.

## 2. Equivalent-theorem search

The whole `DkMath.Analysis.DkReal` tree was searched for the requested
two-point common-interval uniqueness statement and related names.  The only
prior theorem with the required semantic content was:

```lean
eq_semanticValue_of_mem_all_intervals
```

It identifies one candidate with `semanticValue x`; it does not directly
accept two candidates and conclude equality.  Therefore a new one-line
corollary was necessary and appropriate.  No optional rational corollary was
added because it would add no interface needed by ZDI-002.

## 3. Exact theorem and docstring

The theorem and its docstring are in:

`DkMath/Analysis/DkReal/Semantic.lean:144-160`

The docstring records that the theorem concerns two real points in the same
cast approximation intervals, that uniqueness comes from widths tending to
zero, and that it introduces neither a completeness assumption nor a new real
representation.

The proof is:

```lean
by
  calc
    r = semanticValue x := eq_semanticValue_of_mem_all_intervals x r hr
    _ = s := (eq_semanticValue_of_mem_all_intervals x s hs).symm
```

No `def`, structure, or helper provider was introduced.

## 4. RH-independence audit

The changed source file imports only:

```lean
import DkMath.Analysis.DkReal.CanonicalOrder
```

The new theorem's statement and proof mention only:

```text
DkReal, lowerReal, upperReal, Set.Icc, semanticValue,
eq_semanticValue_of_mem_all_intervals
```

There is no import or occurrence of any RH-specific declaration, zeta
declaration, CFBRC declaration, prime-counting declaration, critical-strip
assumption, or historical CFZP provider.  The theorem remains reusable as the
generic handoff shape for later interval construction work.

## 5. Axiom audit

The following checker was run from the nested Lake project:

```text
cd /home/deskuma/develop/lean/dkmath/lean/dk_math
lake env lean ../../ZDI002Check.lean
```

The exact results were:

```text
'DkMath.Analysis.DkReal.eq_semanticValue_of_mem_all_intervals'
  depends on axioms: [propext, Classical.choice, Quot.sound]

'DkMath.Analysis.DkReal.eq_of_mem_all_intervals'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` dependency.  `propext`, `Classical.choice`, and
`Quot.sound` are standard Lean/Mathlib foundations and are distinct from an
unresolved project-local assumption.

## 6. Verification

The required narrow build was run:

```text
cd /home/deskuma/develop/lean/dkmath/lean/dk_math
./lean-build.sh DkMath.Analysis.DkReal.Semantic
```

Result: build succeeded.

The temporary `ZDI002Check.lean` file used for declaration and axiom
inspection is an audit fixture only and is not part of the repository change.
No RH umbrella build was needed because the public RH import surface was not
changed.

## 7. ZDI-003 handoff

ZDI-002 supplies only this generic logical interface:

```text
one DkReal representation x
  + candidate r in every interval of x
  + candidate c in every interval of x
  → r = c
```

ZDI-003 may now audit whether existing unconditional finite prime/zeta facts
can construct one common interval family containing `s.re` and `1 / 2` at every
stage.  That construction is not attempted here.  In particular, this task
does not assume a critical strip, a zeta zero location, or any RH-equivalent
frontier.
