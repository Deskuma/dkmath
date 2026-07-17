# Petal / FloatWindow implementation report - checkpoint 321

## Scope

This checkpoint starts the fixed-depth pressure-amplitude reduction requested
after cp-320.  The implementation is in
`DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude` and remains
finite, source-incidence based, and no-sorry.

## Implemented facts

### Block-preserving accounting

Positive-drift units now embed blockwise into the selected incidence carrier
or the saturated token of the same block.  The dependent-sum embedding retains
the canonical block coordinate definitionally.  The earlier global
cardinality-only embedding remains available through a compatibility theorem.

### Active depth support

The new active support contains exactly depths selected by positive,
nonsaturated blocks.  Every member of this support has a nonempty selected
bucket.  Saturated zero buckets are therefore no longer interpreted as
pressure witnesses.

### Fixed-depth transport and normal form

Each selected bucket embeds into both:

- the existing endpoint-prefix continuation fiber after forgetting its block;
- the complete continuation carrier over the original block window while
  retaining its block.

At every positive depth, local pressure is exactly successor continuation mass
minus the indicator that the block has that exact length.  Summing gives the
same identity over arbitrary finite windows and over endpoint prefixes.

### Exact-length charge plus amplitude

For every `d >= 1`, the selected bucket cardinality is bounded by

```text
exact-length block count at d
  + Int.toNat (fixed-depth window pressure at d).
```

A finite embedding into exact-length block tokens plus anonymous positive
pressure-amplitude units is supplied.  This is not a boundary allocation and
does not identify any later repayment event.

## What is now proved

The dynamic selected-depth carrier is not an unrelated auxiliary count.  At a
fixed depth it is a genuine subcarrier of successor continuation incidence.
The continuation mass has an exact two-term accounting law: one exact-length
recovery charge per matching block, with only the positive pressure remainder
left over.  Thus pressure amplitude, rather than positive-depth support or
source overlap, is the next nontrivial mass.

## Remaining route

1. Package exact-length tokens over active depths and forget depth injectively;
   uniqueness of canonical block length should bound their total by the block
   interval cardinality.
2. Package positive pressure amplitudes over active depths.
3. Sum the bucket decomposition to reduce the global selected carrier to block
   count plus the amplitude carrier, then combine saturated-token packing.
4. Audit pressure superlevels.  Existing level-zero pulse/packing results count
   positive depths, but currently do not bound multiple amplitude units at one
   depth.  No such strengthening should be claimed without a superlevel pulse
   invariant or a bounded-multiplicity transport map.

The first anticipated mathematical obstruction remains the Stage-I transport:
an amplitude unit has not yet been assigned injectively, or with bounded
multiplicity, to an upper-zero boundary, separator, or NoLift obstruction.
