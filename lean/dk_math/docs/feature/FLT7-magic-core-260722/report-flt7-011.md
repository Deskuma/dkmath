# FLT7-011 implementation report

## Outcome

Outcome A. The away second-coordinate load decomposition, all three exact
valuation transfers, unified carrier packet, strict depth drop, and full
valuation route are complete.

This checkpoint proves a strict `7`-adic depth drop. It does not yet prove a
recursive descent, because the new root coordinate has not been reconstructed
as an endpoint of another primitive counterexample packet.

## Files changed

- `DkMath/FLT/Seven/AwaySecondCoordinateLoad.lean`
- `DkMath/FLT/Seven/AwayValuationTransfer.lean`
- `DkMath/FLT/Seven.lean`
- `DkMathTest/FLT/SevenAwaySecondCoordinateLoad.lean`
- `DkMathTest/FLT/SevenAwayValuationTransfer.lean`
- `docs/feature/FLT7-magic-core-260722/report-flt7-011.md`

## Away root and second-coordinate load

`AwayCoordinateNormalForm.root_norm_not_seven_dvd` proves that the norm of an
away root lies outside the ramified `7` channel. The coordinate equality and
multiplicativity of the trace-one norm identify the corresponding cyclotomic
norm with `norm(root)^7`. The GN/cyclotomic bridge and the away gap criterion
give `7 ∤ GN`; hence `7` cannot divide `norm(root)`.

The inherited theorem
`AwayCoordinateNormalForm.sndCore_not_seven_dvd` then applies the FLT7-010
norm/core result directly.

The signed normalization is isolated in
`cyclotomicSevenSnd_eq_neg_endpoint_product`. Taking absolute values in the
away coordinate equation yields

```text
y*z*(y+z) = |seventhPowerSnd(root)|.
```

Using `seventhPowerSnd = 7*v*SndCore` and multiplicativity of `natAbs` gives
the exact natural load decomposition

```text
y*z*(y+z) = 7*|v|*|SndCore(u,v)|.
```

Both `v` and `SndCore` are proved nonzero. The core is also nondivisible by
`7`, so its `padicValNat 7` contribution is exactly zero.

## One-hot valuation transfer

Two specialized reusable lemmas expose the arithmetic mechanism:

- `padicValNat_unique_factor_of_triple`
- `padicValNat_seven_mul_of_core_not_dvd`

The first removes the two nonexceptional endpoint factors from the left-hand
valuation. The second removes the core on the right and retains exactly the
explicit leading `7`. Consequently:

```text
v7(y)   = 1 + v7(|root.snd|)   in the Y/right branch,
v7(z)   = 1 + v7(|root.snd|)   in the Z/left branch,
v7(y+z) = 1 + v7(|root.snd|)   in the sum branch.
```

These are respectively implemented by
`away_right_padicValNat_transfer`, `away_left_padicValNat_transfer`, and
`away_sum_padicValNat_transfer`. They all use the same load identity and
one-hot isolation, rather than separate residue calculations.

## Unified carrier packet and provenance

`AwayExceptionalCarrierSource` records whether the selected carrier is `y`,
`z`, or `y+z`, together with its exact divisibility and nondivisibility facts.
`AwayValuationTransferPacket` stores:

- the away coordinate normal form;
- the selected natural carrier and its provenance;
- positivity of the carrier and `|root.snd|`;
- the exact valuation equality.

The packet is constructed by `nonempty_awayValuationTransferPacket`, with the
chosen form exposed as `awayValuationTransferPacket`.

## Exact carry and strict depth

`AwayValuationTransferPacket.fortyNine_dvd_carrier_iff` proves

```text
49 ∣ carrier  <->  (7 : Z) ∣ root.snd.
```

The proof translates divisibility into valuation bounds, rewrites with the
packet equality, and transfers divisibility through integer `natAbs`.

The same equality immediately gives:

- `AwayValuationTransferPacket.root_snd_depth_lt_carrier`;
- `AwayValuationTransferPacket.one_le_carrier_depth`.

Thus the proved comparison is a strict `7`-adic depth drop. No claim is made
about ordinary numerical size.

## Final valuation route

`ValuationCounterexampleRoute` preserves the ramified coordinate packet and
replaces the away branch with `AwayValuationTransferPacket`.
`valuationCounterexampleRoute_of_pack` constructs this route from every
abstract `CounterexamplePack`.

## Verification

The following checks passed:

- focused builds for both new modules;
- `lake build DkMath.FLT.Seven`;
- both focused test files via `lake env lean`;
- `lake build DkMath.FLT`;
- forbidden-token scan over the new modules and tests;
- `git diff --check`.

Focused axiom audits report only `[propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, custom axiom, or `native_decide` was introduced.

## Recommended FLT7-012 boundary

Investigate closure: determine whether the root coordinates together with the
selected exceptional carrier canonically reconstruct a new primitive
FLT7/cyclotomic packet. Only after such a target packet is explicitly built
may the strict depth theorem be promoted to a descent step. If reconstruction
does not follow from the current data, expose the exact missing reconstruction
provider instead of asserting recursion.
