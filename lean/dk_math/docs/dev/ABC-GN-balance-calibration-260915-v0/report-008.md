# BCAL-008: quantitative calibration frontier audit

## Scope and outcome

This report audits the quantitative APIs that are present in the production
and archive-side ABC/GN development.  It does not improve an exponent, add a
new uniform constant, or assert an ABC theorem.

**Outcome A — CALIBRATED QUANTITATIVE MAP COMPLETE.**  The existing numerical
and quantitative interfaces can be classified against the current balance
coordinates.  The audit also identifies the exact missing deterministic bridge
between counting/average results and a pointwise calibration budget.  Thus the
map is complete, but no new numerical optimization is justified at this
checkpoint.

The current coordinates are:

\[
 S=\texttt{GNChannelSupportMass},\quad
 E=\texttt{GNChannelDepthMass},\quad
 M=S+E,\quad Q=S-E,
 \quad \mathrm{Cal}=M-\rho R,
 \quad R=\texttt{Triple.radLog}.
\]

Here `S` is the logarithm of the fresh non-exceptional support product and `E`
is the non-exceptional valuation excess.  The balance file is a coordinate
layer: it introduces no new support product, valuation estimate, or provider.

## Coordinate taxonomy

The following classes are used throughout the audit.

| class | meaning |
|---|---|
| A | support/radical-growth quantity (`S` or a support budget) |
| B | valuation/depth quantity (`E`, `piSqRad`, `twoTail`, or a depth layer) |
| C | total channel mass or an affine joint pressure (`M`) |
| D | signed support-minus-depth balance (`Q`) |
| E | calibration residual or intrinsic-epsilon consumer (`Cal`) |
| F | counting, density, incidence, shell, or moment quantity |

The class is not determined by the presence of a logarithm alone.  In
particular, a shell cardinality, an average over `a`, and a finite moment are
class F until a theorem identifies them with a pointwise `S`, `E`, `M`, or
`Cal` budget.

## Quantitative API inventory

| theorem / source | population | raw measured quantity | current coordinate class | normalization | statement type | constant / exponent | directly composable? yes/no | required bridge / limitation |
|---|---|---|---|---|---|---|---|---|
| `delta_0435_final` / `DkMath/ABC/QualityTailBridge.lean:30-37` | one fixed `(a,b,c)` with `a+b=c` | same-base radical product powers | F (archival wrapper) | powers of `rad a * rad b` | pointwise implication | `0.20`, `0.23`, `0.005`, `0.435` appear as exponents | **No** | The conclusion is exactly its `Hbig` hypothesis. `Hmid` and `Hsmall` are not composed, and the theorem never mentions `S`, `E`, `M`, `Q`, or `Cal`. |
| historical 0.435 narrative / `DkMath/ABC/docs/ABC.md:112-160` | band decomposition in the archived plan | small-, middle-, and large-band contributions | F (plan text) | additive exponent bookkeeping | informal roadmap text | `0.20+0.23+0.005=0.435` | **No** | This records intended assembly, not a Lean proof of a current affine `M` bound or a uniform constant. |
| `GNLiftRadicalGrowthBudgetAffine`, `GNNonExceptionalSupportBudgetAffine` / `DkMath/ABC/GNSupportReturn.lean:266-289` | one positive triple and one exponent | lifted radical growth, then fresh support log | A | affine in `R` | definitions plus conditional transport theorem | slope `σ`, constant `C` | **Yes, conditionally** | Requires the pointwise lifted-growth hypothesis. No numerical `σ,C` provider is supplied by this declaration. |
| `GNSupportBudgetAffine_of_nonExceptional` and related support transport / `DkMath/ABC/GNSupportReturn.lean:292-314` | one triple | fresh support plus the original radical term | A | affine in `R` | exact/conditional budget transport | inherited slope and constant | **Yes, conditionally** | This is a support-side bridge; it does not control valuation depth. |
| `valuationExcess`, `GNValuationExcess_eq_log_rad_add` / `DkMath/ABC/GNValuationExcess.lean:33-101` | one GN value and its factorization support | `sum (v_q-1) log q`, with exact log decomposition | B | logarithmic factorization identity | exact identity and exceptional/non-exceptional split | no new exponent | **Yes** as an accounting identity | It supplies the `E` coordinate, not an upper bound for it. |
| `GNNonExceptionalValuationExcess_eq_log_piSqRad_add_log_twoTail` / `DkMath/ABC/GNLegacyTailCountingBridge.lean:196-200` | one non-exceptional GN part | `E = log(piSqRad) + log(twoTail)` | B | exact logarithmic decomposition | exact identity | coefficients `1,1` | **Yes** for rewriting | The two summands are not separately bounded pointwise by this theorem. |
| `GNExcessLargeBoundaryPacket.log_piSqRad_or_log_twoTail` / `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:605-656` | one large repeated-modulus packet | either `log piSqRad` or `log twoTail` is large | B | normalized by `log(X+1)` | finite conditional disjunction | thresholds `1/4`, `1/2` | **No** for an upper `E` budget | It is a lower-threshold OR statement, not an upper bound and not a balance statement. |
| `GNExcessActiveProfileMass_target_eq_log_sqTail` / `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:668-734` | one interval point and its depth profile | active profile mass equals `log(sqTail)` | B | logarithmic exact coordinate | exact identification | coefficient `1` | **Yes** for depth rewriting | It remains depth-side; no support compensation or pointwise calibration bound follows. |
| `GNExcessRootAddressCharge_target_le_piSqRad` / `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:738-810` | one active excess profile | root-address charge versus repeated support shell | F/B proxy | finite cardinality/product comparison | exact finite inequality | `charge <= piSqRad` | **No** as `S` or `E` | Address charge is a combinatorial shell proxy. Equality with channel mass is not established. |
| `GNExcess_target_boundaryWeight_le_repeatedPart_rpow` / `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:814-910` | one active profile | address charge times exponential profile weight | F | finite repeated-part `3/4` power | pointwise weighted shell inequality | `t=1/2`, exponent `3/4` | **No** as an `M` slope | The `3/4` rpow is a shell weight, not a slope for `M <= rho*R+C`. |
| `sum_padicValNat_GN_le_of_simpleRoot_layers` / `DkMath/ABC/GNLegacyTailCountingBridge.lean:1164-1218` | fixed prime, `a in [0,X]` | sum of `q`-adic valuations over the interval | F/B average | interval sum and finite layer-cake | finite conditional average bound | layer count up to `log_q(p(X+b)^p)` | **No** pointwise | Requires fixed-prime simple-root hypotheses and averages over `a`; it does not select a per-triple depth budget. |
| `sum_padicValNat_GN_mul_log_le_of_simpleRoot` / `DkMath/ABC/GNLegacyTailCountingBridge.lean:1266-1289` | fixed prime and interval | log-weighted valuation sum | F/B average | sum over `a in [0,X]` | finite conditional average bound | factor `p-1` and finite logarithmic layer term | **No** pointwise | Same population mismatch; the estimate is not a uniform `E <= tau*R+D` theorem. |
| `sum_GN_depthMass_over_interval_le` / `DkMath/ABC/GNLegacyTailCountingBridge.lean:1299-1331` | finite prime family and all `a in [0,X]` | averaged multi-prime GN depth mass | F/B average | double interval/family sum | finite conditional average bound | explicit finite family sum | **No** | The file explicitly leaves family selection and pointwise compensation separate. |
| `GNExcessCubicRealizedLargeModulusSpace` and `...Moment_eq_sum_modulusSpace` / `DkMath/ABC/GNExcessCubicRealizedModuli.lean:117-164` | realized cubic large profiles, then distinct integer moduli | profile cardinality and `sum M^(3/8)` | F | finite image and `3/8` moment | exact finite image/cardinality/moment identities | exponent `3/8` | **No** | The modulus moment is not `S`, `E`, or `M`; it needs a pointwise incidence-to-channel bridge. |
| realized cubic modulus witness/divisor/height theorems / `DkMath/ABC/GNExcessCubicRealizedModuli.lean:166-279` | each realized modulus | witness, divisibility, interval and height constraints | F | finite integer modulus | exact structural theorems | `X+1 < M <= 3(X+1)^2`; prime residues `q % 3 = 1` | **No** | These constrain the shell population but do not produce a pointwise calibration residual bound. |
| `exp_GNExcessMassAt_sum_cubic_three_eighths_le_finiteEuler_add_realizedModuli` / `DkMath/ABC/GNExcessCubicRealizedModuli.lean:283-300` | all `a in [0,X]` | exponential active-mass sum | F | finite Euler term plus realized-modulus moment | finite aggregate inequality | `3/8` | **No** | It is an aggregate moment estimate. A count/moment-to-pointwise `Cal` selector is missing. |
| cubic realized boundary and incidence APIs / `DkMath/ABC/GNExcessCubicRealizedBoundary.lean:70-190`, `GNExcessCubicRealizedIncidence.lean:117-301` | realized cubic fibers, sectors, and repeated-modulus packets | fiber counts, incidence, spacing, and weighted moments | F | finite fibers, unions, and modulus moments | exact finite incidence/packing inequalities | `3/8` and related finite weights | **No** | These are shell-count and incidence controls. They do not identify the shell with all channel mass or supply a deterministic per-triple cover. |
| `GNNonExceptionalChannelMassBudgetAffine` and its pressure equivalence / `DkMath/ABC/GNJointPressureOddPrime.lean:260-313` | one positive triple at an odd prime exponent | `S+E <= rho*R+C`, equivalently odd-prime joint pressure | C | affine in `R` | exact definition and equivalence | slope `rho`, constant `C` | **Yes** once hypothesized | This is the correct current `M` interface, but the declaration is a budget predicate; it does not prove a numerical budget. |
| `GNOddPrimeJointPressureBudgetAffine.of_liftGrowth_and_nonExceptional` / `DkMath/ABC/GNJointPressureOddPrime.lean:320-328` | one triple with two pointwise hypotheses | addition of lifted support and non-exceptional excess budgets | C | both budgets affine in the same `R` | one-way conditional composition | slopes/constants add | **Yes, conditionally** | It is composable only when both input budgets hold pointwise with the same population and normalization. |
| `Triple.log_c_mul_pred_le_of_oddPrime_jointPressure` / `DkMath/ABC/GNJointPressureOddPrime.lean:334-342` and `Triple.log_c_mul_pred_le_of_support_and_excessBudget` / `DkMath/ABC/GNFinalBudgetBridge.lean:57-70` | one positive triple | logarithmic height from a joint or split budget | C | affine in `R` | pointwise supporting-line theorem | `rho` (or `sigma+tau`) and additive constants | **Yes** | These are consumers of an already available pointwise budget, not providers of one. |
| `GNValuationExcessBudgetAffine.of_split` / `DkMath/ABC/GNFinalBudgetBridge.lean:26-54` | one triple | exceptional plus non-exceptional excess | B/C | affine in the same `R` | exact conditional budget addition | slopes/constants add | **Yes, conditionally** | The split theorem is valid only after both component upper budgets are supplied. |
| `Triple.abcEpsilon_le_GNEpsilon_add_correction` and balance residual specialization / `DkMath/ABC/ABCEpsilonSlopeBridge.lean:58-90`, `DkMath/ABC/GNBalanceCalibration.lean:67-105` | one positive triple and odd prime exponent | intrinsic epsilon from slope plus finite correction | E | divide by `(p-1)*R`; `Cal=M-rho*R` | pointwise conditional consumer | `GNEpsilon p rho = rho/(p-1)-1`; correction `(C+log(rad p))/((p-1)R)` | **Yes** once `Cal <= C` is known | It preserves the residual correction. It is not an unconditional epsilon or exponent theorem. |
| `eventually_abcEpsilon_lt_of_oddPrime_jointPressure_slope` / `DkMath/ABC/ABCEpsilonSlopeBridge.lean:107-180` | a family of triples | eventual intrinsic-epsilon control | E | eventual filter and `radLog -> atTop` | conditional asymptotic theorem | strict slope margin | **No** for a uniform finite pointwise claim | Requires eventual joint pressure and diverging radical-log scale. |
| `Keystone_eventual_ratio_bound`, `MiddleBand_exception_bound`, `Keystone_density_zero_fraction` / `DkMath/ABC/RatioBound.lean:39-98` | bad-pair population indexed by `X` | `BadCount(0.435) X / X^2` | F | normalized population density | eventual/density result; middle-band input is an axiom | `1.75+epsilon < 2`; `0.435` | **No** | This is a population-density statement. `MiddleBand_exception_bound` is an existing axiom and does not furnish a per-triple `M` or `Cal` bound. |

## Status of the historical 0.435 route

The archived prose identifies the intended arithmetic as

\[
  0.20\;\text{(large band)} + 0.23\;\text{(middle band)}
  + 0.005\;\text{(small-band absorption)}=0.435.
\]

The production theorem `delta_0435_final` does not establish this assembly.
Its first hypothesis is already the desired `0.20 <= 0.435` same-base power
comparison, and its proof returns that hypothesis directly.  The other two
hypotheses and `a+b=c` are not used in the proof.  Therefore the 0.435 route
is a historical, non-composable wrapper at the current Lean boundary.  The
associated `BadCount` statements are useful finite-density bookkeeping, but
they live in class F and cannot be reinterpreted as a pointwise `M` estimate.

This is a classification result, not a refutation of any external analytic
estimate: the required bridges simply are not present in the current source.

## Strongest current pointwise interfaces

The strongest pointwise calibration-facing interface is the exact equivalence

\[
 \texttt{GNNonExceptionalChannelMassBudgetAffine}
 \quad\Longleftrightarrow\quad
 \mathrm{Cal}\le C,
\]

implemented by
`GNNonExceptionalChannelMassBudgetAffine_iff_calibrationResidual_le`.  At an
odd prime exponent it is exactly equivalent to the existing joint-pressure
budget.  The subsequent `abcEpsilon` theorem consumes this hypothesis and
adds the explicit finite correction involving `rad p` and `R`.

No unconditional numerical value of `rho`, `C`, or `Cal` is proved by these
interfaces.  The strongest split route is likewise conditional: a pointwise
support budget and a pointwise valuation-excess budget with the same `R`
normalization can be added and then passed to the logarithmic height bridge.

## Strongest counting / average interface

The strongest directly relevant aggregate theorem is
`sum_GN_depthMass_over_interval_le`.  It controls a finite-family, interval-
averaged, log-weighted valuation quantity under fixed-prime simple-root
hypotheses.  The cubic realized APIs additionally control finite shell fibers
and a `3/8` modulus moment.  Neither result is pointwise in the triple, and
neither includes the support channel needed for `M` or `Cal`.

## Exact missing deterministic bridge

To connect the aggregate APIs to the current calibration coordinates, one
would need a theorem of the following shape, with all hypotheses and
populations made explicit:

1. select a specified triple from the counted/averaged population, or prove a
   deterministic cover/compensation statement for every triple;
2. convert the selected shell, layer-cake, incidence, or moment quantity into
   a pointwise upper bound for `E` (and, separately, for `S` if support is
   needed);
3. combine those bounds in the same affine `R` normalization to obtain
   `GNNonExceptionalChannelMassBudgetAffine`, equivalently `Cal <= C`.

The current files provide exact factorizations, finite counting, and
conditional budget consumers, but no such selector/cover theorem.  In
particular, a density-zero statement cannot be promoted to a pointwise
statement, and a shell exponent or moment exponent cannot be read as the
slope of `M`.

## Optimization decision

Numerical optimization is **not justified** at BCAL-008.  Before optimizing
`rho`, `C`, or a candidate exponent, the missing deterministic bridge must
first supply a dimensionally compatible pointwise `M`/`Cal` budget.  The
checkpoint therefore preserves the existing historical constants and all
semantic barriers: no exponent improvement, universal provider, global
density-to-pointwise inference, lift-existence claim, or ABC conclusion is
introduced.

## Validation

This checkpoint changes documentation only.  The report was checked against
the theorem declarations and source locations cited above; no production Lean
file was modified by BCAL-008, so no new Lean build or axiom audit is required
for this checkpoint.  The final repository check is `git diff --check`.
