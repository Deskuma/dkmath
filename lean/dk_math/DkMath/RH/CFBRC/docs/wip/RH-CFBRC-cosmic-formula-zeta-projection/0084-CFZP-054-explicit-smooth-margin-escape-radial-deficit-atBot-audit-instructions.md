# CFZP-0084 / CFZP-054

## explicit smooth-margin escape + radial deficit `atBot` — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-051: PNT ratio provider -> eventual combined discrepancy debt `<= Margin / 8`
- CFZP-052: discrepancy finite analytic readiness auto
- CFZP-053: smooth-Abel finite readiness auto + one-cell descent + adjacent-cell recurrence + finite telescoping

CFZP-053 は **Green-A**。

---

## 0. 今回の狙い

CFZP-053 は、late carrier cell 上で

```text
G_(n+1) <= G_n - Margin_n / 8
```

を、PNT ratio provider の下で eventually 得るところまで閉じた。

ここで

```text
U_n := cfzp039CarrierCellLeft W c n
beta := cfzp039PrimeAxisGrowthExponent W = 1 - W.rectangle.sigma
M0 := cfzp039ExponentialCarrierPeriodTransform epsilon W c
```

とすると explicit smooth margin は exact に

```text
Margin_n = exp (beta * U_n) * (M0 / (4 * U_n)).
```

CFZP-039 interior strip から `0 < beta`、positive transform から `0 < M0`、CFZP-047 から

```text
U_n -> +infinity.
```

したがって本 checkpoint の第一魔核は

```text
Margin_n -> +infinity.
```

である。

ここから eventually `8 <= Margin_n` を取れば CFZP-053 recurrence は

```text
G_(n+1) <= G_n - 1
```

へ強化される。

ゆえに無限和の極限交換を使わず、有限 induction だけで

```text
G_n -> -infinity
```

を証明できる。

さらに natural carrier cutoff 自体も cofinal であることを示し、任意の自然数 cutoff 下限 `N` と任意の radial target `eta` に対して

```text
exists n,
  N <= NaturalLeft(n) and
  radialDeficit(NaturalLeft(n)) <= eta
```

を得る。

**CFZP-054 では PNT 自体は証明しない。**
`Cfzp051PrimeCountingPNTRatioAtTop` は明示的 arithmetic provider のまま保持する。

---

## 1. New module

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaExplicitSmoothMarginEscapeRadialAtBotAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaExplicitSmoothMarginEscapeRadialAtBotAudit.lean
```

imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFiniteSmoothAbelReadinessRadialEighthDescentAudit
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

---

## 2. Existing API to reuse

必ず current repository の exact signature を確認して再利用すること。

```text
cfzp039PrimeAxisGrowthExponent
cfzp039PrimeAxisGrowthExponent_pos
cfzp039ExponentialCarrierPeriodTransform

cfzp044ExplicitSmoothMargin

cfzp047CarrierCellLeft_tendsto_atTop
cfzp047_tendsto_mul_exp_neg_half
Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero

cfzp053LeftRadialDeficit
cfzp053_pntRatio_eventually_leftRadialDeficit_succ_le_sub_eighthMargin
cfzp053_leftRadialDeficit_iterate_le_sub_sum

cfzp040CarrierCellNaturalLeft
cfzp040CarrierCellExpLeft
cfzp039CarrierCellLeft
```

Do not duplicate existing exponential-decay lemmas if CFZP-047 already gives the needed shape.

---

## 3. Gate A — positive exponential growth beats the linear denominator

まず一般 real-analysis lemma を一つだけ作る。

Green target:

```lean
theorem cfzp054_exp_mul_inv_tendsto_atTop
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun U : Real => Real.exp (beta * U) / U)
      Filter.atTop Filter.atTop := by
  ...
```

### Preferred proof route

CFZP-047 と同じ標準 Mathlib theorem

```lean
Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
```

を使う。

`T = beta * U` とすると

```text
U * exp (-beta * U)
  = (1 / beta) * ((beta * U) * exp (-(beta * U)))
  -> 0.
```

そして任意 `K > 0` に対し、eventually

```text
(K * U) * exp (-beta * U) <= 1
```

を得れば、eventual `0 < U` の下で

```text
K <= exp (beta * U) / U.
```

`inv` の filter API が扱いにくければ、上記 inequality を直接 `tendsto_atTop_atTop.2` に入れること。

### Firewall

この lemma は pure real analysis。
prime-counting、PNT、prime sum は一切入れない。

---

## 4. Gate B — actual explicit smooth margin tends to `+infinity`

Green-required theorem:

```lean
theorem cfzp054ExplicitSmoothMargin_tendsto_atTop
    {epsilon : Real}
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : Real)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    Filter.Tendsto
      (fun n : Nat => cfzp044ExplicitSmoothMargin epsilon W c n)
      Filter.atTop Filter.atTop := by
  ...
```

Use:

```text
hbeta : 0 < cfzp039PrimeAxisGrowthExponent W
  := cfzp039PrimeAxisGrowthExponent_pos W hstrip

hU : U_n -> +infinity
  := cfzp047CarrierCellLeft_tendsto_atTop W c
```

and exact definition

```text
cfzp044ExplicitSmoothMargin epsilon W c n
 = exp (beta * U_n) * (M0 / (4 * U_n)).
```

A positive constant multiple of `exp(beta U) / U` tends to `+infinity`.

If direct filter multiplication is awkward, prove the `atTop` criterion manually:

```text
forall K, eventually K <= Margin_n.
```

For `K <= 0`, use eventual positivity.
For `0 < K`, divide by the positive constant `M0 / 4` and use Gate A.

---

## 5. Gate C — useful eventual fixed floors

Derive small API wrappers:

```lean
theorem cfzp054ExplicitSmoothMargin_eventually_ge
    {epsilon K : Real}
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (c : Real)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c) :
    forall^f n : Nat in Filter.atTop,
      K <= cfzp044ExplicitSmoothMargin epsilon W c n := by
  ...
```

and especially

```lean
theorem cfzp054ExplicitSmoothMargin_eventually_ge_eight ... :
    forall^f n : Nat in Filter.atTop,
      8 <= cfzp044ExplicitSmoothMargin epsilon W c n := by
  ...
```

Also retain eventually nonnegative/positive margin if convenient.

---

## 6. Gate D — PNT recurrence becomes unit radial descent

From CFZP-053:

```text
G_(n+1) <= G_n - Margin_n / 8
```

eventually under

```text
hPNT
hstrip
hsub
hM
```

and Gate C:

```text
8 <= Margin_n
```

eventually.

Prove:

```lean
theorem cfzp054_pntRatio_eventually_leftRadialDeficit_succ_le_sub_one
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : Real)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    forall^f n : Nat in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c (n + 1) <=
        cfzp053LeftRadialDeficit epsilon W c n - 1 := by
  ...
```

This is the canonical late recurrence for the rest of the checkpoint.

No new prime estimate is allowed here.

---

## 7. Gate E — finite linear descent from a tail index

Convert the eventual recurrence into a concrete tail threshold.

Target equivalent:

```lean
theorem cfzp054_leftRadialDeficit_iterate_le_sub_nat
    {epsilon : Real}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real)
    (N m : Nat)
    (hstep : forall k : Nat, N <= k ->
      cfzp053LeftRadialDeficit epsilon W c (k + 1) <=
        cfzp053LeftRadialDeficit epsilon W c k - 1) :
    cfzp053LeftRadialDeficit epsilon W c (N + m) <=
      cfzp053LeftRadialDeficit epsilon W c N - (m : Real) := by
  ...
```

Pure finite induction only.

It is also acceptable to derive this from

```text
cfzp053_leftRadialDeficit_iterate_le_sub_sum
```

plus eventual `Margin >= 8`, but the resulting public theorem should expose the simple linear descent shape.

---

## 8. Gate F — radial deficit tends to `-infinity`

This is the main Green theorem of CFZP-054.

```lean
theorem cfzp054_pntRatio_leftRadialDeficit_tendsto_atBot
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : Real)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop) :
    Filter.Tendsto
      (cfzp053LeftRadialDeficit epsilon W c)
      Filter.atTop Filter.atBot := by
  ...
```

### Preferred proof

1. extract `N` from Gate D such that all `k >= N` satisfy unit descent;
2. Gate E gives

```text
G_(N+m) <= G_N - m;
```

3. for arbitrary real target `eta`, choose a natural `m0` with

```text
G_N - m0 <= eta
```

by Archimedean property;
4. for every later index, use the same finite descent to stay below `eta`.

Use `Filter.tendsto_atTop_atBot` / `tendsto_atTop.2` exact current API as appropriate.

Do not introduce an infinite series.

---

## 9. Gate G — arbitrary radial target eventually holds

Expose the practical consequence:

```lean
theorem cfzp054_pntRatio_eventually_leftRadialDeficit_le
    {epsilon eta : Real} ... :
    forall^f n : Nat in Filter.atTop,
      cfzp053LeftRadialDeficit epsilon W c n <= eta := by
  exact (cfzp054_pntRatio_leftRadialDeficit_tendsto_atBot ...).eventually ...
```

Also provide a cofinal-index version if useful:

```lean
theorem cfzp054_pntRatio_exists_leftRadialDeficit_le
    {epsilon eta : Real} ... (N : Nat) :
    exists n : Nat, N <= n /\
      cfzp053LeftRadialDeficit epsilon W c n <= eta := by
  ...
```

This closes the old abstract `left eighth-credit` / cumulative-credit frontier at the radial-sequence level.

---

## 10. Gate H — natural carrier cutoffs are cofinal

To translate the cell-index escape into an actual natural cutoff statement, prove:

```lean
theorem cfzp054CarrierCellNaturalLeft_tendsto_atTop
    (W : PascalCenteredXiResidueTransportWindow)
    (c : Real) :
    Filter.Tendsto
      (fun n : Nat => cfzp040CarrierCellNaturalLeft W c n)
      Filter.atTop Filter.atTop := by
  ...
```

Suggested route:

```text
U_n -> +infinity
exp(U_n) -> +infinity
floor(exp(U_n)) -> +infinity.
```

Use the current Mathlib floor API if available. If not, prove the `atTop` criterion directly:
for each `N : Nat`, eventually

```text
(N : Real) <= exp(U_n)
```

and conclude

```text
N <= floor(exp(U_n)).
```

Be careful with the exact `Nat.floor` lemma and positivity premise.

---

## 11. Gate I — cofinal natural-cutoff radial escape

Combine Gate G and Gate H.

Green target:

```lean
theorem cfzp054_pntRatio_cofinal_naturalCutoff_radialDeficit_le
    {epsilon eta : Real} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (c : Real)
    (hM : 0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (N : Nat) :
    exists n : Nat,
      N <= cfzp040CarrierCellNaturalLeft W c n /\
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
          (cfzp040CarrierCellNaturalLeft W c n) <= eta := by
  ...
```

Prefer an even stronger eventual pair:

```text
forall^f n,
  N <= NaturalLeft(n) and radialDeficit(NaturalLeft(n)) <= eta.
```

if it falls out cleanly from the two Tendsto theorems.

This is the first theorem in the chain where the arbitrary natural cutoff lower bound is explicit again.

---

## 12. Optional Gate J — positive phase existential wrapper

CFZP-039 already has a positive-transform existence theorem under interior strip.
If the exact current theorem is convenient, add a wrapper eliminating `c` and `hM`:

```lean
theorem cfzp054_exists_phase_pntRatio_cofinal_naturalCutoff_radialDeficit_le
    {epsilon eta : Real} (hepsilon : 0 < epsilon)
    (hepsilon2 : epsilon < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (hstrip : Cfzp039PrimeAxisInteriorStrip W)
    (hsub : Cfzp027SubcriticalPhaseAspect W)
    (hPNT : Cfzp051PrimeCountingPNTRatioAtTop)
    (N : Nat) :
    exists c : Real, exists n : Nat,
      0 < cfzp039ExponentialCarrierPeriodTransform epsilon W c /\
      N <= cfzp040CarrierCellNaturalLeft W c n /\
      pascalCenteredXiPrimeSideFiniteRadialContactDeficit epsilon W
          (cfzp040CarrierCellNaturalLeft W c n) <= eta := by
  ...
```

Only add this if the existing positive-phase theorem gives exactly the required hypotheses without new assumptions.

---

## 13. Do NOT jump to CFZP-018 / RH yet unless an exact existing adapter is already present

CFZP-054 Green criterion stops at the cofinal natural-cutoff radial deficit statement.

Do **not** invent a new identification between

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit
```

and CFZP-018 approximate reach unless an existing theorem in the repository already performs that conversion exactly.

If a direct existing adapter is found, it may be recorded in the roadmap as the next ready bridge, but leave its actual composition to CFZP-055.

---

## 14. Roadmap update

Add CFZP-054 section.

Expected status on Green:

```text
explicit smooth margin -> +infinity: CLOSED
explicit margin eventually >= 8: CLOSED
PNT recurrence -> eventual unit radial descent: CLOSED
finite unit-descent iteration: CLOSED
left radial deficit -> -infinity: CLOSED under PNT + explicit window hypotheses
arbitrary radial target eventually reached: CLOSED
carrier natural cutoffs cofinal: CLOSED
cofinal natural-cutoff radial escape: CLOSED under PNT + explicit window hypotheses
cumulative eighth-margin credit escape GAP: RETIRED
cofinal final radial budget GAP: RETIRED at radial-deficit level
standard PNT ratio theorem itself: OPEN / arithmetic provider
automatic interior-strip provider: OPEN / GAP
automatic subcritical-window provider: OPEN / GAP
CFZP-018 adapter composition: NEXT FRONTIER
RH: OUT OF SCOPE
```

Remove/retire stale gap constructors that claim cumulative margin escape or cofinal radial budget is still absent once the above theorems exist.

---

## 15. Firewall

CFZP-054 must not prove or assume anything stronger than explicitly stated.

Do not use or claim:

- a proof of PNT;
- explicit PNT error rates beyond the existing `Cfzp051PrimeCountingPNTRatioAtTop` interface;
- Mertens;
- Dirichlet;
- Bertrand;
- prime-log equidistribution;
- infinite prime sums;
- exchange of an infinite sum and a limit;
- RH;
- automatic `Cfzp039PrimeAxisInteriorStrip W`;
- automatic `Cfzp027SubcriticalPhaseAspect W`.

The key point is precisely that **no infinite smooth-margin summation theorem is needed**:
pointwise `Margin_n -> +infinity` already converts the eventual eighth recurrence into a uniform unit descent.

---

## 16. Green criterion

CFZP-054 is Green only if the repository contains a theorem-level chain equivalent to

```text
interior strip
  -> beta = 1 - sigma > 0

U_n -> +infinity
  + positive phase transform M0 > 0
  -> Margin_n = exp(beta U_n) * M0/(4 U_n) -> +infinity
  -> eventually Margin_n >= 8

PNT ratio provider
  -> eventually combined discrepancy <= Margin_n/8
  -> CFZP-053 eventual recurrence
       G_(n+1) <= G_n - Margin_n/8
  -> eventually G_(n+1) <= G_n - 1
  -> finite induction: G_(N+m) <= G_N - m
  -> G_n -> -infinity

U_n -> +infinity
  -> NaturalLeft(n) -> +infinity

therefore:
for every natural cutoff floor N and every real target eta,
  cofinally there is a carrier cutoff X >= N
  with radialDeficit(X) <= eta.
```

No infinite prime sum and no infinite margin sum is required.
