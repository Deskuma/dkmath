# CFZP-0073 / CFZP-045

## higher-prime-power sigma-tail envelope / finite cell reduction — implementation instructions

作業 branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

前段:

- CFZP-039: exact prime-axis leading carrier + remainder, radial reservoir
- CFZP-040: finite Abel / prime-counting discrepancy split
- CFZP-041: smooth/discrepancy cell reservoir
- CFZP-042: smooth Abel cell = transformed carrier main + weight variation error
- CFZP-043: explicit positive smooth margin on sufficiently late positive-transform cells
- CFZP-044: explicit smooth-margin radial budget; sufficiently late cell では exceptional prime-axis support / mass = 0

CFZP-044 は Green-A。特に current source で以下が CLOSED:

```text
cfzp044RadialLateThreshold
cfzp044PrimeAxisBlockSupport_eq_eligible
cfzp044ExceptionalPrimeAxisPairBlockSupport_eq_empty
cfzp044ExceptionalPrimeAxisReferenceMass_eq_zero
cfzp044ExplicitSmoothMargin
cfzp044_exp_transform_div_four_le_smoothCell
Cfzp044ExplicitSmoothMarginBudgetAt
cfzp044ExplicitSmoothMarginBudget_implies_radialContactDeficit_le
Cfzp044CofinalExplicitSmoothMarginBudget
```

**CFZP-045 の目的は、044 に唯一残る finite structural residual の一つである `cfzp034HigherPowerReferenceMass` を、各 prime-power pair の exact sigma decay を保持した finite sigma-tail に置換すること。**

この段ではまだ sigma-tail 自体が explicit smooth margin より小さいことまでは証明しない。まず

```text
raw higher-power reference mass
  <= explicit constant * finite higher-power sigma tail
```

を exact finite theorem として閉じ、044 radial budget の `HigherPowerReferenceMass` をこの tail envelope に差し替える。

prime-counting discrepancy は 041/044 の named finite debt `D` のまま固定する。

本段では PNT、Mertens、Dirichlet、Bertrand、prime-log equidistribution、infinite prime sums、summability、limit exchange、automatic `σ < 1`、CFZP-018 provider、global RH を導入しない。

---

## 1. 新規 module

候補:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaHigherPrimePowerSigmaTailEnvelopeAudit
```

file:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaHigherPrimePowerSigmaTailEnvelopeAudit.lean
```

主 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimeAxisExplicitSmoothMarginRadialBudgetAudit
import Mathlib.Tactic
```

公開 import を `DkMath/RH.lean` に追加する。

---

## 2. Gate A — higher-power support really means exponent >= 2

034 の support は pair `pk : ℕ × ℕ` に対して actual exponent を `pk.2 + 1` と読む。

```lean
theorem cfzp045HigherPowerActualExponent_two_le
    {A B : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport A B) :
    2 ≤ pk.2 + 1 := by
  ...
```

を閉じる。

同時に higher support から base prime を回収する convenience theorem を追加する。

```lean
theorem cfzp045HigherPower_basePrime
    {A B : ℕ} {pk : ℕ × ℕ}
    (hpk : pk ∈ cfzp034HigherPowerPairBlockSupport A B) :
    Nat.Prime pk.1 := by
  ...
```

必要なら actual exponent positivity も helper とする。

これは完全な finite support fact。

---

## 3. Gate B — log-coordinate factor `log p / (j log p) = 1/j`

033 coordinate:

```text
cfzp033PrimePowerLogCoordinate p j = (j : ℝ) * log p
```

を使い、prime `p`, `0 < j` の下で

```lean
theorem cfzp045_log_div_primePowerLogCoordinate_eq_inv
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j) :
    Real.log (p : ℝ) /
        cfzp033PrimePowerLogCoordinate p j =
      1 / (j : ℝ) := by
  ...
```

を閉じる。

`hp.one_lt` から `0 < log p`、従って `log p ≠ 0` を使うだけでよい。

---

## 4. Gate C — canonical per-pair sigma envelope

033 には既に safety 条件

```text
2 * ε <= u
1 <= u
u := cfzp033PrimePowerLogCoordinate p j
```

の下で概念的に

```text
ReferenceMass(p,j)
<= 128 * (T+1)^2 * exp(a*ε)
   * (log p / u)
   * exp(-σ*u)
```

という upper bound がある。

034 には

```text
cfzp034PrimePowerSigmaWeight_eq_primeAxisWeight_pow
```

があり

```text
exp(-σ * j log p) = PrimeAxisSigmaWeight(p)^j
```

を exact に持つ。

定数を first-class にする。

```lean
noncomputable def cfzp045HigherPowerReferenceMassConstant
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow) : ℝ :=
  128 * (W.rectangle.T + 1) ^ 2 *
    Real.exp (cfzpModePhaseAbscissa W * ε)
```

※ current 033 theorem の exact constant / exponent notation を repository source に合わせること。既存 theorem RHS と definitional に一致する形を優先する。

per-pair envelope:

```lean
noncomputable def cfzp045HigherPowerSigmaEnvelopeTerm
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (p j : ℕ) : ℝ :=
  cfzp045HigherPowerReferenceMassConstant ε W *
    (cfzp034PrimeAxisSigmaWeight W p) ^ j / (j : ℝ)
```

主 theorem:

```lean
theorem cfzp045PrimePowerReferenceMass_le_sigmaEnvelopeTerm
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {p j : ℕ} (hp : Nat.Prime p) (hj : 0 < j)
    (hsafe2 : 2 * ε ≤ cfzp033PrimePowerLogCoordinate p j)
    (hsafe1 : 1 ≤ cfzp033PrimePowerLogCoordinate p j) :
    cfzp031PrimePowerReferenceMass ε W p j ≤
      cfzp045HigherPowerSigmaEnvelopeTerm ε W p j := by
  ...
```

proof spine:

1. 033 fixed-prime sigma-weight upper bound;
2. Gate B で `log p / u = 1/j`;
3. 034 sigma weight power identity;
4. ring / field normalization only.

この theorem は distribution-free。

---

## 5. Gate D — finite higher-power sigma tail on a block

raw higher support と同じ Finset を使い、

```lean
noncomputable def cfzp045HigherPowerSigmaTail
    (W : PascalCenteredXiResidueTransportWindow)
    (A B : ℕ) : ℝ :=
  ∑ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
    (cfzp034PrimeAxisSigmaWeight W pk.1) ^ (pk.2 + 1) /
      ((pk.2 + 1 : ℕ) : ℝ)
```

を定義する。

最低限:

```text
0 <= cfzp045HigherPowerSigmaTail W A B
```

を閉じる。

prime-axis sigma weight は positive なので各項 nonnegative。

---

## 6. Gate E — block safety and raw mass <= constant * sigma tail

まず generic finite safety predicate を用意する。

```lean
def Cfzp045HigherPowerBlockSafe
    (ε : ℝ) (A B : ℕ) : Prop :=
  ∀ pk ∈ cfzp034HigherPowerPairBlockSupport A B,
    2 * ε ≤ cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1) ∧
    1 ≤ cfzp033PrimePowerLogCoordinate pk.1 (pk.2 + 1)
```

この predicate の下で Finset sum monotonicity により

```lean
theorem cfzp045HigherPowerReferenceMass_le_sigmaTail
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    {A B : ℕ}
    (hsafe : Cfzp045HigherPowerBlockSafe ε A B) :
    cfzp034HigherPowerReferenceMass ε W A B ≤
      cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp045HigherPowerSigmaTail W A B := by
  ...
```

を閉じる。

各 `pk` について:

- Gate A で `j = pk.2+1 > 0`;
- Gate A で base prime;
- `hsafe`;
- Gate C per-pair bound;
- sum を constant 外出し。

ここでは geometric series / infinite sum を使わない。

---

## 7. Gate F — carrier-cell higher-power block is automatically safe when late

これは CFZP-045 の重要接続 target。

cell natural endpoints:

```text
A := cfzp040CarrierCellNaturalLeft W c n
B := cfzp040CarrierCellNaturalRight W c n
U := cfzp039CarrierCellLeft W c n
```

039/040/041/044 の cell bridge と prime-power pair support membership を使い、

```lean
theorem cfzp045CarrierCellHigherPowerBlockSafe
    {ε : ℝ}
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    Cfzp045HigherPowerBlockSafe ε
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) := by
  ...
```

を閉じる。

狙う finite arithmetic:

- `pk ∈ block(A,B)` から actual prime power `pk.1 ^ (pk.2+1)` が `(A,B]` にあることを current pair-support API から回収する;
- `A = floor(exp U)` と `A < p^j` から `exp U < p^j` または必要十分な log lower boundへ橋渡しする;
- `U < log(p^j) = j log p`;
- `hLate` から `2ε ≤ U < u` と `1 ≤ U < u`。

**support API の current exact orientation を必ず source から確認し、推測した theorem name を作らないこと。**

もし floor bridge で strictness が煩雑なら、040 の raw-cell proof patternを generalized prime-power valueへ再利用する helper を先に作る。

この Gate は 045 の canonical cell specialization に必要なので Green 条件とする。

---

## 8. Gate G — carrier-cell higher-power mass envelope

Gate E + Gate F から直接:

```lean
theorem cfzp045CarrierCellHigherPowerReferenceMass_le_sigmaTail
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < Real.log 2)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hLate : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp034HigherPowerReferenceMass ε W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) ≤
      cfzp045HigherPowerReferenceMassConstant ε W *
        cfzp045HigherPowerSigmaTail W
          (cfzp040CarrierCellNaturalLeft W c n)
          (cfzp040CarrierCellNaturalRight W c n) := by
  ...
```

を閉じる。

---

## 9. Gate H — sigma-tail explicit-margin budget -> radial endpoint

044 canonical budget の raw higher mass を sigma-tail envelope へ置換する。

```lean
def Cfzp045SigmaTailExplicitSmoothMarginBudgetAt
    (ε η D : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) : Prop :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalLeft W c n) +
    cfzp039PrimeAxisRemainderCellDebt ε W c n
      (cfzp040CarrierCellNaturalLeft W c n)
      (cfzp040CarrierCellNaturalRight W c n) +
    cfzp045HigherPowerReferenceMassConstant ε W *
      cfzp045HigherPowerSigmaTail W
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) + D ≤
    cfzp044ExplicitSmoothMargin ε W c n + η
```

そして 044 main theorem と Gate G を使い:

```lean
theorem cfzp045SigmaTailExplicitSmoothMarginBudget_implies_radialContactDeficit_le
    ... :
    pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W
      (cfzp040CarrierCellNaturalRight W c n) ≤ η := by
  ...
```

を閉じる。

044 が要求する:

- `0 < ε`, `ε < log 2`;
- positive transform;
- radial-late threshold;
- `SmoothAbel = SmoothLogCell` readiness;
- 041 Abel/discrepancy regularity;
- discrepancy functional bound `D`;

はそのまま受け取ってよい。

証明は:

1. radial-late -> Gate F safety;
2. Gate G raw higher mass ≤ sigma-tail budget;
3. sigma-tail budget -> `Cfzp044ExplicitSmoothMarginBudgetAt`;
4. 044 radial theorem。

prime distribution は使わない。

---

## 10. Gap / firewall

候補:

```lean
inductive Cfzp045HigherPrimePowerSigmaTailEnvelopeGap : Prop
  | noAutomaticInteriorStripWindowProvider
  | noAutomaticSmoothAbelLogCellReadinessProvider
  | noPrimeCountingDiscrepancyFunctionalDecayProvider
  | noPointwiseDiscrepancyToFunctionalBound
  | noHigherPowerSigmaTailCardinalityBound
  | noHigherPowerSigmaTailExponentialDecay
  | noCofinalSigmaTailExplicitSmoothMarginBudgetProvider
```

**`noHigherPrimePowerResidualDomination` のような raw residual gap は、Gate G/H が閉じたなら残さない。**

この段で閉じるのは raw higher-power residual → explicit finite sigma-tail envelope まで。

以下は禁止:

- PNT / Mertens / Dirichlet / Bertrand
- infinite prime sums / Euler products
- summability / limit exchange
- prime-log equidistribution
- automatic `σ < 1`
- sigma-tail の無条件 negligible claim
- CFZP-018 provider
- RH

---

## 11. Roadmap

CFZP-045 entry を追加し、最低限:

```text
higher-power actual exponent >= 2: CLOSED
higher-power base prime recovery: CLOSED
log p / (j log p) = 1/j: CLOSED
per-pair reference mass <= constant * sigmaWeight^j / j: CLOSED
finite higher-power sigma tail: CLOSED
raw higher-power block mass <= constant * sigma tail: CLOSED
late carrier-cell higher-power block safety: CLOSED
carrier-cell higher-power mass <= sigma-tail envelope: CLOSED
sigma-tail explicit-margin budget -> radial endpoint: CLOSED
higher-power sigma-tail cardinality bound: OPEN / GAP
higher-power sigma-tail exponential decay: OPEN / GAP
prime-counting discrepancy decay: OPEN / GAP
actual cofinal budget provider: OPEN / GAP
infinite prime distribution / limit exchange / global RH: OUT OF SCOPE
```

---

## Completion criterion

Green の最小条件:

```text
Gate A CLOSED
Gate B CLOSED
Gate C CLOSED
Gate D CLOSED
Gate E CLOSED
Gate F CLOSED
Gate G CLOSED
Gate H CLOSED
public import added
roadmap updated
no sorry / new axiom / native_decide
```

---

## Strategic target after CFZP-045

045 が閉じると higher-power residual は raw event mass ではなく

```text
K(ε,W) * Σ_{(p,j) in one finite cell, j>=2}
  sigmaWeight(p)^j / j
```

だけになる。

次の CFZP-046 では prime distribution を使わず、one log-cell `(U,U+P]` の deterministic geometryだけでこの有限 tail の項数と base range を押さえる。

概念的には higher power `j >= 2` なら

```text
j log p <= U + P
=> 2 log p <= U + P
=> p <= exp((U+P)/2).
```

また fixed `p` について cell に入れる指数 `j` の個数は interval length `P/log p` から一様有限個に抑えられる。

その結果、PNT 抜きで概念的に

```text
HigherPowerSigmaTail(cell U)
<= C(W) * exp((1/2 - σ) U)
```

型の finite exponential envelope を狙う。

043/044 の smooth margin は

```text
exp((1-σ)U) / U
```

型なので、比は概念的に

```text
U * exp(-U/2)
```

へ落ちる。ここが 046→047 の次の魔核である。