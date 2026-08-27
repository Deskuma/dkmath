# CFZP-0002 — CFZP-003 finite aggregate Big / Body / Gap 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成時点で GitHub 上の最新 Green 実装 checkpoint:

```text
a624947b50eac5a5bdabe243090bd42954ec3473
Add: CFZP-0001: CFZP-002 mirror Gap analytic Beam
```

CFZP-002 は Green-A として閉じてよい。

実装済み主要 surface:

```text
cfzpMirrorAmplitudeDifference
cfzpMirrorAmplitudeDifferenceBeam
cfzpMirrorGapBeam

cfzpMirrorAmplitudeDifference_eq_delta_mul_beam
primeMirrorOffsetGap_eq_delta_sq_mul_cfzpMirrorGapBeam
primeMirrorOffsetGapAt_eq_centeredSigma_sq_mul_cfzpMirrorGapBeam

tendsto_cfzpMirrorAmplitudeDifferenceBeam_zero
continuousAt_cfzpMirrorAmplitudeDifferenceBeam_zero
tendsto_cfzpMirrorGapBeam_zero
cfzpMirrorGapBeam_zero_pos
```

CFZP-001 / CFZP-002 を再設計しない。

---

# 1. 今回の目的

CFZP-003 では、single mode で得た mirror completion

```text
MirrorBig_q(δ)
  = MirrorBody_q(δ) + MirrorGap_q(δ)
```

を、canonical finite prime-power support 上で同じ正重みにより有限集約する。

今回の正本は、まず Big / Body / Gap を三本とも同じ support・同じ weight から構成し、その後で exact に

```text
AggregateMirrorBig_X(δ)
  = AggregateMirrorBody_X(δ)
    + AggregateMirrorGap_X(δ)
```

を証明することである。

さらに CFZP-002 の mode-level factorization

```text
MirrorGap_q(δ)
  = δ^2 * MirrorGapBeam_q(δ)
```

を有限和へ持ち上げ、aggregate でも共通 cosmic coordinate Gap `δ^2` を外へ factor する。

概念目標:

```text
AggregateMirrorGap_X(δ)
  = δ^2 * AggregateMirrorGapBeam_X(δ)
```

これにより

```text
Cosmic coordinate Gap δ^2
  ↓ finite positive analytic Beam ledger
Aggregate prime-mirror Gap
```

という finite projection を得る。

---

# 2. 既存 Core を再利用する

## 2.1 canonical prime-power support

既存:

```lean
canonicalPrimePowerSupportUpTo (X : ℕ) : Finset ℕ
```

membership theorem:

```lean
mem_canonicalPrimePowerSupportUpTo_iff
```

意味:

```text
q ∈ canonicalPrimePowerSupportUpTo X
  ↔ q ≤ X ∧ IsPrimePowerLabel q
```

今回の aggregate support はこれを正本とする。

prime-only の

```lean
pascalPrimeCoordinateSupportUpTo
```

へ退化させない。

CFZP-003 は prime-power aggregate である。

---

## 2.2 canonical finite von-Mangoldt weight

既存 finite arithmetic weight:

```lean
canonicalPrimePowerShadowCost q
```

prime-power witness `q = p^k` 上で

```text
canonicalPrimePowerShadowCost q = log p
```

を持つ。

既存別 module では、この cost が Mathlib の classical `ArithmeticFunction.vonMangoldt q` と全自然数上で extensionally equal であることまで既に証明済みである。

ただし今回の module は finite amplitude ledger だけを扱うので、LSeries / zeta 依存を増やすためだけに `PascalVonMangoldtLSeriesBridge` を import しないことを優先する。

今回の weight は lower-dependency の

```lean
canonicalPrimePowerShadowCost
```

を使用する。

コメントでは「canonical finite von-Mangoldt weight / shadow cost」と記述してよい。

Mathlib von Mangoldt との再同定は後段 projection で既存 theorem を再利用する。

---

## 2.3 mode-level Big / Body / Gap

既存 mirror state:

```lean
primeMirrorOffsetState q δ
```

既存 theorem:

```lean
primeMirrorOffsetState_interaction_eq_two
primeMirrorOffsetState_squareMass_eq_two_add_gap
```

したがって mode level では

```text
Big_q(δ)
  := squareMass state.core state.beam

Body_q(δ)
  := cf2dInteractionBeam state

Gap_q(δ)
  := primeMirrorOffsetGap q δ
```

として

```text
Big_q = Body_q + Gap_q
Body_q = 2
```

が source-derived にある。

今回 `Body` は RH 固有 projection API 上の暫定名であり、一般 `CoreBeamGap.BodyN` と definitional equality であるとは主張しない。

---

# 3. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaFiniteAggregateProjection.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFiniteAggregateProjection
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaMirrorGapBeamProjection
import DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
import DkMath.RH.CFBRC.PascalPrimePowerCanonicalFold
import Mathlib.Tactic
```

不要な import は削ってよい。

`PascalVonMangoldtLSeriesBridge`、`riemannZeta`、LSeries、Mellin、rectangle source は今回不要。

---

# 4. 定義 surface

命名は repository style に合わせて多少調整してよいが、Big / Body / Gap の意味を変えないこと。

## 4.1 Aggregate Big

概念定義:

```lean
noncomputable def cfzpAggregateMirrorBigUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      squareMass
        (primeMirrorOffsetState q δ).core
        (primeMirrorOffsetState q δ).beam
```

Big は `2 + Gap` を先に定義してはならない。

**Big を source state の squareMass から先に構成する。**

後で theorem として `Body + Gap` へ分解する。

---

## 4.2 Aggregate Body

概念定義:

```lean
noncomputable def cfzpAggregateMirrorBodyUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cf2dInteractionBeam (primeMirrorOffsetState q δ)
```

この Body は mode product invariant から最終的に `2 * totalWeight` へ簡約される。

ただし定義自体は interaction observable から作る。

---

## 4.3 Aggregate Gap

概念定義:

```lean
noncomputable def cfzpAggregateMirrorGapUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      primeMirrorOffsetGap q δ
```

これは既存 generic

```lean
primeMirrorEnergy
```

と exact に一致する theorem を置くこと。

---

## 4.4 Aggregate Gap Beam

CFZP-002 を有限和へ上げるため、次を定義する。

```lean
noncomputable def cfzpAggregateMirrorGapBeamUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cfzpMirrorGapBeam q δ
```

この Beam ledger は Gap そのものではない。

```text
AggregateGap = δ^2 * AggregateGapBeam
```

の右側 factor である。

---

# 5. support / weight Core

aggregate theorem の前に、canonical support が本当に positive nonconstant mode だけを持つことを named theorem として固定する。

## Gate A — support mode is greater than one

推奨 theorem:

```lean
theorem one_lt_of_mem_canonicalPrimePowerSupportUpTo
    {X q : ℕ}
    (hq : q ∈ canonicalPrimePowerSupportUpTo X) :
    1 < q
```

証明では membership から `IsPrimePowerLabel q` を取り、`primePowerShadow_spec` または witness を使う。

prime `p > 1` と positive exponent から `q = p^k > 1` を出す。

---

## Gate B — canonical weight is strictly positive on support

推奨 theorem:

```lean
theorem canonicalPrimePowerShadowCost_pos_of_mem
    {X q : ℕ}
    (hq : q ∈ canonicalPrimePowerSupportUpTo X) :
    0 < canonicalPrimePowerShadowCost q
```

`primePowerShadow_spec` と

```lean
canonicalPrimePowerShadowCost_eq_log_of_witness
```

を使い、base prime `p > 1` から `Real.log p > 0` を得る。

この theorem は後続の positive aggregate で再利用する。

---

## Gate C — cutoff `X ≥ 2` contains mode `2`

推奨 theorem:

```lean
theorem two_mem_canonicalPrimePowerSupportUpTo
    {X : ℕ} (hX : 2 ≤ X) :
    2 ∈ canonicalPrimePowerSupportUpTo X
```

`2 = 2^1` を prime-power witness とする。

これから support nonempty を得る。

```lean
theorem canonicalPrimePowerSupportUpTo_nonempty
    {X : ℕ} (hX : 2 ≤ X) :
    (canonicalPrimePowerSupportUpTo X).Nonempty
```

---

# 6. exact aggregate completion

## Gate D — Gap is generic finite mirror energy

```lean
theorem cfzpAggregateMirrorGapUpTo_eq_primeMirrorEnergy
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ =
      primeMirrorEnergy
        (canonicalPrimePowerSupportUpTo X)
        canonicalPrimePowerShadowCost
        δ
```

これは generic positivity theorem を再利用するための bridge。

---

## Gate E — Big = Body + Gap

今回の中心 finite completion theorem:

```lean
theorem cfzpAggregateMirrorBigUpTo_eq_body_add_gap
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorBigUpTo X δ =
      cfzpAggregateMirrorBodyUpTo X δ +
        cfzpAggregateMirrorGapUpTo X δ
```

証明は Finset の各 mode について

```lean
primeMirrorOffsetState_squareMass_eq_two_add_gap
```

と

```lean
primeMirrorOffsetState_interaction_eq_two
```

を使う。

Big の定義を RHS に合わせて作ることで theorem を自明化しない。

source squareMass から作った Big が、結果として Body + Gap に分解されることを示す。

---

## Gate F — Body is a fixed positive mass ledger

可能なら total weight を補助定義してよい。

```lean
noncomputable def cfzpAggregateMirrorWeightUpTo (X : ℕ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q
```

そして

```lean
theorem cfzpAggregateMirrorBodyUpTo_eq_two_mul_weight
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorBodyUpTo X δ =
      2 * cfzpAggregateMirrorWeightUpTo X
```

を得る。

RHS の乗算順序は repository style に合わせてよい。

重要なのは、Body が `δ` に依存しない fixed positive mass であることを theorem として露出させること。

---

# 7. positivity / zero set

## Gate G — aggregate Gap nonnegative

```lean
theorem cfzpAggregateMirrorGapUpTo_nonneg
    (X : ℕ) (δ : ℝ) :
    0 ≤ cfzpAggregateMirrorGapUpTo X δ
```

既存 `primeMirrorEnergy_nonneg` と Gate B を再利用する。

---

## Gate H — aggregate Gap vanishes exactly at `δ = 0`

`X ≥ 2` なら support に mode `2` が入り、全 support weight が strict positive なので、既存 generic theorem を使って

```lean
theorem cfzpAggregateMirrorGapUpTo_eq_zero_iff_delta_eq_zero
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ = 0 ↔
      δ = 0
```

を得る。

これは既存 mode-level zero theoremを足し上げて手作業で再証明するより、`primeMirrorEnergy_eq_zero_iff_delta_eq_zero` を再利用することを優先する。

必要なら complex point wrapper も追加してよい。

```lean
theorem cfzpAggregateMirrorGapAtUpTo_eq_zero_iff_re_eq_half
    {X : ℕ} (hX : 2 ≤ X) (s : ℂ) :
    cfzpAggregateMirrorGapUpTo X (centeredSigma s.re) = 0 ↔
      s.re = (1 : ℝ) / 2
```

ただし本体は real `δ` theorem とする。

---

## Gate I — Body / Big positivity

`X ≥ 2` なら weight `2` が正なので、Body は正。

```lean
theorem cfzpAggregateMirrorBodyUpTo_pos
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    0 < cfzpAggregateMirrorBodyUpTo X δ
```

その後、Big completion と Gap nonneg から

```lean
theorem cfzpAggregateMirrorBigUpTo_pos
    {X : ℕ} (hX : 2 ≤ X) (δ : ℝ) :
    0 < cfzpAggregateMirrorBigUpTo X δ
```

を得る。

この二つは「finite positive aggregate Big」という CFZP-003 の意味を固定するため、可能な限り実装する。

---

# 8. CFZP-002 を aggregate へ持ち上げる

## Gate J — aggregate coordinate Gap factorization

最重要 theorem の一つ:

```lean
theorem cfzpAggregateMirrorGapUpTo_eq_delta_sq_mul_gapBeam
    (X : ℕ) (δ : ℝ) :
    cfzpAggregateMirrorGapUpTo X δ =
      δ ^ 2 * cfzpAggregateMirrorGapBeamUpTo X δ
```

各 summand に

```lean
primeMirrorOffsetGap_eq_delta_sq_mul_cfzpMirrorGapBeam
```

を適用し、共通 factor `δ^2` を finite sum の外へ出す。

この theorem により single-mode の

```text
δ^2 → MirrorGap_q
```

が finite prime-power ledger の

```text
δ^2 → AggregateMirrorGap_X
```

へ上がる。

ここでも zero-set theorem から逆算しない。

量の exact factorization を Finset algebra で証明する。

---

## Gate K — aggregate Gap Beam is noncollapsed at center

`X ≥ 2` なら mode `2` が positive weight で含まれ、

```lean
cfzpMirrorGapBeam_zero_pos
```

がある。

他 mode の Beam summand は square なので nonnegative。

従って

```lean
theorem cfzpAggregateMirrorGapBeamUpTo_zero_pos
    {X : ℕ} (hX : 2 ≤ X) :
    0 < cfzpAggregateMirrorGapBeamUpTo X 0
```

を得る。

これは重要な監査 theorem である。

`X ≥ 2` では中心で

```text
AggregateGap_X(0) = 0
AggregateGapBeam_X(0) > 0
```

なので、aggregate Gap の消失も Beam collapse ではなく共通 coordinate Gap `δ^2` の collapse である。

proof engineering が極端に重い場合は Gate K を named audit / TODO に落とさず、まず一つの positive summand + nonnegative remainder で直接閉じる方法を試すこと。

`sorry` にはしない。

---

# 9. 今回の数学的到達点

CFZP-003 が Green なら、次の exact chain が成立する。

```text
single mode:
  MirrorBig_q
    = MirrorBody_q + MirrorGap_q

single-mode Gap:
  MirrorGap_q
    = δ^2 * MirrorGapBeam_q

finite canonical prime-power aggregate:
  AggregateBig_X
    = AggregateBody_X + AggregateGap_X

aggregate Gap:
  AggregateGap_X
    = δ^2 * AggregateGapBeam_X
```

さらに `X ≥ 2` で

```text
AggregateBody_X > 0
AggregateBig_X > 0
AggregateGap_X = 0 ↔ δ = 0
AggregateGapBeam_X(0) > 0
```

まで得られるのが理想。

これはまだ signed PHZ、polarization、Mellin source、rectangle remainder ではない。

**positive amplitude mass ledger が finite prime-power scale で完成した**、というところで止める。

---

# 10. Firewall

今回の module で禁止すること。

```text
- CFZP-004 polarization へ進まない
- finite PHZ の signed complex sum と AggregateGap を同一視しない
- SymmetricEulerRate = AggregateGap のような theorem を作らない
- Mellin weight / top-edge integral を導入しない
- RectangleBackground / TopZetaMismatchScalar を導入しない
- rectangle remainder を Gap と呼ばない
- riemannZeta / completed-zeta zero を使わない
- infinite Euler product / LSeries limit を使わない
- Big を `Body + Gap` の RHS として定義して theorem を自明化しない
- prime-only support へ退化しない
- CFZP-001 / CFZP-002 を再設計しない
- sorry / admit / axiom を残さない
```

今回扱うのは **finite canonical prime-power support 上の positive amplitude mass** だけである。

---

# 11. 検証

最低限:

```bash
cd lean/dk_math
lake env lean DkMath/RH/CFBRC/CosmicFormulaZetaFiniteAggregateProjection.lean
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

追加 module 内について

```text
sorry
admit
axiom
```

がないことを確認する。

既存 repository 由来の警告と、今回追加コードの警告を区別して報告する。

Green 後は実装結果を push し、そこで停止する。

---

# 12. Green 後に報告する内容

```text
- branch head
- changed files
- new definitions
- major theorem names
- module build result
- lake build DkMath.RH result
- ./lean-build.sh result
- ./lean-test.sh result
- git diff --check result
- new module 内 sorry / admit / axiom の有無
```

CFZP-004 へは進まない。

次 frontier は repository 上の Green 実装を賢狼がレビューした後に決定する。
