# CFZP-0003 — CFZP-004 polarization / common-carrier 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した branch head:

```text
98a5fb0bb646f40e25171780a50e97bb0e7514c2
Add: CFZP-0002: CFZP-003 finite aggregate Big / Body / Gap
```

CFZP-003 は local full build / test Green 済みとして扱う。

今回の対象は CFZP-004 のみ。
CFZP-005 の Mellin weight、rectangle source、completed-zeta には進まない。

---

# 1. CFZP-003 review checkpoint

現 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFiniteAggregateProjection
```

は canonical prime-power support と同一の positive shadow cost を用いて、

```text
cfzpAggregateMirrorBigUpTo
cfzpAggregateMirrorBodyUpTo
cfzpAggregateMirrorGapUpTo
cfzpAggregateMirrorGapBeamUpTo
```

を構成済み。

主要 exact theorem:

```text
AggregateBig = AggregateBody + AggregateGap
AggregateGap = primeMirrorEnergy
AggregateGap = δ^2 * AggregateGapBeam
AggregateBody = 2 * AggregateWeight
```

さらに `2 ≤ X` では

```text
AggregateBody > 0
AggregateBig > 0
AggregateGap = 0 ↔ δ = 0
AggregateGapBeam(0) > 0
```

まで閉じている。

ここは再設計しない。

---

# 2. 今回の最重要監査結果

CFZP-003 の `Body` と signed PHZ mirror difference を直接同一視してはならない。

mode label `q`、

```text
L_q(δ) = exp(-δ log q)
R_q(δ) = exp(+δ log q)
```

に対し、CFZP-003 の mode Body は

```text
2 * L_q(δ) * R_q(δ) = 2
```

である。

一方、same-height critical mirror の linear mode difference は

```text
q^(-criticalMirror s) - q^(-s)
```

であり、CFZP-001 の factorization から共通 carrier `K_q(s)` を使って

```text
q^(-s)                = K_q(s) * L_q(δ)
q^(-criticalMirror s) = K_q(s) * R_q(δ)
```

したがって

```text
q^(-criticalMirror s) - q^(-s)
  = K_q(s) * (R_q(δ) - L_q(δ))
```

となる。

つまり signed PHZ mirror channel は **difference channel** であり、
CFZP-003 の amplitude interaction Body そのものではない。

今回の目的は、この違いを隠さず、

```text
quadratic Big / Body / Gap
↔ plus/minus polarization
↔ same-height common-carrier linear mirror difference
↔ per-mode quadraticization
```

を exact theorem として一本にすることである。

---

# 3. 正本となる二つの polarization

## 3.1 amplitude ThreeElement polarization

`primeMirrorOffsetState q δ` の二座標は `L_q(δ), R_q(δ)`。

一般 `CF2D.ThreeElementBridge` には既に

```text
cf2dPlusWhole
cf2dMinusWhole
cf2dInteractionBeam
squareMass
```

がある。

したがって mode level では

```text
Plus_q  = (L_q + R_q)^2
Minus_q = (L_q - R_q)^2
Big_q   = L_q^2 + R_q^2
Body_q  = 2 L_q R_q
Gap_q   = (L_q - R_q)^2
```

となる。

特に

```text
Minus_q = Gap_q
Plus_q + Minus_q = 2 Big_q
Plus_q - Minus_q = 2 Body_q
```

を exact に読む。

## 3.2 actual complex mode common-carrier polarization

same-height `criticalMirror s` は imaginary coordinate を保存する。
CFZP-001 では左右 mode が同じ cycle state を共有している。

共通 carrier を概念的に

```text
K_q(s)
  := cfzpPrimePowerCommonRadialCarrier q
     * cfzpPrimePowerCycleState q s.im
```

と置く。

`0 < q` なら `K_q(s) ≠ 0`。

すると

```text
q^(-s) / K_q(s) = L_q(centeredSigma s.re)
q^(-criticalMirror s) / K_q(s) = R_q(centeredSigma s.re)
```

を exact に証明できる。

これは actual complex prime-power mode から amplitude ThreeElement state を回収する bridge である。

---

# 4. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaFinitePolarizationProjection.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFiniteAggregateProjection
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerModeProjection
import DkMath.CosmicFormula.Rotation.CF2D.ThreeElementBridge
import Mathlib.Tactic
```

必要な既存 API が上記 import から入るなら追加 import は避ける。

旧 CS18 / CS25 は設計上の audit 参照であり、今回の clean CFZP module から巨大な prime-side audit dependency を逆流させない。

特に次の既存 pattern は参考にしてよい。

```text
CS18:
  complex q2 polarization
  plus/minus whole
  interactionBeam = 2 Re(A * conj B)

CS25:
  common carrier + signed interaction
  plus/minus energy difference recovers interaction
```

ただし theorem を再利用するためだけに CS18 / CS25 自体を import する必要はない。
一般 ThreeElement / CF2D Core を優先する。

---

# 5. Gate A — same-height common carrier

定義候補:

```lean
noncomputable def cfzpPrimePowerSameHeightCommonCarrier
    (q : ℕ) (s : ℂ) : ℂ :=
  cfzpPrimePowerCommonRadialCarrier q *
    cfzpPrimePowerCycleState q s.im
```

`q > 0` で非零を固定する。

```lean
theorem cfzpPrimePowerSameHeightCommonCarrier_ne_zero
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpPrimePowerSameHeightCommonCarrier q s ≠ 0
```

proof engineering は既存 `Complex.cpow_ne_zero` / `Complex.exp_ne_zero` 等を実際の Mathlib API に合わせること。
API 名を推測せず local source を確認する。

---

# 6. Gate B — actual mode から amplitude を回収

CFZP-001 の theorem を再利用して、まず積形式を薄くまとめる。

```lean
theorem natCpowNeg_eq_sameHeightCarrier_mul_leftAmplitude
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-s) =
      cfzpPrimePowerSameHeightCommonCarrier q s *
        (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ)
```

```lean
theorem natCpowNeg_criticalMirror_eq_sameHeightCarrier_mul_rightAmplitude
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (q : ℂ) ^ (-(criticalMirror s)) =
      cfzpPrimePowerSameHeightCommonCarrier q s *
        (primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ)
```

積の associativity の整理だけで既存 CFZP-001 を再証明しない。

可能なら normalization theorem まで置く。

```lean
theorem natCpowNeg_div_sameHeightCarrier_eq_leftAmplitude ...
```

```lean
theorem natCpowNeg_criticalMirror_div_sameHeightCarrier_eq_rightAmplitude ...
```

ただし division theorem が proof engineering を大きくする場合、必須は積形式まででよい。

---

# 7. Gate C — mode linear mirror difference

定義候補:

```lean
noncomputable def cfzpSameHeightMirrorModeDifference
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-(criticalMirror s)) -
    (q : ℂ) ^ (-s)
```

中心 theorem:

```lean
theorem cfzpSameHeightMirrorModeDifference_eq_commonCarrier_mul_amplitudeDifference
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpSameHeightMirrorModeDifference q s =
      cfzpPrimePowerSameHeightCommonCarrier q s *
        ((primeMirrorRightAmplitude q (centeredSigma s.re) -
          primeMirrorLeftAmplitude q (centeredSigma s.re) : ℝ) : ℂ)
```

符号は定義に合わせて一貫させる。

CFZP-002 の

```text
cfzpMirrorAmplitudeDifference = Left - Right
```

とは逆符号になる可能性がある。
その場合は theorem 名または `neg` を明示し、符号をごまかさない。

---

# 8. Gate D — mode difference の quadraticization

linear mirror difference の normSq は carrier normSq と amplitude Gap の積になる。

必須 theorem:

```lean
theorem normSq_cfzpSameHeightMirrorModeDifference
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    Complex.normSq (cfzpSameHeightMirrorModeDifference q s) =
      Complex.normSq (cfzpPrimePowerSameHeightCommonCarrier q s) *
        primeMirrorOffsetGap q (centeredSigma s.re)
```

これが重要な次数変換である。

```text
linear actual mode difference
  ↓ normSq
carrier mass × amplitude Gap
```

ここで `normSq` を有限和の外へ配らない。

---

# 9. Gate E — amplitude plus/minus whole aggregate

CFZP-003 と同じ canonical support / shadow cost を使う。

定義候補:

```lean
noncomputable def cfzpAggregateMirrorPlusWholeUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cf2dPlusWhole (primeMirrorOffsetState q δ)
```

```lean
noncomputable def cfzpAggregateMirrorMinusWholeUpTo
    (X : ℕ) (δ : ℝ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      cf2dMinusWhole (primeMirrorOffsetState q δ)
```

必須 exact theorem:

```text
AggregatePlusWhole  = AggregateBig + AggregateBody
AggregateMinusWhole = AggregateBig - AggregateBody
AggregateMinusWhole = AggregateGap
```

さらに polarization として

```text
AggregatePlusWhole + AggregateMinusWhole = 2 * AggregateBig
AggregatePlusWhole - AggregateMinusWhole = 2 * AggregateBody
```

を置く。

この Gate が CFZP-003 の Big / Body / Gap を一般 ThreeElement plus/minus observable へ戻す bridge である。

---

# 10. Gate F — canonical finite PHZ same-height mirror difference

既存 canonical polynomial:

```text
pascalPrimePowerPHZCanonicalUpTo X s
```

を使う。

新しい finite linear source を定義してよい。

```lean
noncomputable def cfzpCanonicalSameHeightMirrorLinearSourceUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q : ℂ) *
      cfzpSameHeightMirrorModeDifference q s
```

中心 theorem:

```lean
theorem cfzpCanonicalSameHeightMirrorLinearSourceUpTo_eq_PHZ_difference
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalSameHeightMirrorLinearSourceUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X (criticalMirror s) -
        pascalPrimePowerPHZCanonicalUpTo X s
```

証明には

```text
pascalPrimePowerPHZCanonicalUpTo_eq_support_sum
```

を再利用する。

この theorem は finite PHZ mirror channel の exact source identification である。

---

# 11. Gate G — common-carrier 展開された finite linear source

Gate C を finite sum に持ち上げる。

期待 theorem:

```text
CanonicalMirrorLinearSource
  = Σ_q weight(q)
      * CommonCarrier_q(s)
      * (RightAmplitude_q - LeftAmplitude_q)
```

Lean theorem 名は repository style に合わせてよい。

この段階では carrier が `q` ごとに異なるため、有限和の外へ common factor として出さない。

**mode ごとの common carrier** と **aggregate 全体の common carrier** を混同しない。

---

# 12. Gate H — carrier-weighted quadratic Gap ledger

per-mode quadraticization を有限集約するため、必要なら次を定義する。

```lean
noncomputable def cfzpAggregateCarrierWeightedMirrorGapUpTo
    (X : ℕ) (s : ℂ) : ℝ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    canonicalPrimePowerShadowCost q *
      Complex.normSq (cfzpPrimePowerSameHeightCommonCarrier q s) *
        primeMirrorOffsetGap q (centeredSigma s.re)
```

そして

```lean
theorem cfzpAggregateCarrierWeightedMirrorGapUpTo_eq_modeDifferenceNormSqSum ...
```

として

```text
Σ weight(q) * normSq(modeMirrorDifference_q)
```

との一致を証明する。

可能なら nonneg も置く。

これは CFZP-003 の raw amplitude Gap そのものではない。
carrier normSq が入った **actual complex mode quadratic mass** である。

両者の名前を分けること。

---

# 13. 重要な obstruction / negative audit

次の誤った式を証明しようとしてはならない。

```text
normSq(Σ modeDifference_q)
  = Σ normSq(modeDifference_q)
```

一般には cross term があるため偽である。

同様に

```text
PHZ mirror difference = AggregateBody
PHZ mirror difference = AggregateGap
```

も次数・型が違う。

今回の正しい関係は

```text
PHZ mirror difference
  = weighted sum of linear mode differences

per-mode normSq(linear mode difference)
  = carrier normSq × amplitude Gap
```

である。

必要なら named obstruction / comment としてこの firewall を残す。
ただし `Prop` の空疎な obstruction 型を量産する必要はない。

---

# 14. CS18 / CS25 との整合監査

旧 CS18 では一般複素 pair `A,B` に対して

```text
plus/minus q2 polarization
interactionBeam ↔ 2 Re(A * conj B)
```

を確認済み。

旧 CS25 では normalized ray state `Z` に対して

```text
|Z + 1|^2 = common + interaction
|Z - 1|^2 = common - interaction
```

とし、plus/minus energy difference から interaction を回収している。

CFZP-004 の amplitude plus/minus theorem がこれらと同じ algebra pattern になっていることをコメントで確認する。

しかし CFZP-004 はより前段の clean finite prime-power projection であり、CS18 / CS25 の Mellin / rectangle context を import しない。

---

# 15. same-height と functional reflection を分ける

今回の主対象は

```text
criticalMirror s
```

である。

これは `s.im` を保存するため、左右 mode が同じ cycle state を共有し、common-carrier factorization が最も clean になる。

`1 - s` は imaginary coordinate の符号も反転する。
CFZP-001 には既にその factorization があるが、今回の主 theorem surfaceへ混ぜない。

functional reflection 側の conjugate / counter-cycle transport は CFZP-005 以降で必要になった時に扱う。

---

# 16. Firewall

今回禁止すること。

```text
- CFZP-003 の Big / Body / Gap を再設計しない
- signed PHZ difference を AggregateBody と直接同一視しない
- signed PHZ difference を AggregateGap と直接同一視しない
- normSq of finite sum を sum of normSq と同一視しない
- q ごとの common carrier を aggregate 全体の一つの carrier として外へ出さない
- Complex.arg を導入しない
- phase unwrapping を導入しない
- Mellin weight を導入しない
- interval integral を導入しない
- rectangle source / TopZetaMismatchScalar を導入しない
- completed zeta / riemannZeta zero を使わない
- infinite Euler product を使わない
- RH statement を置かない
- sorry / admit / axiom を残さない
```

---

# 17. 成功条件

最低限、次の chain が Lean Green で一本になれば CFZP-004 完了とする。

```text
actual q^(-s), q^(-criticalMirror s)
  ↓ CFZP-001 same-height common carrier
Left / Right amplitude pair
  ↓ ThreeElement polarization
PlusWhole / MinusWhole
  ↓ finite canonical aggregate
Aggregate Big / Body / Gap

actual same-height mode difference
  = common carrier × amplitude difference
  ↓ per-mode normSq
carrier normSq × amplitude Gap

finite canonical PHZ mirror difference
  = weighted sum of actual mode differences
```

この段階で、linear channel と quadratic ledger の関係が exact に型分離されていれば成功。

---

# 18. Validation

実装後は最低限:

```bash
cd lean/dk_math
lake env lean DkMath/RH/CFBRC/CosmicFormulaZetaFinitePolarizationProjection.lean
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module 内に

```text
sorry
admit
axiom
```

を残さない。

Green 後、`DkMath.RH` root import へ新 module を追加してよい。

---

# 19. 次 frontier

CFZP-004 が Green になるまで CFZP-005 へ進まない。

CFZP-004 Green 後にレビューすべき問いは一つ。

```text
same-height finite PHZ linear mirror source に
actual Mellin weight / orientation を掛けたとき、
既存 CS38 mirror scalar density へ exact に射影できるか？
```

これが CFZP-005 の開始条件である。
