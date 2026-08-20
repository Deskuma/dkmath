# CFZP-0004 — CFZP-005 Mellin / functional-reflection source projection 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した Green checkpoint:

```text
9a53fa28a35624e1962bd8b887a4e5c2583d9326
Add: CFZP-0003: CFZP-004 polarization / common-carrier
```

CFZP-004 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
```

CFZP-004 は次を exact に閉じている。

```text
same-height common carrier
actual left/right mode recovery
same-height signed mirror mode difference
mode-wise normSq quadraticization
aggregate Plus / Minus polarization
AggregateBig / AggregateBody / AggregateGap recovery
canonical finite same-height PHZ mirror difference
carrier-weighted quadratic Gap ledger
```

今回 CFZP-005 では、この Green API を壊さない。

---

# 1. 今回の最重要区別

CFZP-004 の same-height critical reflection と、CS37 / CS38 の functional reflection は同じではない。

既存定義:

```text
criticalMirror(s)
```

は実部だけを `1 - Re(s)` へ反射し、虚部を保存する。

一方 CS37 の symmetric Euler rate は

```text
pascalPrimePowerPHZFiniteUpTo X (1 - s)
  - pascalPrimePowerPHZFiniteUpTo X s
```

を使う。

`1 - s` は虚部も反転する。

したがって今回、次のような同一視は禁止する。

```text
criticalMirror s  ≠  1 - s   generally
```

CFZP-001 には既に functional reflection 用 theorem

```lean
natCpowNeg_one_sub_eq_commonRadial_mul_rightAmplitude_mul_cycle
```

があり、`1 - s` では cycle state が `-s.im` へ反転する。

この theorem を正本として使うこと。

---

# 2. 今回の目的

CFZP-005 の目的は、finite cosmic / prime-power projection を actual CS37 / CS38 source channel へ exact に接続することである。

正本の経路は次。

```text
functional-reflection prime-power mode difference
  ↓ finite canonical q-sum
CFZP functional-reflection linear source
  ↓ exact identification
CS37 FiniteSymmetricEulerRate
  ↓ actual top Mellin weight
CFZP Mellin symmetric-Euler density
  ↓ exact identification
CS38 FiniteSymmetricEulerMirrorDensity
  ↓ completed + gamma channels と再結合
CS38 ResidualMirrorScalarDensity
  ↓ oriented half interval
TopZetaMismatchScalar
```

今回の source projection は **linear observable** である。

CFZP-003 / 004 の nonnegative quadratic Gap ledger と同一視しない。

---

# 3. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaMellinSourceProjection.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteResidualMirrorWeightedSourceRecoveryAudit
import Mathlib.Tactic
```

必要最小限へ調整してよい。

既存 CS37 / CS38 theorem を再証明しない。

---

# 4. Gate A — functional-reflection mode difference

まず natural label `q` に対する actual functional-reflection mode difference を定義する。

候補:

```lean
noncomputable def cfzpFunctionalReflectionModeDifference
    (q : ℕ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-(1 - s)) - (q : ℂ) ^ (-s)
```

CFZP-004 の

```lean
cfzpSameHeightMirrorModeDifference
```

とは別名・別定義のまま保持すること。

次に CFZP-001 の factorization を使って、概念的に

```text
FunctionalDifference_q(s)
  = Radial_q *
      (RightAmplitude_q(δ) * Cycle_q(-t)
        - LeftAmplitude_q(δ) * Cycle_q(t))
```

を exact theorem として得る。

ここでは `Radial_q` は共通だが、cycle state は共通ではない。

したがって cycle を aggregate 外へ出したり、same-height common carrier をそのまま使ったりしない。

候補 theorem:

```lean
theorem cfzpFunctionalReflectionModeDifference_eq_commonRadial_mul_phaseDisplacedAmplitude
    {q : ℕ} (hq : 0 < q) (s : ℂ) :
    cfzpFunctionalReflectionModeDifference q s =
      cfzpPrimePowerCommonRadialCarrier q *
        ((primeMirrorRightAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q (-s.im) -
          (primeMirrorLeftAmplitude q (centeredSigma s.re) : ℂ) *
            cfzpPrimePowerCycleState q s.im)
```

RHS の括弧・積順は Lean の扱いやすさに合わせてよい。

---

# 5. Gate B — canonical finite functional-reflection source

CFZP-004 と同じ canonical prime-power support / shadow cost を使う。

候補:

```lean
noncomputable def cfzpCanonicalFunctionalReflectionLinearSourceUpTo
    (X : ℕ) (s : ℂ) : ℂ :=
  ∑ q ∈ canonicalPrimePowerSupportUpTo X,
    (canonicalPrimePowerShadowCost q : ℂ) *
      cfzpFunctionalReflectionModeDifference q s
```

まず canonical PHZ との exact theorem を得る。

```lean
theorem cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_canonicalPHZ_difference
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
      pascalPrimePowerPHZCanonicalUpTo X (1 - s) -
        pascalPrimePowerPHZCanonicalUpTo X s
```

次に既存 canonical fold を用い、実際の finite PHZ へ接続する。

最重要 theorem:

```lean
theorem cfzpCanonicalFunctionalReflectionLinearSourceUpTo_eq_finiteSymmetricEulerRate
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s =
      pascalCenteredXiPrimeSideFiniteSymmetricEulerRate X s
```

証明では既存

```lean
pascalPrimePowerPHZFiniteUpTo_eq_canonical
```

を再利用すること。

ここが CFZP finite source と CS37 の same-object bridge である。

---

# 6. Gate C — same-height source との関係は「差異」を保存する

可能なら、CFZP-004 の same-height source と今回の functional-reflection source の関係を、誤同一視防止用 theorem / comment として残す。

重要なのは、一般に

```text
cfzpCanonicalSameHeightMirrorLinearSourceUpTo X s
```

と

```text
cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s
```

は同じではないこと。

無理に `≠` theorem を一般形で証明する必要はない。

最低限 module docstring で、前者は same-height cycle、後者は `±s.im` cycle を使う別 observable と明記すること。

もし既存 conjugation API から自然に exact relation が短く得られるなら追加してよいが、今回の必須 Gate ではない。

---

# 7. Gate D — actual Mellin weight を掛けた Euler mirror density

CS38 が実際に使う weight は既存

```lean
pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u
```

である。

これをそのまま使う。

新しい別 weight を作らない。

候補定義:

```lean
noncomputable def cfzpFiniteMellinSymmetricEulerDensity
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  (pascalCenteredXiPrimeSideFiniteResidualTopMellinWeight ε W u *
    cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
      (pascalSymmetricRectangleTopEdge u W.rectangle.T)).im
```

必須 exact theorem:

```lean
theorem cfzpFiniteMellinSymmetricEulerDensity_eq_cs38
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) :
    cfzpFiniteMellinSymmetricEulerDensity ε X W u =
      pascalCenteredXiPrimeSideFiniteSymmetricEulerMirrorDensity ε X W u
```

これは Gate B の source equality を Mellin-weighted scalar observable まで運ぶ theorem である。

単なる rename にしない。

`cfzpFiniteMellinSymmetricEulerDensity` の定義には CFZP source を直接入れ、theorem で CS38 density と一致させること。

---

# 8. Gate E — full CS38 mirror scalar density への埋め込み

CS38 の full mirror scalar density は Euler channel 単独ではない。

既存 exact decomposition:

```text
ResidualMirrorScalarDensity
  = CompletedMirrorDensity
    + GammaMirrorDensity
    + SymmetricEulerMirrorDensity
```

を尊重する。

したがって prime-power CFZP source 単独を

```text
TopZetaMismatchScalar
```

と同一視してはならない。

CFZP Euler channel を埋め込んだ full projected density を定義する。

候補:

```lean
noncomputable def cfzpProjectedMirrorScalarDensity
    (ε : ℝ) (X : ℕ)
    (W : PascalCenteredXiResidueTransportWindow)
    (u : ℝ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteCompletedMirrorDensity ε W u +
    pascalCenteredXiPrimeSideFiniteGammaMirrorDensity ε W u +
    cfzpFiniteMellinSymmetricEulerDensity ε X W u
```

必須 pointwise theorem:

```lean
theorem pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity_eq_cfzpProjected
    {ε : ℝ}
    {W : PascalCenteredXiResidueTransportWindow}
    (hSafe : IsPascalCenteredXiTopLogDerivDecompositionSafe W)
    {X : ℕ} {u : ℝ}
    (hu : u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)) :
    pascalCenteredXiPrimeSideFiniteResidualMirrorScalarDensity ε X W u =
      cfzpProjectedMirrorScalarDensity ε X W u
```

証明は既存 CS38 decomposition theorem と Gate D の Euler density equality を使う。

completed / gamma channel の再証明は禁止。

---

# 9. Gate F — oriented half-integral / TopZetaMismatchScalar

CFZP-005 の最上位 surface として、既存 CS38 source-recovery theorem を CFZP projected density で書き直す。

既存 theorem

```lean
pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_mirror_weighted_half_integral
```

と同じ安全性・積分可能性仮定を受け取り、最終的に概念的に

```text
TopZetaMismatchScalar
  = (1 / π) * ∫_{σ..1/2} cfzpProjectedMirrorScalarDensity
```

を得る。

候補 theorem 名:

```lean
pascalCenteredXiPrimeSideFiniteTopZetaMismatchScalar_eq_cfzpProjected_half_integral
```

証明方針:

1. 既存 CS38 half-integral theorem をそのまま適用する。
2. `σ..1/2` 上で Gate E の pointwise equality を使い `intervalIntegral.integral_congr_ae` 等で integrand を置換する。
3. `u ∈ Set.uIcc W.rectangle.σ (1 - W.rectangle.σ)` が必要なら、既存 window の幾何条件から half interval が full mirror interval に含まれることを示す。
4. orientation を勝手に反転しない。
5. 係数 `1 / Real.pi` を変更しない。

proof engineering 上、subset proof に既存 lemma があるなら必ず再利用する。

この Gate は、CFZP finite arithmetic source が full CS38 source ledger の一成分として actual TopZetaMismatchScalar まで運ばれたことを示す。

ただし、これは

```text
CFZP Euler channel alone = TopZetaMismatchScalar
```

という theorem ではない。

completed / gamma channels を含む full projected density を通じた equality である。

---

# 10. Quadratic audit は別 observable のまま保持する

CFZP-004 の

```lean
cfzpAggregateCarrierWeightedMirrorGapUpTo
```

は非負の mode-wise quadratic ledger である。

今回の Mellin density は

```text
Im(weight * linear source)
```

であり signed scalar observable である。

次は禁止。

```text
cfzpFiniteMellinSymmetricEulerDensity
  = cfzpAggregateCarrierWeightedMirrorGapUpTo
```

または

```text
normSq (Σ modeDifference)
  = Σ normSq(modeDifference)
```

という一般には偽の分配。

Mellin multiplication後の imaginary part に対し nonnegativity を主張しない。

今回の目的は quadratic Gap の sign transfer ではなく、linear source の exact transport である。

---

# 11. Optional audit — per-mode Mellin quadraticization

もし短く自然に閉じるなら、mode-wise に限って

```text
normSq(weight * modeDifference)
  = normSq(weight) * normSq(modeDifference)
```

を使い、CFZP-004 carrier-weighted Gap との関係を補助 theorem として追加してよい。

ただし finite sum 全体へ normSq を分配しない。

この optional theorem は CFZP-006 以降の Big / Body / Gap source projection audit 用の準備であり、今回の必須 Gate ではない。

---

# 12. Firewall

今回の module で禁止すること。

```text
- criticalMirror s と 1 - s を同一視しない
- same-height common cycle を functional reflection に流用しない
- mode-dependent carrier を finite sum の外へ出さない
- normSq を finite sum に分配しない
- quadratic Gap と signed Mellin scalar density を同一視しない
- Mellin density の非負性を根拠なく主張しない
- Euler channel 単独を TopZetaMismatchScalar と同一視しない
- completed / gamma channel を捨てない
- RectangleBackground - TopZetaMismatchScalar を Gap と呼ばない
- rectangle completion Gap の同定へ進まない
- infinite Euler product を導入しない
- Complex.arg / phase unwrapping を導入しない
- 新しい global Complex.log branch を導入しない
- RH 結論へ進まない
- sorry / admit / axiom を残さない
```

CFZP-006 には進まない。

---

# 13. Public export

新規 module が local Green になった後にのみ

```text
DkMath/RH.lean
```

へ import を追加する。

推奨位置は CFZP-004 の直後。

---

# 14. Build / audit

最低限:

```bash
cd lean/dk_math
lake build DkMath.RH.CFBRC.CosmicFormulaZetaMellinSourceProjection
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module について確認:

```text
sorry なし
admit なし
axiom なし
```

既存 repository 由来の warning は今回の変更と分離して報告する。

---

# 15. Green 判定条件

CFZP-005 を Green とする最低条件は次。

```text
A. functional-reflection mode difference が CFZP-001 factorization から exact 展開される
B. canonical finite q-sum が canonical PHZ difference と一致する
C. canonical finite source が CS37 FiniteSymmetricEulerRate と一致する
D. actual top Mellin weight 後の CFZP Euler density が CS38 SymmetricEulerMirrorDensity と一致する
E. full ResidualMirrorScalarDensity が completed + gamma + CFZP Euler density と pointwise exact に一致する
F. TopZetaMismatchScalar が CFZP projected full density の oriented half-integralとして exact に書ける
G. same-height / functional-reflection、linear / quadratic、Euler / full source の区別が firewall 上保存される
H. full build/test Green
```

---

# 16. Green 後の次 frontier

CFZP-005 が Green なら、次は CFZP-006。

その段階で初めて

```text
finite cosmic Big / Body / Gap
  ↓ projection
source-side Big / Body / Gap
```

を同じ projection map / observable family 上で監査する。

特に既存 rectangle ledger と比較し、

```text
RectangleBackground - TopZetaMismatchScalar
```

が本当に source-derived completion Gap なのかを調べる。

CFZP-005 ではまだその同定を行わない。
