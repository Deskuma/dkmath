# CFZP-0011 — CFZP-006G full signed Gram zero-width limit recovery 実装指示書

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
60f88ba5d2ab075bf8c118a43d3a75603ebbe01d
Add: CFZP-0010: CFZP-006F full-support signed Mellin Gram bridge
```

CFZP-006F 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedMellinGramBridgeAudit
```

006F は canonical support 全体を一つの finite signed spectral family へ flatten し、exact に

```text
FullSignedGramEnergy(ε,X,s)
  = (2ε)^(-1) * ∫_{-ε}^{ε}
      normSq(Source_X(s+τ)) dτ
```

を閉じた。

さらに zero shift では

```text
FullSignedFeatureSum(X,s,0) = Source_X(s)
```

および

```text
normSq(FullSignedFeatureSum(X,s,0))
  = TotalSourceMass_X(s)
```

を持つ。

今回の CFZP-006G では、centered Mellin approximate identity を使って **box width `ε → 0⁺` で full Gram energy が fixed-point source mass に収束すること**を閉じる。

---

# 1. 今回の数学的核心

006F の full Gram energy は一般 fixed `ε > 0` では中心一点の source mass ではなく horizontal-box average である。

今回初めて

```text
FullSignedGramEnergy(ε,X,s)
  -- ε → 0⁺ -->
TotalSourceMass_X(s)
```

を limit theorem として証明する。

さらに 006D の exact theorem

```text
FullPairSum_X(s) = TotalSourceMass_X(s)
```

を使えば

```text
FullSignedGramEnergy(ε,X,s)
  -- ε → 0⁺ -->
FullPairSum_X(s)
```

となる。

これにより

```text
signed spectral Gram indices
  ↓ zero-width limit
prime-power ordered pair indices
```

が同じ fixed-point quadratic observable 上で合流する。

重要なのは、これは `CompletionRemainder` との bridge ではないこと。

---

# 2. 実装を二層に分ける

## 2.1 一般 Analysis 層

推奨新規 module:

```text
lean/dk_math/DkMath/Analysis/MellinQuadraticGramLimit.lean
```

module:

```text
DkMath.Analysis.MellinQuadraticGramLimit
```

推奨 import:

```lean
import DkMath.Analysis.MellinQuadraticGramKernel
import Mathlib.Tactic
```

この module に RH / CFBRC / zeta 固有定義を import しない。

## 2.2 RH-CFBRC bridge 層

推奨新規 module:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaFullSignedGramLimitRecoveryAudit.lean
```

module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedGramLimitRecoveryAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedMellinGramBridgeAudit
import DkMath.Analysis.MellinQuadraticGramLimit
import Mathlib.Tactic
```

`DkMath/RH.lean` に public import を追加する。

`DkMath/Analysis.lean` への public import は必須ではない。既存方針に合わせて判断してよい。

---

# 3. Gate A — generic Mellin multiplier limit wrapper

既存

```lean
tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
```

を `mellinQuadraticBoxMultiplier` 名義へ bridge する。

推奨 theorem shape:

```lean
theorem tendsto_mellinQuadraticBoxMultiplier_one
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxMultiplier ε z)
      (𝓝[>] 0) (𝓝 1)
```

これは定義 unfold / exact reuse だけでよい。

新しい積分極限を再証明しない。

---

# 4. Gate B — generic Gram-kernel zero-width limit

任意 `z w : ℂ` に対して

```text
GramKernel_ε(z,w)
  = z * conj(w) * Multiplier_ε(z + conj(w))
```

なので Gate A から

```text
GramKernel_ε(z,w)
  -- ε → 0⁺ -->
z * conj(w)
```

を証明する。

推奨 theorem:

```lean
theorem tendsto_mellinQuadraticBoxGramKernel_zeroWidth
    (z w : ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxGramKernel ε z w)
      (𝓝[>] 0)
      (𝓝 (z * starRingEnd ℂ w))
```

証明は constant × Gate A の `Tendsto.mul` 等で閉じる。

---

# 5. Gate C — generic finite Gram quadratic-form limit

`n`、`z : Fin n → ℂ`、`c : Fin n → ℂ` を固定する。

既存 quadratic form は有限 double sum:

```text
Σ_i Σ_j
  c_i * conj(c_j) * GramKernel_ε(z_i,z_j)
```

である。

Gate B を有限和へ lift して

```text
QuadraticForm_ε(z,c)
  -- ε → 0⁺ -->
Σ_i Σ_j
  c_i * conj(c_j) * z_i * conj(z_j)
```

を閉じる。

その target は exact に

```text
normSq(Σ_j c_j * z_j)
```

である。

推奨 final theorem shape:

```lean
theorem tendsto_mellinQuadraticBoxGramQuadraticForm_zeroWidth
    {n : ℕ} (z : Fin n → ℂ) (c : Fin n → ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxGramQuadraticForm ε z c)
      (𝓝[>] 0)
      (𝓝 ((Complex.normSq (∑ j, c j * z j) : ℝ) : ℂ))
```

cast の exact syntax は Lean に合わせてよい。

### target identification の推奨方法

既存

```lean
mellinQuadraticBoxGram_feature_normSq_eq_double_sum z c 0
```

を `exp 0 = 1` で simplify して使うのが安全。

直接巨大 ring 証明にしなくてよい。

### finite sum Tendsto

`Finset.tendsto_sum`、`Filter.Tendsto.sum`、または Mathlib の現行 API に合わせる。

---

# 6. Gate D — generic Gram energy limit

既存 theorem

```lean
mellinQuadraticBoxGramQuadraticForm_eq_energy
```

は `0 < ε` の下で

```text
QuadraticForm_ε = (GramEnergy_ε : ℂ)
```

を与える。

positive epsilon filter `𝓝[>] 0` では eventual に `0 < ε` なので、Gate C と `Filter.Eventually` / `Tendsto.congr'` を使って energy limit を得る。

最終的には real-valued theorem を first-class surface とする。

推奨:

```lean
theorem tendsto_mellinQuadraticBoxGramEnergy_zeroWidth
    {n : ℕ} (z : Fin n → ℂ) (c : Fin n → ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxGramEnergy ε z c)
      (𝓝[>] 0)
      (𝓝 (Complex.normSq (∑ j, c j * z j)))
```

必要なら先に complex-cast version を証明し、`Complex.re` の continuity で real version を得てよい。

### 注意

`ε = 0` に Gram energy を評価して target を作らない。

今回の theorem は **one-sided limit** であり、`mellinQuadraticBoxGramEnergy 0 ...` の definitional behavior には依存しない。

---

# 7. Gate E — CFZP zero-shift coefficient-node sum

006F の Fin family を使い、次を明示 theorem にする。

```text
Σ j,
  CoefficientFin_X,s(j) * NodeFin_X(j)

= cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s
```

推奨 theorem name:

```lean
cfzpCanonicalSignedLogCoefficientNodeSum_eq_source
```

これは既存

```lean
cfzpCanonicalSignedLogFinFeatureSum_zeroShift
```

を `exp 0 = 1` で simplify して得る。

新しい source decomposition を作らない。

---

# 8. Gate F — full signed Gram energy → TotalSourceMass

Gate D を 006F の Fin-indexed node / coefficient familyへ instantiate する。

load-bearing theorem:

```lean
theorem tendsto_cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_totalSourceMass
    (X : ℕ) (s : ℂ) :
    Tendsto
      (fun ε : ℝ =>
        cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s)
      (𝓝[>] 0)
      (𝓝 (cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s))
```

証明は Gate E と既存 `TotalSourceMass` 定義を exact に使う。

これが今回の中心 theorem である。

同様に quadratic-form complex versionも安価なら閉じる:

```text
FullSignedGramQuadraticForm(ε,X,s)
  -- ε → 0⁺ -->
(TotalSourceMass_X(s) : ℂ)
```

---

# 9. Gate G — 006D FullPairSum への exact limit target rewrite

006D の既存 theorem

```lean
cfzpCanonicalFunctionalReflectionFullPairSumUpTo_eq_totalSourceMass
```

を使って、Gate F を次の target でも公開する。

```text
FullSignedGramEnergy(ε,X,s)
  -- ε → 0⁺ -->
cfzpCanonicalFunctionalReflectionFullPairSumUpTo X s
```

推奨 theorem:

```lean
tendsto_cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_fullPairSum
```

さらに安価なら 006D decomposition を使って

```text
limit target
  = DiagonalPairSum_X(s) + OffDiagonalPairSum_X(s)
```

または

```text
limit target
  = SquaredWeightDiagonal_X(s) + CrossModeInterference_X(s)
```

という rewrite corollary を置いてよい。

ここでは off-diagonal の符号は主張しない。

---

# 10. 今回の意味

006D では fixed point で

```text
TotalSourceMass
  = diagonal + cross-mode interference
```

を得た。

006F では positive finite box width で

```text
FullSignedGramEnergy ≥ 0
```

を得た。

006G で両者を

```text
FullSignedGramEnergy(ε)
  -- ε → 0⁺ -->
TotalSourceMass
  = FullPairSum
```

として exact に繋ぐ。

これは Mellin Gram positivity の source-derived index bridge を閉じるが、**rectangle/source completion gap の positivity を閉じるものではない**。

---

# 11. 今回閉じてはいけないもの

CFZP-006G では以下を禁止する。

- `CompletionRemainder = FullSignedGramEnergy`
- `CompletionRemainder = TotalSourceMass`
- `RectangleBackground = FullSignedGramEnergy`
- `TopZetaMismatchScalar = FullSignedGramEnergy`
- `cfzpAggregateCarrierWeightedMirrorGapUpTo = TotalSourceMass`
- linear-weight quadratic ledger と squared-weight diagonal の同一視
- off-diagonal / cross-mode interference の非負性
- source remainder の非負性
- `SourceBig / SourceBody / SourceGap` の premature naming
- `X → ∞` limit
- infinite Euler product
- RH / zeta zero conclusion
- `Complex.arg`
- 新しい global `Complex.log` branch
- `sorry` / `admit` / `axiom`

また、既存 generic Gram positivity から `CompletionRemainder ≥ 0` を導かない。

---

# 12. 実装上の firewall

一般 Analysis module は

```text
DkMath.Analysis.MellinQuadraticGramKernel
DkMath.Analysis.MellinMultiplicativeApproxIdentity
```

の依存だけで閉じる。

RH / zeta / CFBRC を一般 Analysis 層へ逆 import しない。

CFZP module は既存 006F surface と一般 limit theoremを組み合わせるだけにする。

---

# 13. 成功条件

最低限、次が Green なら CFZP-006G 完了とする。

```text
1. generic multiplier ε→0⁺ limit wrapper
2. generic Gram kernel ε→0⁺ limit
3. generic finite Gram quadratic-form ε→0⁺ limit
4. generic real Gram energy ε→0⁺ limit
5. CFZP coefficient-node sum = fixed source
6. FullSignedGramEnergy ε→0⁺ TotalSourceMass
7. FullSignedGramEnergy ε→0⁺ 006D FullPairSum
8. general Analysis layer に RH 固有依存なし
9. DkMath.RH public import
10. target modules build Green
11. lake build DkMath.RH Green
12. nested ./lean-build.sh Green
13. nested ./lean-test.sh Green
14. git diff --check Green
15. 新規 module に sorry / admit / axiom なし
```

---

# 14. 次 Gate への判断材料

006G が Green になったら、次は **CFZP-006H source-derived Mellin quadraticization alignment audit** を検討する。

比較対象は既存

```text
PascalCenteredXiPrimeSideQuadraticizationAudit
```

の

```text
pascalCenteredXiPrimeSideQuadraticizationBoxFeature
pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature
```

等である。

そこで初めて

```text
CFZP signed spectral Gram family
  ↔ existing source-derived quadraticization box feature
```

が exact に同じ object か、単に類似構造かを監査する。

006H が閉じるまでは、Gram positivity を rectangle completion remainder へ輸送しないこと。
