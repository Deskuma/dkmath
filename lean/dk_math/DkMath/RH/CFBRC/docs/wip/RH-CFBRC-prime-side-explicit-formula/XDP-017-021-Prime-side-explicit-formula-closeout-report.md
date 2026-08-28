# RH-CFBRC Prime-side Explicit Formula Transport — XDP-017〜021 Closeout Report

作成日: 2026-08-13

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-side-explicit-formula-260813-v0
workdir: lean/dk_math
scope: XDP-017 〜 XDP-021
status: representation block complete / merge-ready
```

本レポートは、fixed finite Xi zero window から出発し、right-edge zeta transport、Pascal / von Mangoldt arithmetic cutoff、Mellin quadratic realization、ordered limit、fixed-Xi second-moment defect representation までを Lean 4 上で接続した XDP-017〜021 の作業を総括する。

このブロックの目的は RH を直接証明することではなく、既存の fixed-Xi second-moment defect を、有限 Pascal / von Mangoldt arithmetic surface の ordered endpoint として表現できるところまで橋を建設することであった。

最終的に得られたものは、概念的に次の chain である。

```text
finite Xi zero moment / second contour
        ↓ finite rectangle explicit formula
right-edge decomposed integral + top-horizontal correction
        ↓ ordinary-zeta component
Pascal / von Mangoldt finite cutoff integral
        ↓ Mellin second-difference specialization
quadratic-Mellin arithmetic approximant
        ↓ X → ∞ at fixed ε > 0
quadratic-Mellin Xi zero moment
        ↓ ε → 0+
fixed Xi second contour
        ↓ fixed radial observableとの差
fixed Xi second-moment defect
```

この chain は極限順序を明示的に保持する。`X → ∞` と `ε → 0+` の交換、joint/product-filter limit、`T → ∞` は導入していない。

---

## 2. 開始時点

XDP-016 までに、fixed finite residue window `W` に対して finite rectangle residue assembly が Green となっていた。

主要 endpoint は、generic centered even entire weight `h` に対する finite explicit-formula skeleton である。

```text
-(2πi) × weighted zero moment
  = 2 × right-edge decomposed integral
    + 2 × top-horizontal contribution
```

ここで top-horizontal contribution は finite height の補正として保持され、消去していない。

一方 prime-side には、`Re(s) > 1` で既に次の pointwise chain が存在していた。

```text
Pascal prime-power shadow
→ von Mangoldt partial sum
→ von Mangoldt L-series
→ -ζ'(s) / ζ(s)
```

XDP-017〜021 は、この pointwise arithmetic surface を finite interval integral、Mellin quadratic observable、最終 defect まで昇格させる作業であった。

---

# 3. XDP-017 — Finite right-edge prime cutoff integral transport

実装 module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeRightEdgeTransport
```

## 3.1 目的

既存の pointwise convergence

```text
pascalPrimePowerPHZFiniteUpTo X s
→ pascalXiOrdinaryZetaNegLogDeriv s
```

を、固定 `σ > 1`、有限 `[-T,T]` 上の weighted interval integral convergence へ持ち上げることを目的とした。

## 3.2 荷重点

right edge `s = σ + it` 上で、von Mangoldt L-series term の norm を real point `σ` へ比較し、`X` と `t` に依存しない absolute majorant を構成した。

主に利用した既存 API は次である。

```lean
LSeries.norm_term_le_of_re_le_re
LSeriesSummable_vonMangoldt
```

この majorant により interval dominated convergence を適用し、有限 right edge 上で prime cutoff integral の `X → ∞` を Green にした。

## 3.3 到達点

主要 surface:

```lean
tendsto_pascalPrimePowerRightEdgeCutoffIntegral
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
tendsto_pascalPrimePowerRightEdgeCutoffIntegral_of_residueTransportWindow
```

有限 `X` では von Mangoldt finite sum と interval integral の交換まで行い、prime arithmetic kernel を actual theorem として露出した。

判定:

```text
Strong Green through Gate G
```

archimedean / elementary 分解は XDP-018 へ分離した。

---

# 4. XDP-018 — Finite right-edge decomposition and arithmetic explicit-formula assembly

実装 module:

```text
DkMath.RH.CFBRC.PascalCenteredXiFiniteArithmeticExplicitFormula
```

## 4.1 目的

XDP-016 の finite spectral skeleton と XDP-017 の prime cutoff integral transport を一つの finite arithmetic explicit formula に assembly する。

## 4.2 right-edge decomposition

right-edge decomposed negative logarithmic derivativeを次の三部分へ分離した。

```text
ordinary-zeta
archimedean
 elementary
```

Gamma 項の独立 continuity を新たに仮定せず、既存 fixed-Xi right-edge regularity と ordinary-zeta integrability の差から combined non-prime integrability を得た。

その後 elementary term を直接 continuous / interval-integrable として閉じ、archimedean term を subtraction で得た。

この route により、`deriv Gammaℝ` の continuity を暗黙に仮定することを避けた。

## 4.3 finite arithmetic explicit formula

principal finite identity:

```text
-(2πi) × finite Xi weighted zero moment
  = 2 × zeta right-edge integral
    + 2 × archimedean correction
    + 2 × elementary correction
    + 2 × top-horizontal correction
```

さらに zeta right-edge integral を XDP-017 の Pascal / von Mangoldt cutoff で近似し、finite arithmetic approximant を定義した。

主要 surface:

```lean
pascalCenteredXiFiniteExplicitFormula_eq_zeta_archimedean_elementary_top
pascalCenteredXiFiniteArithmeticApproximant
tendsto_pascalCenteredXiFiniteArithmeticExplicitFormula
pascalCenteredXiFiniteArithmeticApproximant_eq_vonMangoldt_sum
```

判定:

```text
Ideal Green through Gate I
```

この段階で fixed finite spectral window に対する prime-cutoff arithmetic approximation theorem が完成した。

---

# 5. XDP-019 — Fixed Mellin second-difference arithmetic specialization

実装 module:

```text
DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
```

## 5.1 目的

XDP-018 の generic weight `h` を canonical compact Mellin box familyへ specialize する。

canonical weight:

```lean
centeredMellinSecondDifferenceWeight
  (centeredMellinBoxApprox ε) τ
```

固定条件は次である。

```text
ε > 0
τ : ℝ fixed
finite residue window W fixed
```

## 5.2 admissibility

既存 Mellin API により、box support / continuity / global differentiability / centered evenness を新しい provider assumption なしで供給した。

主要 bridge:

```lean
pascalCenteredXiMellinSecondDifferenceWeight_differentiable
pascalCenteredXiMellinSecondDifferenceWeight_even
```

## 5.3 `τ = 0` patch

現行 `centeredMellinSecondDifferenceWeight` は `τ = 0` を zero function へ totalizeしていない。

定義上、`τ = 0` では exact に

```text
z² × centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z
```

を返す。

したがって all-`τ` arithmetic Tendsto theorem と、`τ ≠ 0` exponential kernel surface、`τ = 0` quadratic-Mellin surfaceを分離して公開した。

主要 surface:

```lean
pascalCenteredXiMellinFiniteExplicitFormula
tendsto_pascalCenteredXiMellinFiniteArithmeticExplicitFormula
pascalCenteredXiMellinFiniteArithmeticApproximant_eq_vonMangoldt_sum
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
pascalCenteredXiMellinSecondDifferenceWeight_tau_zero_eq_quadraticWeight
```

判定:

```text
Ideal Green through Gate H
Gate I: limit ledger only
```

`τ → 0`、`ε → 0+` はこの phase では実施しなかった。

---

# 6. XDP-020 — Tau-zero quadratic arithmetic endpoint / epsilon iterated closure

実装 module:

```text
DkMath.RH.CFBRC.PascalCenteredXiMellinQuadraticArithmeticLimit
```

## 6.1 重要な設計判断

`τ = 0` が definitionally patched quadratic weight であるため、RH 本線に必要な quadratic observable を得るために `τ → 0` と integral の交換を行う必要はない。

そこで XDP-019 を exact に `τ := 0` へ specialize した。

## 6.2 fixed-ε arithmetic endpoint

各 fixed `ε > 0` に対して arithmetic approximant を先に `X → ∞` へ送った。

```text
finite arithmetic approximant
  ↓ X → ∞
-(2πi) × quadratic-Mellin Xi zero moment
```

## 6.3 epsilon zero-side closure

既存 XDP-007 theorem

```lean
tendsto_pascalCenteredXiZeroDiskMellinBoxQuadraticMoment_secondMoment
```

を再利用した。

zero-side は finite `Finset` sum であるため、各 zero に対する pointwise convergence

```text
z² Hε(z) → z²
```

だけで

```text
quadratic-Mellin finite zero moment
→ centered Xi second moment
```

が成立する。zero disk 上の uniform estimate は不要である。

## 6.4 ordered iterated limit

最終 endpoint:

```text
fixed ε > 0
A(ε,X) → E(ε) as X → ∞

E(ε) → fixed second Xi outer-contour mass as ε → 0+
```

この順序を theorem type 自体に保持した。

主要 surface:

```lean
pascalCenteredXiMellinQuadraticZeroMoment
pascalCenteredXiMellinQuadraticArithmeticApproximant
tendsto_pascalCenteredXiMellinQuadraticArithmeticApproximant
pascalCenteredXiMellinQuadraticArithmeticApproximant_eq_vonMangoldt_sum
tendsto_pascalCenteredXiMellinQuadraticZeroMoment_epsilon
pascalCenteredXiMellinQuadraticArithmeticEndpoint
tendsto_pascalCenteredXiMellinQuadraticArithmeticEndpoint_secondContour
pascalCenteredXiMellinQuadraticIteratedLimitCertificate
```

判定:

```text
Ideal Green through Gate H
```

意味する極限は厳密に ordered limit であり、`X ↔ ε` exchange や joint limit ではない。

---

# 7. XDP-021 — Ordered arithmetic fixed-Xi defect representation

実装 module:

```text
DkMath.RH.CFBRC.PascalCenteredXiArithmeticDefectRepresentation
```

## 7.1 目的

XDP-020 の unnormalized arithmetic second-contour endpoint を、既存 fixed-Xi defect と同じ normalization へ移し、fixed radial observable と組み合わせて defect 自体を arithmetic endpoint として表現する。

fixed holomorphic contour convention:

```lean
pascalCenteredXiFixedHolomorphicSecondContourFunctional R :=
  (2 * Real.pi * Complex.I)⁻¹ *
    pascalCenteredXiSecondOuterContourMass R
```

## 7.2 normalization sign

XDP-020 endpoint は

```text
-(2πi) × Mε
```

であるため、normalization 後は

```text
(2πi)⁻¹ × (-(2πi) × Mε)
→ -Mε
```

となる。

この符号は theorem

```lean
pascalCenteredXiMellinQuadraticNormalizedArithmeticEndpoint_eq
```

で explicit に固定した。

## 7.3 arithmetic defect

finite arithmetic defect approximant を

```text
fixed radial second moment
  minus
real part of normalized arithmetic holomorphic approximant
```

として定義した。

概念的には

```text
D(ε,X,W)
  := Qradial(W.R) - Re(Hnormalized(ε,X,W))
```

である。

各 fixed `ε > 0` で

```text
D(ε,X,W) → Dendpoint(ε,W) as X → ∞
```

さらに

```text
Dendpoint(ε,W)
→ pascalCenteredXiFixedSecondMomentDefectFunctional W.R
  as ε → 0+
```

を証明した。

## 7.4 principal endpoint

主要 certificate:

```lean
pascalCenteredXiMellinQuadraticArithmeticDefectIteratedLimitCertificate
```

意味は厳密に

```text
lim ε→0+ (lim X→∞ D(ε,X,W))
  = fixed Xi second-moment defect
```

である。

この certificate は inner `X → ∞` theorem family と outer `ε → 0+` theorem の conjunction であり、二変数 Tendsto を主張しない。

## 7.5 finite arithmetic surface

有限 `X` の段階で defect を actual von Mangoldt surface として露出した。

主要 theorem:

```lean
pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_vonMangoldt_surface
```

概念的には

```text
fixed radial observable
  - Re[
      (2πi)⁻¹ × (
        finite von Mangoldt weighted sum
        + archimedean correction
        + elementary correction
        + top-horizontal correction
      )
    ]
```

である。

さらに radial side は既存 CF2D `q2` mass へ rewrite できる。

```lean
pascalCenteredXiMellinQuadraticArithmeticDefectApproximant_eq_cf2dRadial_sub_normalized
```

判定:

```text
Ideal Green through Gate I
```

---

# 8. 最終 Green chain

XDP-017〜021 を通して、Lean 内に次の representation chain が構築された。

```text
finite Xi zeros
   │
   ▼
fixed Xi weighted zero moment
   │
   ▼
finite rectangle residue / explicit formula
   │
   ├─ right-edge ordinary-zeta
   ├─ archimedean correction
   ├─ elementary correction
   └─ finite top-horizontal correction
   │
   ▼
Pascal / von Mangoldt finite cutoff integral
   │
   ▼
canonical Mellin second-difference specialization
   │
   ▼
τ := 0 exact quadratic-Mellin specialization
   │
   ▼
X → ∞ at fixed ε > 0
   │
   ▼
quadratic-Mellin finite Xi zero moment
   │
   ▼
ε → 0+
   │
   ▼
fixed Xi second contour
   │
   ▼
normalize by (2πi)⁻¹
   │
   ▼
subtract Re from fixed radial observable
   │
   ▼
fixed Xi second-moment defect
```

従って fixed safe residue window `W` に対し、既存 RH frontier defect は prime-side finite arithmetic approximants の ordered endpoint として表現できる。

---

# 9. defect frontier との関係

既存 theorem により boundary-safe radius では

```text
fixed Xi defect
  = 2 × finite horizontal energy
```

である。

従って既に zero-side から

```text
0 ≤ fixed Xi defect
```

が Green である。

また全 boundary-safe radiusで defect が vanish する条件は formal Riemann Hypothesis と同値である。

しかし XDP-017〜021 はこの nonnegativity や RH equivalence を prime-side から証明し直していない。

今回新しく得られたのは、同じ defect が

```text
ordered Pascal / von Mangoldt arithmetic endpoint
```

としても表現できるという bridge である。

これにより representation construction と sign problem を明確に分離できた。

---

# 10. 明示的に未解決の数学的 obligation

以下は本 block の未整備ではなく、次研究 phase の数学的課題である。

```text
finite arithmetic defect approximant の符号
prime-side からの fixed defect ≤ 0
fixed defect vanishing
independent sign mechanism
X ↔ ε limit exchange
joint / product-filter limit
uniform-in-ε prime cutoff convergence
ε → 0+ を right-edge integral 内へ入れること
ε → 0+ を Gamma / elementary correction 内へ入れること
ε → 0+ を top-horizontal correction 内へ入れること
T → ∞
horizontal contribution の消去
R → ∞
critical-line concentration
Riemann Hypothesis
```

特に最重要 blocker は

```text
independent prime-side sign mechanism
```

である。

既存 zero-side theorem により defect は非負であるため、もし RH-equivalent assumption を使わず arithmetic surface から

```text
fixed Xi defect ≤ 0
```

を導ければ、両側を合わせて defect vanishing が得られる。

しかし、その符号 theorem は現時点では存在しない。

---

# 11. 設計上の重要な安全策

この block では次を一貫して維持した。

1. finite height `T` を保持し、top-horizontal correction を消去しない。
2. fixed same-zero-set window のまま `T → ∞` を行わない。
3. `τ = 0` の quadratic patch を exact specialization として利用し、不必要な `τ → 0` integral exchange を避ける。
4. `X → ∞` と `ε → 0+` の順序を theorem type に保持する。
5. finite zero-side `ε → 0+` は finite `Finset` sum theoremだけで閉じ、right-edge integral の domination と混同しない。
6. Gamma correction の integrability を未証明 continuity assumption で処理しない。
7. `Complex.arg`、偏角、三角関数展開へ崩さず `Complex.cpow` surface を保持する。
8. defect representation と defect sign theorem を明確に分離する。
9. RH-equivalent defect vanishing assumption を provider として再利用しない。

---

# 12. Validation / trust boundary

各 phase result では以下を検証している。

```text
module-specific lake build
lake build DkMath.RH
./lb DkMath.RH
git diff --check
major theorem #print axioms audit
```

新規 source には以下を導入していない。

```text
sorry
admit
new axiom
native_decide
Complex.arg
```

主要 theorem の axiom audit は標準の

```text
propext
Classical.choice
Quot.sound
```

のみである。

wrapper build に残る `ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は本 branch と無関係の既存 warning として分離している。

---

# 13. Merge readiness

`develop` との差分監査時点で branch は

```text
10 commits ahead
0 commits behind
```

であった。

branch 差分は主に次で構成される。

```text
new Lean modules: 5
RH.lean public imports: 5
XDP-017〜021 implementation instructions
XDP-017〜021 result documents
```

既存 core theorem の途中改変や temporary provider、未接続の experimental definition は確認されていない。

従って本 representation block は `develop` へ merge して close してよい状態と判断する。

---

# 14. 次研究 phase

次 phase は representation の延長ではなく、**Prime-side Sign Mechanism Audit** とするのが自然である。

最初の課題は finite arithmetic defect surface

```text
CF2D radial mass
  - Re[
      normalized finite von Mangoldt term
      + normalized archimedean correction
      + normalized elementary correction
      + normalized top-horizontal correction
    ]
```

の各成分について、実部・共役・critical-mirror symmetry・finite-height correction・von Mangoldt coefficient の符号構造を監査することである。

ここでは最初から `≤ 0` を仮定した provider を置かず、どの項が符号を決定し、どの項が obstruction になるかを Lean 上で分解する必要がある。

想定される次の研究問いは次である。

```text
Q1. finite von Mangoldt contribution 単体に definite sign はあるか。
Q2. archimedean / elementary correction は符号を補償するか、妨げるか。
Q3. finite top-horizontal correction は sign theorem に不可欠か。
Q4. CF2D radial mass と prime weighted kernel の間に independent inequality はあるか。
Q5. fixed ε / finite X で eventual sign を得られるか。
Q6. endpoint sign を ordered limitだけで輸送できる十分条件は何か。
```

この audit により、独立 sign mechanism が存在するか、あるいは現在の arithmetic representation が sign closure には不足しているかを判定する。

---

# 15. 結論

XDP-017〜021 により、fixed finite Xi spectral observable から Pascal / von Mangoldt arithmetic surfaceへの橋は defect level まで完成した。

得られた最終 representation は、概念的に

```text
fixed Xi defect
  = ordered endpoint of finite Pascal / von Mangoldt defect approximants
```

である。

この結果は RH の証明ではない。また fixed defect の反対向き符号もまだ得ていない。

一方で、これまで混在していた

```text
residue / contour representation
prime arithmetic transport
Mellin quadratic realization
fixed second moment
fixed defect
```

が一つの Lean-verified chain として接続されたため、次に解くべき問題は明確になった。

representation の建設は本 block で close する。

次 frontier は、RH-equivalent assumption に依存しない **independent prime-side sign mechanism** の有無を判定することである。
