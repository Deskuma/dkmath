# BodyGapMassBridge 実装ロードマップ

## 目的

`Big = Body + Gap` を、宇宙式・質量分解・確率的質量・無限降下の共通語彙として固定する。

現時点で重要なのは、大定理を直接証明することではない。まず次の形を、Lean 上で再利用できる中間表現として置く。

```text
Big = Boundary + Tail
Tail = GapAxis * Kernel
```

重み付き二項展開では、すでに次が得られている。

```text
(x + u)^d = u^d + x * GTail d 1 x u
(x + u)^d - u^d = x * GTail d 1 x u
```

これは単なる二項定理の展開ではなく、「全体から境界を外すと、差分軸と核に分かれる」という保存分解である。

この分解を `DkMath.CosmicFormula.Mass.*` と接続し、ABC 側の確率的質量、FLT/Kummer 側の normal-form descent、Zsigmondy/p-adic 側の GN/GTail 構造へ橋を架ける。

## 現状調査

### 既存の宇宙式分解

`DkMath.CosmicFormula.CoreBeamGap` には、すでに次の層がある。

```text
Big d x u
BodyN d x u
Gap d u
Core d x
Beam d x u
```

主要補題:

```lean
big_eq_body_add_gap
body_eq_core_add_beam
big_eq_core_beam_gap
```

つまり、宇宙式側の

```text
Big = Body + Gap
Big = Core + Beam + Gap
```

は既にある。

### 既存の質量 API

`DkMath.CosmicFormula.Mass.Core` には、次の最小構造がある。

```lean
structure MassSpace (α : Type _) where
  μ : α → ℚ
  nonneg : ∀ a, 0 ≤ μ a
```

さらに、`CosmicMassAPI` と `CosmicResidualMassAPI` があり、`Big/Body/Gap/Core/Beam/Residual` を抽象 API として束ねている。

`DkMath.CosmicFormula.Mass.Decompose` には、既存宇宙式を質量 API として読み替える補題がある。

```lean
mass_big_eq_mass_body_add_mass_gap_of_coreBeamGap
mass_body_eq_mass_core_add_mass_beam_of_coreBeamGap
mass_big_eq_mass_core_add_mass_beam_add_mass_gap_of_coreBeamGap
mass_big_eq_mass_body_add_mass_gap_of_residualNat
mass_residual_eq_mass_gap_of_residualNat
```

`DkMath.CosmicFormula.Mass.Branch` には、有限分岐の sub-conservative 質量骨格がある。

```lean
structure Branching (α : Type _) where
  children : α → Finset α

class SubConservative (M : MassSpace α) (B : Branching α) : Prop where
  outgoing_le : ∀ a, outgoingMass M B a ≤ M.μ a
```

これは確率を直接扱う前の「質量が親を超えない」という有限保存層として使える。

### 既存の確率・ABC 側

`DkMath.Kernel.SubProbability` では、正規化された capacity kernel が sub-probability provider になることが証明されている。

```lean
normalizedRealWeightProvider_subProbability
```

`DkMath.ABC.MassBridge` は、ABC 側で `supportMass = rad` を質量として読み替えている。

```lean
supportMass
abc_big_eq_body_add_gap_mass
abc_gap_mass_le_big_mass
abc_residual_eq_gap_mass
supportMass_ge_prod_of_prime_channel_family
```

したがって、ABC 側の未解決確率部分は、いきなり Janson/Suen を埋めるより、まず

```text
100% mass = good mass + bad mass
bad mass <= allowed error
support channels force supportMass growth
```

という有限質量分解へ押し込むのが自然である。

### 既存の GTail / p-adic 側

`DkMath.Lib.Cosmic.GTail` は、一般 tail kernel を持つ。

```lean
add_pow_eq_prefix_add_xpow_mul_GTail
higher_tail_eq_pow_mul_GTail
GTail_zero_eq_add_pow
GTail_one_eq_sum
```

`DkMath.NumberTheory.WeightedBinomial` には、重み付き Pascal 行と `GTail d 1` の橋がある。

```lean
weightedBinomialRowSum_eq_left_add_positiveTail
add_pow_eq_left_add_x_mul_GTail_one
add_pow_sub_left_eq_x_mul_GTail_one
x_dvd_add_pow_sub_left
```

これは FLT/Kummer/Zsigmondy 側で使う「差分は gap 軸を因子に持つ」の最小入口である。

## 基本方針

### 方針A. 既存 Mass API を壊さない

`MassSpace`、`CosmicMassAPI`、`SubConservative` はすでに薄く置かれている。

ここへ急に確率論や可測性を持ち込まない。まずは有限和、有限分岐、非負性、上界だけを扱う。

### 方針B. BodyGapSplit は「証明済み等式を包む」だけにする

新構造は、数学を作り直すものではない。既存の等式を名前付きで持ち運ぶための wrapper とする。

候補:

```lean
structure BodyGapSplit (R : Type _) [Add R] where
  big : R
  body : R
  gap : R
  split : big = body + gap
```

積核まで含める場合:

```lean
structure BodyGapKernelSplit (R : Type _) [Add R] [Mul R] where
  big : R
  boundary : R
  gapAxis : R
  kernel : R
  split : big = boundary + gapAxis * kernel
```

最初は `CommSemiring` まで要求せず、補題が必要とする型クラスだけで始める。

### 方針C. 確率は「有限質量」として読む

Janson/Suen の直接証明に入る前に、確率的対象を次の形に読み替える。

```text
totalMass = goodMass + badMass
badMass <= error
goodMass <= totalMass
```

この段階では `ENNReal` や測度論へ寄せない。既存の `ℚ` / `ℝ` の有限和 API と `SubProbability` を優先する。

### 方針D. 降下法は「normal form split」として読む

FLT/Kummer 側では、未解決の主因は単なる計算不足ではなく、normal form descent の存在核である。

したがって、次を分離する。

```text
normal part
residual gap
support separation
minimality witness
```

`BodyGapKernelSplit` は、このうち `normal part + residual gap` を薄く記録する入口になる。

## 実装フェーズ

## Phase 0. 文書化と境界固定

目的:

- この文書を実装方針として固定する。
- 既存 API の所有範囲を明記する。
- 実装時に ABC 確率、Kummer principalization、GTail 可除性が混線しないようにする。

成果物:

```text
DkMath/CosmicFormula/docs/BodyGapMassBridgeRoadmap.md
```

## Phase 1. BodyGapSplit の最小定義

候補ファイル:

```text
DkMath/CosmicFormula/Mass/BodyGapSplit.lean
```

候補定義:

```lean
structure BodyGapSplit (R : Type _) [Add R] where
  big : R
  body : R
  gap : R
  split : big = body + gap
```

候補補題:

```lean
theorem BodyGapSplit.gap_le_big_nat
theorem BodyGapSplit.body_le_big_nat
theorem BodyGapSplit.rewrite_big
```

注意:

- `Nat` の不等式補題は、`split` と非負性だけで閉じる。
- 汎用 `OrderedCancelCommMonoid` へ急がない。

## Phase 2. BodyGapKernelSplit の最小定義

候補定義:

```lean
structure BodyGapKernelSplit (R : Type _) [Add R] [Mul R] where
  big : R
  boundary : R
  gapAxis : R
  kernel : R
  split : big = boundary + gapAxis * kernel
```

候補補題:

```lean
theorem BodyGapKernelSplit.tail_eq_gap_mul_kernel
theorem BodyGapKernelSplit.gapAxis_dvd_tail_nat
theorem BodyGapKernelSplit.big_sub_boundary_eq_gap_mul_kernel_nat
```

注意:

- `Nat` の `sub` は side condition なしで扱えるが、等式の向きは `Nat.sub_eq_of_eq_add` を使う。
- `CommSemiring` 版は `sub` が必要になった時点で `CommRing` に分ける。

## Phase 3. WeightedBinomial から split を作る

候補補題:

```lean
def weightedBodyGapKernelSplit (d x u : ℕ) :
  BodyGapKernelSplit ℕ
```

中身:

```text
big      = (x + u)^d
boundary = u^d
gapAxis  = x
kernel   = GTail d 1 x u
split    = add_pow_eq_left_add_x_mul_GTail_one d x u
```

派生補題:

```lean
theorem weighted_split_tail_dvd_gapAxis
theorem weighted_split_sub_eq_tail
theorem weighted_split_supports_x_dvd_add_pow_sub_left
```

目的:

`WeightedBinomial` の個別補題を、一般 split API から呼べるようにする。

## Phase 4. CosmicMassAPI との接続

候補補題:

```lean
def coreBeamGapBodyGapSplit
def residualNatBodyGapSplit
theorem residualNat_split_gap_eq_residual
```

目的:

既存の `CosmicMassAPI` / `CosmicResidualMassAPI` を、`BodyGapSplit` で読めるようにする。

これにより、宇宙式側では

```text
Big = Body + Gap
```

質量側では

```text
total = kept + residual
```

という同じ構文を使える。

## Phase 5. SubProbability / Branching への接続

候補補題:

```lean
def subProbabilityBodyGapSplit
theorem badMass_le_totalMass
theorem goodMass_add_badMass_eq_totalMass
```

実装は保守的に進める。

最初の対象は有限集合 `S` と重み `w : α → ℚ` または `w : α → ℝ`。

```text
totalMass S = goodMass G + badMass (S \ G)
```

を証明する。

この段階では Janson/Suen 本体には入らない。

## Phase 6. ABC MassBridge への接続

目的:

ABC 側の `supportMass = rad` と、有限 channel の質量増加補題を split API へ接続する。

候補補題:

```lean
theorem supportMass_split_lower_bound_of_channels
theorem bad_channel_mass_forces_support_growth
theorem abc_quality_gap_budget_surface
```

注意:

- ここで ABC 予想本体を証明しない。
- `abc_main_axiom` の置換を急がない。
- まずは `supportMass_ge_prod_of_prime_channel_family` を split vocabulary で再輸出する。

## Phase 7. FLT/Kummer normal-form descent への接続

目的:

`CyclotomicPrincipalization` や Branch A の open kernel に直接入らず、まず normal form の split を固定する。

候補構造:

```lean
structure DescentSplit where
  current : ℕ
  normal : ℕ
  residual : ℕ
  witness : ℕ
  split : current = normal + residual
```

または `BodyGapSplit` の wrapper として置く。

候補補題:

```lean
theorem branchA_reduced_form_bodyGapSplit
theorem support_separation_reads_residual
theorem minimality_blocks_nontrivial_residual
```

注意:

- Principalization core を先に増やさない。
- GTail/p-adic 境界で小補題を証明し、それを Kummer 側へ渡す。
- `support separation` だけでは矛盾に足りないことを前提に、minimality/descent data を別フィールドとして扱う。

## Phase 8. p-adic / Zsigmondy への接続

目的:

`Body = x * GTail` を、valuation と primitive divisor の入口にする。

候補補題:

```lean
theorem padicValNat_body_eq_padicValNat_gapAxis_add_kernel
theorem primitive_prime_of_body_not_gapAxis_reads_kernel
theorem zsigmondy_bodyGapKernelSplit
```

注意:

- `d` が合成数のときの二項係数可除性は慎重に扱う。
- `d = p^a` では内側二項係数がすべて `p` で割れる場合があるため、単純な composite 判定を使わない。
- まずは prime row の前向き補題を使う。

## 優先順位

### すぐ実装する

1. `BodyGapSplit`
2. `BodyGapKernelSplit`
3. `WeightedBinomial` から `BodyGapKernelSplit` を作る wrapper
4. `x ∣ tail` 型の既存補題を split API から再輸出

### 次に実装する

1. `CosmicMassAPI` との wrapper
2. 有限集合の `total = good + bad` 分解
3. `SubConservative` との薄い接続
4. `ABC.MassBridge` の supportMass 補題の split vocabulary 化

### 後で実装する

1. Janson/Suen への本格接続
2. Kummer principalization の normal-form descent core
3. p-adic valuation の一般上界
4. reverse prime/binomial 判定

## 実装時の注意

- 新しい構造は薄くする。
- `Valid`、`Compatible`、`Monotone` などの重い条件を先回りして入れない。
- 定理が要求した時点でフィールドを増やす。
- `Nat`、`Int`、`CommSemiring`、`CommRing` を無理に一つの定理にまとめない。
- `sub` を含む定理は、まず `Nat` 専用または `CommRing` 専用に分ける。
- ABC 確率側は、最初は有限質量分解に留める。
- FLT/Kummer 側は、Principalization 本体ではなく GTail/valuation 境界から入る。

## 期待される効果

この計画で得たいのは、証明の一撃ではなく、証明が通るための共通中間言語である。

```text
Big = Boundary + GapAxis * Kernel
```

が Lean の定義として固定されると、次が同じ形で扱える。

```text
二項展開:
  (x + u)^d = u^d + x * GTail d 1 x u

質量分解:
  totalMass = keptMass + residualMass

確率:
  1 = goodMass + badMass

無限降下:
  current = normalPart + residualGap

Zsigmondy / p-adic:
  Body = gapAxis * kernel
```

これにより、既存の `sorry` や `axiom` は「何が足りないか分からない穴」ではなく、

```text
どの split が未構成か
どの kernel 評価が未証明か
どの residual を潰す data が不足しているか
```

として分類できるようになる。

## 最初のチェックポイント

次の Lean 実装を第一 checkpoint とする。

```text
DkMath.CosmicFormula.Mass.BodyGapSplit
```

内容:

```lean
structure BodyGapSplit
structure BodyGapKernelSplit
def weightedBodyGapKernelSplit
theorem weightedBodyGapKernelSplit_gapAxis_dvd_tail
```

この checkpoint は、`WeightedBinomial` の既存補題を wrapper 化するだけでよい。
新しい深い数学は入れない。
