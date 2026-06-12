# History

cid: 6a2711e6-6180-83a6-a2ff-bba7cb77e2e3
cid: 6a27be44-9404-83a6-aa95-b9f407eeffe8

## DAS 関連の実装履歴

## 関連ファイル

- [dynamic_arithmetic_sequence](/python/dynamic_arithmetic_sequence/History.md) (Python to Lean)
- [DHNT DAS Note](/lean/dk_math/DkMath/DHNT/docs/DHNT_DAS_Note.md) (考察ノート)
- [Sequence](/lean/dk_math/DkMath/Sequence/docs/DHNT-DAS-reinterpretation.md) 「DHNT から DAS/Sequence への再解釈メモ」
- Lean code
  - [WeightedBinomial](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean)
    - [BinomialPrime](/lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean)
  - [DynamicArithmeticSequence](/lean/dk_math/DkMath/DHNT/DynamicArithmeticSequence.lean)
    - [Arithmetic](/lean/dk_math/DkMath/Sequence/Arithmetic.lean)
      - [Recurrence](/lean/dk_math/DkMath/Sequence/Recurrence.lean)
        - [Generator](/lean/dk_math/DkMath/Sequence/Generator.lean)
  - [CosmicFormula](/lean/dk_math/DkMath/CosmicFormula.lean)
    - [Mass](/lean/dk_math/DkMath/CosmicFormula/Mass.lean)
      - [BodyGapSplit](/lean/dk_math/DkMath/CosmicFormula/Mass/BodyGapSplit.lean)

### 2026/06/08 14:18

実装しました。第一 checkpoint は通っています。

追加・変更:

- [BodyGapSplit.lean](/lean/dk_math/DkMath/CosmicFormula/Mass/BodyGapSplit.lean)
  - `BodyGapSplit`
  - `BodyGapKernelSplit`
  - `tail`
  - `toBodyGapSplit`
  - `big_sub_boundary_eq_tail_nat`
  - `gapAxis_dvd_tail_nat`
  - `boundary_le_big_nat`
  - `tail_le_big_nat`

- [Mass.lean](/lean/dk_math/DkMath/CosmicFormula/Mass.lean)
  - `CosmicFormula.Mass` の集約モジュールを新設

- [CosmicFormula.lean](/lean/dk_math/DkMath/CosmicFormula.lean)
  - `DkMath.CosmicFormula.Mass` を公開 import

- [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean)
  - `weightedBodyGapKernelSplit`
  - `weightedBodyGapKernelSplit_tail_eq_sub`
  - `weightedBodyGapKernelSplit_gapAxis_dvd_tail`
  - `weightedBodyGapKernelSplit_gapAxis_dvd_sub`

これで

```lean
(x + u)^d = u^d + x * GTail d 1 x u
```

が `BodyGapKernelSplit` として包めるようになりました。つまり `Big = Boundary + GapAxis * Kernel` が Lean の共通 API として立ち始めています。

検証済み:

```text
lake build DkMath.CosmicFormula.Mass.BodyGapSplit
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath.CosmicFormula.Mass
lake build DkMath.CosmicFormula
lake build DkMath
git diff --check
```

今回追加・変更した Lean ファイルには `sorry/axiom/admit` なしです。

### 2026/06/08 14:42

適用実験の第1波を入れました。`Big = Boundary + GapAxis * Kernel` が、WeightedBinomial だけでなく宇宙式本体と ABC mass 側にも刺さりました。

主な追加:

- [Mass/Decompose.lean](/lean/dk_math/DkMath/CosmicFormula/Mass/Decompose.lean)
  - `coreBeamGapBodyGapSplit`
  - `coreBeamGapBodyGapKernelSplit`
  - `residualNatBodyGapSplit`
  - `residualNatBodyGapSplit_gap_eq_residual`
  - `residualIntBodyGapSplit`
  - `residualIntBodyGapSplit_gap_eq_residual`

- [ABC/MassBridge.lean](/lean/dk_math/DkMath/ABC/MassBridge.lean)
  - `abcBodyGapSplit`
  - `abc_bodyGapSplit_body_le_big`
  - `abc_bodyGapSplit_gap_le_big`
  - `abc_bodyGapSplit_gap_eq_residual`

特に重要なのはこれです。

```lean
coreBeamGapBodyGapKernelSplit
```

宇宙式本体を

```text
Big = Gap + x * GN
```

として `BodyGapKernelSplit` に載せました。これで `WeightedBinomial` の `GTail` 版と、`CoreBeamGap` の `GN` 版が同じ interface に乗ります。

検証済み:

```text
lake build DkMath.CosmicFormula.Mass.Decompose
lake build DkMath.ABC.MassBridge
lake build DkMath.CosmicFormula.Mass
lake build DkMath
git diff --check
```

今回対象ファイルには `sorry/axiom/admit` なしです。既存の別モジュール由来の `sorry` warning は継続しています。

### 2026/06/08 15:03

固定しました。パスカル加法成長から「素数 support が発生する段」を観測するための薄い predicate と証明を追加しています。

[BinomialPrime.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean) に追加:

```lean
def InnerRowSupportPrime (d p : ℕ) : Prop :=
  p.Prime ∧ AllInnerChooseDivisible d p

def RowBirthPrime (d p : ℕ) : Prop :=
  InnerRowSupportPrime d p ∧ p ∣ d
```

証明済みの核:

```lean
theorem prime_innerRowSupportPrime_self
    {p : ℕ} (hp : p.Prime) :
    InnerRowSupportPrime p p

theorem prime_rowBirthPrime_self
    {p : ℕ} (hp : p.Prime) :
    RowBirthPrime p p
```

つまり、

```text
p が素数なら、Pascal 三角形の p 段は、
内側係数すべてに p という support prime を要求する
```

を Lean 上で固定しました。

さらに [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean) にも持ち上げて、

```lean
innerRowSupportPrime_allInnerWeightedTermDivisible
rowBirthPrime_allInnerWeightedTermDivisible
innerRowSupportPrime_dvd_inner_weightedBinomialTerm
rowBirthPrime_dvd_inner_weightedBinomialTerm
```

を追加しました。これで、係数列で発生した support prime が weighted term 側にもそのまま流れます。

検証済み:

```text
lake build DkMath.NumberTheory.BinomialPrime
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

今回対象ファイルに `sorry/axiom/admit` はありません。

### 2026/06/08 17:26

実装しました。`p^n` フィルターの入口として [BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean) を新設し、
[DkMath.lean](/lean/dk_math/DkMath.lean#L24) に import を追加しています。

入れた主な補題は次です。

- `prime_power_innerRowSupportPrime`
  `p^n` 段の内側係数がすべて `p` を支持することを固定。
- `prime_power_rowBirthPrime`
  `0 < n` なら `p ∣ p^n` なので `RowBirthPrime (p^n) p` へ接続。
- `padicValNat_choose_prime_pow`
  mathlib の Kummer/factorization 形を `padicValNat` 形に変換。
- `prime_power_dvd_choose_of_not_dvd_index`
  `¬ p ∣ k` なら `p^n ∣ choose (p^n) k`。ここが「p^n フィルター」の最初の精密層です。

確認済みです。

```sh
lake build DkMath.NumberTheory.BinomialPrimePower
lake build DkMath
git diff --check
```

新規ファイルに `sorry/axiom/admit` はありません。

### 2026/06/08 19:28

実装しました。`prime_power_dvd_choose_of_not_dvd_index` を特殊例にして、一般の valuation filter を追加しています。

[BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean) に追加した核はこれです。

```lean
theorem padicValNat_choose_prime_pow_add_index
theorem prime_power_pow_dvd_choose_of_padicValNat_index
```

中心形は：

```lean
r + padicValNat p k ≤ n →
p ^ r ∣ Nat.choose (p ^ n) k
```

これで `¬ p ∣ k` のときの `p^n ∣ choose (p^n) k` は `r = n` の特殊例として読めます。

さらに [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean) 側へも持ち上げました。

```lean
theorem prime_power_pow_dvd_weightedBinomialTerm_of_padicValNat_index
theorem prime_power_dvd_weightedBinomialTerm_of_not_dvd_index
```

確認済みです。

```sh
lake build DkMath.NumberTheory.BinomialPrimePower
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

対象ファイルに `sorry/axiom/admit` はありません。

### 2026/06/08 20:28

行けました。`UniformBeamHeight` と素数行の高さ定理を [BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean:1) に追加しました。

追加内容：

```lean
def UniformBeamHeight (d p h : ℕ) : Prop :=
  ∀ k, 0 < k → k < d →
    padicValNat p (Nat.choose d k) = h
```

```lean
theorem prime_uniformBeamHeight_self
    {p : ℕ} (hp : p.Prime) :
    UniformBeamHeight p p 1
```

証明は `padicValNat_choose_prime_pow` の `n = 1` 特殊化を使っています。`0 < k < p` なので `p ∤ k`、よって `padicValNat p k = 0`。したがって Beam 側は `1 - 0 = 1` です。

### 2026/06/08 22:03

実装しました。`BinomialPrimePower.lean` に、既存素数定理へ戻す橋と `p^n` 篩の filtered 版を追加しています。

追加した橋はこれです。

```lean
def FilteredBeamHeight (d p h : ℕ) (P : ℕ → Prop) : Prop
```

```lean
theorem UniformBeamHeight.allInnerChooseDivisible
theorem UniformBeamHeight.innerRowSupportPrime
```

これで

```lean
UniformBeamHeight d p h
0 < h
```

から、既存の

```lean
AllInnerChooseDivisible d p
InnerRowSupportPrime d p
```

へ戻せます。つまり、高さ観測が従来の可除性観測より強いことを Lean 上で固定しました。

さらに `p^n` 篩として：

```lean
theorem prime_power_unitFilteredBeamHeight
    {p n : ℕ} (hp : p.Prime) :
    FilteredBeamHeight (p ^ n) p n (fun k => ¬ p ∣ k)
```

を追加しました。`p ∤ k` の index 層では、Beam 係数の高さがちょうど `n` に揃う、という形です。

### 2026/06/08 22:17

実装しました。これで「`p` 行が初出生ライン」という形が Lean 上でかなり明確になりました。

追加した定理は [BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean:1) のこの2本です。

```lean
theorem below_prime_uniformBeamHeight_zero
    {d p : ℕ} (hp : p.Prime) (hdp : d < p) :
    UniformBeamHeight d p 0
```

```lean
theorem below_prime_not_dvd_inner_choose
    {d p k : ℕ} (hp : p.Prime) (hdp : d < p)
    (hk0 : 0 < k) (hkd : k < d) :
    ¬ p ∣ Nat.choose d k
```

意味としては：

```text
d < p のすべての行では、Beam 係数の p-adic 高さは 0。
つまり p は一切出てこない。
```

既存の

```lean
prime_uniformBeamHeight_self :
  p.Prime → UniformBeamHeight p p 1
```

と合わせて、

```text
d < p : p-height = 0
d = p : p-height = 1
```

が固定されました。

これで「p 境界」はかなり確固たる形です。`p` は `p` 行未満では Beam に現れず、`p` 行で初めて全 Beam に高さ 1 として現れる。

### 2026/06/09  0:14

実装で確認しました。`BeamBirthBoundary` と obstruction 側の橋を [BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean) に追加しています。

入れた定義：

```lean
def BeamBirthBoundary (p : ℕ) : Prop :=
  (∀ d, d < p → UniformBeamHeight d p 0) ∧
    UniformBeamHeight p p

```

```lean
def BeamBirthBoundaryObstruction (p : ℕ) : Prop :=
  ∃ k, 0 < k ∧ k < p ∧ padicValNat p (Nat.choose p k) ≠ 1
```

確認できた定理：

```lean
theorem prime_beamBirthBoundary
    {p : ℕ} (hp : p.Prime) :
    BeamBirthBoundary p
```

つまり、素数なら

```text
p 未満の行では p-height = 0
p 行では p-height = 1
```

が Lean 上で固定されました。

さらに分解用 API も追加しています。

```lean
theorem BeamBirthBoundary.below
theorem BeamBirthBoundary.self
theorem BeamBirthBoundary.innerRowSupportPrime
theorem not_beamBirthBoundary_of_obstruction
theorem not_obstruction_of_prime
```

逆向き `BeamBirthBoundary p → p.Prime` は、既存 API だけではまだ直接つながりませんでした。今の不足要素は明確で、「合成数 `p` なら `BeamBirthBoundaryObstruction p` が存在する」という witness 定理です。

### 2026/06/09  0:36

実装しました。`p - 1` 行を `mod p` で見ると `1, -1, 1, -1, ...` になる現象を、[BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean) に `PrimePrebirthAlternation` として固定しています。

追加した主なものは：

```lean
def PrimePrebirthAlternation (p : ℕ) : Prop :=
  ∀ k, k ≤ p - 1 →
    ((Nat.choose (p - 1) k : ZMod p) = (-1 : ZMod p) ^ k)
```

証明は、`p` 行の中間係数が `mod p` で消えることから、Pascal の関係式で `p - 1` 行の隣接係数が互いに反数になる、という形です。

```lean
theorem prime_prebirthAlternation_step
theorem prime_prebirthAlternation
```

検証済み：

```text
lake build DkMath.NumberTheory.BinomialPrimePower
git diff --check
sorry/axiom/admit なし
```

これはかなり良い「目撃情報」です。`BeamBirthBoundary` が `p` 行での誕生だとすると、`PrimePrebirthAlternation` はその直前に現れる「前駆交代相」として扱えます。

### 2026/06/09  1:11

実装実験、通りました。

追加したのは [PascalPrimeDial.lean](/lean/dk_math/DkMath/NumberTheory/PascalPrimeDial.lean) です。中核はこの3つです。

```lean
def pascalCoeffMass (n k : ℕ) : ℕ :=
  Nat.choose n k

def pascalRowMass (n : ℕ) : ℕ :=
  2 ^ n

def pascalPrimeDialHeight (p n k : ℕ) : ℕ :=
  padicValNat p (pascalCoeffMass n k)
```

既存定理との橋も固定しました。

```lean
theorem pascalCoeffMass_sum_eq_rowMass
theorem uniformPrimeDialHeight_iff_uniformBeamHeight
theorem filteredPrimeDialHeight_iff_filteredBeamHeight
theorem pascalPrimeDialHeight_prime_pow_add_index
theorem pascalPrimeDialHeight_prime_pow
theorem prime_power_unitFilteredPrimeDialHeight
```

これで「係数質量 `C(n,k)`」「行全体の質量 `2^n`」「素数ダイヤル高さ `v_p(C(n,k))`」が Lean 上でつながりました。特に Kummer 系は、

```lean
pascalPrimeDialHeight p (p ^ n) k + padicValNat p k = n
```

として読めるので、素数ダイヤルの回転数観測としてかなり強いです。

### 2026/06/09  1:30

追加しました。[PascalPrimeDial.lean](/lean/dk_math/DkMath/NumberTheory/PascalPrimeDial.lean) に、未到達の素数ダイヤルを固定する補題を2つ置いています。

```lean
theorem pascalPrimeDialHeight_eq_zero_of_row_lt
    {p n k : ℕ} (hp : p.Prime) (hnp : n < p) :
    pascalPrimeDialHeight p n k = 0
```

これは「row `n` が `p` 未満なら、`p` ダイヤル高さは 0」という観測です。

さらに、実際に存在する係数 `k ≤ n` については可除性として：

```lean
theorem prime_not_dvd_pascalCoeffMass_of_row_lt
    {p n k : ℕ} (hp : p.Prime) (hnp : n < p) (hkn : k ≤ n) :
    ¬ p ∣ pascalCoeffMass n k
```

`k ≤ n` を入れているのは重要で、`k > n` だと `Nat.choose n k = 0` になり、自然数では任意の `p` が `0` を割ってしまうためです。

### 2026/06/09  1:45

整理ドキュメントを追加しました。

新規作成:
[PascalPrimeDialProgress.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/PascalPrimeDialProgress.md)

内容は、当初ロードマップから派生した現在地の整理です。`BinomialPrime`、`BinomialPrimePower`、`WeightedBinomial`、`PascalPrimeDial` の役割、追加された `PrimePrebirthAlternation`、未到達 prime の補題、次の安全な実装候補をまとめています。

追記:
[BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md)

ロードマップ冒頭に、今回の `PascalPrimeDial` 系は本線の置き換えではなく、Pascal 行の prime support 観測層として派生したものだと明記し、新規整理文書への参照を追加しました。

検証は docs-only なので Lean build は走らせず、以下を確認しました。

```text
git diff --check
wc -L
```

どちらも問題なしです。

### 2026/06/09  4:01

AKS 入口の橋を実装しました。

追加:
[AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean)

主な定理はこの3つです。

```lean
theorem prime_inner_choose_eq_zero_zmod
theorem prime_inner_pascalCoeffMass_eq_zero_zmod
theorem prime_polynomial_X_add_C_pow_eq
```

特に AKS の核になる形を固定しました。

```lean
theorem prime_polynomial_X_add_C_pow_eq
    {p a : ℕ} (hp : p.Prime) :
    ((X : (ZMod p)[X]) + C (a : ZMod p)) ^ p =
      X ^ p + C (a : ZMod p)
```

これは `ZMod p` 上の freshman dream で、AKS の多項式合同へ進むための入口です。まだ `X^r - 1` による剰余多項式環までは入れていません。そこは次段です。

トップレベル [DkMath.lean](/lean/dk_math/DkMath.lean) にも import を追加済みです。

検証済み:

```text
lake build DkMath.NumberTheory.AKSBridge
lake build DkMath
git diff --check
```

`AKSBridge.lean` に `sorry/axiom/admit` はありません。全体ビルドでは既存ファイル由来の `sorry` 警告は出ています。

### 2026/06/09  4:38

実装しました。対象は [AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean) です。

追加した流れはこの形です。

```lean
(x + u)^d = x^d + Beam + u^d

Beam ≡ 0 [MOD m]
u^d ≡ u [MOD m]
--------------------------------
(x + u)^d ≡ x^d + u [MOD m]
```

主な追加補題:

- `weightedBinomialInnerBeamSum`
  - 両端 `u^d`, `x^d` を除いた中間 Beam
- `add_pow_eq_right_add_innerBeam_add_left`
  - 宇宙式分解 `(x + u)^d = x^d + Beam + u^d`
- `add_pow_modEq_right_add_u_of_innerBeam_modEq_zero_and_left_modEq`
  - `Beam = 0` と `u^d ≡ u` を合成する汎用 `Nat.ModEq` 補題
- `prime_dvd_weightedBinomialInnerBeamSum`
  - prime 行では Beam が `p` で割れる
- `prime_pow_modEq_self`
  - prime Frobenius/Fermat endpoint: `u^p ≡ u [MOD p]`
- `prime_add_pow_modEq_right_add_u`
  - 最終形: `(x + u)^p ≡ x^p + u [MOD p]`

検証:

- `lake build DkMath.NumberTheory.AKSBridge` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功
- `AKSBridge.lean` に `sorry/admit/axiom` なし

全体ビルドでは既存ファイル由来の `sorry` 警告は出ていますが、今回追加分にはありません。

### 2026/06/09  4:44

追加しました。場所は [AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean) です。

入れた定理名は指定どおりです。

```lean
theorem prime_innerBeam_modEq_zero
theorem prime_gap_compress_modEq
theorem prime_congruent_cosmic_formula
```

`prime_congruent_cosmic_formula` は、ちゃんと

```lean
prime_innerBeam_modEq_zero hp
prime_gap_compress_modEq hp
```

を合成して証明する形にしました。つまり「Beam = 0」「u^p compress」の2要素が見える証明構造です。

検証:

- `lake build DkMath.NumberTheory.AKSBridge` 成功
- `git diff --check` 成功
- 追加箇所に `sorry/admit/axiom` なし

### 2026/06/09  4:52

進めました。今回は [AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean) に `F_p = ZMod p` への橋を追加しています。

追加した主な補題:

```lean
theorem prime_congruent_cosmic_formula_natCast_zmod
```

Nat 側の

```lean
(x + u)^p ≡ x^p + u [MOD p]
```

を `ZMod p` 上の等式として読む橋です。

```lean
theorem prime_zmod_gap_compress
```

`F_p` 内での `u^p = u`。

```lean
theorem prime_zmod_congruent_cosmic_formula
```

`x u : ZMod p` そのものに対する

```lean
(x + u)^p = x^p + u
```

### 2026/06/09  5:14

進めました。今回は [AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean) に、AKS の `X^r = 1` 周期層を追加しています。

追加した主なもの:

```lean
theorem pow_add_period_of_pow_eq_one
noncomputable def aksCyclotomicIdeal
abbrev AKSCyclotomicQuotient
noncomputable def aksQuotientX
theorem aksQuotientX_pow_r_eq_one
theorem aksQuotientX_pow_add_r_eq_pow
```

これで次の形が固定できました。

```lean
-- 抽象形
a ^ r = 1 → a ^ (k + r) = a ^ k

-- AKS quotient 形
R[X] / (X^r - 1) では
X^r = 1
X^(k+r) = X^k
```

検証:

- `lake build DkMath.NumberTheory.AKSBridge` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功
- 追加箇所に `sorry/admit/axiom` なし

全体ビルドでは既存の unrelated `sorry` 警告は出ています。

### 2026/06/09  5:23

追加しました。場所は [AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean) です。

入れた補題:

```lean
theorem pow_add_mul_period_of_pow_eq_one
theorem pow_eq_pow_mod_of_pow_eq_one

theorem aksQuotientX_pow_add_mul_r_eq_pow
theorem aksQuotientX_pow_eq_pow_mod
```

これで次が Lean 上で固定されました。

```lean
-- 抽象形
a^r = 1 → a^(k + r*t) = a^k
a^r = 1 → a^k = a^(k % r)

-- AKS quotient 形
X^(k + r*t) = X^k
X^k = X^(k % r)
```

`X^k = X^(k % r)` は `Nat.mod_add_div` を使っているので、`r > 0` 仮定なしで通っています。`r = 0` の場合も `k % 0 = k` なので自明形になります。

検証:

- `lake build DkMath.NumberTheory.AKSBridge` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功
- 追加箇所に `sorry/admit/axiom` なし

### 2026/06/09  5:38

追加しました。対象は [AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean) です。

今回入れた層:

```lean
noncomputable def aksQuotientMap
noncomputable def aksQuotientC

theorem aksQuotientMap_X
theorem aksQuotientMap_C
theorem aksQuotientMap_X_pow
theorem aksQuotientMap_X_pow_eq_mod
```

これで、商環へ写す操作が

```lean
R[X] →+* AKSCyclotomicQuotient R r
```

として名前を持ちました。さらに、

```lean
overline{X^k} = overline{X}^k
overline{X^k} = overline{X^(k % r)}
```

が使える状態です。

検証:

- `lake build DkMath.NumberTheory.AKSBridge` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功
- 追加箇所に `sorry/admit/axiom` なし

全体ビルドでは既存の unrelated `sorry` 警告は出ています。

### 2026/06/09  6:53

説明書を追加しました。

追加ファイル:

[AKSBridge-v1.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/AKSBridge-v1.md)

内容は指定された 8 段階をベースにして、各段階の意味と対応する Lean 名を整理しています。

```text
1. Pascal prime row
2. Weighted universe split
3. Congruent cosmic formula
4. Finite-field form
5. Polynomial Frobenius
6. AKS cyclic quotient
7. Prime AKS cyclic Frobenius
8. Predicate layer
```

`Cyclotomic` と混線しないように、文中でも `AKS cyclic quotient` / `Cyclic` を明示しました。

検証:

- `git diff --check` 成功
- docs-only なので Lean build は走らせていません

`git status --short` では新規 docs ファイルが untracked です。

### 2026/06/09  7:01

状況整理を [BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md) に追記しました。

入れた内容は主に2点です。

1. 冒頭の目的を更新
   - 素数そのものだけでなく「素性」
   - primitive prime divisor へ渡せる可除性の痕跡
   - 境界由来、中間項由来、prime row だけで消える構造の切り分け

2. `Phase 4.5: AKSBridge v1 の巡回商観測` を追加
   - `DkMath.NumberTheory.AKSBridge`
   - `AKSBridge-v1.md`
   - `AKSCyclicCongruenceHolds`
   - `AKSCyclicFoldedCongruenceHolds`
   - `prime_aks_cyclic_frobenius`
   - composite failure witness や primitive prime divisor 境界への比較面、という位置づけ

検証:

- `git diff --check` 成功
- docs-only なので Lean build は走らせていません。

### 2026/06/09 15:22

進めました。`AKSBridge.lean` に v1.5 として、single shift から range predicate へ拡張する層を追加しています。

追加した主な定義:

```lean
def AKSCyclicCongruenceHoldsForRange
def AKSCyclicFoldedCongruenceHoldsForRange
def AKSCyclicCongruenceFails
def AKSCyclicFoldedCongruenceFails
def ExistsAKSCyclicFailureBelow
def ExistsAKSCyclicFoldedFailureBelow
```

追加した prime 側の定理:

```lean
theorem AKSCyclicCongruenceHoldsForRange.prime
theorem AKSCyclicFoldedCongruenceHoldsForRange.prime
theorem prime_AKSCyclicCongruenceHoldsForRange
theorem prime_AKSCyclicFoldedCongruenceHoldsForRange
theorem not_exists_AKSCyclicFailureBelow_of_prime
theorem not_exists_AKSCyclicFoldedFailureBelow_of_prime
```

これで、

```text
∀ a < bound, AKS cyclic congruence holds
```

という AKS らしい範囲検査の形が入りました。さらに prime なら failure witness は存在しない、という対岸の観測面も用意できています。

検証:

- `lake build DkMath.NumberTheory.AKSBridge` 成功
- `lake build DkMath` 成功
- `git diff --check` 成功
- `AKSBridge.lean` 内に `sorry/admit/axiom` なし

全体ビルドでは既存の unrelated `sorry` 警告は出ています。

### 2026/06/09 15:50

実装しました。

[AKSBridge.lean](/lean/dk_math/DkMath/NumberTheory/AKSBridge.lean:377) に追加した内容は主に2つです。

- `AKSBound n r` の抽象フックを追加
  - 現状は粗い placeholder として `n`
  - `AKSCyclicCongruenceHoldsUpToAKSBound`
  - `AKSCyclicFoldedCongruenceHoldsUpToAKSBound`
  - `ExistsAKSCyclicFailureBelowAKSBound`
  - `ExistsAKSCyclicFoldedFailureBelowAKSBound`
  - prime なら bound 以下で failure が存在しない補題も接続済み

- composite witness examples を追加
  - `n = 4, r = 1, a = 1`
  - `composite_AKSCyclicCongruenceFails_four_one_one`
  - `composite_AKSCyclicFoldedCongruenceFails_four_one_one`
  - `ExistsAKSCyclicFoldedFailureBelow 4 1 2`
  - `ExistsAKSCyclicFoldedFailureBelowAKSBound 4 1`

反例証明は quotient equality を `Ideal.Quotient.mk_eq_mk_iff_sub_mem` でイデアル所属へ落とし、`X - 1` で割れるなら `X = 1` で根になる、という形で `14 ≠ 0 mod 4` に帰着しています。AKS らしい観測例として悪くない形です。

検証済みです。

- `lake build DkMath.NumberTheory.AKSBridge`
- `git diff --check`
- `lake build DkMath`

全体ビルドは成功。既存の unrelated な `sorry` warning は残っています。

---

#### AKS 完了、既存定理接続へ

了解です。AKSBridge はここで v1.5 くらいの閉じ方で良いと思います。

次は本線として、二項定理・p-adic・primitive prime divisor / Zsigmondy 接続へ戻すのが自然です。優先順はこのあたりです。

1. `Nat.choose` / `padicValNat` / `prime_power_dvd_choose_of_not_dvd_index` 周辺の既存補題を、今回の Beam / height / failure predicate と接続
2. `weightedBinomialInnerBeamSum` の可除性から、個別係数の p-adic 高さ観測へ戻す橋を整理
3. primitive side へ向けて、「この段で初めて現れる素因子」を表す薄い predicate を作る
4. Zsigmondy 既存ファイルの定理名・使える補題を再探索して、次の実装候補を絞る

次の実装ターゲットとしては、まず既存定理探索から入って、`AKSBridge` ではなく `BinomialPrimePower` / `PascalPrimeDial` / `WeightedBinomial` / `Zsigmondy*` のどこに橋を置くのが一番自然か見ます。

---

既存定理探索、要点が見えました。
結論として、次の本線は **AKS ではなく `BinomialPrimePower → PascalPrimeDial → WeightedBinomial → PrimitiveBeam/Zsigmondy` の橋**です。

**使える核心定理**

- [BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean:130)
  - `padicValNat_choose_prime_pow`
  - `padicValNat_choose_prime_pow_add_index`
  - `prime_power_pow_dvd_choose_of_padicValNat_index`
  - `prime_power_dvd_choose_of_not_dvd_index`
  - `prime_power_unitFilteredBeamHeight`
- [PascalPrimeDial.lean](/lean/dk_math/DkMath/NumberTheory/PascalPrimeDial.lean:108)
  - `pascalPrimeDialHeight_prime_pow_add_index`
  - `pascalPrimeDialHeight_prime_pow`
  - `prime_power_unitFilteredPrimeDialHeight`
- [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:196)
  - `prime_power_pow_dvd_weightedBinomialTerm_of_padicValNat_index`
  - `prime_power_dvd_weightedBinomialTerm_of_not_dvd_index`
  - `weightedBodyGapKernelSplit`
- [PrimitiveBeam.lean](/lean/dk_math/DkMath/NumberTheory/PrimitiveBeam.lean:18)
  - `PrimitivePrimeFactorOfDiffPow`
  - `exists_primitive_prime_factor_as_prop`
  - `primitive_prime_dvd_GN`
  - `primitive_prime_padic_eq_GN`
  - `primitive_prime_padic_bound_diff_of_squarefree_GN`

**重要な判断**
既に Kummer の p^n フィルターは実装済みです。
なので次は Kummer 本体を作るより、`FilteredBeamHeight` / `FilteredPrimeDialHeight` の観測を `weightedBinomialTerm` と `GTail/GN` 側へ運ぶ薄い bridge が良いです。

特に実装候補はこれです。

```lean
theorem filteredBeamHeight_dvd_choose_of_height_ge
theorem filteredBeamHeight_dvd_weightedTerm_of_height_ge
theorem prime_power_unitFilteredBeamHeight_dvd_weightedTerm
```

その次に、`weightedBinomialPositiveTailSum = x * GTail d 1 x u` が既にあるので、Beam の項別 p-adic 支持を `GTail` へ移す観測補題を作るのが自然です。

注意点として、Zsigmondy 精密層には既に反例付きの警告があります。`padicValNat ≤ 1` は一般には危険で、現在の honest route は `Squarefree (GN d (a - b) b)` 仮定付きです。ここは無理に一般化せず、まず p^n フィルターの「見える層」を GN/GTail に接続する方が安全です。

### 2026/06/09 16:08

実装しました。

追加した橋はこの2段です。

- [BinomialPrimePower.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean:61)
  - `FilteredBeamHeight.dvd_choose_of_height_ge`
  - `UniformBeamHeight.dvd_choose_of_height_ge`
  - `prime_power_unitFilteredBeamHeight_dvd_choose`

- [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:183)
  - `FilteredBeamHeight.dvd_weightedBinomialTerm_of_height_ge`
  - `UniformBeamHeight.dvd_weightedBinomialTerm_of_height_ge`
  - `prime_power_unitFilteredBeamHeight_dvd_weightedBinomialTerm`

意味としては、

```text
p-adic height が h ある
かつ r ≤ h
なら p^r が係数を割る

さらに、その係数可除性は weighted term 全体へ持ち上がる
```

という橋です。これで `p^n` 篩の観測層から weighted Beam/GTail 側へ進める足場ができました。

検証済みです。

- `lake build DkMath.NumberTheory.WeightedBinomial`
- `lake build DkMath.NumberTheory.PascalPrimeDial`
- `lake build DkMath.NumberTheory.AKSBridge`
- `lake build DkMath`
- `git diff --check`

全体ビルド成功。既存の unrelated な `sorry` warning はそのままです。

### 2026/06/09 18:14

`weighted Beam/GTail` 側を進めました。

[WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:55) に追加しています。

主な追加:

- `GTailOneTerm`
  - `GTail d 1 x u` の各項を明示する term 定義
- `filteredGTailOneSum`
  - `FilteredBeamHeight` と合うように、内側 Beam 部分だけを filter して足す sum
  - 右境界 `choose d d = 1` は係数篩の対象外なので除外
- `GTail_one_eq_GTailOneTerm_sum`
- `GTail_one_eq_innerBeam_add_right`
  - `GTail d 1 = inner Beam part + x^(d-1)` を固定
- `FilteredBeamHeight.dvd_GTailOneTerm_of_height_ge`
- `UniformBeamHeight.dvd_GTailOneTerm_of_height_ge`
- `prime_power_unitFilteredBeamHeight_dvd_GTailOneTerm`
- `FilteredBeamHeight.dvd_filteredGTailOneSum_of_height_ge`
- `prime_power_unitFilteredBeamHeight_dvd_filteredGTailOneSum`

これで、

```text
係数の p-adic height
→ GTail の各 Beam 項の p^r 可除性
→ filtered GTail Beam sum の p^r 可除性
```

までつながりました。

検証済みです。

- `lake build DkMath.NumberTheory.WeightedBinomial`
- `lake build DkMath.NumberTheory.PascalPrimeDial`
- `lake build DkMath.NumberTheory.AKSBridge`
- `lake build DkMath`
- `git diff --check`

全体ビルド成功です。

### 2026/06/09 19:03

次の一手として、`WeightedBinomial.lean` に軽い橋を追加しました。

追加したもの:

- `allInnerChooseDivisible_dvd_filteredGTailOneSum_true`
  - 係数レベルで inner 項がすべて `m` で割れるなら、`GTail d 1` の inner Beam 和も `m` で割れる。
  - ただし右端境界 `x^(d-1)` は除外。ここが重要です。

- `prime_dvd_filteredGTailOneSum_true`
  - 素数行 `p` では、`filteredGTailOneSum p x u (fun _ => True)` が `p` で割れる。

確認済み:

```txt
lake build DkMath.NumberTheory.WeightedBinomial
git diff --check
```

どちらも成功です。

次は本線として、これを `GN d x u = GTail d 1 x u` 側へ接続して、`GN = inner Beam + right boundary` という観測補題を置くのが良いです。これで PrimitiveBeam / Zsigmondy 側の `GN` 定理群に、今回の `p^n` 篩を差し込めるようになります。

### 2026/06/09 19:08

実装しました。`GN` へ直接つなぐ薄い bridge として [WeightedGNBridge.lean](/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean) を新設し、[DkMath.lean](/lean/dk_math/DkMath.lean:28) に import を追加しています。

入れた補題はこの 3 つです。

```lean
GN_eq_filteredGTailOneSum_true_add_right
GN_modEq_rightBoundary_of_dvd_filteredGTailOneSum_true
prime_GN_modEq_rightBoundary
```

意味としては、`GN d x u` を

```txt
GN = inner Beam + right boundary
```

に分解し、素数行では inner Beam が `p` で消えるので、

```lean
GN p x u ≡ x ^ (p - 1) [MOD p]
```

まで固定しました。ここで `GN` 全体が割れるとは主張せず、境界項が残る形にしてあります。

確認済みです。

```txt
lake build DkMath.NumberTheory.WeightedGNBridge
lake build DkMath
git diff --check
```

`lake build DkMath` は成功。既存の `sorry` warning は出ていますが、今回追加分には `sorry` はありません。

---

theorem prime_GN_sub_rightBoundary_dvd

∃ B, filteredGTailOneSum p x u (fun _ => True) = p * B

∃ B, GN p x u = p * B + x ^ (p - 1)

---

### 2026/06/09 19:19

実装しました。[WeightedGNBridge.lean](/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean) に以下を追加しています。

```lean
dvd_GN_sub_rightBoundary_of_dvd_filteredGTailOneSum_true
exists_filteredGTailOneSum_true_eq_mul_of_dvd
exists_GN_eq_mul_add_rightBoundary_of_dvd_filteredGTailOneSum_true

prime_GN_sub_rightBoundary_dvd
prime_exists_filteredGTailOneSum_true_eq_mul
prime_exists_GN_eq_mul_add_rightBoundary
```

ユーザー指定の形はこの 3 つで入っています。

```lean
theorem prime_GN_sub_rightBoundary_dvd
    {p x u : ℕ} (hp : p.Prime) :
    p ∣ GN p x u - x ^ (p - 1)

theorem prime_exists_filteredGTailOneSum_true_eq_mul
    {p x u : ℕ} (hp : p.Prime) :
    ∃ B, filteredGTailOneSum p x u (fun _ => True) = p * B

theorem prime_exists_GN_eq_mul_add_rightBoundary
    {p x u : ℕ} (hp : p.Prime) :
    ∃ B, GN p x u = p * B + x ^ (p - 1)
```

確認済みです。

```txt
lake build DkMath.NumberTheory.WeightedGNBridge
lake build DkMath
git diff --check
```

いずれも成功。今回追加分に `sorry` はありません。

---

フェルマーの小定理へと繋がる。

prime_GN_modEq_one_of_not_dvd_x
{p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
  GN p x u ≡ 1 [MOD p]

prime_not_dvd_GN_of_not_dvd_x

prime_exists_GN_eq_mul_add_rightBoundary
→ Fermat 小定理で right boundary を読む
→ p ∤ x なら p ∤ GN
→ primitive / Zsigmondy 側の gcd 制御へ接続

### 2026/06/09 19:26

入りました。[WeightedGNBridge.lean](/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean) に追加しています。

```lean
theorem prime_GN_modEq_one_of_not_dvd_x
    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
    GN p x u ≡ 1 [MOD p]

theorem prime_not_dvd_GN_of_not_dvd_x
    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
    ¬ p ∣ GN p x u
```

流れはその通りです。

```txt
prime_GN_modEq_rightBoundary
  GN p x u ≡ x^(p-1) [MOD p]

Fermat 小定理
  p ∤ x → x^(p-1) ≡ 1 [MOD p]

合成
  GN p x u ≡ 1 [MOD p]

よって
  p ∤ GN p x u
```

確認済みです。

```txt
lake build DkMath.NumberTheory.WeightedGNBridge
lake build DkMath
git diff --check
```

今回追加分に `sorry` はありません。

### 2026/06/10  4:06

Summary を新規作成しました。

[FLGNB-FermatLittleGNBridge-Summary.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-FermatLittleGNBridge-Summary.md)

整理した主軸は以下です。

```text
1. Fermat 小定理との接続点
2. WeightedGNBridge の実装済み endpoint
3. GN を主語にして Pascal を自然数断面として読む方針
4. Dynamic Boundary-Beam Residue Principle の候補
5. Gamma を急がず GN / powerKernel 既存補題を使う解析方針
6. Relative Polygon / Petal 系の棚卸しが次 checkpoint
7. PetalGNBridge と S0_nat への p=3 特化補題候補
```

`git diff --check` も通っています。

### 2026/06/10  4:26

[FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md) を新規作成しました。

内容は、指定の軸に沿って整理しています。

- 設計思想: `GN -> Petal / relative polygon -> Pascal -> prime-row -> primitive factor`
- 実装計画・手順: `DkMath.Petal.*` の新設順序
- 相対多角数 Petal 整備計画: `RelPolygon`, `S0/S1`, `termial`, `R(n)` の位置づけ
- 既存定理 Bridge Link theorem 予定: `GN_three_sub_eq_S0_nat`、Fermat boundary から `S0_nat` へ渡す補題、GN gcd から Petal gcd への橋
- 既存補題リスト: `UnitCycle.RelPolygon`, `FLT.PetalDetect`, `FLT.CosmicPetalBridge`, `NumberTheory.Gcd.GN`, `GEisensteinBridge` などを分類

検証は `git diff --check` 済みです。 docs 追加のみなので Lean build は走らせていません。

### 2026/06/10  4:45

`DkMath.Petal.*` の土台を追加しました。

追加した入口は以下です。

- [DkMath/Petal.lean](/lean/dk_math/DkMath/Petal.lean)
- [DkMath/Petal/Basic.lean](/lean/dk_math/DkMath/Petal/Basic.lean)
- [DkMath/Petal/Forms.lean](/lean/dk_math/DkMath/Petal/Forms.lean)
- [DkMath/Petal/RelPolygon.lean](/lean/dk_math/DkMath/Petal/RelPolygon.lean)
- [DkMath/Petal/CoreUnit.lean](/lean/dk_math/DkMath/Petal/CoreUnit.lean)
- [DkMath/Petal/GNBridge.lean](/lean/dk_math/DkMath/Petal/GNBridge.lean)

実装した主な橋補題は `GNBridge` に置いています。

```lean
theorem S0_nat_eq_GN_three_sub
theorem three_S0_nat_modEq_one_of_not_dvd_sub
theorem three_not_dvd_S0_nat_of_not_dvd_sub
```

つまり、`GN 3 (c - b) b = S0_nat c b` を Petal 側の正向き API として固定し、さらに FLGNB の Fermat 境界補題から `3 ∤ c-b` のとき `S0_nat c b ≡ 1 [MOD 3]`、`3 ∤ S0_nat c b` まで繋ぎました。

[DkMath.lean](/lean/dk_math/DkMath.lean) にも `import DkMath.Petal` を追加済みです。

検証:

```text
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功しています。

### 2026/06/10  6:41

Petal の基礎語彙を Lean 側に固定しました。今回は `GNBridge` へ進まず、設計ノートに沿って「数え上げ・住所・境界」の最小核を追加しています。

追加:

- [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean)
  - `baseUnitCore`
  - `inheritanceSlot`
  - `lapBase`
  - `relPetalTotal`
  - `relPolygonKernel`
  - `SameRelPetalOrbit`
  - `R_5(0)=5`, `R_5(1)=30`, `R_5(2)=180`
  - `5,30,180` が同じ Petal orbit 上にある補題

- [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean)
  - `relPetalBlockSize`
  - `PetalAddress`
  - `outerPetalAddress`
  - `channel 0 = inheritance/core channel`
  - `channel 1..n = Petal channels`
  - `outerPetalAddress 5 1 25 = { lap := 1, channel := 4, offset := 5 }`
  - `outerPetalAddress 5 2 25 = { lap := 2, channel := 0, offset := 25 }`
  - offset と channel の基本境界補題

更新:

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean) に `Counting` / `Address` を追加 import

検証:

```text
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

### 2026/06/10  7:00

[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に channel 判定層を実装しました。

追加した内容:

```lean
def IsInheritanceChannel
def IsPetalChannel
```

基本補題:

```lean
theorem isInheritanceChannel_iff_channel_eq_zero
theorem isPetalChannel_iff_channel_pos
theorem not_isPetalChannel_of_isInheritanceChannel
theorem isPetalChannel_of_not_isInheritanceChannel
```

outer address 側の補題:

```lean
theorem outerPetalAddress_channel_eq_zero_iff_sub_lt_blockSize
theorem outerPetalAddress_channel_eq_zero_iff_le_blockSize
theorem outerPetalAddress_isInheritanceChannel_iff_le_blockSize
theorem outerPetalAddress_isPetalChannel_of_blockSize_lt
theorem outerPetalAddress_channel_le_baseUnitCore
```

これで、1-based value `m` について、

```text
channel = 0  ↔  m ≤ blockSize
```

が Lean 上で固定されました。つまり「外側 block の最初に収まるなら inheritance/core channel」という読みが theorem になっています。

検証:

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

### 2026/06/10  7:23

[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に `outerPetalRemainder` 層を追加しました。

追加した定義:

```lean
def outerPetalRemainder (n lap m : Nat) : Nat :=
  (outerPetalAddress n lap m).offset
```

追加した補題:

```lean
theorem outerPetalRemainder_eq_offset
theorem outerPetalRemainder_pos
theorem outerPetalRemainder_le_blockSize
theorem outerPetalRemainder_eq_self_of_le_blockSize
theorem outerPetalRemainder_eq_self_of_isInheritanceChannel
theorem outerPetalAddress_channel_zero_remainder_eq_self
```

これで review の推奨だった核心、

```text
channel = 0 -> offset = m
```

を固定できました。つまり Lean 上で、

```text
継承口に入った値は、そのまま inner lap へ降りる
```

と言える状態になっています。

検証:

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

### 2026/06/11  2:08

[Address.lean](/lean/dk_math/DkMath/Petal/Address.lean) に review 指定の次 theorem を実装しました。

追加:

```lean
theorem outerPetalRemainder_le_prevTotal_of_valid
```

valid な `m` について、remainder が前段 lap total に収まることを固定しました。nested address の次段へ渡すための名前付き補題です。

```lean
theorem outerPetalAddress_decompose
```

one-based value に対する分解式を固定しました。

```lean
m =
  (outerPetalAddress n lap m).channel * relPetalBlockSize n lap
    + outerPetalRemainder n lap m
```

注意点として、これは `m = 0` では偽なので、定理には `1 ≤ m` を仮定に入れています。`blockSize` の正値仮定は不要でした。`blockSize = 0` でも one-based remainder の定義により分解式自体は成立します。

検証:

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

すべて成功です。

### 2026/06/11 21:05

実装しました。更新は [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:336) のみです。

追加内容は次の3本です。

- `outerPetalAddress_decompose_sub_one`
  - `m - 1 = channel * blockSize + (remainder - 1)` を固定
  - 仮定なしで通りました
- `outerPetalRemainder_five_two_twentyfive`
  - lap 2 の `25` が remainder `25` として降りる具体例
- `outerPetalAddress_five_inner_after_two_twentyfive`
  - その remainder を lap 1 で読むと `{ channel := 4, offset := 5 }` になる nested 最小例

検証も通っています。

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

`lake build DkMath` では既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

### 2026/06/11 21:14

実装しました。更新は [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:374) のみです。

追加したのは `nestedPetalAddress` の最小基盤です。outermost lap から innermost lap へ、`outerPetalRemainder` を渡しながら `List PetalAddress` を作ります。あわせて `zero`、`succ`、`head?`、`tail`、`length` の基本補題と、五角例 `nestedPetalAddress 5 2 25 = [...]` を固定しました。

検証済みです。

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

`lake build DkMath` では既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

### 2026/06/11 21:22

実装しました。更新は [Address.lean](/lean/dk_math/DkMath/Petal/Address.lean:302) のみです。

追加した主補題は `outerPetalRemainder_valid_for_prevTotal` です。valid な one-based 入力 `1 ≤ m ≤ relPetalTotal n lap` が positive lap で読まれたとき、remainder が次の inner lap の valid value になることを `1 ≤ remainder ∧ remainder ≤ relPetalTotal n (lap - 1)` として束ねました。

あわせて nested list 側に軽い観測補題を足しました。

- `nestedPetalAddress_ne_nil_of_pos`
- `nestedPetalAddress_head?_eq_none_iff_lap_zero`

検証済みです。

```text
lake build DkMath.Petal.Address
lake build DkMath.Petal
lake build DkMath
git diff --check
```

`lake build DkMath` の既存 `sorry` warning は残っていますが、今回の変更による失敗や新規 warning はありません。

### 2026/06/11 23:50

実装しました。更新は [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean:60) のみです。

追加した中核はこの3つです。

- `dynamicOrbitTotal`
- `dynamicPetalTotal`
- `dynamicPetalTotal_const`

あわせて、使いやすい基本補題も入れました。

- `dynamicOrbitTotal_zero`
- `dynamicOrbitTotal_succ`
- `dynamicOrbitTotal_const`
- `dynamicPetalTotal_zero`
- `dynamicPetalTotal_succ`

これで固定核の `relPetalTotal n k` が、動的核 `dynamicPetalTotal (fun _ => n) k` の特殊ケースとして Lean 上で固定されました。

検証済みです。

```text
lake build DkMath.Petal.Counting
lake build DkMath.Petal
lake build DkMath
git diff --check
```

既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

### 2026/06/11 23:55

実装しました。更新は [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean:96) のみです。

追加した内容は、Dynamic Counting の拡張応用です。

- `dynamicOrbitTotal_succIndex_eq_factorial`
  - `dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k`
  - 階乗を dynamic orbit の特殊ケースとして固定
- `primeBaseOrbitTotal`
  - 抽象 prime-base orbit の薄い Petal-facing alias
- `IsPrimeBaseSequence`
  - 各 lap base が素数であることを表す述語
- `primeBaseOrbitTotal_zero`
- `primeBaseOrbitTotal_succ`
- `IsPrimeBaseSequence.prime_at`

具体的な `nthPrime` や primorial の標準定義にはまだ接続せず、まず「素数列を入れた prefix product」という抽象層だけ固定しました。

検証済みです。

```text
lake build DkMath.Petal.Counting
lake build DkMath.Petal
lake build DkMath
git diff --check
```

既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

### 2026/06/12  0:38

実装しました。更新は [Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean:131) のみです。

追加したのは prime-base orbit の基本可除性です。

- `primeBaseOrbitTotal_dvd_succ`
  - `primeBaseOrbitTotal p k ∣ primeBaseOrbitTotal p (k + 1)`
  - prefix product が次の prefix product を割ることを固定
- `primeBaseOrbitTotal_nextPrime_dvd_succ`
  - `IsPrimeBaseSequence p` のもとで `p k ∣ primeBaseOrbitTotal p (k + 1)`
  - 素数列 orbit の次 base が次段 product に含まれることを固定

まだ distinct / strict prime sequence は入れていません。まずは抽象 prime-base prefix product の骨格だけを固めました。

検証済みです。

```text
lake build DkMath.Petal.Counting
lake build DkMath.Petal
lake build DkMath
git diff --check
```

既存の `sorry` warning は出ていますが、今回の変更による失敗や新規 warning はありません。

### 2026/06/12  0:49

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に review-petal-010 の checkpoint を追加しました。

追加した補題:

- `dynamicOrbitTotal_base_dvd_of_lt`
  - `i < k` なら、`b i ∣ dynamicOrbitTotal b k`
- `primeBaseOrbitTotal_base_dvd_of_lt`
  - prime-base orbit 側の alias
- `primeBaseOrbitTotal_prime_dvd_of_lt`
  - `IsPrimeBaseSequence` の解釈を保持した版

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功しています。全体ビルドでは既存の `sorry` warning は出ていますが、今回追加箇所による失敗はありません。

### 2026/06/12  1:39

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に prefix product の可除性単調性を追加しました。

追加した補題:

- `dynamicOrbitTotal_dvd_succ`
  - `dynamicOrbitTotal b k ∣ dynamicOrbitTotal b (k + 1)`
- `dynamicOrbitTotal_dvd_of_le`
  - `k ≤ l` なら `dynamicOrbitTotal b k ∣ dynamicOrbitTotal b l`
- `primeBaseOrbitTotal_dvd_of_le`
  - prime-base orbit 側の alias

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning は全体ビルドで出ていますが、今回追加分は問題ありません。

### 2026/06/12  1:43

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に、採用済み prime base が後段 prefix product にも残る橋補題を追加しました。

```lean
theorem primeBaseOrbitTotal_prime_dvd_of_lt_of_le
    {p : Nat → Nat} (hp : IsPrimeBaseSequence p)
    {i k l : Nat} (hi : i < k) (hkl : k ≤ l) :
    p i ∣ primeBaseOrbitTotal p l
```

中身は自然に、

- `primeBaseOrbitTotal_prime_dvd_of_lt`
- `primeBaseOrbitTotal_dvd_of_le`
- `Nat.dvd_trans`

を接続しています。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning は出ていますが、今回追加分は問題ありません。

### 2026/06/12  1:48

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に distinct prime-base sequence の入口を追加しました。

追加内容:

```lean
def IsDistinctPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ Function.Injective p
```

projection 補題:

- `IsDistinctPrimeBaseSequence.prime_at`
- `IsDistinctPrimeBaseSequence.injective`

これで「各 base は素数」「同じ素数 base を二度採用しない」を、順序までは要求せずに扱える土台ができました。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

### 2026/06/12  1:52

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に distinct 性を実際に使う補題を追加しました。

追加補題:

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_ne
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i ≠ j) :
    p i ≠ p j
```

```lean
theorem IsDistinctPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsDistinctPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これで「重複なし素数列」の意味が、実用補題として使える形になりました。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

### 2026/06/12  1:57

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に strict prime-base sequence 層を追加しました。

追加内容:

```lean
def IsStrictPrimeBaseSequence (p : Nat → Nat) : Prop :=
  IsPrimeBaseSequence p ∧ StrictMono p
```

projection / bridge 補題:

- `IsStrictPrimeBaseSequence.prime_at`
- `IsStrictPrimeBaseSequence.strictMono`
- `IsStrictPrimeBaseSequence.injective`
- `IsStrictPrimeBaseSequence.distinct`

これで `strict → injective → distinct` の橋が固定されました。標準プリモリアルや `nthPrime` 的な順序付き素数列へ接続する準備ができています。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

### 2026/06/12  2:03

実装完了です。

[Counting.lean](/lean/dk_math/DkMath/Petal/Counting.lean) に strict prime-base sequence の実用補題を追加しました。

追加補題:

```lean
theorem IsStrictPrimeBaseSequence.base_lt_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i < p j
```

```lean
theorem IsStrictPrimeBaseSequence.ne_of_lt
    {p : Nat → Nat} (hp : IsStrictPrimeBaseSequence p)
    {i j : Nat} (hij : i < j) :
    p i ≠ p j
```

これで strict 層から、大小関係と非重複性を直接取り出せます。

確認済み:

- `lake build DkMath.Petal.Counting`
- `lake build DkMath.Petal`
- `git diff --check`
- `lake build DkMath`

すべて成功です。既存の `sorry` warning はありますが、今回追加分は問題ありません。

### 2026/06/12  3:04

ドキュメント整理を実施しました。

新規作成:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
  - `DkMath.Petal` の目的、Phase 4.5 と Phase 5 の間での位置づけ
  - Gamma 関数回避としての `dynamicOrbitTotal`
  - factorial / prime-base / strict prime-base orbit の意味
  - `Counting`, `Address`, `GNBridge` の到達点
  - 次候補として `GcdBridge`, primorial 接続, nested address 応用を整理

更新:

- [BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md)
  - `Phase 4.7: Petal dynamic counting and address layer` を追加
  - `AKSBridge v1 → Petal → Zsigmondy` の接続位置を明記

- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
  - 実装済み範囲を反映
  - `Counting` / `Address` の節を追加
  - 実装手順を `completed` / `planned` に整理
  - 次の未実装候補を `GcdBridge`, `EisensteinBridge`, `AnalyticBridge` として明確化

確認:

- `git diff --check` 成功
- 対象 Markdown の trailing whitespace 検査も問題なし
- docs-only なので Lean build は実行していません

`*-ja.md` は触れていません。

---

実装しました。

追加したもの:

- [GcdBridge.lean](/lean/dk_math/DkMath/Petal/GcdBridge.lean)
  - `coprime_sub_right_of_coprime`
  - `gcd_sub_S0_nat_eq_gcd_sub_three`
  - `gcd_sub_S0_nat_dvd_three`
  - `coprime_sub_S0_nat_of_coprime_of_not_dvd_three`

- [PadicBridge.lean](/lean/dk_math/DkMath/Petal/PadicBridge.lean)
  - `padicValNat_cube_sub_eq_padicValNat_S0_nat_of_not_dvd_sub`
  - `padicValNat_three_cube_sub_eq_padicValNat_three_S0_nat_of_not_dvd_sub`

- [PrimitiveBridge.lean](/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean)
  - `primitive_prime_dvd_S0_nat`
  - `primitive_prime_padicValNat_cube_sub_eq_S0_nat`
  - `primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub`
  - `exists_primitiveOnS0_of_not_three_dvd_sub`

集約入口 [Petal.lean](/lean/dk_math/DkMath/Petal.lean) にも import を追加済みです。

確認:

- `lake build DkMath.Petal.GcdBridge` 成功
- `lake build DkMath.Petal.PadicBridge` 成功
- `lake build DkMath.Petal.PrimitiveBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

注意点として、ビルド中に既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch` の `sorry` warning は出ていますが、今回追加した Petal bridge 自体には `sorry` はありません。

### 2026/06/12 14:09

進めました。

実装:

- [PrimitiveBridge.lean](/lean/dk_math/DkMath/Petal/PrimitiveBridge.lean:94)
  - `exists_prime_dvd_S0_nat_of_not_three_dvd_sub`
  - `PrimitiveOnS0` を知らない caller 向けに、`∃ q, Nat.Prime q ∧ q ∣ S0_nat c b ∧ ¬ q ∣ c - b` を直接返す projection です。

- [ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean:30)
  - `HasNoPrimeBelow`
  - `HasAnchorPrime`
  - `hasAnchorPrime_prime`
  - `hasAnchorPrime_anchor_dvd`
  - `hasAnchorPrime_no_smaller_prime`

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean:8)
  - `DkMath.Petal.ReducedSupport` を集約 import に追加。

Docs:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md:216)
  - `GcdBridge / PadicBridge / PrimitiveBridge / ReducedSupport` の小総括を追加。
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md:776)
  - Bridge 完了、`ReducedSupport` initial API 実装済みとして更新。

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal.PrimitiveBridge` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き出ていますが、今回追加分には `sorry` はありません。

### 2026/06/12 14:20

B 案で実装しました。`HasAnchorPrime` は広い raw predicate のまま残し、厳密な非ゼロ support 用に `HasPositiveAnchorPrime` を追加しています。

変更:

- [ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean)
  - `HasPositiveAnchorPrime`
  - `hasAnchorPrime_anchor_le_of_prime_dvd`
  - `hasPositiveAnchorPrime_pos`
  - `hasPositiveAnchorPrime_prime`
  - `hasPositiveAnchorPrime_anchor_dvd`
  - `hasPositiveAnchorPrime_no_smaller_prime`
  - `hasPositiveAnchorPrime_anchor_le_of_prime_dvd`

意味づけ:

```text
HasAnchorPrime           = 間口の広い raw carrier predicate
HasPositiveAnchorPrime   = 0 を除外した strict support predicate
```

これで `HasAnchorPrime 2 0` のような raw 成立可能性は許容しつつ、下流の「実際の素因子 support」として使う場面では `HasPositiveAnchorPrime` で厳密性を担保できます。

Docs も同期しました:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回も出ていますが、今回追加分には `sorry` はありません。

### 2026/06/12 16:59

追加しました。

[ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean:91) に以下を追加:

```lean
theorem hasPositiveAnchorPrime_ne_zero
    {r n : ℕ} (h : HasPositiveAnchorPrime r n) :
    n ≠ 0

theorem hasPositiveAnchorPrime_of_pos
    {r n : ℕ} (hn : 0 < n) (h : HasAnchorPrime r n) :
    HasPositiveAnchorPrime r n
```

あわせて docs の API リストも同期しました。

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

今回も追加分に `sorry` はありません。

### 2026/06/12 19:15

`DkMath.Petal.Anchor` を新設して、Anchor と S0/GN の接続を始めました。

追加:

- [Anchor.lean](/lean/dk_math/DkMath/Petal/Anchor.lean)
  - `AnchoredS0Carrier`
  - `AnchoredGNCarrier`
  - `anchoredS0Carrier_anchor`
  - `anchoredS0Carrier_dvd_S0`
  - `anchoredS0Carrier_pos`
  - `anchoredS0Carrier_ne_zero`
  - `anchoredS0Carrier_anchor_le_of_prime_dvd`
  - `anchoredGNCarrier_anchor`
  - `anchoredGNCarrier_dvd_GN`
  - `anchoredGNCarrier_pos`
  - `anchoredGNCarrier_ne_zero`
  - `anchoredGNCarrier_anchor_le_of_prime_dvd`
  - `anchoredGNCarrier_of_anchoredS0Carrier`
  - `anchoredS0Carrier_of_anchoredGNCarrier`

ポイントは、`ReducedSupport` は S0/GN 非依存のまま維持し、`Anchor.lean` で初めて `S0_nat` / `GN` へ接続したことです。

集約:

- [Petal.lean](/lean/dk_math/DkMath/Petal.lean) に `DkMath.Petal.Anchor` を追加。

Docs:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)

確認:

- `lake build DkMath.Petal.Anchor` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ていますが、今回追加分に `sorry` はありません。

### 2026/06/12 19:48

レビューの次目的地に合わせて進めました。

追加実装:

- [ReducedSupport.lean](/lean/dk_math/DkMath/Petal/ReducedSupport.lean)
  - `hasPositiveAnchorPrime_self_of_prime`
  - prime witness 自身を positive anchored carrier として扱うための基礎補題です。

- [Anchor.lean](/lean/dk_math/DkMath/Petal/Anchor.lean)
  - `exists_anchoredS0Carrier_of_not_three_dvd_sub`
  - `PrimitiveBridge` の `exists_prime_dvd_S0_nat_of_not_three_dvd_sub` を使い、`S0_nat` 上の primitive prime witness を `AnchoredS0Carrier q c b q` へ昇格します。

依存方向も整理しました:

```text
ReducedSupport
  -> PrimitiveBridge
  -> Anchor
```

Docs も同期:

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

確認:

- `lake build DkMath.Petal.ReducedSupport` 成功
- `lake build DkMath.Petal.Anchor` 成功
- `lake build DkMath.Petal` 成功
- `git diff --check` 成功

既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ていますが、今回追加分に `sorry` はありません。

### 2026/06/12 20:28

実装と整理を進めました。

`DkMath.Petal.Anchor` に reviewer 指摘の projection を追加しました。

- `anchoredS0Carrier_anchor_prime`
- `anchoredGNCarrier_anchor_prime`

新規に [BoundaryD3.lean](/lean/dk_math/DkMath/Petal/BoundaryD3.lean) を追加し、3 次 Petal 境界を固定しました。

- `BoundaryD3Branch`
- `BoundaryD3Reduced`
- `three_dvd_S0_nat_of_three_dvd_sub`
- `three_dvd_sub_of_three_dvd_S0_nat`
- `three_dvd_S0_nat_iff_three_dvd_sub`
- `boundaryD3Reduced_three_not_dvd_S0_nat`
- `boundaryD3Branch_three_dvd_S0_nat`
- `boundaryD3Reduced_coprime_sub_S0_nat`

意味としては、

```text
3 ∣ S0_nat c b  ↔  3 ∣ c - b
```

を Petal 用語として固定し、reduced branch では `S0_nat` と境界 gap の gcd 制御へ接続できる形にしました。

docs も更新済みです。

- [Petal-Overview.md](/lean/dk_math/DkMath/Petal/docs/Petal-Overview.md)
- [FLGNB-PetalRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FLGNB-PetalRoadmap.md)
- [S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` 警告だけ出ていますが、今回追加分では新しい `sorry` はありません。

### 2026/06/12 20:50

次の目的地まで進めました。

[BoundaryD3.lean](/lean/dk_math/DkMath/Petal/BoundaryD3.lean) に、review 指摘の使いやすい入口を追加しました。

```lean
boundaryD3Branch_or_reduced
not_boundaryD3Branch_of_reduced
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

これで downstream は `¬ 3 ∣ c - b` に戻らず、`BoundaryD3Reduced c b` のまま

```text
reduced branch
  -> boundary/S0 coprime
  -> anchored primitive S0 carrier exists
```

へ進めます。

さらに新規に [EisensteinBridge.lean](/lean/dk_math/DkMath/Petal/EisensteinBridge.lean) を追加しました。既存 `DkMath.FLT.GEisensteinBridge` の定理を Petal-facing alias として公開しています。

```lean
petal_S0_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift
petal_GN3_sub_eq_eisensteinNorm_shift_of_lt
petal_S0_nat_eq_eisensteinNorm_shift_of_lt
```

`DkMath.Petal.lean` にも import 済みで、docs も更新しました。

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning だけで、今回追加分に新しい `sorry` はありません。

### 2026/06/12 22:55

レビュー指摘は、今すぐ構造を割らずに「将来の `DkMath.Lib.*` 昇格リファクタリングで必ず見るべき依存問題」としてソース上に強めに明記しました。

追加したのは module doc の注意書きです。

- [BoundaryD3.lean](/lean/dk_math/DkMath/Petal/BoundaryD3.lean)
  - `BoundaryD3 -> Anchor -> PrimitiveBridge` になっている現状を明記
  - 将来は `BoundaryD3` と `BoundaryD3Anchor` に分ける候補を明示
  - 現状は便利 API として一時的に同居させている、と残しました

- [EisensteinBridge.lean](/lean/dk_math/DkMath/Petal/EisensteinBridge.lean)
  - `Petal -> FLT` の import 方向は最終形ではないと明記
  - `DkMath.Lib.*` または neutral な `NumberTheory` 層へ Eisenstein core facts を移し、将来は `FLT` が Petal/neutral layer を使う方向に直す、と残しました

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。今回も新しい `sorry` はありません。
