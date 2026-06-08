# History

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
