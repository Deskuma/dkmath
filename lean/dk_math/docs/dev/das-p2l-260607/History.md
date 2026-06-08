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

行けました。`UniformBeamHeight` と素数行の高さ定理を [BinomialPrimePower.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean:1) に追加しました。

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

追加した定理は [BinomialPrimePower.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/BinomialPrimePower.lean:1) のこの2本です。

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
