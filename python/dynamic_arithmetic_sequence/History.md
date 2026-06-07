# History

## Agent Log

### 2026/06/07 17:20

実装しました。`ln` / `exp` は使わず、DAS の本体を「公差 `d` を `k` でスケールした通常の等差列」として定義しています。

追加したもの:

- [DynamicArithmeticSequence.lean](/lean/dk_math/DkMath/DHNT/DynamicArithmeticSequence.lean#L28)
  - `dynamicStep`
  - `arithmeticTerm`
  - `dynamicTerm`
  - `dynamicSequence`
  - `dynamicTerm_eq_arithmeticTerm_scaledDiff`
  - `dynamicTerm_one`
  - `dynamicTerm_zeroScale`
  - `dynamicTerm_zeroDiff`
  - `dynamicTerm_succ`
  - Python デモ相当の `ℚ` 具体例

- [DynamicArithmeticSequence.lean](/lean/dk_math/DkMath/KUS/DynamicArithmeticSequence.lean#L28)
  - `gArithmeticTerm`
  - `gDynamicTerm`
  - `gDynamicSequence`
  - `toCoeff` / `extract_g` 補題
  - `gDynamicTerm_eq_gArithmeticTerm_scaledDiff`
  - `gDynamicTerm_one`
  - `gDynamicTerm_zeroScale`

入口にも追加済みです。

- [DHNT.lean](/lean/dk_math/DkMath/DHNT.lean#L6)
- [KUS.lean](/lean/dk_math/DkMath/KUS.lean#L19)

検証:

```bash
lake build DkMath.DHNT.DynamicArithmeticSequence
lake build DkMath.KUS.DynamicArithmeticSequence
lake build DkMath.DHNT
lake build DkMath.KUS
```

すべて成功しました。

一点だけ、`ℚ` のリスト具体例は `Rat` の通常 `decide` が詰まったため、局所的に `native_decide` linter を無効化して固定しています。本体定義と主要補題は通常の `simp`/`rfl` ベースです。

---

### 2026/06/07 17:59

`Sequence` パッケージを新設しました。DAS はそこへ移し、DHNT/KUS はその上に乗る形に整理しています。

追加した新カテゴリ:

- [DkMath/Sequence.lean](/lean/dk_math/DkMath/Sequence.lean#L7)
- [Sequence/Generator.lean](/lean/dk_math/DkMath/Sequence/Generator.lean#L22)
  - `Closed`
  - `AdditiveGenerator`
  - `term`, `take`, `toClosed`, `rescale`
- [Sequence/Recurrence.lean](/lean/dk_math/DkMath/Sequence/Recurrence.lean#L20)
  - `Recurrence`
  - `StateRecurrence`
  - `state`, `term`, `take`
- [Sequence/Arithmetic.lean](/lean/dk_math/DkMath/Sequence/Arithmetic.lean#L22)
  - `arithmeticGenerator`
  - `dynamicGenerator`
  - `dynamicTerm`, `dynamicSequence`
  - `variableDiffRecurrence`, `variableDiffTerm`
- [Sequence/Fibonacci.lean](/lean/dk_math/DkMath/Sequence/Fibonacci.lean#L20)
  - `fibonacciState`
  - `fibonacciTerm`
  - `fibonacciSequence`

既存側の整理:

- [DHNT/DynamicArithmeticSequence.lean](/lean/dk_math/DkMath/DHNT/DynamicArithmeticSequence.lean#L28) は `DkMath.Sequence` への薄い alias/bridge に変更。
- [KUS/DynamicArithmeticSequence.lean](/lean/dk_math/DkMath/KUS/DynamicArithmeticSequence.lean#L29) は `DHNT` ではなく `Sequence` の定義を直接参照するように変更。
- [DkMath.lean](/lean/dk_math/DkMath.lean#L17) に `import DkMath.Sequence` を追加。

検証済み:

```bash
lake build DkMath.Sequence
lake build DkMath.DHNT.DynamicArithmeticSequence
lake build DkMath.KUS.DynamicArithmeticSequence
lake build DkMath.DHNT
lake build DkMath.KUS
lake build DkMath
```

すべて成功しました。トップ build では既存ファイル由来の `sorry` warning は出ていますが、今回追加した `Sequence` 周りは warning なしです。

### 2026/06/07 20:36

`DkMath.PowerSwap.NormalForm` を追加しました。`z^n` を「冪正規形」として持つ薄い層です。

追加内容:

- [NormalForm.lean](/lean/dk_math/DkMath/PowerSwap/NormalForm.lean#L24)
  - `PowNormalForm`
  - `PowNormalForm.eval`
  - `PowNormalForm.ofPow`
  - `PowNormalForm.power`
  - `PowNormalForm.mulSameBase`
  - `HasPowNormalForm`
  - `HasPowNormalForm.ofPow`
  - `HasPowNormalForm.power`
  - `HasPowNormalForm.mulSameBase`
  - `normalForm_power_of_eq_pow`
  - `eval_normalForm_power_of_eq_pow`

`normalForm_power_of_eq_pow` は、既存の `exchange_condition_minimal_nat` を正規形 API として包んだものです。

```lean
A = a ^ t → A ^ m has normal form a ^ (t * m)
```

集約にも追加しました。

- [PowerSwap.lean](/lean/dk_math/DkMath/PowerSwap.lean#L10)

検証:

```bash
lake build DkMath.PowerSwap.NormalForm
lake build DkMath.PowerSwap
lake build DkMath
```

すべて成功しました。トップ build では既存ファイル由来の `sorry` warning はありますが、今回追加した `NormalForm` は warning なしです。

### 2026/06/08  0:44

解説ドキュメントを追加しました。

追加先:
[DkMath/Sequence/docs/DHNT-DAS-reinterpretation.md](/lean/dk_math/DkMath/Sequence/docs/DHNT-DAS-reinterpretation.md:1)

内容は、単なる実装履歴ではなく、

- DHNT の異単位調和演算
- 指数対数法則と単位分岐
- `e^{iπ} = -1` と宇宙式 `(x+1)^2 - x(x+2) = 1` の接続視点
- DAS を `ln(e^k)` から `a + i * (d*k)` へ正規化した理由
- `Sequence` へ切り出した理由
- KUS で support 固定の係数軌道として読む理由
- PowerSwap の冪正規形との今後の接続
- 現時点で「まだ入れない」境界

をまとめています。

検証は docs-only なので Lean build は回さず、`git diff --check` を通しました。

補足: `git status` には既存の `lean/dk_math/DkMath/DHNT/docs/DHNT_DAS_Note.md` と `python/dynamic_arithmetic_sequence/lean-implements-design.md` の変更も出ていますが、今回こちらで編集したのは新規追加した `Sequence/docs/DHNT-DAS-reinterpretation.md` だけです。

### 2026/06/08  1:31

実装前の地固めとして、ロードマップ文書を追加しました。

追加ファイル: [BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md)

中身は、二項係数から素数性を読む `BinomialPrime` と、`choose d k * x^k * u^(d-k)` の可除性を分離する `WeightedBinomial` を、段階的に実装する計画です。特に「まず Zsigmondy へ急がず、係数由来・x 由来・u 由来の因子を Lean 上で区別する」という方針に寄せています。

確認済みです。

```bash
git diff --check
```

Lean ファイルはまだ増やしていないので、今回は `lake build` は走らせていません。次の実装チェックポイントは `DkMath.NumberTheory.BinomialPrime` の最小 API、つまり `AllInnerChooseDivisible` と prime 段の内側二項係数可除性です。

### 2026/06/08  4:30

進めました。Phase 1 と Phase 2 の確実に閉じる部分を Lean 実装しています。

追加:

- [BinomialPrime.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean#L25)
  - `AllInnerChooseDivisible`
  - `prime_allInnerChooseDivisible_self`
  - `prime_dvd_inner_choose`
- [WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean#L27)
  - `weightedBinomialTerm`
  - 係数由来 / `x` 由来 / `u` 由来の可除性補題
  - `prime_dvd_inner_weightedBinomialTerm`
  - 境界項 `u^d`, `x^d`

`DkMath.lean` にも import を追加しました。新規ファイルに `sorry` / `axiom` / `admit` はありません。

確認:

```bash
lake build DkMath.NumberTheory.BinomialPrime
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

全部通っています。`prime_iff_allInnerChooseDivisible_self` の逆向きは、証明負荷が大きいので今回は無理に入れず、まず可除性 API を固めました。次はこの逆向きの証明経路を調査するか、先に `WeightedBinomial` と GN/CFBRC の橋を薄く作るのが自然です。
