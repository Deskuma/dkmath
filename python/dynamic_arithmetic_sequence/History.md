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
