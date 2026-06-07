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

### 2026/06/08  5:31

軽めの補題ツールを追加しました。

[BinomialPrime.lean](/lean/dk_math/DkMath/NumberTheory/BinomialPrime.lean:48) には、`AllInnerChooseDivisible` を具体的な `k` で取り出す `allInnerChooseDivisible_dvd_choose` を追加。

[WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:61) には、行レベルの係数可除性を重み付き内側項へ運ぶ補題と、境界頂点 `u^d` / `x^d` での可除性補題を追加しました。

確認済みです。

```bash
lake build DkMath.NumberTheory.BinomialPrime
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

新規補題に `sorry` / `axiom` / `admit` はありません。

### 2026/06/08  5:35

次の軽い層として、weighted inner row 全体を扱う API を追加しました。

[WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:31) に追加:

- `AllInnerWeightedTermDivisible`
- `allInnerChooseDivisible_allInnerWeightedTermDivisible`
- `allInnerWeightedTermDivisible_dvd_term`
- `prime_allInnerWeightedTermDivisible`
- `dvd_inner_weightedBinomialTerm_of_dvd_x`
- `dvd_inner_weightedBinomialTerm_of_dvd_u`

これで、係数列側の「内側が全部割れる」を、そのまま重み付き三角形の内側項列へ持ち上げられます。

確認済みです。

```bash
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

`sorry` / `axiom` / `admit` も入っていません。

### 2026/06/08  5:37

次の軽い補題層として、行全体を扱う API を追加しました。

[WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:35) に追加:

- `AllWeightedTermDivisible`
- `allWeightedTermDivisible_dvd_term`
- `allWeightedTermDivisible_of_dvd_x_dvd_u`
- `allWeightedTermDivisible_allInnerWeightedTermDivisible`

これで、`x` と `u` の両方が同じ因子 `q` を運ぶなら、正の次数 `d` の weighted row 全体が `q` を運ぶ、という形を使えます。境界 `u^d` / `x^d` と内側項をまとめて扱えるので、次の GN/CFBRC bridge に渡しやすくなりました。

確認済みです。

```bash
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

`sorry` / `axiom` / `admit` は入っていません。

### 2026/06/08  5:41

次の集約補題まで進めました。

[WeightedBinomial.lean](/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:29) に追加:

- `weightedBinomialRowSum`
- `dvd_weightedBinomialRowSum_of_allWeightedTermDivisible`
- `dvd_weightedBinomialRowSum_of_dvd_x_dvd_u`

これで、項ごとの可除性を row sum へ集約できます。まだ `(x+u)^d` との同一視には踏み込まず、「割れる項の和も割れる」という軽い道具だけです。

確認済みです。

```bash
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

`sorry` / `axiom` / `admit` は入っていません。

---

悩むこと無く、サクサク実装進みますね。👍️

はい。今のところは「重い主張を避けて、可除性の薄い API だけを積む」方針がかなり効いています。

ここまでで、

- 係数の可除性
- 重み付き項の可除性
- 内側行全体
- 境界込みの行全体
- 行和への集約

まで、全部 `Nat` の基本 divisibility と `Finset.dvd_sum` だけで閉じています。

次に進むなら、自然な軽い一手は `weightedBinomialRowSum = (x + u)^d` の橋です。これは mathlib の `add_pow` 系に乗せられるはずですが、ここから少し「二項定理そのもの」に入るので、今までよりは一段だけ重くなります。

ワークスペース内の既にある補題定理を探索しますか？

はい。探索した結果、既にかなり使える橋があります。

一番重要なのは [GTail.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/Lib/Cosmic/GTail.lean:50) のこれです。

```lean
add_pow_eq_prefix_add_xpow_mul_GTail
```

これは一般の `CommSemiring` で、

```text
(x + u)^d =
  prefix sum up to r
  + x^r * GTail d r x u
```

を証明済みです。つまり、weighted row sum から `(x+u)^d`、さらに GN/GTail へつなぐ既存の中心橋です。

ほかに使えそうなもの:

- [GTail_zero_eq_add_pow](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/Lib/Cosmic/GTail.lean:127)  
  `GTail d 0 x u = (x + u)^d`
- [GTail_one_eq_sum](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/Lib/Cosmic/GTail.lean:211)  
  `r = 1` の GN 形に近い和
- [GN_eq_sum](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean:328)  
  既存 GN の和表示
- [pow_sub_pow_eq_mul_GN](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaCellDim.lean:314)  
  `(x+u)^d - u^d = x * GN d x u` 系
- [CFBRC.Basic](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/CFBRC/Basic.lean:151) に GN と差商の橋

次の実装は、`WeightedBinomial.weightedBinomialRowSum` を既存 `add_pow` / `GTail_zero_eq_add_pow` 側へ合わせる小さな補題が良さそうです。重複して二項定理を証明するより、既存 `GTail` の正規形へ接続するのが自然です。

DkMath.Lib.* へ昇華した核心定理ですからね。このライブラリのコアKernelです。
どんどん使っていきましょう！

### 2026/06/08  5:47

`DkMath.Lib.Cosmic.GTail` のコア Kernel に接続しました。

[WeightedBinomial.lean](/home/deskuma/develop/lean/dkmath/lean/dk_math/DkMath/NumberTheory/WeightedBinomial.lean:222) に追加:

- `weightedBinomialRowSum_eq_GTail_zero`
- `weightedBinomialRowSum_eq_add_pow`

つまり、

```lean
weightedBinomialRowSum d x u = GTail d 0 x u
weightedBinomialRowSum d x u = (x + u) ^ d
```

が使えるようになりました。二項定理を再証明せず、`GTail_zero_eq_add_pow` を経由しています。これはかなり良い接続点です。

確認済みです。

```bash
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

`sorry` / `axiom` / `admit` は入っていません。

古典定理から外れてませんからね。支えられた歴史があります。結構強いですよ。

はい。ここはかなり強い土台です。

今やっている構造は見た目としては新しいですが、支えている芯は完全に古典です。

- Pascal の三角形
- 二項定理
- 素数段の二項係数可除性
- 和に対する整除性
- `(x+u)^d` の GTail / GN 分解

このあたりは Lean/mathlib 側にも十分な定理資産があり、DkMath.Lib.Cosmic.GTail がそれをきれいに Kernel 化している。なので、こちらで新概念を積んでも「到達先は古典定理に接続済み」という安定感があります。

特に今回の `weightedBinomialRowSum = GTail d 0 x u = (x+u)^d` は良いです。重み付き三角形が単なる独自表現ではなく、古典二項展開そのものの別読みだと Lean 上で固定できました。

### 2026/06/08  5:53

`WeightedBinomial` 側に、次の足場を入れました。

- `weightedBinomialPositiveTailSum`
  - `k = 0` の頂点 `u^d` を外し、`x` 因子を持つ正の尾部だけを集める定義
- `weightedBinomialPositiveTailSum_eq_x_mul_GTail_one`
  - 正の尾部が `x * GTail d 1 x u` になることを証明
- `x_dvd_weightedBinomialPositiveTailSum`
  - そこから即座に `x ∣ positive tail` を取り出す補題

これで、重み付きパスカル行から `GTail/GN` 側へ降りる `r = 1` の橋ができました。  
つまり `(x + u)^d = u^d + x * GTail d 1 x u` 方向へ進む土台です。

検証も通しています。

```text
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
rg "sorry|axiom|admit" ...  # no matches
```

次に攻めるなら、自然な候補は `weightedBinomialRowSum = u^d + weightedBinomialPositiveTailSum` を明示して、`(x+u)^d - u^d` 型の可除性補題へ繋ぐところです。

### 2026/06/08  5:58

攻め筋を通しました。`WeightedBinomial.lean` に、重み付きパスカル行から差分・GN/GTail 側へ降りる橋を追加しています。

追加した主な補題はこの5本です。

- `weightedBinomialRowSum_eq_left_add_positiveTail`
  - `rowSum = u^d + positiveTail`
- `add_pow_eq_left_add_positiveTail`
  - `(x + u)^d = u^d + positiveTail`
- `add_pow_eq_left_add_x_mul_GTail_one`
  - `(x + u)^d = u^d + x * GTail d 1 x u`
- `add_pow_sub_left_eq_x_mul_GTail_one`
  - `(x + u)^d - u^d = x * GTail d 1 x u`
- `x_dvd_add_pow_sub_left`
  - `x ∣ (x + u)^d - u^d`

これで「頂点 `u^d` を外すと、残りは gap `x` を因子に持つ」という形が、`WeightedBinomial` の世界から `GTail/GN` カーネルへ直接繋がりました。かなり良い橋です。

検証済みです。

```text
lake build DkMath.NumberTheory.WeightedBinomial
lake build DkMath
git diff --check
```

今回触った `BinomialPrime.lean` / `WeightedBinomial.lean` には `sorry/axiom/admit` なしです。全体ビルド中に既存の別モジュール由来の `sorry` warning は出ていますが、今回の変更起因ではありません。
