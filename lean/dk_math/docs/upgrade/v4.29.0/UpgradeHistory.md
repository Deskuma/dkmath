# v4.28.0 to v4.29.0 Upgrade History

## Lakefile.toml

- Updated the `rev` field for the `mathlib` dependency to point to the new version `v4.29.0`. This ensures that our project is using the latest compatible version of mathlib, which may include new features, bug fixes, and performance improvements.

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.29.0"
```

### lake update

After updating the `lakefile.toml`, run the following command in your terminal to update the dependencies:

```bash
lake clean && lake update
```

## `*.lean` Files

### 2026-04-17: v4.29.0 build fix

`upgrade-v4.28to29-build.log` に出ていたエラーを順に潰し、個別ターゲットの確認後に full `lake build` が通る状態まで修正した。

#### 修正内容

- `DkMath/DHNT/DHNT_Base.lean`
  - `MulOneClass` の `mul_one` / `one_mul` で、`simp only [instMulUnit]` だけでは閉じなくなった。
  - 期待する等式へ `change` で落としてから `simpa` で閉じる形に修正した。

- `DkMath/RH/Lemmas.lean`
  - `phaseVel_inv` で `deriv_fun_div` の簡約結果の形が変わり、そのままでは一致しなくなった。
  - 中間補題 `hderiv₀`, `hone` を置き、`[one_div]` を明示して式変形する形に修正した。

- `DkMath/KUS/Transport.lean`
  - `DecodeStrategy` の outParam の扱いが v4.29 で厳密になり、class field 経由の構成が壊れた。
  - `T`, `BT` を class parameter に持ち上げ、関連 instance と `harmonizeAddBy` / `harmonizeMulBy` / `toCoeff_*` を追従修正した。

- `DkMath/ABC/ABC008.lean`
  - `blocksOverlap` の decidable instance 構成がそのままでは通らなくなった。
  - `dsimp [blocksOverlap]; infer_instance` に簡約した。

- `DkMath/DHNT/UnitNatLayers.lean`
  - `> 0` の自動簡約に依存していた bridge の positivity 証明が通らなくなった。
  - `change ... + 1 > 0` の形へ落として `Nat.succ_pos _` を使う明示的な証明へ置き換えた。

- `DkMath/RH/EulerZetaLemmas.lean`
  - `ContinuousSMul ℝ ℂ` がそのままでは見つからない箇所があり、複数の微分補題も v4.29 の式展開に追従できなかった。
  - `ContinuousSMul ℝ ℂ` の local instance を追加し、`hasDerivAt_vertical_mul_log_p`,
    `hasDerivAt_eulerZeta_exp_s_log_p_sub_one`,
    `phaseVel_eulerZeta_exp_s_log_p_sub_one_eq`,
    `phaseVel_exp_vertical_mul_log_p_eq_log`
    を明示的な `convert` / `change` / `field_simp` ベースへ修正した。

- `DkMath/FLT/PrimeProvider/TriominoCosmicBranchARestore.lean`
  - `ZMod q` 上の逆元計算で、`y ≠ 0` と cast の一致を Lean が自動で拾えなくなった。
  - `hy_ne_zero`, `hy_cast` を補助事実として追加し、`inv_mul_cancel₀` へつなぐ形に修正した。

- `DkMath/RH/CFBRCBridge.lean`
  - `Classical.choose` に依存する provider 構成が computable definition 扱いでは通らなくなった。
  - 該当 3 定義を `noncomputable def` に変更した。

- `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean`
  - `Ideal.count_normalizedFactors_eq` 周辺で `DecidableEq` instance の不一致が発生した。
  - 補助定理 `dedekindIdealCountNormalizedFactorsEq` から明示的な `[DecidableEq (Ideal R)]` binder を外し、`classical` に委ねる形へ修正した。
  - `CyclotomicField p ℚ` 上の `IsCyclotomicExtension {p} ℚ _` を `inferInstance` では取れない箇所があった。
  - `CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)` を明示して canonical instance を与えるよう修正した。

#### 確認

- 個別確認
  - `lake build DkMath.RH.CFBRCBridge`
  - `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization`

- 全体確認
  - `lake build`
  - Lean `v4.29.0` 環境で build 完了を確認した。

#### 未対応の警告

- 今回は build break の解消を優先し、既存の deprecated warning / `push_neg` warning / `sorry` warning は未整理のままとした。

### 2026-04-17: deprecated warning cleanup

v4.29.0 移行後に残っていた deprecated warning を解消した。今回の対象は、build を壊してはいないが今後の追従コストが高くなる warning 群である。

#### 修正内容

- `padicValNat.zero` / `padicValNat.one`
  - `DkMath/ABC/PadicValNat.lean`
  - `DkMath/ABC/ABC025.lean`
  - `padicValNat_zero_right`, `padicValNat_one_right` へ置換した。

- `Nat.factorization_prod_pow_eq_self`
  - `DkMath/ABC/Rad.lean`
  - `DkMath/ABC/Core.lean`
  - `DkMath/ABC/Square.lean`
  - `DkMath/ABC/RatioBound.lean`
  - `DkMath/ABC/ABC016.lean`
  - `DkMath/NumberTheory/UniqueFactorizationGN.lean`
  - `DkMath/FLT/Basic.lean`
  - `DkMath/FLT/PrimeProvider/TriominoCosmicPrimeGe5Core.lean`
  - `DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean`
  - 新しい定理名 `Nat.prod_factorization_pow_eq_self` へ置換した。

- `push_neg`
  - ABC / Collatz / CosmicFormula / FLT 系の使用箇所を `push Not` へ置換した。
  - 置換対象:
    `DkMath/ABC/ABC017.lean`,
    `ABC018.lean`,
    `ABC021.lean`,
    `ABC024.lean`,
    `ABC028.lean`,
    `ABC031.lean`,
    `ABC033.lean`,
    `ABC038.lean`,
    `ABCFinalChernoffPrototype.lean`,
    `DkMath/Collatz/V2.lean`,
    `Collatz/Shift.lean`,
    `DkMath/CosmicFormula/CosmicFormulaCellDim.lean`,
    `DkMath/FLT/Basic.lean`,
    `FLT/Kummer/Basic.lean`,
    `FLT/Kummer/CyclotomicPrincipalization.lean`,
    `FLT/PetalDetect.lean`,
    `FLT/PrimeProvider/TriominoCosmicBranchADescentChain.lean`,
    `FLT/PrimeProvider/TriominoCosmicBranchARestore.lean`,
    `FLT/PrimeProvider/TriominoCosmicBranchARestoreArithmeticStrong.lean`

- Kummer 側の deprecated theorem
  - `DkMath/FLT/Kummer/CyclotomicPrincipalization.lean`
  - `Ideal.inf_eq_mul_of_isCoprime` を `Ideal.mul_eq_inf_of_isCoprime` に差し替え、向きは `.symm` で合わせた。
  - `IsDedekindDomain.inf_prime_pow_eq_prod` を `IsDedekindDomain.inf_pow_eq_prod_of_prime` に差し替えた。

#### 確認

- 個別確認
  - `lake build DkMath.ABC`
  - `lake build DkMath.NumberTheory.UniqueFactorizationGN`
  - `lake build DkMath.Collatz.V2`
  - `lake build DkMath.Collatz.Shift`
  - `lake build DkMath.CosmicFormula.CosmicFormulaCellDim`
  - `lake build DkMath.FLT`

- 全体確認
  - `lake build > ./tmp/v429-deprecated-check.log 2>&1`
  - `rg "deprecated:" ./tmp/v429-deprecated-check.log`
  - full build ログ上で deprecated warning が 0 件であることを確認した。

### 2026-04-17: unnecessary `simpa` warning cleanup

`try 'simp' instead of 'simpa'` の linter warning を解消した。今回の対象は 3 件のみで、いずれも証明内容はそのままに tactic を `simp` へ落とすだけで足りた。

#### 修正内容

- `DkMath/DHNT/DHNT_Base.lean`
  - `MulOneClass` の `mul_one`, `one_mul` の末尾を `simpa` から `simp` へ変更した。

- `DkMath/RH/EulerZetaLemmas.lean`
  - `phaseVel_eulerZeta_exp_s_log_p_sub_one_eq` 内の商の導出で、`simpa [...]` を `simp [...]` に変更した。

#### 確認

- 個別確認
  - `lake build DkMath.DHNT.DHNT_Base`
  - `lake build DkMath.RH.EulerZetaLemmas`

- 全体確認
  - `lake build > ./tmp/v429-simpa-check.log 2>&1`
  - `rg "try 'simp' instead of 'simpa'|unnecessarySimpa" ./tmp/v429-simpa-check.log`
  - full build ログ上で `unnecessarySimpa` warning が 0 件であることを確認した。

### `@[reducible]` / `@[implicit_reducible]` の追加検討

これは Lean 4.29 で強く出るようになった「クラス値の `def` は、透明性を明示してほしい」という警告です。

今の警告は例えばこういうものです。

- [UnitNatLayers.lean](/lean/dk_math/DkMath/DHNT/UnitNatLayers.lean#L80) の `piBridge`, `floorBridge` など
- [GEisensteinBridge.lean](/lean/dk_math/DkMath/FLT/GEisensteinBridge.lean#L1394) の `numberTheoryHasKernelFamily_of_hasStep` など
- [CyclotomicPrincipalization.lean](/lean/dk_math/DkMath/FLT/Kummer/CyclotomicPrincipalization.lean#L1828) の `IsCyclotomicExtension_p_as_pow1`

意味としては、

- その `def` の返り値が「class 型」
- なのに普通の `def` のまま
- 透明性属性が付いていない

ので、Lean が

- 型クラス探索
- definitional equality の比較
- implicit 引数の型合わせ

で、その定義をどこまで自動展開してよいか分かりづらい、ということです。

**`@[reducible]` と `@[implicit_reducible]` の違い**

- `@[reducible]`
  - より強いです。
  - 普通の簡約でも積極的に展開されます。
  - ほぼ「略記・別名」として扱いたい定義向けです。
- `@[implicit_reducible]`
  - より弱く、通常の簡約ではあまり展開せず、`instances` 透明性以上で展開されます。
  - class instance や、implicit 引数の型合わせ用の補助定義に向いています。
  - Lean の `instance` コマンドは通常これを自動で付けます。

実務上は、

- 「ただの instance alias / bridge」なら `@[implicit_reducible]`
- 「常に展開されてよい略記」なら `@[reducible]`

を選ぶことが多いです。

今回の警告対象だと、感覚的にはこうです。

- `piBridge` みたいな concrete bridge 値: `@[implicit_reducible]` が第一候補
- `IsCyclotomicExtension_p_as_pow1` みたいな class adapter: `@[implicit_reducible]` か、場合によっては `instance` 化
- 本当に「定義の壁」を残したいなら別ですが、その場合は意図を持って `@[irreducible]` にする、という判断になります

要するに、この warning は「class を返す `def` なのに、Lean に unfold 方針を教えていない」という意味です。

必要なら次に、

1. どの warning に `@[implicit_reducible]` を付けるべきか
2. `def` のままにするか `instance` に変えるべきか

を、今の警告箇所ごとに切り分けます。
