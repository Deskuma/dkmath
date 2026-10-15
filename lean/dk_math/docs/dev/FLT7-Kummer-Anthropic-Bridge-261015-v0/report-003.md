# Gate 003 — GN7 と円分 Kummer の共通 source

2026-10-15。HEAD: `8708a54b1eb1a9536b064fd133aef43a32140332`、branch:
`research/FLT7-Kummer-Anthropic-Bridge-261015-v0`。新しい数論定理は追加しない。
既存対応の整理であり、新しい FLT7 制約・下降ではない。**FLT7 OPEN、Gate 003 で停止。**

## CI 入口の配線

- `DkMath/FLT/Seven.lean` に `DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicKummerUnit` を追加。
  通常の `DkMath → DkMath.FLT → DkMath.FLT.Seven` から G1–G3 を参照する。
- `DkMathTest.lean` に既存 `DkMathTest.FLT.Seven.KummerAnthropicBridgeAudit002` を追加。
  任意の合同単数への `degreeSixKummerUnitLemmaAtSeven` の適用を既存テスト入口に接続する。
- `lakefile.toml` で `DkMathTest` 本体も module として登録。
  `.github/workflows/lean_action_ci.yml` の既存 job に、その **入口 module のみ**を対象とする step を追加。
  全 submodule glob の一括起動、Gate-001 inventory、追加 suite は用いない。統合の判定は CI に委ねる。

新しい proof name はない。以下、FLT7 のファイル名は `DkMath/FLT/Seven/` を省略する。
その他の source path は Lean root `lean/dk_math/` からの相対パス。

## 同じ source 上の正確な等式

`ρ : PrimitiveCounterexampleRamifiedProvenance source` を固定し、
`a=ρ.summit.endpointLeft : ℤ`、`b=ρ.summit.endpointRight : ℤ`、`g=a-b`、
`R=SevenCyclotomicDegreeSixInt.Ring`、`π=1-zeta`、`L=directLinearFactor ρ : R` とする。
full norm は `N=SevenCyclotomicDegreeSixInt.cyclotomicNormHom : R →* ℤ`。

```text
GN (R:=ℤ) 7 g b = cyclotomicSeven a b = N(L)
g * N(L) = a^7 - b^7 = ρ.summit.distinguished^7
L = ofReal(g) + π * ofReal(b) = π * directRamifiedQuotient ρ
ofReal(7) = π^6 * ramifiedSevenUnit,   IsUnit ramifiedSevenUnit
```

既存根拠は `DkMath.CosmicFormula.GTail_one_eq_GTailCyclotomicShell`
（`DkMath/Lib/Cosmic/GTailCyclotomic.lean:166`）と
`directCyclotomicNorm_eq_cyclotomicSeven` / `directLinearFactor_norm_product_identity`
（`PrimeTraceOneDirectCyclotomicSecondCaseAudit.lean:108,118`）、
`cyclotomicNormHom_directLinearFactor` / `directLinearFactor_eq_uniformizer_mul_quotient`
（`PrimeTraceOneDirectCyclotomicIdealOwnership.lean:138,65`）。
`directGap_eq_uniformizer_pow`（同:42）は同じ gap を `π^36 * unit^6 * gapRoot^7` とし、
`directLinearFactor_not_mem_ramifiedPrime_sq`（同:113）は endpoint-right の7非可除性を使う。
7 の分岐指数6は `ofReal_seven_eq_uniformizer_pow_six_mul_unit`
（`SevenRamifiedFusionCyclotomicRamifiedPrime.lean:87`）で既証明。

多項式でも `GN (R:=ℤ[X]) 7 (-X) 1 = (Polynomial.cyclotomic 7 ℤ).comp (1-X)`。
GN は commutative semiring 上の `GTail 7 1` の別名であり、負の引数には上の環を使う。
この等式は前記 shell と `GTailCyclotomicHomEval_prime_eq_shell`（同 GTail file:207）の特殊化。
自然数版の norm 対応は `GN_seven_sub_eq_traceOneNorm_negTwo`
（`QuadraticBridge.lean:58`、仮定 `b≤a`）にある。norm 値の一致から異なる carrier を同一視しない。

`DkMath.NumberTheory.prime_uniformBeamHeight_self`
（`DkMath/NumberTheory/BinomialPrimePower.lean:311`）は
`0<k<7 → padicValNat 7 (Nat.choose 7 k)=1` を既に与える。
carry の一般式も `DkMath.NumberTheory.GcdNext.kummer_theorem_for_binomial_coeff`
（`DkMath/NumberTheory/ZsigmondyCyclotomic.lean:572`）にある。
係数の付値は和の付値を無条件には決めない。同じ primitive gap での正確な1回可除性も
`PrimitiveCyclotomicDepth.lean:43` と `CounterexampleRouting.lean:139` にあり、
`N(L)=7*residualRoot^7` と既存 chosen-factor 結果を越える新制約は今回得ていない。

## 残る一つの障害

**π-adic strict-successor construction**：`m : ℕ`、`ε,ε' : Rˣ` として、円分整数上の
`A^7+B^7=ε*(π^(m+1)*C)^7`、`π∤B,C` から、
`A'^7+B'^7=ε'*(π^m*C')^7`、`π∤B',C'` を満たす実際の次解を構成すること。
norm の乗法式や係数の可除性はこの加法的 witness を供給しない。
この状態や後続定理を新たに定義・実装する作業には進んでいない。
