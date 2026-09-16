# FLT3U-001 実装報告: Primitive Cubic Lift Packet

## 実装したもの

`DkMath.FLT.Three.PrimitiveCubicLiftPacket` を追加した。これは
`a ^ 3 + b ^ 3 = c ^ 3` を満たす正の primitive 座標と、
`c ^ 3 - b ^ 3` の primitive prime `q` から、GN degree-three API が直接
消費できる有限 packet を構成する層である。

公開構造 `PrimitiveCubicLiftPacket a b c q` は、座標を
`u = c - b`, `x = b` として次を保持する。

- `q` の素数性、`q ∣ c ^ 3 - b ^ 3`、`q ∤ c - b`
- `Nat.Coprime (c - b) b`
- `q ∣ GN 3 (c - b) b`
- `q ≠ 3`、`3 ∣ q - 1`
- `q ∤ 2 * (c - b) + 3 * b`
- `3 ≤ padicValNat q (GN 3 (c - b) b)`

構成定理 `primitiveCubicLiftPacket_of_counterexample_prime` は、既存の
`PhaseLift` と `GNThreeHenselDepth` の定理を使ってこの packet を構成する。
特に valuation 下界は `NoLift` 仮定からではなく、
`c ^ 3 - b ^ 3 = a ^ 3`、`q ∣ a`、および primitive factorization による
`padicValNat` の輸送から得ている。

各 field の供給元は次のとおりである。

- `hq`, `hqDiff`, `hqBoundary`: constructor の supplied prime witness
- `hcopCoordinates`: `PhaseLift.coprime_cb_of_eq` と
  `Nat.coprime_sub_self_left`
- `hqGN`: `CosmicPetalBridge.prime_dvd_S0_via_cosmic_bridge` と
  `GN_three_sub_eq_S0_nat`
- `hqThree`: `GNThreePrimeArithmetic.three_dvd_GN_three_iff_dvd_boundary`
  による `q = 3` の直接矛盾。新規補題は不要だった
- `hresidue`: `three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three`
- `hderivative`: `prime_not_dvd_cubic_boundary_derivative`
- `hdepth`: `cube_sub_eq_of_add_eq`、`hq.dvd_of_dvd_pow`、
  `padicValNat_lower_bound_of_dvd_d3`、および
  `pow_sub_pow_factor_cosmic_N` / `padicValNat_factorization` と
  `padicValNat.eq_zero_of_not_dvd` による局所 valuation transport

## 境界と非目標

- 新規モジュールは `DkMath.FLT.Main` を import しない。
- `GNThreeHenselDepth` の有限一段 lift API を利用可能な形にしたが、
  `q^k` の再帰、無限 q-adic 構成、strict descent は実装していない。
- Eisenstein 整域、ramified prime の unit 分類、FLT3 の最終定理には進んでいない。
- valuation の「3 の倍数」という追加の exactness lemma は、packet に方程式を
  再格納せず、次段の入力側で必要になった時点に延期した。
- 既存の `GN 3 17 1 = 343` および `7^2 ∣ GN 3 17 1` の回帰事実は変更していない。

## 検証

nested Lean checkout (`lean/dk_math`) で次を実行した。

```text
lake build DkMath.FLT.Three.PrimitiveCubicLiftPacket
```

結果は `Build completed successfully (8698 jobs).` である。新規ソースに
`sorry`、`axiom`、`DkMath.FLT.Main`、完成済み FLT shortcut の import はない。
実際の直接 import は `DkMath.FLT.PhaseLift` と
`DkMath.NumberTheory.GNThreeHenselDepth` の 2 本である。

この段階の判定は Outcome A（packet と GN/Hensel consumer の接続準備完了）であり、
次の strict-descent 段階を開始するものではない。
