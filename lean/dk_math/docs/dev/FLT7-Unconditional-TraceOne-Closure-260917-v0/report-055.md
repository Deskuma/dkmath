# FLT7TC-005R49 — Post-Astra sharpened branch packet

## 実装結果

`instruction-055.md` の consolidation checkpoint として、R39–R48 の
既存 public API を一つの provenance-preserving branch surface に束ねた。

追加した production module:

`DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicSharpenedBranch.lean`

追加した packet:

- `DirectOrbitTrivialCommonFactorSharpenedPacket`
- `DirectOrbitNontrivialCommonFactorSharpenedPacket`

追加した主要 theorem:

- `directOrbitTrivialCommonFactor_exists_nontrivial_7pow9_correction`
- `directOrbitTrivialCommonFactor_correction_norm_one`
- `directOrbitTrivialCommonFactor_correction_not_torsion`
- `directOrbitCommonFactor_large_residue_one_support`
- `directOrbitCommonFactor_large_residue_one_height`
- `directOrbit_sharpened_common_factor_dichotomy`

`DkMath/FLT/Seven.lean` に production module の facade import を追加した。

## C=1 branch

- 既存の `gap_scalar_unit_of_c_eq_one` と
  `quotient_scalar_unit_of_c_eq_one` から `eta`, `xi` を取得した。
- 既存の global seventh correction と theta-linear closure から `v` を取得した。
- `directOrbitPairedDeepJet_current_depth9_wrapper` から
  `v = t^(7^8)` と `W = rho * t^(7^9)` を取得した。
- R47 の `directOrbitDeepJetWUnit_ne_calibration` により、直接
  `t^(7^9) ≠ 1` を導出した。
- `norm W = 1`, `norm rho = 1`、unit norm が `±1` であること、`7^9` が奇数で
  あることから、`norm t = 1` を短い補題として実装した。
- `modelUnitsEquivRingOfIntegers` と
  `NumberField.Units.torsion_eq_one_or_neg_one_of_odd_finrank` を使い、
  norm-one から `-1` を排除し、`t^(7^9) ≠ 1` と合わせて transported unit が
  torsion subgroup に属さないことを示した。

## C>1 branch と dichotomy

- R48 の `directOrbitCommonFactor_c_ge_29` と
  `directOrbitCommonPrime_q_mod_seven_one` を薄く接続し、
  `29 ≤ h.c ∧ ∀ q, q.Prime → q ∣ h.c → q % 7 = 1` を追加した。
- 既存の `h.height : h.c * h.u^5 < h.v` と `29 ≤ h.c` から、
  `29 * h.u^5 < h.v` を算術的に導出した。
- `h.c = 1` と `1 < h.c` を `h.c_pos` から分岐し、二つの packet の
  `Nonempty` dichotomy を構成した。source/r/p/h は全 theorem で保持している。

## 境界と deferred audit

この checkpoint では新しい矛盾、alpha / `1 + alpha` による生成元主張、
fundamental-unit basis、Thue completeness、`q % 28 = 1`、reciprocity、
新規 Hensel depth、successor/descent、FLT7 conclusion を追加していない。
cyclic product `R * sigma(R) * sigma^2(R) = -1` も使用していない。
14乗条件の oriented Galois-shifted prime への transport が未実装のため、
character/mod-28 route は意図的に保留した。

## facade / API / axiom / scratch

追加した client:

- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSharpenedBranchApi.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSharpenedBranchAxiom.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSharpenedBranchR49Scratch.lean`

API client は C=1 correction と final dichotomy の facade 経由 application を確認した。
axiom audit は C=1 correction、C>1 support、final dichotomy、non-torsion theorem
を確認し、すべての依存公理は `[propext, Classical.choice, Quot.sound]`。
新規 R49 theorem に `sorryAx` はない。

## 検証結果

Lean は並列実行せず、次を順番に実行し、すべて exit 0 だった。

1. `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSharpenedBranch`
2. `lake build DkMath.FLT.Seven`
3. `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSharpenedBranchApi`
4. `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicSharpenedBranchAxiom`
5. `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicSharpenedBranchR49Scratch.lean`
6. 新規 R49 source/client/scratch に対する `sorry`, `admit`, `axiom`,
   `unsafe`, `native_decide` の placeholder scan — 該当なし。
7. `git diff --check` と新規ファイルの whitespace check — 問題なし。

R49 は、必須 dichotomy と任意指定された norm/torsion/height refinement が
すべて green のため **Outcome A** とした。
