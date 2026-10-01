# FLT7TC-005R48 — Common-prime residue-one strengthening

## 実装結果

`instruction-054.md` の指定に従い、共通素因子に対する `q % 7 = 1` bridge を
独立した production module に昇格した。

追加した module:

`DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCommonPrimeResidueOne.lean`

公開した endpoint は次の通りである。

- `quotient_eval_mod_seven_one`
- `common_norm_prime_mod_seven_one`
- `directOrbitCommonPrime_q_mod_seven_one`
- `directOrbitCommonFactor_c_ge_29`

既存の `common_norm_prime_mod_seven` は変更していない。

## 実装した証明内容

- `quotient_eval_mod_seven_one` では、七乗差の因数分解、`IsCoprime` による
  二つの評価値の非零性、評価値の不等性から、商の単元が位数 7 を持つことを
  示した。
- 有限体の乗法群の位数から `7 ∣ q - 1` を得て、`q % 7 = 1` を導出した。
- `common_norm_prime_mod_seven_one` では、既存の square-refinement と
  完全分解した素イデアルの residue-field equivalence を使い、商側の
  quotient/root pair に neutral lemma を適用した。
- `directOrbitCommonPrime_q_mod_seven_one` では、canonical common-factor
  endpoint の `q ∣ h.c` を上記 bridge に接続した。
- さらに `q % 7 = 1` の素数は `q < 29` では存在しないことを有限ケース分けで
  検証し、`1 < h.c` から `29 ≤ h.c` を得る補題を追加した。

校正値排除、14乗積、cyclic product、degree-six phase、reciprocity、successor/
descent、`C > 1` の矛盾、FLT7 の終端定理は今回の module に追加していない。
したがって、`q = 379` の局所 Kummer calibration は依然として可能であり、
この R48 endpoint 単独では一般 FLT7 の閉包を主張しない。

## facade / client / audit

`DkMath/FLT/Seven.lean` に production module の import を追加した。

追加した client:

- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneApi.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneAxiom.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneR48Scratch.lean`

API client は facade 経由の三つの endpoint と canonical application を確認し、
axiom client は production の三つの endpoint を監査した。R48 の新規 theorem の
axiom 出力に `sorryAx` は含まれず、依存公理は
`[propext, Classical.choice, Quot.sound]` だった。facade build の出力には既存の
依存 module `DkMath.FLT.Kummer.CyclotomicPrincipalization` に由来する
`declaration uses sorry` 警告が再表示されたが、R48 の axiom audit には含まれていない。

## 検証結果

Lean は並列実行せず、次の順で実行し、すべて exit 0 だった。

1. `lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeResidueOne`
2. `lake build DkMath.FLT.Seven`
3. `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneApi`
4. `lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneAxiom`
5. `lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneR48Scratch.lean`
6. 新規 source/client/scratch に対する `sorry`, `admit`, `axiom`,
   `native_decide` の placeholder scan — 該当なし。
7. `git diff --check` および新規ファイルの whitespace check — 問題なし。
