/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveGNDescent
import DkMath.FLT.Kummer.SevenPrimaryNorm

/-!
# FLT5 実装後の、既存 FLT7 単元判定への限定的な照合

実三次単元の rank が2であることだけを未解決の障害と呼ぶのは不正確。
既存の射影対数の七乗判定から、整数と mod 7 で合同な実三次単元の七乗性を
実際に得られることを確認する。六次の現在の因子単元がこの入力条件を満たす
ことや、新しい FLT7 解と厳密減少は、この検査の結論ではない。
-/

namespace DkMathTest.FLT.Kummer.FiveSevenComparison

open DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubicInt

open DkMath.FLT.Kummer.SevenPrimaryNorm

#print axioms realCubic_primary_unit_log_zero
#print axioms realCubic_primary_unit_seventh

run_cmd do
  for n in #[``realCubic_primary_unit_log_zero, ``realCubic_primary_unit_seventh] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"

end DkMathTest.FLT.Kummer.FiveSevenComparison
