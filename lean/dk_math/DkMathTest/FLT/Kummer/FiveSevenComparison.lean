/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveGNDescent
import DkMath.FLT.Seven.SevenRealCubicUnitClass

/-!
# FLT5 実装後の、既存 FLT7 単元判定への限定的な照合

実三次単元の rank が2であることだけを未解決の障害と呼ぶのは不正確。
既存の射影対数の七乗判定から、整数と mod 7 で合同な実三次単元の七乗性を
実際に得られることを確認する。六次の現在の因子単元がこの入力条件を満たす
ことや、新しい FLT7 解と厳密減少は、この検査の結論ではない。
-/

namespace DkMathTest.FLT.Kummer.FiveSevenComparison

open DkMath.FLT.Seven DkMath.FLT.Seven.SevenRealCubicInt

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- 実三次環の整数合同は二成分の射影対数を零にする。 -/
theorem realCubic_primary_unit_log_zero (u : SevenRealCubicIntˣ) (n : ℤ)
    (h : (7 : SevenRealCubicInt) ∣ (u : SevenRealCubicInt) - (n : SevenRealCubicInt)) :
    projectiveLog (Additive.ofMul u) = 0 := by
  obtain ⟨w, hw⟩ := h
  have hs : (7 : ℤ) ∣ (u : SevenRealCubicInt).snd := by
    refine ⟨w.snd, ?_⟩
    have hs := congrArg SevenRealCubicInt.snd hw
    simpa [show (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ from rfl] using hs
  have ht : (7 : ℤ) ∣ (u : SevenRealCubicInt).thd := by
    refine ⟨w.thd, ?_⟩
    have ht := congrArg SevenRealCubicInt.thd hw
    simpa [show (7 : SevenRealCubicInt) = ⟨7, 0, 0⟩ from rfl] using ht
  have hs0 : ((u : SevenRealCubicInt).snd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr hs
  have ht0 : ((u : SevenRealCubicInt).thd : ZMod 7) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mpr ht
  rw [projectiveLog_apply]
  ext <;> simp [unitNilpotentX, unitNilpotentY, thetaLinearModSeven,
    thetaSquareModSeven, hs0, ht0]

/-- 既存の七乗判定を実際に適用する。追加の類数・単元分類仮定を要求しない。 -/
theorem realCubic_primary_unit_seventh (u : SevenRealCubicIntˣ)
    (h : ∃ n : ℤ, (7 : SevenRealCubicInt) ∣ (u : SevenRealCubicInt) - (n : SevenRealCubicInt)) :
    ∃ v : SevenRealCubicIntˣ, u = v ^ 7 := by
  obtain ⟨n, hn⟩ := h
  exact (SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero u).mpr
    (realCubic_primary_unit_log_zero u n hn)

#print axioms realCubic_primary_unit_log_zero
#print axioms realCubic_primary_unit_seventh

run_cmd do
  for n in #[``realCubic_primary_unit_log_zero, ``realCubic_primary_unit_seventh] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {n}"

end DkMathTest.FLT.Kummer.FiveSevenComparison
