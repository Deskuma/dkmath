/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularKummerUnit
import DkMath.FLT.Kummer.RegularStateTransport
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import DkMath.Lib.NumberTheory.CyclotomicElevenPID

#print "file: DkMath.FLT.Kummer.ElevenRegularTransport"

/-!
# 11次の算術 provider と共通 State 降下

指数固有の入力は円分整数環の PID 証明だけである。そこから類数1、類群の
11-torsion-free 性、一般 Kummer 単元 criterion を順に供給する。
最終的な State 排除は既存 `RegularDescent.no_state` の特殊化であり、
このファイルに新しい降下アルゴリズムは実装しない。
一般 Case I や整数反例の向き付けを閉じたという結論は含まない。
-/

namespace DkMath.FLT.Kummer.RegularDescent

open DkMath.Lib.NumberTheory
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {11} ℚ K]

local instance elevenPrime : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Minkowski の素イデアル検査により証明した PID 性から、類数1を供給する。
State の不可能性を先に仮定して類数条件を作る循環はない。 -/
theorem eleven_classGroup_card_eq_one : Fintype.card (ClassGroup (𝓞 K)) = 1 := by
  let : IsPrincipalIdealRing (𝓞 K) := CyclotomicElevenPID.eleven_pid K
  simpa only [Fintype.card_eq_nat_card] using card_classGroup_eq_one (R := 𝓞 K)

/-- 類数1なので、特に類群の 11-torsion は自明である。 -/
theorem eleven_classGroup_torsion_free : classGroupPTorsionFreeAt (𝓞 K) 11 :=
  classGroupPTorsionFreeAt_of_coprime_card (by rw [eleven_classGroup_card_eq_one]; decide)

/-- 11次単元 criterion の実供給。指数固有の単元分類を仮定せず、
類数条件を一般 Kummer 補題に渡して、同じ単元の 11 乗根を復元する。 -/
theorem eleven_kummer_unit_power_criterion : KummerUnitPowerCriterion (𝓞 K) 11 :=
  regular_kummer_unit_power_criterion (K := K) (p := 11) (by decide)
    (by rw [eleven_classGroup_card_eq_one]; decide)

/-- 共通 State の算術条件をすべて供給する。分岐の符号は `λ=1−ζ` に統一する。 -/
theorem eleven_conditions {ζ : K} (hζ : IsPrimitiveRoot ζ 11) :
    Conditions (cyclotomicRamifiedPhase hζ (by decide)) where
  odd := by decide
  three_le := by decide
  ramification := cyclotomicRamifiedPhase_prime_dvd hζ (by decide)
  class_group := eleven_classGroup_torsion_free
  unit_power := eleven_kummer_unit_power_criterion

/-- 正深度の 11次 State は存在しない。遷移・底・帰納法は共通核から得る。
`m ≥ 1` は本質的であり、深度0の State や整数上の一般 Case I は結論しない。 -/
theorem no_eleven_state {ζ : K} (hζ : IsPrimitiveRoot ζ 11) (m : ℕ) (hm : 1 ≤ m) :
    ¬ Nonempty (State (cyclotomicRamifiedPhase hζ (by decide)) m) :=
  no_state (eleven_conditions hζ) m hm

end DkMath.FLT.Kummer.RegularDescent
