/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularPrimeFLT
import DkMath.FLT.Kummer.ElevenRegularTransport
import DkMath.FLT.Kummer.ThirteenRegularTransport

#print "file: DkMath.FLT.Kummer.ElevenThirteenFLT"

/-!
# GN–Kummer 経路による FLT11 と FLT13

指数固有のコードは類数1の供給に限る。Case I の共役・係数剛性、Case II の
原始性を保つ整数入口、正深度 State 降下、gcd 原始化はすべて一般核を使う。
したがって、ここでの結論は正深度 State の排除だけでなく標準 FLT 述語である。
-/

namespace DkMath.FLT.Kummer

open scoped NumberField

/-- 11次円分体の類数1を一般正則素数 FLT に渡した、無条件の FLT11。 -/
theorem fermatLastTheoremFor_eleven : FermatLastTheoremFor 11 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  let K := CyclotomicField 11 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 11 ℚ K
  exact fermatLastTheoremFor_of_regular_prime hζ (by decide)
    (by rw [RegularDescent.eleven_classGroup_card_eq_one]; decide)

/-- 同じ共通核へ13次円分体の類数1を渡す、無条件の FLT13。 -/
theorem fermatLastTheoremFor_thirteen : FermatLastTheoremFor 13 := by
  have : Fact (Nat.Prime 13) := ⟨by decide⟩
  let K := CyclotomicField 13 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 13 ℚ K
  exact fermatLastTheoremFor_of_regular_prime hζ (by decide)
    (by rw [RegularDescent.thirteen_classGroup_card_eq_one]; decide)

/-- 整数の符号や共通因子を制限しない FLT11 の入口。 -/
theorem fermatLastTheoremWith_int_eleven : FermatLastTheoremWith ℤ 11 :=
  fermatLastTheoremFor_iff_int.mp fermatLastTheoremFor_eleven

/-- 整数の符号や共通因子を制限しない FLT13 の入口。 -/
theorem fermatLastTheoremWith_int_thirteen : FermatLastTheoremWith ℤ 13 :=
  fermatLastTheoremFor_iff_int.mp fermatLastTheoremFor_thirteen

end DkMath.FLT.Kummer
