/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNCaseIContract
import DkMath.FLT.Kummer.CaseIConjugationPacket

#print "file: DkMath.FLT.Kummer.GNCaseIObstruction"

/-!
# GN 因子抽出と古典的 Kummer 供給の既定アダプタ

GN 側は `GN_kummer_structure_of_first_case` によって同じ因子の単元倍 p 乗表示を
作る。古典的な CM 共役・単元比の証明は `classical_factor_packet_provider` が担う。
終端の非合同化と位相係数剛性は `GNCaseIContract` の供給非依存な定理である。

以前の整数ノルムの結論 `GN_p=t^p` だけから矛盾を導くものではない。
GN による代替証明を開発するときは、古典的供給を直接改変せず、固定した
`FactorPacketProvider` または `SolutionPacketProvider` の別の証明を渡す。
既存の公開定理の名前・引数・結論は維持する。
-/

namespace DkMath.FLT.Kummer

open scoped NumberField

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {ζ : K}

/-- 既存 GN 因子抽出と古典的共役を合成した既定の方程式単位の供給。
正則性は供給側で消費され、Packet の固定型に新たな仮定を加えない。 -/
theorem classical_solution_packet_provider (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    CaseIConjugation.SolutionPacketProvider (p := p) hζ.toInteger :=
  solution_packet_provider_using hζ hp5 hreg
    (CaseIConjugation.classical_factor_packet_provider hp5 hζ.toInteger_isPrimitiveRoot)

/-- GN の i=1 因子を古典的共役 packet に変換する互換入口。
同じ因子・単元・根を運ぶ実処理は `first_case_conjugation_packet_using` に置く。 -/
theorem first_case_conjugation_packet (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) (hcop : IsCoprime a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    Nonempty (CaseIConjugation.Packet (p := p) hζ.toInteger a b) :=
  classical_solution_packet_provider hζ hp5 hreg heq hcop hfirst

/-- 非合同な原始的 Case I の既定入口。古典的供給を中立な4項障害へ渡す。 -/
theorem not_int_solution_caseI_of_not_modEq (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (hcop : IsCoprime a b) (hab : ¬ Int.ModEq p a b)
    (hfirst : ¬ (p : ℤ) ∣ a * b * c) : a ^ p + b ^ p ≠ c ^ p :=
  not_int_solution_caseI_of_not_modEq_using hζ hp5
    (classical_solution_packet_provider hζ hp5 hreg) hcop hab hfirst

/-- p≥5 の一般 Case I の既定入口。整数の原始性と類数条件を仮定する。
Case II 用の単元 p 乗 criterion や State 0 の不存在は仮定しない。 -/
theorem not_int_solution_caseI
    (hζ : IsPrimitiveRoot ζ p)
    (hp5 : 5 ≤ p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (hcop : IsCoprime a b) (hfirst : ¬ (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p :=
  not_int_solution_caseI_using hζ hp5 (classical_solution_packet_provider hζ hp5 hreg) hcop hfirst

end DkMath.FLT.Kummer
