/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldCompletionComparison
import DkMath.Lib.NumberTheory.CyclicKummer

#print "file: DkMath.Lib.NumberTheory.KummerLocalPower"

/-!
# 同じ Kummer 根の完備体への降下と同じ定数の局所冪

同じ素点で e=f=1 を満たす場合、自然な完備化写像の全射性で同じ根の像を降ろす。
得られる根の冪が同じ定数の像となることを、可換な埋め込みと単射性で証明する。
別の根や別の定数へ取り替えない。単元還元 b=εc^p への移送も同じ ε を保つ。
-/

namespace DkMath.Lib.NumberTheory.KummerLocalPower

open IsDedekindDomain CyclicKummer NumberFieldCompletionComparison
open scoped NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    {p : ℕ} (P : Presentation p F M)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal]

/-- 同じ根の像を底の完備体の単元へ降ろす。冪等式と上の根との一致をともに返す。 -/
theorem exists_unit_pow_constant_of_ef_eq_one (hp : 1 < p)
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hf : w.asIdeal.inertiaDeg (𝓞 F) = 1) :
    ∃ t : (v.adicCompletion F)ˣ,
      completionMap v w (t : v.adicCompletion F) = algebraMap M (w.adicCompletion M) P.radical ∧
      (t : v.adicCompletion F) ^ p = algebraMap F (v.adicCompletion F) P.constant := by
  obtain ⟨t, ht⟩ := (completionMap_bijective_of_ef_eq_one v w he hf).surjective
    (algebraMap M (w.adicCompletion M) P.radical)
  have ht0 : t ≠ 0 := by
    intro h0
    apply P.radical_ne_zero hp
    apply (algebraMap M (w.adicCompletion M)).injective
    rw [← ht, h0, map_zero, map_zero]
  refine ⟨Units.mk0 t ht0, ht, ?_⟩
  apply (completionMap v w).injective
  change completionMap v w (t ^ p) = completionMap v w (algebraMap F (v.adicCompletion F) P.constant)
  rw [map_pow, ht, ← map_pow, P.radical_pow, completionMap_algebraMap]

omit [NumberField F] in
/-- b=εc^p と同じ局所根 t^p=b から、同じ ε の局所根 t/c を得る。
この代数的移送そのものは整数性・Selmer 所属・類群消滅を要求しない。 -/
theorem unit_pow_of_constant_pow {E : Type*} [Field E] (φ : F →+* E)
    {b ε : F} (c : Fˣ) (t : Eˣ)
    (hdecomp : b = ε * (c : F) ^ p) (hpow : (t : E) ^ p = φ b) :
    ((t / Units.map φ.toMonoidHom c : Eˣ) : E) ^ p = φ ε := by
  rw [Units.val_div_eq_div_val]
  change ((t : E) / φ (c : F)) ^ p = φ ε
  rw [div_pow, hpow, hdecomp, map_mul, map_pow]
  exact mul_div_cancel_right₀ _ (pow_ne_zero _ ((map_ne_zero φ).mpr c.ne_zero))

end
end DkMath.Lib.NumberTheory.KummerLocalPower
