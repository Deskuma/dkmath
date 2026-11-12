/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmer
import DkMath.Lib.NumberTheory.CyclicKummer
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Basic

#print "file: DkMath.Lib.NumberTheory.KummerLocalValuation"

/-!
# 同じ Kummer 方程式の付値と分岐指数

同じ `α^p=b` と同じ素点の上昇について `p v_w(α)=e v_v(b)` を証明する。
実際の有限慣性群が同じ根を固定すれば、その生成性から慣性群は自明となる。
従って e=1 となり、同じ定数の付値は p 可除になる。局所 p 乗性とは区別する。
-/

namespace DkMath.Lib.NumberTheory.KummerLocalValuation

open IsDedekindDomain WithZero CyclicKummer KummerSelmer
open scoped nonZeroDivisors NumberField
set_option backward.isDefEq.respectTransparency false
noncomputable section

section Valuation
variable {R S F M : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    [Field F] [Field M] [Algebra F M]
    [Algebra R F] [IsFractionRing R F] [Algebra R M] [IsScalarTower R F M]
    [Algebra S M] [IsFractionRing S M] [IsScalarTower R S M]
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]

/-- 同じ根と定数の正規化付値に対する、実際の分岐指数を保った等式。 -/
theorem log_pow_eq_ramification_mul (p : ℕ) (α : M) (b : F)
    (hpow : α ^ p = algebraMap F M b) :
    (p : ℤ) * log (w.valuation M α) =
      (v.asIdeal.ramificationIdx' w.asIdeal : ℤ) * log (v.valuation F b) := by
  have he := congrArg (fun x : M => log (w.valuation M x)) hpow
  rw [map_pow, log_pow, ← HeightOneSpectrum.valuation_liesOver M v w, log_pow] at he
  simpa only [nsmul_eq_mul] using he

/-- e=1 なら同じ非零定数の主分数イデアルの指数は p 可除。
根や定数を整数化して取り替える必要はない。 -/
theorem count_dvd_of_ramification_eq_one (p : ℕ) (α : M) (b : Fˣ)
    (hpow : α ^ p = algebraMap F M (b : F))
    (he : v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    (p : ℤ) ∣ FractionalIdeal.count F v (FractionalIdeal.spanSingleton R⁰ (b : F)) := by
  have h := log_pow_eq_ramification_mul v w p α (b : F) hpow
  rw [he, Nat.cast_one, one_mul] at h
  rw [DedekindFractionalValuation.count_spanSingleton v (b : F) b.ne_zero, ← h]
  exact ⟨-log (w.valuation M α), by ring⟩

end Valuation

section NumberField
variable {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M]
    {p : ℕ} (P : Presentation p F M)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 M))
    [w.asIdeal.LiesOver v.asIdeal]

/-- 有限慣性群が生成根を固定すれば、同じ拡大の分岐指数は実際に1となる。 -/
theorem ramification_eq_one_of_inertia_fixes_radical
    (hfix : ∀ σ : M ≃ₐ[F] M, σ ∈ w.asIdeal.inertia (M ≃ₐ[F] M) → σ P.radical = P.radical) :
    v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  let : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  let : IsGaloisGroup (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) F M
  let : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have ht : w.asIdeal.inertia (M ≃ₐ[F] M) = ⊥ := by
    apply bot_unique
    intro σ hσ
    have he : σ = 1 := by
      apply DFunLike.ext
      intro a
      exact DFunLike.congr_fun
        (P.algHom_ext (f := σ.toAlgHom) (g := AlgHom.id F M) (hfix σ hσ)) a
    rw [he]
    exact Subgroup.one_mem ⊥
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[F] M) v.asIdeal w.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (M ≃ₐ[F] M),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot] at hc
  simpa only [ht, Nat.card_unique] using hc.symm

/-- 同じ Kummer 根の有限慣性固定性から、元の同じ定数の付値可除性へ。 -/
theorem count_dvd_of_inertia_fixes_radical (hp : 1 < p)
    (hfix : ∀ σ : M ≃ₐ[F] M, σ ∈ w.asIdeal.inertia (M ≃ₐ[F] M) → σ P.radical = P.radical) :
    (p : ℤ) ∣ FractionalIdeal.count F v
      (FractionalIdeal.spanSingleton (𝓞 F)⁰ P.constant) := by
  exact count_dvd_of_ramification_eq_one v w p P.radical
    (Units.mk0 P.constant (P.constant_ne_zero hp)) P.radical_pow
    (ramification_eq_one_of_inertia_fixes_radical P v w hfix)

end NumberField
end
end DkMath.Lib.NumberTheory.KummerLocalValuation
