/-
Adapted in part from leanprover-community/flt-regular, commit
b8a5f23ab44a7be9fd49f6e3c831da54573c3c89, FltRegular/CaseI/Statement.lean.
Licensed under Apache-2.0; see RegularKummer/LICENSE.
-/

import DkMath.Lib.NumberTheory.CyclotomicPhaseCoefficientRigidity
import Mathlib.Data.Int.ModEq

#print "file: DkMath.Lib.NumberTheory.SparsePhaseObstruction"

/-!
# 疎な円分位相の障害

全 p 位相より少ない台を持つ配置は、係数0を一つ持つ。
したがって評価値が整数 m で割れるなら、配置全体の係数が m で割れる。
FLT の方程式・正則性・State はこの一般原理に不要である。
4項式への特殊化では、衝突を含めて係数を計算する。
-/

namespace DkMath.Lib.NumberTheory

open Finset
open scoped NumberField

variable {p : ℕ}

/-- 台の濃度が位相数未満なら、可除性を全係数へ戻せる。
台の外の係数が0という仮定を明示し、疎性を数論的非零性と混同しない。 -/
theorem dvd_phase_coefficients_of_support_lt
    {L : Type*} [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (hp : p.Prime) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)
    {f : Fin p → ℤ} {m : ℤ} (s : Finset (Fin p)) (hs : s.card < p)
    (hsupport : ∀ i, i ∉ s → f i = 0)
    (hdiv : (m : 𝓞 L) ∣ ∑ i, f i • ζ ^ (i : ℕ)) : ∀ i, m ∣ f i := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show s.card < (Finset.univ : Finset (Fin p)).card by simpa using hs)
  exact dvd_phase_coefficients_of_zero hp hζ ⟨j, hsupport j hj⟩ hdiv

/-- 4つの位相への整数配置。衝突した位相では係数を加減する。 -/
def fourPhaseCoeff (a b : ℤ) (k₁ k₂ : ℕ) : ℕ → ℤ := fun j ↦
  (if j = 0 then a else 0) + (if j = 1 then b else 0) -
    (if j = k₁ then a else 0) - (if j = k₂ then b else 0)

/-- 配置を円分位相で評価すると、元の4項式に戻る。 -/
theorem sum_fourPhaseCoeff {R : Type*} [Ring R] (hp : 1 < p) (a b : ℤ)
    (k₁ k₂ : Fin p) (ζ : R) :
    ∑ j : Fin p, fourPhaseCoeff a b k₁ k₂ j • ζ ^ (j : ℕ) =
      ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ fourPhaseCoeff a b k₁ k₂ j • ζ ^ j) p]
  simp only [fourPhaseCoeff, add_smul, sub_smul, ite_smul, sum_add_distrib,
    sum_sub_distrib, sum_ite, Finset.range_filter_eq]
  simp [Nat.zero_lt_of_lt hp, hp, Fin.is_lt]

/-- p≥5 なら4項の配置には必ず空の位相がある。 -/
theorem exists_fourPhaseCoeff_eq_zero (hp5 : 5 ≤ p) (a b : ℤ)
    (k₁ k₂ : Fin p) : ∃ j : Fin p, fourPhaseCoeff a b k₁ k₂ j = 0 := by
  let zero : Fin p := ⟨0, by omega⟩
  let one : Fin p := ⟨1, by omega⟩
  let s : Finset (Fin p) := {zero, one, k₁, k₂}
  have hs : s.card ≤ 4 := card_le_four
  have hslt : s.card < Fintype.card (Fin p) := by
    simpa using lt_of_le_of_lt hs hp5
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hslt
  refine ⟨j, ?_⟩
  simp only [s, mem_insert, mem_singleton, not_or] at hj
  have hj0 : (j : ℕ) ≠ 0 := fun h ↦ hj.1 (Fin.ext h)
  have hj1 : (j : ℕ) ≠ 1 := fun h ↦ hj.2.1 (Fin.ext (by simpa [one] using h))
  have hjk₁ : (j : ℕ) ≠ k₁ := fun h ↦ hj.2.2.1 (Fin.ext h)
  have hjk₂ : (j : ℕ) ≠ k₂ := fun h ↦ hj.2.2.2 (Fin.ext h)
  simp [fourPhaseCoeff, hj0, hj1, hjk₁, hjk₂]


/-- 隣接する負側位相を持つ4項式の剛性。
可能な衝突は `p∣a`、`p∣b`、`a≡b` のいずれかへ帰着する。
`a≢b` は実際に必要であり、ここで暗黙に消去してはならない。 -/
theorem four_phase_obstruction
    {L : Type*} [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (hp : p.Prime) (hp5 : 5 ≤ p) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b)
    (hab : ¬ Int.ModEq p a b) (k₁ k₂ : Fin p)
    (hcong : Int.ModEq p (k₂ : ℤ) ((k₁ : ℤ) - 1)) :
    ¬ (p : 𝓞 L) ∣ (a : 𝓞 L) + b * ζ - a * ζ ^ (k₁ : ℕ) - b * ζ ^ (k₂ : ℕ) := by
  intro hdiv
  have key : ((p : ℤ) : 𝓞 L) ∣ ∑ j : Fin p, fourPhaseCoeff a b k₁ k₂ j • ζ ^ (j : ℕ) := by
    rw [sum_fourPhaseCoeff hp.one_lt]
    simpa only [Int.cast_natCast] using hdiv
  have hall := dvd_phase_coefficients_of_zero hp hζ
    (exists_fourPhaseCoeff_eq_zero hp5 a b k₁ k₂) key
  by_cases hk₁ : (k₁ : ℕ) = 0
  · have hk₂ : (k₂ : ℕ) ≠ 1 := by
      intro hk₂
      have hp2z : (p : ℤ) ∣ 2 := by
        rw [← Int.dvd_neg]
        simpa [hk₁, hk₂] using hcong.dvd
      have hp2 : p ∣ 2 := by exact_mod_cast hp2z
      have := Nat.le_of_dvd (by decide : 0 < 2) hp2
      omega
    apply hb
    simpa [fourPhaseCoeff, hk₁, hk₂, Ne.symm hk₂] using hall ⟨1, by omega⟩
  · by_cases hk₂ : (k₂ : ℕ) = 0
    · have habdvd : (p : ℤ) ∣ a - b := by
        simpa [fourPhaseCoeff, hk₁, Ne.symm hk₁, hk₂] using hall ⟨0, by omega⟩
      exact hab (by rw [Int.modEq_iff_dvd]; simpa only [neg_sub] using Int.dvd_neg.mpr habdvd)
    · apply ha
      simpa [fourPhaseCoeff, hk₁, hk₂, Ne.symm hk₁, Ne.symm hk₂] using hall ⟨0, by omega⟩

end DkMath.Lib.NumberTheory
