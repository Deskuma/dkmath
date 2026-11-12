/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeDepthBridge
import DkMath.FLT.Kummer.IrregularCharacter37

#print "file: DkMathTest.FLT.PrimeDepthTransport"

/-!
# NOTE-008 回帰: 正確な深度、例外素数、実際の類群

付値等式はq=3を許し、単純根のHensel枝では除く。p=2の実在するSourceは
2の付値のp倍性を持つので、p≥5の例外分類を無条件にはできない。
37次のStateや類群については存在を作らず、実際の型の任意の入力で検査する。
-/
namespace PrimeDepthTransportTest
open DkMath.NumberTheory.Legendre FreyC4CentralSeat
open DkMath.FLT.Frey
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example : padicValRat 7 (rationalJ 18 (by decide)) = 9 := by
  exact rationalJ_depth_of_exact_divisibility (by decide) (by decide) (by decide)
    (by decide) (by decide) (k := 3)
example : padicValRat 3 (rationalJ 1 (by decide)) = 3 := by
  exact rationalJ_depth_of_exact_divisibility (by decide) (by decide) (by decide)
    (by decide) (by decide) (k := 1)
-- 18+7³·3=1047 は一段上がり、Q=7⁴·457 となる。
example : padicValRat 7 (rationalJ 1047 (by decide)) = 12 := by
  exact rationalJ_depth_of_exact_divisibility (by decide) (by decide) (by decide)
    (by decide) (by decide) (k := 4)
example : ∃! t : Fin 7, (7 : ℤ) ^ 4 ∣ centralPolynomial.eval (18 + 7 ^ 3 * t.val) :=
  existsUnique_central_next_digit (by decide) (by decide) (by decide) (by decide)
example : (7 : ℤ) ^ 4 ∣ centralPolynomial.eval (18 + 7 ^ 3 * (3 : Fin 7).val) := by
  norm_num [centralPolynomial]
example : (3 : ℤ) ∣ centralPolynomial.derivative.eval 1 := by
  norm_num [centralPolynomial, Polynomial.derivative_add, Polynomial.derivative_pow]
example : ¬ 2 ∣ centralSeat 18 := by decide
example : padicValRat 2 (rationalJ 1 (by decide)) = 6 := by
  have hj : rationalJ 1 (by decide) = 1728 := by rw [rationalJ_eq]; norm_num [centralSeat]
  have hv : padicValNat 2 1728 = 6 := by
    rw [Nat.padicValNat_def]
    exact multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  rw [hj, show (1728 : ℚ) = ((1728 : ℕ) : ℚ) from rfl, padicValRat.of_nat, hv]
  rfl

-- p=2 は古典的なピタゴラス解から実際に構成可能。
def pythagorean : Source 2 where
  a := 4
  b := 3
  c := 5
  a_ne := by decide
  b_ne := by decide
  c_ne := by decide
  coprime := ⟨1, -1, by norm_num⟩
  equation := by norm_num
  normalization := ⟨by norm_num, by norm_num⟩
example : (2 : ℤ) ∣ padicValRat 2 pythagorean.rationalCurve.Δ :=
  pythagorean.exponent_dvd_two_valuation_iff.mpr (by norm_num)
example (S : Source 37) : (padicValRat 2 S.rationalCurve.Δ : ZMod 37) = -8 :=
  S.two_discriminant_cast
example (S : Source 37) {q : ℕ} [Fact q.Prime] :
    (37 : ℤ) ∣ padicValRat q S.rationalCurve.Δ ↔ q ≠ 2 :=
  S.exponent_dvd_valuation_iff_ne_two (by decide)
example (S : Source 37) :
    (padicValRat 37 S.rationalCurve.Δ : ZMod 37) = 0 := by
  simpa using S.discriminant_cast_profile (ℓ := 37)
example (S : Source 37) :
    padicValRat 7 (rationalJ 18 (by decide)) = 3 * (padicValNat 7 (centralSeat 18) : ℤ) ∧
    padicValRat 7 S.rationalCurve.Δ = 74 * (padicValInt 7 (S.a * S.b * S.c) : ℤ) :=
  S.centralSeat_depth_pair (by decide) (by decide) (by decide) (by decide)

open DkMath.Lib.NumberTheory
open DkMath.FLT.Kummer.IrregularPrime37
attribute [local instance] prime37 cyclotomic37
open scoped NumberField DirectSum
example (x : Cyclotomic37CharacterDecomposition.Space Cyclotomic37) : ∑ a : (ZMod 37)ˣ, Cyclotomic37CharacterDecomposition.projector a x = x := Cyclotomic37CharacterDecomposition.sum_projector x
example : Cyclotomic37CharacterDecomposition.projector (K := Cyclotomic37) 1 = 0 := Cyclotomic37CharacterDecomposition.projector_one
example (x : Cyclotomic37CharacterDecomposition.Space Cyclotomic37) (a : (ZMod 37)ˣ) :
    x ∈ Cyclotomic37CharacterDecomposition.component a ↔ Cyclotomic37CharacterDecomposition.underlying x ∈
      DkMath.Lib.NumberTheory.CyclotomicPhaseGalois.characterComponent (Cyclotomic37CharacterDecomposition.character a) :=
  Cyclotomic37CharacterDecomposition.mem_component_iff a x
noncomputable example : Cyclotomic37CharacterDecomposition.Space Cyclotomic37 ≃ₗ[ZMod 37] ⨁ a : (ZMod 37)ˣ, Cyclotomic37CharacterDecomposition.component (K := Cyclotomic37) a :=
  Cyclotomic37CharacterDecomposition.decomposition
example {m : ℕ} (E : DkMath.FLT.Kummer.RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37)) :
    (∀ i, (observe E).phases.obstruction i = 1) ∨
    ((observe E).phases.obstruction 0 = 1 ∧ ∀ i, i ≠ 0 → (observe E).phases.obstruction i ≠ 1) :=
  observe_obstruction_dichotomy E A B hx hy
example {m : ℕ} (E : DkMath.FLT.Kummer.RegularDescent.State phase37 (m + 1))
    (hne : (observe E).phases.obstruction 1 ≠ 1) :
    ∃ a : (ZMod 37)ˣ, a ≠ 1 ∧ Cyclotomic37CharacterDecomposition.projector a (observeVector E 1) ≠ 0 :=
  observe_nontrivial_character E 1 hne
end PrimeDepthTransportTest
