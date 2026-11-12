/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.FiniteFieldFrobeniusFixed
import DkMath.Lib.NumberTheory.WeierstrassModelReduction
import DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import DkMath.Lib.NumberTheory.ValuationFrobenius
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard
import DkMath.Lib.Algebra.FiniteFixedQuotient
import Mathlib.Algebra.Algebra.ZMod

#print "file: DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction"

/-!
# 良還元の Frobenius 固定捩れ点を実際の有限体の点へ単射に送る

同じ整数モデル、同じ付値環、同じ幾何学的点の座標を還元する。
Frobenius に固定された座標の剰余は `q` 乗で固定され、`ZMod q` へ降りる。
prime-to-`q` 捩れでの実際の還元単射性により固定捩れ点の濃度を有限体の点数で抑える。
Frobenius 特性方程式、Hasse 評価、有限体上の isogeny の次数は使わない。
-/

namespace DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open EllipticTorsionRepresentation EllipticGoodReductionSeparation EllipticSmoothReduction
open WeierstrassVariableChange WeierstrassModelReduction ValuationInertia ValuationFrobenius

noncomputable section
local instance instDecidableEqFrobeniusFixedReduction {α : Type*} : DecidableEq α := Classical.decEq _

private theorem residueModel_eq (W : WeierstrassCurve ℤ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (W.map (Int.castRingHom A)).map (residue A) = W.baseChange (ResidueField A) := by
  ext <;> simp [WeierstrassCurve.baseChange]

private theorem genericModel_eq (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (W.map (Int.castRingHom A)).map A.subtype = E.baseChange (AlgebraicClosure ℚ) := by
  rw [← hW]
  ext <;> simp [WeierstrassCurve.baseChange]

/-- 同じ整数モデルの実際の還元。剰余体を有限体とは仮定しない。 -/
def integerReduction (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Points E → (W.baseChange (ResidueField A)).toAffine.Point :=
  fun P => pointEquivOfModelEq (residueModel_eq W A)
    (modelReduce A (W.map (Int.castRingHom A)) _ (genericModel_eq E W hW A) P)

theorem integerReduction_zero (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    integerReduction E W hW A 0 = 0 := by
  unfold integerReduction modelReduce
  change pointEquivOfModelEq (residueModel_eq W A)
    (reducePointSmooth (W.map (Int.castRingHom A))
      (pointEquivOfModelEq (genericModel_eq E W hW A).symm 0)) = 0
  rw [map_zero, reducePointSmooth_zero, map_zero]

/-- 有限整点は同じ二座標の剰余へ還元する。 -/
theorem integerReduction_some (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) (A : ValuationSubring (AlgebraicClosure ℚ))
    {x y : AlgebraicClosure ℚ} (h : (E.baseChange (AlgebraicClosure ℚ)).toAffine.Nonsingular x y)
    (hx : x ∈ A) (hy : y ∈ A)
    (hs : (W.baseChange (ResidueField A)).toAffine.Nonsingular
      (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)) :
    integerReduction E W hW A (.some x y h) = .some _ _ hs := by
  let hs' := (residueModel_eq W A).symm ▸ hs
  unfold integerReduction
  rw [modelReduce_some A _ _ _ h hx hs', pointEquivOfModelEq_some]

/-- `q∤n` は、同じ延長付値環で `n` の単元性を供給する。 -/
theorem torsion_index_unit {q n : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    A.valuation (n : AlgebraicClosure ℚ) = 1 := by
  have hnd : ¬ (q : ℤ) ∣ (n : ℤ) := by exact_mod_cast hqn
  simpa only [Int.cast_natCast] using ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
    ((ValuationSubring.mem_nonunits_iff A).mp hA) hnd

/-- 良還元の prime-to-`q` 捩れ上で、同じ実際の還元は単射である。 -/
theorem integerReduction_injOn_torsion (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) {q n : ℕ} (hq : q.Prime)
    (hgood : ¬ (q : ℤ) ∣ W.Δ) (hqn : ¬ q ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    Set.InjOn (integerReduction E W hW A) {P : Points E | n • P = 0} := by
  let : CharP (ResidueField A) q := ValuationPrimeSupport.charP_residueField A hq hA
  let M := W.map (Int.castRingHom A)
  have hΔ : (M.map (residue A)).Δ ≠ 0 := by
    simpa only [M, WeierstrassCurve.map_Δ, Int.coe_castRingHom, map_intCast,
      ne_eq, CharP.intCast_eq_zero_iff (ResidueField A) q] using hgood
  let e := pointEquivOfModelEq (genericModel_eq E W hW A).symm
  intro P hP Q hQ he
  apply e.injective
  apply EllipticSmoothTorsionReduction.reduce_injOn_torsion M (torsion_index_unit hq hqn A hA)
  · exact ⟨hasSmoothReduction_of_good M hΔ _,
      (map_nsmul e n P).symm.trans ((congrArg e hP).trans (map_zero e))⟩
  · exact ⟨hasSmoothReduction_of_good M hΔ _,
      (map_nsmul e n Q).symm.trans ((congrArg e hQ).trans (map_zero e))⟩
  exact (pointEquivOfModelEq (residueModel_eq W A)).injective he

/-- Frobenius 固定元の整座標の剰余は実際に `q` 乗で固定される。 -/
theorem residue_pow_eq_of_frobenius_fixed
    {q : ℕ} (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : IsFrobeniusAt A σ q)
    {x : AlgebraicClosure ℚ} (hx : x ∈ A) (hfix : σ x = x) :
    (residue A (⟨x, hx⟩ : A)) ^ q = residue A (⟨x, hx⟩ : A) := by
  have h := (hσ.smul_residue_eq (residue A (⟨x, hx⟩ : A))).symm
  exact h.trans (congrArg (residue A) (Subtype.ext hfix))

/-- 同じ整数曲線の有限体点を、同じ剰余体へ座標ごとに埋め込む。
環準同型で直接構成し、異なる algebra tower の暗黙の同一視を避ける。 -/
def finitePointEmbedding (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    (W.baseChange (ZMod q)).toAffine.Point → (W.baseChange (ResidueField A)).toAffine.Point := by
  let : Fact q.Prime := ⟨hq⟩
  let : CharP (ResidueField A) q := ValuationPrimeSupport.charP_residueField A hq hA
  let : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
  let f := algebraMap (ZMod q) (ResidueField A)
  have he : (W.baseChange (ZMod q)).map f = W.baseChange (ResidueField A) := by
    ext <;> simp [WeierstrassCurve.baseChange, f]
  exact fun Q => pointEquivOfModelEq he (match Q with
    | .zero => .zero
    | .some u v h => .some (f u) (f v)
        (((W.baseChange (ZMod q)).toAffine.map_nonsingular f.injective u v).mpr h))

theorem finitePointEmbedding_zero (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    finitePointEmbedding W hq A hA 0 = 0 := by
  unfold finitePointEmbedding
  dsimp only
  exact map_zero _

/-- 実際の Frobenius 固定捩れ点の還元は、同じ整数曲線の `ZMod q` 点の像に入る。 -/
theorem exists_finite_point_of_fixed_torsion
    (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) {q n : ℕ} (hq : q.Prime)
    (hgood : ¬ (q : ℤ) ∣ W.Δ) (hqn : ¬ q ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : IsFrobeniusAt A σ q)
    {P : Points E} (hP : n • P = 0) (hfix : pointAction E σ P = P) :
    ∃ Q : (W.baseChange (ZMod q)).toAffine.Point,
      finitePointEmbedding W hq A hA Q = integerReduction E W hW A P := by
  let : Fact q.Prime := ⟨hq⟩
  let : CharP (ResidueField A) q := ValuationPrimeSupport.charP_residueField A hq hA
  let : Algebra (ZMod q) (ResidueField A) := ZMod.algebra _ q
  cases P with
  | zero =>
    exact ⟨0, (finitePointEmbedding_zero W hq A hA).trans (integerReduction_zero E W hW A).symm⟩
  | some x y h =>
    let M := W.map (Int.castRingHom A)
    have hΔ : (M.map (residue A)).Δ ≠ 0 := by
      simpa only [M, WeierstrassCurve.map_Δ, Int.coe_castRingHom, map_intCast,
        ne_eq, CharP.intCast_eq_zero_iff (ResidueField A) q] using hgood
    obtain ⟨hx, hy⟩ := EllipticTorsionValuationIntegrality.torsion_coordinates_mem A M _
      (genericModel_eq E W hW A) (torsion_index_unit hq hqn A hA) h hP
    change Affine.Point.map σ.toAlgHom (.some x y h) = .some x y h at hfix
    rw [Affine.Point.map_some, Affine.Point.some.injEq] at hfix
    have hxp := residue_pow_eq_of_frobenius_fixed A σ hσ hx hfix.1
    have hyp := residue_pow_eq_of_frobenius_fixed A σ hσ hy hfix.2
    obtain ⟨u, hu⟩ := FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq (ZMod q) (ResidueField A)
      (residue A ⟨x, hx⟩) (by simpa only [ZMod.card] using hxp)
    obtain ⟨v, hv⟩ := FiniteFieldFrobeniusFixed.exists_preimage_of_pow_card_eq (ZMod q) (ResidueField A)
      (residue A ⟨y, hy⟩) (by simpa only [ZMod.card] using hyp)
    have hs : (W.baseChange (ResidueField A)).toAffine.Nonsingular
        (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
      rw [← residueModel_eq W A]
      exact nonsingular_residue M hΔ ((genericModel_eq E W hW A).symm ▸ h.1)
    have he : (W.baseChange (ZMod q)).map (algebraMap (ZMod q) (ResidueField A)) =
        W.baseChange (ResidueField A) := by
      ext <;> simp [WeierstrassCurve.baseChange]
    have hb : (W.baseChange (ZMod q)).toAffine.Nonsingular u v :=
      ((W.baseChange (ZMod q)).toAffine.map_nonsingular
        (algebraMap (ZMod q) (ResidueField A)).injective u v).mp (by
          change ((W.baseChange (ZMod q)).map (algebraMap (ZMod q) (ResidueField A))).toAffine.Nonsingular
            (algebraMap (ZMod q) (ResidueField A) u) (algebraMap (ZMod q) (ResidueField A) v)
          rw [he, hu, hv]; exact hs)
    refine ⟨.some u v hb, ?_⟩
    rw [integerReduction_some E W hW A h hx hy hs]
    unfold finitePointEmbedding
    dsimp only
    rw [pointEquivOfModelEq_some]
    simp only [Affine.Point.some.injEq]
    exact ⟨hu, hv⟩

/-- 有限体上の実際の点群の有限性。非特異性は `IsElliptic` から供給する。 -/
theorem finite_points {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve F) [W.IsElliptic] :
    Finite W.toAffine.Point := by
  let : Finite (Option {xy : F × F // W.toAffine.Equation xy.1 xy.2}) := inferInstance
  let : Finite (WithZero {xy : F × F // W.toAffine.Equation xy.1 xy.2}) := inferInstanceAs
    (Finite (Option {xy : F × F // W.toAffine.Equation xy.1 xy.2}))
  exact Finite.of_equiv _ W.toAffine.pointEquiv.symm

/-- Frobenius に固定された実際の `E[n]` の点数は `#E(F_q)` 以下。 -/
theorem card_fixed_torsion_le_finite_points
    (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) {q n : ℕ} (hq : q.Prime)
    (hgood : ¬ (q : ℤ) ∣ W.Δ) (hqn : ¬ q ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : IsFrobeniusAt A σ q) :
    Nat.card (LinearMap.ker (representation E n σ - 1)) ≤
      Nat.card (W.baseChange (ZMod q)).toAffine.Point := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let Wq := W.baseChange (ZMod q)
  let : Wq.IsElliptic := (WeierstrassCurve.isElliptic_iff _).mpr (isUnit_iff_ne_zero.mpr (by
    simpa only [Wq, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, Int.coe_castRingHom, eq_intCast,
      ne_eq, CharP.intCast_eq_zero_iff (ZMod q) q] using hgood))
  let : Finite Wq.toAffine.Point := finite_points Wq
  let T := LinearMap.ker (representation E n σ - 1)
  have hfix (P : T) : pointAction E σ P.val.val = P.val.val := by
    exact congrArg Subtype.val (sub_eq_zero.mp P.property)
  choose f hf using fun P : T => exists_finite_point_of_fixed_torsion E W hW hq hgood hqn A hA
    σ hσ P.val.property (hfix P)
  apply Nat.card_le_card_of_injective f
  intro P Q he
  apply Subtype.ext
  apply Subtype.ext
  apply integerReduction_injOn_torsion E W hW hq hgood hqn A hA P.val.property Q.val.property
  exact (hf P).symm.trans ((congrArg (finitePointEmbedding W hq A hA) he).trans (hf Q))

/-- Frobenius の作用差を位数 `n` の群へ吸収すると、実際の有限体点数は `n` 以上。
特性方程式を仮定せず、核・像の個数と実際の良還元単射を直接組み合わせる。 -/
theorem torsion_index_le_finite_point_count_of_absorbing
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E) {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (hgood : ¬ (q : ℤ) ∣ W.Δ) (hqn : ¬ q ∣ n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : IsFrobeniusAt A σ q)
    (K : AddSubgroup (Points E)) [Finite K] (hK : Nat.card K = n)
    (habs : ∀ P : Points E, n • P = 0 → pointAction E σ P - P ∈ K) :
    n ≤ Nat.card (W.baseChange (ZMod q)).toAffine.Point := by
  let : Finite (Torsion E n) := finite_torsion_of_ne_zero E n hn.ne'
  let φ := (representation E n σ).toAddMonoidHom
  let Kt := K.comap (torsionGroup E n).subtype
  have hKt : Nat.card Kt ≤ n := by
    exact (Nat.card_le_card_of_injective (fun x : Kt => (⟨x.val.val, x.property⟩ : K))
      (fun _ _ he => Subtype.ext (Subtype.ext (congrArg (fun z : K => z.val) he)))).trans_eq hK
  have hlow := DkMath.Lib.Algebra.FiniteFixedQuotient.card_le_card_fixed_mul φ Kt
    (fun P => habs P.val P.property)
  have hup : Nat.card (φ - AddMonoidHom.id (Torsion E n)).ker ≤
      Nat.card (W.baseChange (ZMod q)).toAffine.Point :=
    card_fixed_torsion_le_finite_points E W hW hq hgood hqn A hA σ hσ
  have hsq : n * n ≤ Nat.card (W.baseChange (ZMod q)).toAffine.Point * n := by
    calc
      n * n = Nat.card (Torsion E n) := (pow_two n).symm.trans (card_torsion_sq E n hn.ne').symm
      _ ≤ Nat.card (φ - AddMonoidHom.id (Torsion E n)).ker * Nat.card Kt := hlow
      _ ≤ Nat.card (W.baseChange (ZMod q)).toAffine.Point * n := Nat.mul_le_mul hup hKt
  exact Nat.le_of_mul_le_mul_right hsq hn

end
end DkMath.Lib.NumberTheory.EllipticFrobeniusFixedReduction
