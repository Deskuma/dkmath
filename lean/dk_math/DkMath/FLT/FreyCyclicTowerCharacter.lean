/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalTower
import DkMath.Lib.Algebra.CyclicActionCharacter
import DkMath.FLT.FreyGoodReductionTowerObstruction

#print "file: DkMath.FLT.FreyCyclicTowerCharacter"

/-!
# 同じ巡回捩れ段の実際の単元値指標と両立性

段の安定性から点ごとの恒等性を仮定せず、実際の Galois 作用の scalar を構成する。
包含された段の指標は剰余写像で両立する。固定性は指標値1と同値である。
良還元点数による上界には、その具体的な Frobenius 指標値1を明示入力に残す。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation EllipticFrobeniusFixedReduction
open DkMath.Lib.RepresentationTheory
noncomputable section

variable {p : ℕ} [Fact p.Prime] {S : Source p}
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 同じ有限巡回段の座標。値域は位数 p^(n+1) の環である。 -/
def ResidualCyclicStage.coordinates (T : S.ResidualCyclicStage L n) :
    ZMod (p ^ (n + 1)) ≃+ T.carrier :=
  zmodAddEquivOfGenerator T.cyclic.exists_generator.choose_spec T.card

/-- 同じ段への、元の絶対 Galois 点作用の制限。 -/
def ResidualCyclicStage.action (T : S.ResidualCyclicStage L n) :
    Field.absoluteGaloisGroup ℚ →* AddMonoid.End T.carrier where
  toFun σ :=
    { toFun := fun x => ⟨pointAction S.rationalCurve σ x, T.stable σ x x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x.val y.val) }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact pointAction_one S.rationalCurve x.val
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact pointAction_mul S.rationalCurve σ τ x.val

/-- 同じ巡回段への実際の作用を記述する単元値指標。恒等性は仮定しない。 -/
def ResidualCyclicStage.character (T : S.ResidualCyclicStage L n) :
    Field.absoluteGaloisGroup ℚ →* (ZMod (p ^ (n + 1)))ˣ :=
  CyclicActionCharacter.character T.coordinates T.action

/-- 点ごとの scalar 公式。単なる群の集合的安定性より強い内容を構成から証明する。 -/
theorem ResidualCyclicStage.character_spec (T : S.ResidualCyclicStage L n)
    (σ : Field.absoluteGaloisGroup ℚ) (x : Points S.rationalCurve) (hx : x ∈ T.carrier) :
    pointAction S.rationalCurve σ x = (T.character σ : ZMod (p ^ (n + 1))).val • x := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have h := CyclicActionCharacter.action_eq_nsmul T.coordinates T.action σ (⟨x, hx⟩ : T.carrier)
  have he := congrArg T.carrier.subtype h
  rw [map_nsmul] at he
  exact he

/-- 指標値1と同じ段の全点固定は同値。安定性だけから値1を結論しない。 -/
theorem ResidualCyclicStage.character_eq_one_iff (T : S.ResidualCyclicStage L n)
    (σ : Field.absoluteGaloisGroup ℚ) :
    T.character σ = 1 ↔ ∀ x ∈ T.carrier, pointAction S.rationalCurve σ x = x := by
  rw [character, CyclicActionCharacter.character_eq_one_iff]
  constructor
  · intro h x hx
    exact congrArg T.carrier.subtype (h ⟨x, hx⟩)
  · intro h x
    exact Subtype.ext (h x.val x.property)

/-- 既存の実際の全捩れ表現の開核を含むので、この同じ指標も開核を持つ。 -/
theorem ResidualCyclicStage.character_kernel_isOpen (T : S.ResidualCyclicStage L n) :
    IsOpen (T.character.ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  apply Subgroup.isOpen_mono (H₁ := representationKernel S.rationalCurve (p ^ (n + 1))) _
    (representationKernel_isOpen_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  intro σ hσ
  change T.character σ = 1
  apply (T.character_eq_one_iff σ).mpr
  intro x hx
  change representation S.rationalCurve (p ^ (n + 1)) σ = 1 at hσ
  have he : representation S.rationalCurve (p ^ (n + 1)) σ ⟨x, T.killed x hx⟩ = ⟨x, T.killed x hx⟩ := by
    rw [hσ]
    rfl
  exact congrArg (fun z : Torsion S.rationalCurve (p ^ (n + 1)) => z.val) he

/-- 包含された同じ巡回段の作用指標は、標準の剰余写像で両立する。 -/
theorem ResidualCyclicStage.character_compatible (T : S.ResidualCyclicStage L n)
    {m : ℕ} (U : S.ResidualCyclicStage L m) (hnm : n ≤ m) (hTU : T.carrier ≤ U.carrier)
    (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.add_le_add_right hnm 1))
      (ZMod (p ^ (n + 1)))).toMonoidHom (U.character σ) = T.character σ := by
  let : NeZero (p ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have he : (T.character σ : ZMod (p ^ (n + 1))) = (U.character σ : ZMod (p ^ (m + 1))).val := by
    apply CyclicActionCharacter.character_eq_natCast_of_action T.coordinates T.action
    intro x
    apply Subtype.ext
    change T.carrier.subtype (T.action σ x) = T.carrier.subtype ((U.character σ : ZMod (p ^ (m + 1))).val • x)
    rw [map_nsmul]
    exact U.character_spec σ x.val (hTU x.property)
  apply Units.ext
  change ZMod.castHom _ _ (U.character σ : ZMod (p ^ (m + 1))) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact he.symm

/-- 同じ段の指標の mod p 還元は、元の同じ Cofixed 直線の円分指標。 -/
theorem ResidualCyclicStage.character_mod_prime (T : S.ResidualCyclicStage L n)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (dvd_pow_self p (by omega : n + 1 ≠ 0)) (ZMod p)).toMonoidHom
      (T.character σ) = CyclotomicRootModule.cyclotomicCharacter p σ := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  let B := pointSubgroup S.rationalCurve p L
  let e : ZMod p ≃+ B := zmodAddEquivOfGenerator
    (isAddCyclic_pointSubgroup S.rationalCurve p L hline).exists_generator.choose_spec
    (card_pointSubgroup S.rationalCurve p L hline)
  let a : Field.absoluteGaloisGroup ℚ →* AddMonoid.End B :=
    (S.residualCyclicStageZero L hline hcofixed).action
  have hT : (CyclicActionCharacter.character e a σ : ZMod p) =
      (T.character σ : ZMod (p ^ (n + 1))).val := by
    apply CyclicActionCharacter.character_eq_natCast_of_action e a
    intro x
    apply Subtype.ext
    change B.subtype (a σ x) = B.subtype ((T.character σ : ZMod (p ^ (n + 1))).val • x)
    rw [map_nsmul]
    exact T.character_spec σ x.val (T.base x.property)
  have hc : (CyclicActionCharacter.character e a σ : ZMod p) =
      (CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p) := by
    rw [← ZMod.natCast_zmod_val (CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p)]
    apply CyclicActionCharacter.character_eq_natCast_of_action e a
    intro x
    apply Subtype.ext
    change B.subtype (a σ x) = B.subtype ((CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p).val • x)
    rw [map_nsmul]
    exact S.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul L hline hcofixed σ x.property
  apply Units.ext
  change ZMod.castHom _ _ (T.character σ : ZMod (p ^ (n + 1))) = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact hT.symm.trans hc

/-- 良還元上界の一つの十分条件を、同じ Frobenius の具体的な指標値1として露出する。
この値1自体を証明した定理ではなく、商上の作用差吸収とも別の条件である。 -/
theorem ResidualCyclicStage.card_le_good_points_of_character_one (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)
    (hchar : T.character σ = 1) : p ^ (n + 1) ≤ S.goodReductionPointCount ell := by
  let M := p ^ (n + 1)
  let : Finite (Torsion S.rationalCurve M) :=
    finite_torsion_of_ne_zero S.rationalCurve M (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let V := LinearMap.ker (representation S.rationalCurve M σ - 1)
  let f : T.carrier → V := fun x =>
    ⟨⟨x.val, T.killed x.val x.property⟩, by
      change representation S.rationalCurve M σ ⟨x.val, T.killed x.val x.property⟩ -
        ⟨x.val, T.killed x.val x.property⟩ = 0
      apply sub_eq_zero.mpr
      apply Subtype.ext
      exact (T.character_eq_one_iff σ).mp hchar x.val x.property⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : V => z.val.val) h
  have hqn : ¬ ell ∣ M := fun h =>
    hellp ((Nat.prime_dvd_prime_iff_eq hell (Fact.out : p.Prime)).mp (hell.dvd_of_dvd_pow h))
  calc
    p ^ (n + 1) = Nat.card T.carrier := T.card.symm
    _ ≤ Nat.card V := Nat.card_le_card_of_injective f hf
    _ ≤ S.goodReductionPointCount ell :=
      card_fixed_torsion_le_finite_points S.rationalCurve S.curve S.curve_map hell hgood hqn A hA σ hσ

end

section Tower

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad

/-- 構成済みの同じ塔の各段を表す、実際の有限単元値指標族。 -/
noncomputable def residualCyclicTowerCharacter (n : ℕ) : Field.absoluteGaloisGroup ℚ →* (ZMod (p ^ (n + 1)))ˣ :=
  (tower n).character

/-- 指標族の隣接段の両立性。各段の座標を独立に選んでも成り立つ。 -/
theorem residualCyclicTowerCharacter_compatible (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1)))).toMonoidHom
        (S.residualCyclicTowerCharacter L hline hcofixed hζ hp5 hclass hbad (n + 1) σ) =
      S.residualCyclicTowerCharacter L hline hcofixed hζ hp5 hclass hbad n σ :=
  (tower n).character_compatible (tower (n + 1)) (Nat.le_succ n)
    (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1 σ

end Tower
end DkMath.FLT.Frey.Source
