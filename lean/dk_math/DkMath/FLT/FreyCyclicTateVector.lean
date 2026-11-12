/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPadicTowerCharacter
import DkMath.Lib.Algebra.PrimePowerTateSequence

#print "file: DkMath.FLT.FreyCyclicTateVector"

/-!
# 同じ Frey 巡回塔の互換生成元と非零 Tate 点列

既存の同じ次段内 p 倍逆像から互換生成元を依存再帰で構成する。
実際の点群の Tate 点列内に同じ塔の加法部分群を構成し、自然に単射で含める。
各成分の位数 p^(n+1) と生成性を証明する。ここでは ℤₚ 加群構造・階数1同型や
Tate 加群全体の階数2、Weil pairing、Frobenius 特性多項式はまだ構成しない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory
open PrimePowerTateSequence
noncomputable section

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
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 第0段の実際の非零生成元。 -/
def residualTateSeed : (tower 0).carrier := (tower 0).coordinates 1

/-- 底の生成元は実際に非零。 -/
theorem residualTateSeed_ne_zero : S.residualTateSeed L hline hcofixed hζ hp5 hclass hbad ≠ 0 := by
  let : Fact (1 < p ^ (0 + 1)) := ⟨by simpa using (Fact.out : p.Prime).one_lt⟩
  intro h
  apply (one_ne_zero : (1 : ZMod (p ^ (0 + 1))) ≠ 0)
  exact (tower 0).coordinates.injective (h.trans (map_zero (tower 0).coordinates).symm)

/-- 同じ直前の点の p 倍逆像を同じ次段内で選ぶ依存再帰。 -/
def residualTateGenerators : (n : ℕ) → (tower n).carrier :=
  Nat.rec (S.residualTateSeed L hline hcofixed hζ hp5 hclass hbad)
    (fun n x => ⟨(S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n x.val x.property).choose,
      (S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n x.val x.property).choose_spec.1⟩)

local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

/-- 再帰で選んだ実際の隣接点の互換性。 -/
theorem residualTateGenerators_step (n : ℕ) : p • (gen (n + 1)).val = (gen n).val :=
  (S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n (gen n).val (gen n).property).choose_spec.2

/-- 第 n 点の p^n 倍は、同じ元の非零生成元。 -/
theorem residualTateGenerators_to_seed (n : ℕ) : p ^ n • (gen n).val = (gen 0).val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_nsmul', S.residualTateGenerators_step L hline hcofixed hζ hp5 hclass hbad, ih]

/-- 選んだ点は各段で正確に最大位数を持つ。独立な生成元 provider は不要。 -/
theorem residualTateGenerators_order (n : ℕ) : addOrderOf (gen n).val = p ^ (n + 1) := by
  apply addOrderOf_eq_prime_pow
  · rw [S.residualTateGenerators_to_seed L hline hcofixed hζ hp5 hclass hbad]
    intro h
    apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
    exact Subtype.ext h
  · exact (tower n).killed _ (gen n).property

/-- 同じ点が同じ段全体を生成する。最大位数と実際の濃度の一致から証明する。 -/
theorem residualTateGenerators_generate (n : ℕ) :
    AddSubgroup.zmultiples (gen n).val = (tower n).carrier := by
  let := (tower n).finite
  apply AddSubgroup.eq_of_le_of_card_ge (AddSubgroup.zmultiples_le.mpr (gen n).property)
  rw [Nat.card_zmultiples, S.residualTateGenerators_order L hline hcofixed hζ hp5 hclass hbad, (tower n).card]

/-- 全幾何学的点への実際の作用を、元の同じ点作用から組み立てる。 -/
def residualPointActionHom : Field.absoluteGaloisGroup ℚ →* AddMonoid.End (Points S.rationalCurve) where
  toFun := pointAction S.rationalCurve
  map_one' := by
    apply AddMonoidHom.ext
    exact pointAction_one S.rationalCurve
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    exact pointAction_mul S.rationalCurve σ τ

/-- 同じ塔の各段に属する互換点列からなる、実際の加法部分群。 -/
def residualCyclicTate : AddSubgroup (Tate p (Points S.rationalCurve)) where
  carrier := {x | ∀ n, evaluation n x ∈ (tower n).carrier}
  zero_mem' := fun n => (tower n).carrier.zero_mem
  add_mem' := fun hx hy n => (tower n).carrier.add_mem (hx n) (hy n)
  neg_mem' := fun hx n => (tower n).carrier.neg_mem (hx n)

local notation "line" => S.residualCyclicTate L hline hcofixed hζ hp5 hclass hbad

/-- 全幾何学的点の同じ Tate 点列群への自然な加法単射。 -/
def residualCyclicTate_inclusion : line →+ Tate p (Points S.rationalCurve) := (line).subtype

theorem residualCyclicTate_inclusion_injective :
    Function.Injective (S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad) :=
  Subtype.val_injective

/-- 同じ点群の成分ごとの作用が、同じ塔の Tate 点列部分群を保つ。 -/
theorem residualCyclicTate_stable (σ : Field.absoluteGaloisGroup ℚ)
    (x : Tate p (Points S.rationalCurve)) (hx : x ∈ line) :
    action S.residualPointActionHom σ x ∈ line :=
  fun n => (tower n).stable σ (evaluation n x) (hx n)

/-- 同じ加法部分群への実際の Galois 作用の制限。 -/
def residualCyclicTateAction : Field.absoluteGaloisGroup ℚ →* AddMonoid.End line where
  toFun σ :=
    { toFun := fun x => ⟨action S.residualPointActionHom σ x.val,
        S.residualCyclicTate_stable L hline hcofixed hζ hp5 hclass hbad σ x.val x.property⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x.val y.val) }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    change action S.residualPointActionHom 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    change action S.residualPointActionHom (σ * τ) x.val =
      action S.residualPointActionHom σ (action S.residualPointActionHom τ x.val)
    rw [map_mul]
    rfl

/-- 自然な包含は同じ Galois 作用と可換。 -/
theorem residualCyclicTate_inclusion_equivariant (σ : Field.absoluteGaloisGroup ℚ) (x : line) :
    S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad
      (S.residualCyclicTateAction L hline hcofixed hζ hp5 hclass hbad σ x) =
    action S.residualPointActionHom σ
      (S.residualCyclicTate_inclusion L hline hcofixed hζ hp5 hclass hbad x) := rfl

/-- 同じ互換生成元からなる実際の Tate 点列。 -/
def residualCyclicTateVector : line :=
  ⟨⟨fun n => (gen n).val, ⟨fun n => (tower n).killed _ (gen n).property,
    S.residualTateGenerators_step L hline hcofixed hζ hp5 hclass hbad⟩⟩,
    fun n => (gen n).property⟩

/-- 構成した点列は非零。第0成分で実際に検出する。 -/
theorem residualCyclicTateVector_ne_zero :
    S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad ≠ 0 := by
  intro h
  apply S.residualTateSeed_ne_zero L hline hcofixed hζ hp5 hclass hbad
  apply Subtype.ext
  exact congrArg (fun x : line => evaluation 0 x.val) h

/-- 一つの互換生成元点列の固定性が、元の p 進指標値1を正確に検出する。 -/
theorem residualCyclicTateVector_fixed_iff (σ : Field.absoluteGaloisGroup ℚ) :
    action S.residualPointActionHom σ
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val =
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val ↔ padicChar σ = 1 := by
  rw [S.residualPadicTowerCharacter_eq_one_iff L hline hcofixed hζ hp5 hclass hbad]
  constructor
  · intro h x hx
    obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    rw [← S.residualTateGenerators_generate L hline hcofixed hζ hp5 hclass hbad n] at hn
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hn
    have he : pointAction S.rationalCurve σ (gen n).val = (gen n).val :=
      congrArg (evaluation n) h
    rw [map_zsmul, he]
  · intro h
    apply PrimePowerTateSequence.ext
    intro n
    exact h (gen n).val
      ((S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr ⟨n, (gen n).property⟩)

/-- 同じ良還元 Frobenius は、構成した一つの Tate 生成元点列を実際に動かす。
この非固定性は矛盾ではなく、以前の非自明な指標の点列上の実現である。 -/
theorem residualCyclicTateVector_frobenius_moved
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell) :
    action S.residualPointActionHom σ
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val ≠
      (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad).val := by
  intro h
  exact S.residualPadicTowerCharacter_frobenius_ne_one L hline hcofixed hζ hp5 hclass hbad
    hell hellp hgood A hA σ hσ
    ((S.residualCyclicTateVector_fixed_iff L hline hcofixed hζ hp5 hclass hbad σ).mp h)

end
end DkMath.FLT.Frey.Source
