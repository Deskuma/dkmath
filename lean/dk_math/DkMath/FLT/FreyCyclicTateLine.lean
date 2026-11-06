/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateVector
import DkMath.Lib.Algebra.PrimePowerTateModule

#print "file: DkMath.FLT.FreyCyclicTateLine"

/-!
# 同じ Frey Tate 点列の標準 p 進直線

元の点列への標準 scalar を制限する。互換生成元から各成分の係数を読み、
係数の隣接両立性と実際の Cauchy 極限から、a↦a•v の全単射を証明する。
これにより実際の ℤₚ 線形同型と線形包含を得る。hclass と全段 hbad は保持する。
-/

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
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
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad
local notation "vec" => S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad
local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 以前の同じ部分群を、全点列の標準 scalar に閉じた部分加群として公開する。 -/
def residualCyclicTateLine : Submodule ℤ_[p] (Tate p (Points S.rationalCurve)) where
  __ := S.residualCyclicTate L hline hcofixed hζ hp5 hclass hbad
  smul_mem' a x hx n := by
    rw [evaluation_smul]
    exact (tower n).carrier.nsmul_mem (hx n) _

local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad

/-- 同じ全幾何学的点群の Tate 加群への自然な p 進線形包含。 -/
def residualCyclicTateLine_inclusion : line →ₗ[ℤ_[p]] Tate p (Points S.rationalCurve) := (line).subtype

theorem residualCyclicTateLine_inclusion_injective :
    Function.Injective (S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad) :=
  Subtype.val_injective

/-- 同じ互換生成元を1の像に持つ各段の巡回座標。 -/
def residualTateGeneratorCoordinates (n : ℕ) : ZMod (p ^ (n + 1)) ≃+ (tower n).carrier := by
  let := (tower n).finite
  have ho : addOrderOf (gen n) = p ^ (n + 1) :=
    (addOrderOf_injective (tower n).carrier.subtype Subtype.val_injective (gen n)).symm.trans
      (S.residualTateGenerators_order L hline hcofixed hζ hp5 hclass hbad n)
  have ht : AddSubgroup.zmultiples (gen n) = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, ho, (tower n).card])
  exact zmodAddEquivOfGenerator (fun x => ht ▸ AddSubgroup.mem_top x) (tower n).card

local notation "coords" => S.residualTateGeneratorCoordinates L hline hcofixed hζ hp5 hclass hbad

/-- 座標の自然数上の値は、元の同じ生成元の自然数倍。 -/
theorem residualTateGeneratorCoordinates_nat (n k : ℕ) :
    (coords n (k : ZMod (p ^ (n + 1)))).val = k • (gen n).val := by
  have h1 : coords n 1 = gen n := zmodAddEquivOfGenerator_apply_one _ (tower n).card
  have h := congrArg (tower n).carrier.subtype (map_nsmul (coords n) k (1 : ZMod (p ^ (n + 1))))
  simp only [nsmul_eq_mul, mul_one, h1, map_nsmul] at h
  change (coords n (k : ZMod (p ^ (n + 1)))).val = k • (gen n).val at h
  exact h

/-- 任意の同じ点列の第 n 成分を生成元座標で読む。 -/
def residualTateCoefficient (x : line) (n : ℕ) : ZMod (p ^ (n + 1)) :=
  (coords n).symm ⟨evaluation n x.val, x.property n⟩

local notation "coeff" => S.residualTateCoefficient L hline hcofixed hζ hp5 hclass hbad

/-- 第 n 成分は、実際に読み取った同じ係数と同じ生成元の積。 -/
theorem residualTateCoefficient_spec (x : line) (n : ℕ) :
    evaluation n x.val = (coeff x n).val • (gen n).val := by
  have h := S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad n (coeff x n).val
  rw [ZMod.natCast_zmod_val] at h
  simpa only [residualTateCoefficient, AddEquiv.apply_symm_apply] using h

/-- 点列と生成元の両方の p 倍互換性から、係数の標準剰余両立性を導く。 -/
theorem residualTateCoefficient_compatible (x : line) (n : ℕ) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
      (coeff x (n + 1)) = coeff x n := by
  apply (coords n).injective
  apply Subtype.ext
  rw [ZMod.castHom_apply, ZMod.cast_eq_val,
    S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad]
  change (coeff x (n + 1)).val • (gen n).val =
    ((coords n) ((coords n).symm ⟨evaluation n x.val, x.property n⟩)).val
  rw [AddEquiv.apply_symm_apply]
  rw [← S.residualTateGenerators_step L hline hcofixed hζ hp5 hclass hbad n,
    smul_comm, ← S.residualTateCoefficient_spec L hline hcofixed hζ hp5 hclass hbad]
  exact compatible x.val n

/-- 同じ生成元点列による実際の p 進線形写像 a↦a•v。 -/
def residualCyclicTateParametrization : ℤ_[p] →ₗ[ℤ_[p]] line where
  toFun a := a • (⟨(vec).val, (vec).property⟩ : line)
  map_add' a b := add_smul a b _
  map_smul' a b := mul_smul a b _

local notation "param" => S.residualCyclicTateParametrization L hline hcofixed hζ hp5 hclass hbad

/-- 各生成元の巡回座標と全 p 冪剰余の外延性から単射。 -/
theorem residualCyclicTateParametrization_injective : Function.Injective param := by
  intro a b h
  apply PadicCharacterLimit.ext_positive
  intro n
  apply (coords n).injective
  apply Subtype.ext
  have he := congrArg (fun x : line => evaluation n x.val) h
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow (n + 1) a),
    ← ZMod.natCast_zmod_val (PadicInt.toZModPow (n + 1) b)]
  rw [S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad,
    S.residualTateGeneratorCoordinates_nat L hline hcofixed hζ hp5 hclass hbad]
  exact he

/-- 実際の互換係数列の Cauchy 極限から全射。極限や全射性の provider は不要。 -/
theorem residualCyclicTateParametrization_surjective : Function.Surjective param := by
  intro x
  let a := liftResidues (coeff x) (S.residualTateCoefficient_compatible L hline hcofixed hζ hp5 hclass hbad x)
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply PrimePowerTateSequence.ext
  intro n
  change (PadicInt.toZModPow (n + 1) a).val • (gen n).val = evaluation n x.val
  rw [liftResidues_mod]
  exact (S.residualTateCoefficient_spec L hline hcofixed hζ hp5 hclass hbad x n).symm

/-- 同じ Tate 直線の実際の階数1線形同型。標準 scalar の上で全単射を証明した結果。 -/
def residualCyclicTateLineEquiv : ℤ_[p] ≃ₗ[ℤ_[p]] line :=
  LinearEquiv.ofBijective param
    ⟨S.residualCyclicTateParametrization_injective L hline hcofixed hζ hp5 hclass hbad,
      S.residualCyclicTateParametrization_surjective L hline hcofixed hζ hp5 hclass hbad⟩

/-- 同じ実際の Galois 点作用は、全点列上の標準 p 進 scalar 倍に等しい。 -/
theorem residualCyclicTateLine_action_scalar (σ : Field.absoluteGaloisGroup ℚ) (x : line) :
    action S.residualPointActionHom σ x.val = (padicChar σ : ℤ_[p]) • x.val := by
  apply PrimePowerTateSequence.ext
  intro n
  rw [evaluation_action, evaluation_smul]
  have hm := congrArg Units.val (S.residualPadicTowerCharacter_mod L hline hcofixed hζ hp5 hclass hbad n σ)
  change PadicInt.toZModPow (n + 1) (padicChar σ : ℤ_[p]) = _ at hm
  rw [hm]
  exact (tower n).character_spec σ (evaluation n x.val) (x.property n)

/-- 線形包含も、元の同じ Galois 作用に関して同変である。 -/
theorem residualCyclicTateLine_inclusion_scalar (σ : Field.absoluteGaloisGroup ℚ) (x : line) :
    actionLinear S.residualPointActionHom σ
      (S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad x) =
    S.residualCyclicTateLine_inclusion L hline hcofixed hζ hp5 hclass hbad ((padicChar σ : ℤ_[p]) • x) :=
  S.residualCyclicTateLine_action_scalar L hline hcofixed hζ hp5 hclass hbad σ x

end
end DkMath.FLT.Frey.Source
