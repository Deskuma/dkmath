/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCharacters

#print "file: DkMath.FLT.FreyTateCharactersModP"

/-!
# 同じ第二 Tate 指標の mod p 自明性

元の残余 Cofixed 条件を使い、第二基底点列の作用差を還元して同じ L へ戻す。
同じ直線への持ち上げとの差は実際に p 倍となるため、第二係数は mod p で1。
高位で指標が自明、完全列が分裂、一般 hno が閉じたとは主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
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
local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad
local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad
local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad

/-- 法 p^1 から法 p への標準写像も明示した p 進剰余写像。 -/
def tateResidueModP : ℤ_[p] →+* ZMod p :=
  (ZMod.castHom (dvd_pow_self p (by decide : 0 + 1 ≠ 0)) (ZMod p)).comp (PadicInt.toZModPow 1)

local notation "piP" => tateResidueModP (p := p)

/-- 元の同じ Cofixed 条件により、第二指標の mod p は1。
有限段の商作用の結論であり、第二 p 進指標全体の自明性ではない。 -/
theorem residualTateSecondCharacter_mod_prime (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (piP).toMonoidHom (d σ) = 1 := by
  let y := actionLinear S.residualPointActionHom σ w - w
  have hy : tateReduction S.rationalCurve p y ∈ L := by
    change S.residualRepresentation σ (tateReduction S.rationalCurve p w) -
      tateReduction S.rationalCurve p w ∈ L
    exact hcofixed σ _
  let q : L := ⟨tateReduction S.rationalCurve p y, hy⟩
  obtain ⟨c, hc⟩ := S.residualTateLineReduction_surjective L hline hcofixed hζ hp5 hclass hbad q
  have hcpt := congrArg (fun z : L => z.val.val) hc
  change evaluation 0 c.val = evaluation 0 y at hcpt
  have hz0 : reduction (y - c.val) = 0 := by
    apply Subtype.ext
    change evaluation 0 y - evaluation 0 c.val = 0
    exact sub_eq_zero.mpr hcpt.symm
  let z := shiftOfZero (y - c.val) hz0
  have hpz : p • z = y - c.val := nsmul_shiftOfZero _ hz0
  have hcs : ((eqv).symm c.val).2 = 0 := by
    apply (S.residualTateEquiv_mem_line_iff L hline hcofixed hζ hp5 hclass hbad
      ((eqv).symm c.val).1 ((eqv).symm c.val).2).mp
    simpa only [Prod.mk.eta, LinearEquiv.apply_symm_apply] using c.property
  have hw : (eqv).symm w = (0, 1) :=
    (eqv).symm_apply_eq.mpr (S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad).symm
  have hys : ((eqv).symm y).2 = (d σ : ℤ_[p]) - 1 := by
    dsimp only [y]
    rw [map_sub]
    change ((eqv).symm (actionLinear S.residualPointActionHom σ w)).2 - ((eqv).symm w).2 = _
    rw [S.residualTateSecond_coordinate L hline hcofixed hζ hp5 hclass hbad, hw]
  have he := congrArg (eqv).symm hpz
  rw [map_nsmul, map_sub] at he
  have hs := congrArg Prod.snd he
  change p • ((eqv).symm z).2 = ((eqv).symm y).2 - ((eqv).symm c.val).2 at hs
  rw [hys, hcs, sub_zero] at hs
  have hr := congrArg piP hs
  have hz : (0 : ZMod p) = piP (d σ : ℤ_[p]) - 1 := by
    simpa only [map_nsmul, nsmul_eq_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul, map_sub, map_one] using hr
  apply Units.ext
  change piP (d σ : ℤ_[p]) = 1
  exact sub_eq_zero.mp hz.symm

/-- 実際の行列式を mod p に落とすと、以前の同じ円分指標となる。
これは高位 p 進行列式の円分同定を新たに証明した定理ではない。 -/
theorem residualTate_determinant_mod_prime (σ : Field.absoluteGaloisGroup ℚ) :
    piP (mat σ).det = (CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p) := by
  rw [S.residualTate_determinant L hline hcofixed hζ hp5 hclass hbad, map_mul]
  have hd := congrArg Units.val (S.residualTateSecondCharacter_mod_prime L hline hcofixed hζ hp5 hclass hbad σ)
  change piP (d σ : ℤ_[p]) = 1 at hd
  rw [hd, mul_one]
  exact congrArg Units.val (S.residualPadicTowerCharacter_mod_prime L hline hcofixed hζ hp5 hclass hbad σ)

end
end DkMath.FLT.Frey.Source
