/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTateUnion
import DkMath.Lib.NumberTheory.EllipticTateReduction

#print "file: DkMath.FLT.FreyCyclicTateReduction"

/-!
# 同じ Tate 直線の p 飽和性と元の残余直線

全 Tate 加群 mod p は実際の E[p]、直線 mod p は元の同じ L に戻る。
全 Tate 加群の自由階数2・基底拡張・最終 hno はまだ証明しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory PrimePowerTateSequence
noncomputable section

section Ambient
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ Frey 全 Tate 加群の mod p 商の実際の次元は2。 -/
theorem residualTateModP_finrank : Module.finrank (ZMod p) (TateModP S.rationalCurve p) = 2 :=
  tateModP_finrank S.rationalCurve p
end Ambient

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
local notation "union" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad
local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad

/-- 同じ直線は全 Tate 加群内で p に関して飽和している。 -/
theorem residualCyclicTateLine_p_saturated (x : Tate p (Points S.rationalCurve)) :
    p • x ∈ line ↔ x ∈ line := by
  constructor
  · intro hx n
    have hh := hx (n + 1)
    change p • evaluation (n + 1) x ∈ (tower (n + 1)).carrier at hh
    rw [compatible] at hh
    exact ((tower n).mem_iff_killed_in_later (tower (n + 1)) (Nat.le_succ n)
      (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1 _).mpr ⟨hh, killed x n⟩
  · intro hx n
    change p • evaluation n x ∈ (tower n).carrier
    exact (tower n).carrier.nsmul_mem (hx n) p

/-- 第0評価を元の同じ残余直線 L へ戻す自然な加法写像。 -/
def residualTateLineReduction : line →+ L where
  toFun x := ⟨tateReduction S.rationalCurve p x.val, by
    have hx : evaluation 0 x.val ∈ pointSubgroup S.rationalCurve p L := x.property 0
    obtain ⟨q, hq, he⟩ := hx
    have heq : q = tateReduction S.rationalCurve p x.val := Subtype.ext he
    exact heq ▸ hq⟩
  map_zero' := rfl
  map_add' _ _ := rfl

local notation "red" => S.residualTateLineReduction L hline hcofixed hζ hp5 hclass hbad

/-- 同じ U の実際の可除性を、その部分群型の p 倍全射性として公開する。 -/
theorem residualTowerUnion_nsmul_surjective :
    Function.Surjective (nsmulAddMonoidHom p : (union) →+ (union)) := by
  intro x
  obtain ⟨y, hy, he⟩ := S.residualCyclicTowerUnion_divisible L hline hcofixed hζ hp5 hclass hbad x.val x.property
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- 元の L の点は同じ U 内の互換逆像列で持ち上がり、第0評価は L 上に全射。 -/
theorem residualTateLineReduction_surjective : Function.Surjective red := by
  intro q
  have hq : q.val.val ∈ union :=
    (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr
      ⟨0, ⟨q.val, q.property, rfl⟩⟩
  let a : (nsmulAddMonoidHom p : (union) →+ (union)).ker :=
    ⟨⟨q.val.val, hq⟩, Subtype.ext q.val.property⟩
  obtain ⟨t, ht⟩ := reduction_surjective
    (S.residualTowerUnion_nsmul_surjective L hline hcofixed hζ hp5 hclass hbad) a
  refine ⟨S.residualUnionTateLineEquiv L hline hcofixed hζ hp5 hclass hbad t, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (nsmulAddMonoidHom p : (union) →+ (union)).ker => z.val.val) ht

/-- 直線内の第0評価の核も、その直線自身の p 倍像である。
全加群の逆像が同じ直線へ戻ることを飽和性で保証する。 -/
theorem residualTateLineReduction_ker :
    (nsmulAddMonoidHom p : (line) →+ (line)).range = (red).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change p • evaluation 0 x.val = 0
    simpa only [Nat.zero_add, pow_one] using killed x.val 0
  · intro x hx
    have hx0 : reduction x.val = 0 := Subtype.ext (congrArg (fun z : L => z.val.val) hx)
    let w := shiftOfZero x.val hx0
    have hw : w ∈ line := (S.residualCyclicTateLine_p_saturated L hline hcofixed hζ hp5 hclass hbad w).mp
      (by rw [nsmul_shiftOfZero]; exact x.property)
    exact ⟨⟨w, hw⟩, Subtype.ext (nsmul_shiftOfZero x.val hx0)⟩

/-- 直線自身の実際の p 倍による商。 -/
abbrev ResidualTateLineModP := (line) ⧸ (nsmulAddMonoidHom p : (line) →+ (line)).range

local notation "lineModP" => S.ResidualTateLineModP L hline hcofixed hζ hp5 hclass hbad

instance residualTateLineModPModule : Module (ZMod p) lineModP :=
  QuotientAddGroup.zmodModule (fun x => ⟨x, rfl⟩)

/-- 同じ第0評価が与える、実際の直線 mod p と元の L の加法同型。 -/
def residualTateLineModPEquiv : lineModP ≃+ L := by
  change ((line) ⧸ (nsmulAddMonoidHom p : (line) →+ (line)).range) ≃+ L
  rw [S.residualTateLineReduction_ker L hline hcofixed hζ hp5 hclass hbad]
  exact QuotientAddGroup.quotientKerEquivOfSurjective red
    (S.residualTateLineReduction_surjective L hline hcofixed hζ hp5 hclass hbad)

/-- p で消える商の標準 scalar のもとで、この自然な同定は ZMod p 線形。 -/
def residualTateLineModPLinearEquiv : lineModP ≃ₗ[ZMod p] L :=
  (S.residualTateLineModPEquiv L hline hcofixed hζ hp5 hclass hbad).toLinearEquiv
    (fun c x => ZMod.map_smul (S.residualTateLineModPEquiv L hline hcofixed hζ hp5 hclass hbad) c x)

/-- 同じ直線の mod p 商の実際の次元は1。 -/
theorem residualTateLineModP_finrank : Module.finrank (ZMod p) lineModP = 1 :=
  (S.residualTateLineModPLinearEquiv L hline hcofixed hζ hp5 hclass hbad).finrank_eq.trans hline

/-- 直線の還元と全 Tate 加群の還元は同じ E[p] の点を返す。 -/
theorem residualTateLineReduction_inclusion (x : line) :
    (red x).val = tateReduction S.rationalCurve p x.val := rfl

end
end DkMath.FLT.Frey.Source
