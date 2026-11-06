/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicUnitSplit

#print "file: DkMath.FLT.FreyCyclotomicTowerStep"

/-!
# 算術条件付き分裂から、同じ点群の実際の巡回次段へ

段の不変量は位数 p^(n+1)、巡回性、全 Galois 安定性、同じ底の包含である。
有限性と捩れ指数と socle の底への降下はこれらから導く。
分裂や次段の存在を入力せず、既存の実際の hbad/hclass 付き分裂を呼び出す。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicKummerWeight
open DkMath.Lib.RepresentationTheory
noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ Source と同じ残余直線を保つ、位数 p^(n+1) の実際の巡回段。 -/
structure ResidualCyclicStage (L : Submodule (ZMod p) S.ResidualSpace) (n : ℕ) where
  carrier : AddSubgroup (Points S.rationalCurve)
  card : Nat.card carrier = p ^ (n + 1)
  cyclic : IsAddCyclic carrier
  stable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ carrier, pointAction S.rationalCurve σ x ∈ carrier
  base : pointSubgroup S.rationalCurve p L ≤ carrier

variable {S} {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 位数から有限性を導き、有限性 provider を段データへ追加しない。 -/
theorem ResidualCyclicStage.finite (T : S.ResidualCyclicStage L n) : Finite T.carrier :=
  Nat.finite_of_card_ne_zero (T.card ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

/-- 同じ位数の段は、その同じ p^(n+1) 倍で消える。 -/
theorem ResidualCyclicStage.killed (T : S.ResidualCyclicStage L n)
    (x : Points S.rationalCurve) (hx : x ∈ T.carrier) : p ^ (n + 1) • x = 0 := by
  let := T.finite
  exact congrArg (fun z : T.carrier => z.val)
    (T.card ▸ card_nsmul_eq_zero' (x := (⟨x, hx⟩ : T.carrier)))

/-- 元の一次元の底が、どの段の p 捩れも受け取る。 -/
theorem ResidualCyclicStage.socle_mem_base (T : S.ResidualCyclicStage L n)
    (hline : Module.finrank (ZMod p) L = 1)
    {x : Points S.rationalCurve} (hx : x ∈ T.carrier) (hpx : p • x = 0) :
    x ∈ pointSubgroup S.rationalCurve p L := by
  let := T.finite
  let := T.cyclic
  exact S.residual_cyclic_tower_socle_mem_base L hline T.carrier (by omega) T.card T.base hx hpx

variable (S)

/-- 同じ底を第0段として内部構成する。非零点や段の存在を入力しない。 -/
def residualCyclicStageZero (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) : S.ResidualCyclicStage L 0 where
  carrier := pointSubgroup S.rationalCurve p L
  card := by simpa only [zero_add, pow_one] using card_pointSubgroup S.rationalCurve p L hline
  cyclic := isAddCyclic_pointSubgroup S.rationalCurve p L hline
  stable := pointSubgroup_stable S.rationalCurve p L hcofixed.isStable
  base := le_rfl

/-- 既存の hbad と同じ慣性条件。p•y∈K を全 p 冪捩れ条件へ勝手に拡張しない。 -/
def ResonantAbsorptionAt (K : AddSubgroup (Points S.rationalCurve)) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
    ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
      ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
        p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K

variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

include hline hcofixed in
/-- 同じ段の算術条件から、同じ点群内の実際の巡回次段を構成する。
次段の有限性・巡回性・位数・安定性・底の包含は出力であり、入力しない。 -/
theorem residual_cyclic_stage_successor (hp5 : 5 ≤ p) (T : S.ResidualCyclicStage L n)
    (hbad : S.ResonantAbsorptionAt T.carrier)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    ∃ T' : S.ResidualCyclicStage L (n + 1), T.carrier ≤ T'.carrier ∧
      (∀ x ∈ T'.carrier, p • x = 0 → x ∈ T.carrier) := by
  let := T.finite
  let := T.cyclic
  obtain ⟨D, hcompl, hstable⟩ :=
    S.residual_cyclic_extension_has_stable_complement_of_class_vanishing
      L hline hcofixed T.carrier T.stable (by omega) T.card T.base hζ hp5 hbad hclass
  obtain ⟨J, hinc, hcard, hcyclic, _, hstableJ, hdown⟩ :=
    exists_tower_step_of_stable_complement S.rationalCurve T.carrier T.stable
      (by omega) T.card T.killed D hcompl hstable
  refine ⟨⟨J, hcard, hcyclic, hstableJ, T.base.trans hinc⟩, hinc, hdown⟩

end
end DkMath.FLT.Frey.Source
