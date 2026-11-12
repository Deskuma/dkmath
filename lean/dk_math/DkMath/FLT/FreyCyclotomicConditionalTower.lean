/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicTowerStep

#print "file: DkMath.FLT.FreyCyclotomicConditionalTower"

/-!
# 同じ底を保つ実際の巡回捩れ塔の条件付き反復

既存の類群商消滅と、各段での同じ共鳴素点条件を明示入力に残す。
次段の存在は前章の算術分裂から内部供給し、選択した段を依存再帰でつなぐ。
同じ点群内の単調な塔・その合併の p-primary 性と socle を証明する。
高位捩れ全体の慣性吸収や一般 hno の証明とは区別する。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight
open DkMath.Lib.RepresentationTheory
noncomputable section

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

/-- 次段を実際の算術分裂から選ぶ。分裂・次段の存在を別 provider として要求しない。 -/
def residualCyclicNext {n : ℕ} (T : S.ResidualCyclicStage L n) : S.ResidualCyclicStage L (n + 1) :=
  (S.residual_cyclic_stage_successor L hline hcofixed hζ hp5 T (hbad n T) hclass).choose

theorem residualCyclicNext_spec {n : ℕ} (T : S.ResidualCyclicStage L n) :
    T.carrier ≤ (S.residualCyclicNext L hline hcofixed hζ hp5 hclass hbad T).carrier ∧
      (∀ x ∈ (S.residualCyclicNext L hline hcofixed hζ hp5 hclass hbad T).carrier,
        p • x = 0 → x ∈ T.carrier) :=
  (S.residual_cyclic_stage_successor L hline hcofixed hζ hp5 T (hbad n T) hclass).choose_spec

/-- 同じ元の残余直線を底に、選んだ次段を実際に反復する依存再帰。 -/
def residualCyclicTower : (n : ℕ) → S.ResidualCyclicStage L n :=
  Nat.rec (S.residualCyclicStageZero L hline hcofixed)
    (fun _ T => S.residualCyclicNext L hline hcofixed hζ hp5 hclass hbad T)

local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad

/-- 第0段は元の同じ pointSubgroup。別の同型な底へ取り替えない。 -/
theorem residualCyclicTower_zero : (tower 0).carrier = pointSubgroup S.rationalCurve p L := rfl

/-- 同じ選択を使った隣接段の包含と p 捩れの降下。 -/
theorem residualCyclicTower_step (n : ℕ) :
    (tower n).carrier ≤ (tower (n + 1)).carrier ∧
      (∀ x ∈ (tower (n + 1)).carrier, p • x = 0 → x ∈ (tower n).carrier) :=
  S.residualCyclicNext_spec L hline hcofixed hζ hp5 hclass hbad (tower n)

/-- 各段で別々の存在を選んだだけではなく、単調な同じ塔である。 -/
theorem residualCyclicTower_monotone : Monotone (fun n => (tower n).carrier) :=
  monotone_nat_of_le_succ (fun n => (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1)

/-- 各段の濃度と巡回性・安定性・指数・底の包含はすべて構成から従う。 -/
theorem residualCyclicTower_profile (n : ℕ) :
    Nat.card (tower n).carrier = p ^ (n + 1) ∧ IsAddCyclic (tower n).carrier ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ (tower n).carrier,
        pointAction S.rationalCurve σ x ∈ (tower n).carrier) ∧
      pointSubgroup S.rationalCurve p L ≤ (tower n).carrier ∧
      (∀ x ∈ (tower n).carrier, p ^ (n + 1) • x = 0) ∧
      (∀ x ∈ (tower n).carrier, p • x = 0 → x ∈ pointSubgroup S.rationalCurve p L) :=
  ⟨(tower n).card, (tower n).cyclic, (tower n).stable, (tower n).base,
    (tower n).killed, fun _ hx hpx => (tower n).socle_mem_base hline hx hpx⟩

/-- 互いに無関係な段ではなく、同じ次段内に実際の p 乗根（加法では p 倍の逆像）がある。 -/
theorem residualCyclicTower_lift (n : ℕ) (x : Points S.rationalCurve) (hx : x ∈ (tower n).carrier) :
    ∃ y ∈ (tower (n + 1)).carrier, p • y = x := by
  let J := (tower (n + 1)).carrier
  let := (tower (n + 1)).finite
  let := (tower (n + 1)).cyclic
  have hxJ : x ∈ J := (S.residualCyclicTower_step L hline hcofixed hζ hp5 hclass hbad n).1 hx
  let z : J := ⟨x, hxJ⟩
  have hz : z ∈ (nsmulAddMonoidHom p : J →+ J).range := by
    rw [CyclicPrimePowerScalar.range_nsmul_eq_ker (Fact.out : p.Prime)
      (m := n + 1 + 1) (by omega) (tower (n + 1)).card]
    change p ^ (n + 1 + 1 - 1) • z = 0
    apply Subtype.ext
    change J.subtype (p ^ (n + 1 + 1 - 1) • z) = J.subtype 0
    rw [map_nsmul, map_zero]
    change p ^ (n + 1 + 1 - 1) • x = 0
    simpa only [show n + 1 + 1 - 1 = n + 1 from by omega] using (tower n).killed x hx
  obtain ⟨y, hy⟩ := hz
  exact ⟨y.val, y.property, congrArg (fun w : J => w.val) hy⟩

/-- 同じ幾何学的点群内の、構成した単調な塔の合併。 -/
def residualCyclicTowerUnion : AddSubgroup (Points S.rationalCurve) := ⨆ n, (tower n).carrier

local notation "towerUnion" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad

/-- 合併の元は実際にどこか一つの有限段に入る。 -/
theorem mem_residualCyclicTowerUnion (x : Points S.rationalCurve) :
    x ∈ towerUnion ↔ ∃ n, x ∈ (tower n).carrier := by
  apply AddSubgroup.mem_iSup_of_directed
  exact (S.residualCyclicTower_monotone L hline hcofixed hζ hp5 hclass hbad).directed_le

/-- 合併の各元は有限の p 冪で消える。高位捩れ全体を合併へ含める主張ではない。 -/
theorem residualCyclicTowerUnion_primary (x : Points S.rationalCurve) (hx : x ∈ towerUnion) :
    ∃ n, p ^ (n + 1) • x = 0 := by
  obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
  exact ⟨n, (tower n).killed x hn⟩

/-- 構成した同じ合併は p 倍写像で可除。別の可除群を導入しない。 -/
theorem residualCyclicTowerUnion_divisible (x : Points S.rationalCurve) (hx : x ∈ towerUnion) :
    ∃ y ∈ towerUnion, p • y = x := by
  obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
  obtain ⟨y, hy, he⟩ := S.residualCyclicTower_lift L hline hcofixed hζ hp5 hclass hbad n x hn
  exact ⟨y, (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad y).mpr ⟨n + 1, hy⟩, he⟩

/-- 同じ Galois 作用で合併全体も安定である。 -/
theorem residualCyclicTowerUnion_stable (σ : Field.absoluteGaloisGroup ℚ)
    (x : Points S.rationalCurve) (hx : x ∈ towerUnion) : pointAction S.rationalCurve σ x ∈ towerUnion := by
  obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
  exact (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad _).mpr
    ⟨n, (tower n).stable σ x hn⟩

/-- 合併の p 捩れは、元の同じ底と正確に一致する。 -/
theorem residualCyclicTowerUnion_socle (x : Points S.rationalCurve) :
    (x ∈ towerUnion ∧ p • x = 0) ↔ x ∈ pointSubgroup S.rationalCurve p L := by
  constructor
  · rintro ⟨hx, hpx⟩
    obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    exact (tower n).socle_mem_base hline hn hpx
  · intro hx
    exact ⟨(S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr
      ⟨0, hx⟩, pointSubgroup_killed S.rationalCurve p L x hx⟩

/-- 濃度が無限に増大するので合併は無限。有限段ごとの Nat.card を混同しない。 -/
theorem residualCyclicTowerUnion_infinite : Infinite towerUnion := by
  by_contra h
  have : Finite towerUnion := not_infinite_iff_finite.mp h
  let N := Nat.card towerUnion
  let f : (tower N).carrier → towerUnion := fun x =>
    ⟨x.val, (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x.val).mpr ⟨N, x.property⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : towerUnion => z.val) he
  have hle := Nat.card_le_card_of_injective f hf
  rw [(tower N).card] at hle
  have hlt : N < p ^ (N + 1) := lt_trans (Nat.lt_succ_self N) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)
  exact (not_le_of_gt hlt) hle

end
end DkMath.FLT.Frey.Source
