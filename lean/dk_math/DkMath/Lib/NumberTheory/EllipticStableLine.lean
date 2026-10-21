/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFixedTorsion
import DkMath.Lib.NumberTheory.EllipticTorsionGL2
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

#print "file: DkMath.Lib.NumberTheory.EllipticStableLine"

/-!
# 安定直線から、実際の幾何学的な位数pの部分群へ

E[p]内の一次元Fₚ部分空間Lは、点群内の位数pの巡回部分群を定める。
torsionの包含で像を取り、同型を使って位数を移すので、形式的な別の群に置換しない。
Lがガロア安定なら点群内の像も安定であり、像の全ての点はp倍で消える。

これは有理p-isogenyの核となる候補の構成までである。商楕円曲線、Vélu公式、
有理isogenyそのものの構成は含めない。cofixedへの絞り込みには、さらに局所慣性からの
二択と有理p-torsionの不存在が必要で、その二入力を条件として明記する。
-/

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (p : ℕ) [Fact p.Prime]

/-- torsion内の部分空間を、元の幾何学的な点群内の部分群へ写す。 -/
noncomputable def pointSubgroup (L : Submodule (ZMod p) (Torsion E p)) :
    AddSubgroup (Points E) := L.toAddSubgroup.map (torsionGroup E p).subtype

/-- 点群への包含は単射なので、Lとその像の群は同型である。 -/
noncomputable def pointSubgroupEquiv (L : Submodule (ZMod p) (Torsion E p)) :
    L ≃+ pointSubgroup E p L :=
  L.toAddSubgroup.equivMapOfInjective (torsionGroup E p).subtype Subtype.val_injective

omit [E.IsElliptic] in
/-- 一次元部分空間の像には、実際にちょうどp個の点がある。 -/
theorem card_pointSubgroup (L : Submodule (ZMod p) (Torsion E p))
    (hL : Module.finrank (ZMod p) L = 1) : Nat.card (pointSubgroup E p L) = p := by
  rw [← Nat.card_congr (pointSubgroupEquiv E p L).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := L), hL, Nat.card_zmod, pow_one]

omit [E.IsElliptic] in
/-- 位数pの像は巡回群である。商曲線の存在はこの結論に含めない。 -/
theorem isAddCyclic_pointSubgroup (L : Submodule (ZMod p) (Torsion E p))
    (hL : Module.finrank (ZMod p) L = 1) : IsAddCyclic (pointSubgroup E p L) :=
  isAddCyclic_of_prime_card (card_pointSubgroup E p L hL)

omit [CharZero K] [E.IsElliptic] in
/-- 像の点が同じpで消えることを、元の点群で確認する。 -/
theorem pointSubgroup_killed (L : Submodule (ZMod p) (Torsion E p))
    (P : Points E) (hP : P ∈ pointSubgroup E p L) : p • P = 0 := by
  obtain ⟨Q, _, rfl⟩ := hP
  exact Q.property

omit [CharZero K] [E.IsElliptic] in
/-- 部分空間の安定性は、同じ点群内の像のガロア安定性を与える。 -/
theorem pointSubgroup_stable (L : Submodule (ZMod p) (Torsion E p))
    (hL : IsGaloisStable E p L) (σ : Field.absoluteGaloisGroup K)
    (P : Points E) (hP : P ∈ pointSubgroup E p L) :
    pointAction E σ P ∈ pointSubgroup E p L := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact ⟨representation E p σ Q, hL σ Q hQ, rfl⟩

/-- 可約性から、位数pで巡回かつガロア安定な実際の部分群を抽出する029-A。
既存の幾何学的次元2を利用し、位数providerを入力しない。 -/
theorem exists_stable_pointSubgroup_of_reducible (hred : ¬ IsIrreducible E p) :
    ∃ L : Submodule (ZMod p) (Torsion E p), Module.finrank (ZMod p) L = 1 ∧
      IsGaloisStable E p L ∧ Nat.card (pointSubgroup E p L) = p ∧
      IsAddCyclic (pointSubgroup E p L) ∧
      (∀ P ∈ pointSubgroup E p L, p • P = 0) ∧
      (∀ σ P, P ∈ pointSubgroup E p L → pointAction E σ P ∈ pointSubgroup E p L) := by
  obtain ⟨L, hdim, hs⟩ := exists_stable_line_of_not_isIrreducible
    (representation E p) (finrank_torsion_prime E p) hred
  exact ⟨L, hdim, hs, card_pointSubgroup E p L hdim,
    isAddCyclic_pointSubgroup E p L hdim, pointSubgroup_killed E p L,
    pointSubgroup_stable E p L hs⟩

/-- 算術的な二択と有理torsion排除を供給した場合のcofixed直線抽出。
実際のE[p]へ適用するが、二つの算術入力はこの定理では証明しない。 -/
theorem exists_cofixed_line_of_reducible [DecidableEq K] (hred : ¬ IsIrreducible E p)
    (hcases : ∀ L : Submodule (ZMod p) (Torsion E p), Module.finrank (ZMod p) L = 1 →
      IsGaloisStable E p L → IsFixedOn (representation E p) L ∨ IsCofixedOn (representation E p) L)
    (hrat : ∀ Q : E.toAffine.Point, p • Q = 0 → Q = 0) :
    ∃ L : Submodule (ZMod p) (Torsion E p), Module.finrank (ZMod p) L = 1 ∧
      IsGaloisStable E p L ∧ IsCofixedOn (representation E p) L := by
  exact exists_cofixed_line_of_not_isIrreducible (representation E p)
    (finrank_torsion_prime E p) hred hcases
    ((noNonzeroFixed_iff_rational_torsion E p).mpr hrat)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
