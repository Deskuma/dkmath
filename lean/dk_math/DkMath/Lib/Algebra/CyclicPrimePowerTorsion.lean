/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card

#print "file: DkMath.Lib.Algebra.CyclicPrimePowerTorsion"

/-!
# 巡回冪位数群内の全ての低位捩れを同じ部分群へ戻す

位数 p^b の巡回群 K に、位数 p^a の B が含まれ、a≤b なら、
B の p^a 零化から K[p^a]=B を濃度で証明する。素数性はこの群論には不要。
集合的な安定性や高位捩れ全体への包含を仮定する補題ではない。
-/

namespace DkMath.Lib.Algebra.CyclicPrimePowerTorsion
variable {G : Type*} [AddCommGroup G]

/-- 低位の部分群は、大きい巡回群の同じ冪捩れ全体である。 -/
theorem mem_iff_killed {p a b : ℕ} (hab : a ≤ b)
    (K B : AddSubgroup G) [Finite K] [IsAddCyclic K]
    (hK : Nat.card K = p ^ b) (hBK : B ≤ K) (hB : Nat.card B = p ^ a)
    (hkill : ∀ x ∈ B, p ^ a • x = 0) {x : G} :
    x ∈ B ↔ x ∈ K ∧ p ^ a • x = 0 := by
  let f : B → (nsmulAddMonoidHom (p ^ a) : K →+ K).ker := fun y =>
    ⟨⟨y.val, hBK y.property⟩, Subtype.ext (hkill y.val y.property)⟩
  have hf : Function.Injective f := by
    intro u v h
    exact Subtype.ext (congrArg (fun z : (nsmulAddMonoidHom (p ^ a) : K →+ K).ker => z.val.val) h)
  have hker : Nat.card (nsmulAddMonoidHom (p ^ a) : K →+ K).ker = p ^ a := by
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker, hK, Nat.gcd_eq_right (pow_dvd_pow p hab)]
  have hsurj : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hB.trans hker.symm⟩).2
  constructor
  · intro hx
    exact ⟨hBK hx, hkill x hx⟩
  · rintro ⟨hx, hpx⟩
    obtain ⟨y, hy⟩ := hsurj ⟨⟨x, hx⟩, Subtype.ext hpx⟩
    have he : y.val = x := congrArg
      (fun z : (nsmulAddMonoidHom (p ^ a) : K →+ K).ker => z.val.val) hy
    exact he ▸ y.property

end DkMath.Lib.Algebra.CyclicPrimePowerTorsion
