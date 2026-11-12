/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.AbsorbingTorsionFiltration

#print "file: DkMath.Lib.Algebra.CyclicSignSeparation"

/-!
# 和差の二択と底の符号分離から巡回群を吸収先へ送る

生成元での作用差が部分群に入れば、加法性により全巡回群でも入る。
既存の非自明な底の作用の補題を、作用 `f` と `-f` にそれぞれ適用する。
これにより、和差のどちらが吸収されるかを選び直しても、底で `±1` のどちらでもない
作用は同じ巡回群全体を吸収先へ送る。巡回性と二つの非自明性が必要である。
-/

namespace DkMath.Lib.Algebra.CyclicSignSeparation

variable {G : Type*} [AddCommGroup G]

/-- 巡回群上の和差の吸収二択を、同じ部分群への包含へ強める。
底での作用が `+1` または `-1` の場合にはこの結論を適用しない。 -/
theorem le_of_sub_or_add_mem {p m : ℕ} (hp : p.Prime)
    (K H : AddSubgroup G) [IsAddCyclic K]
    (hexp : ∀ x ∈ K, p ^ m • x = 0) (f : G →+ G)
    (hstable : ∀ x ∈ K, f x ∈ K)
    (hminus : ∃ x ∈ K, p • x = 0 ∧ f x ≠ x)
    (hplus : ∃ x ∈ K, p • x = 0 ∧ f x ≠ -x)
    (hdich : ∀ x ∈ K, x ∉ H → f x - x ∈ H ∨ f x + x ∈ H) : K ≤ H := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := K)
  have hgen : ∀ x ∈ K, ∃ a : ℤ, a • g.val = x := by
    intro x hx
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
    exact ⟨a, congrArg (fun z : K => z.val) ha⟩
  have extend (φ : G →+ G) (hd : φ g.val - g.val ∈ H) : ∀ x ∈ K, φ x - x ∈ H := by
    intro x hx
    obtain ⟨a, rfl⟩ := hgen x hx
    rw [map_zsmul, ← zsmul_sub]
    exact H.zsmul_mem hd a
  by_cases hgH : g.val ∈ H
  · intro x hx
    obtain ⟨a, rfl⟩ := hgen x hx
    exact H.zsmul_mem hgH a
  · rcases hdich g.val g.property hgH with hd | ha
    · exact AbsorbingTorsionFiltration.le_of_nontrivial_socle hp K H hexp f hstable hminus (extend f hd)
    · have hs : ∀ x ∈ K, (-f) x ∈ K := fun x hx => K.neg_mem (hstable x hx)
      have hn : ∃ x ∈ K, p • x = 0 ∧ (-f) x ≠ x := by
        obtain ⟨x, hx, hpx, hne⟩ := hplus
        refine ⟨x, hx, hpx, fun h => hne ?_⟩
        simpa only [AddMonoidHom.neg_apply, neg_neg] using congrArg Neg.neg h
      have hd : (-f) g.val - g.val ∈ H := by
        change -(f g.val) - g.val ∈ H
        have he : -(f g.val) - g.val = -(f g.val + g.val) := by abel
        rw [he]
        exact H.neg_mem ha
      exact AbsorbingTorsionFiltration.le_of_nontrivial_socle hp K H hexp (-f) hs hn (extend (-f) hd)

end DkMath.Lib.Algebra.CyclicSignSeparation
