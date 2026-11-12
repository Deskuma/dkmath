/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from S_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean,
blob d3f70a12ac4f51a1f847e1f38c1e51c8f7cc1c82.
Modified: arbitrary field and group representation; direct rank-two hypothesis;
local/global interfaces preserve one common choice for the entire subgroup.
-/

import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.Lib.RepresentationTheory.AbsorbingSubspace"

/-!
# NOTE-031-004A: 真の吸収空間から、慣性群全体の同じ側の二択へ

二次元表現で全変化量(ρ(g)-1)Vが一つの真部分空間Mへ入るとする。
安定な直線NがMに含まれれば次元からN=Mとなり、商が固定される。
含まれなければN∩M=0なので、N内の変化量は零となりNが点ごとに固定される。
この場合分けはgを導入する前に行う。従って結論は(∀g,Fixed)∨(∀g,Cofixed)である。
Mの構成と真性は数論の別の課題として残し、ここでは明示的な仮定に保持する。
-/
namespace DkMath.Lib.RepresentationTheory.AbsorbingSubspace
open LocalFixedCofixed
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- 全変化量を同じ真部分空間が吸収するとき、安定直線またはその商が群全体で固定される。
NとMの位置関係によって一度だけ側を決め、群元ごとには選び直さない。 -/
theorem fixed_or_cofixed (ρ : Representation k G V) (hd : Module.finrank k V = 2)
    (I : Subgroup G) (N : Submodule k V)
    (hN : ∀ g ∈ I, ∀ x ∈ N, ρ g x ∈ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (M : Submodule k V) (hM : M ≠ ⊤) (habs : CofixedOn ρ M I) :
    FixedOn ρ N I ∨ CofixedOn ρ N I := by
  have hN1 := (proper_nonzero_iff_finrank_one hd N).mp ⟨hbot, htop⟩
  by_cases hle : N ≤ M
  · right
    have hMlt := Submodule.finrank_lt hM
    have hNM : N = M := Submodule.eq_of_le_of_finrank_le hle (by omega)
    rwa [hNM]
  · left
    have hinf : N ⊓ M = ⊥ := by
      by_contra hne
      have hpos := Submodule.one_le_finrank_iff.mpr hne
      have heq : N ⊓ M = N := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      exact hle (heq ▸ inf_le_right)
    intro g hg x hx
    have hm : ρ g x - x ∈ N ⊓ M := ⟨N.sub_mem (hN g hg x hx) hx, habs g hg x⟩
    rw [hinf, Submodule.mem_bot] at hm
    exact sub_eq_zero.mp hm

/-- 吸収空間の存在形の入口。全ガロア安定性を同じ局所群へ制限する。 -/
theorem fixed_or_cofixed_of_exists (ρ : Representation k G V) (hd : Module.finrank k V = 2)
    (I : Subgroup G) (N : Submodule k V) (hN : IsStable ρ N) (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (habs : ∃ M : Submodule k V, M ≠ ⊤ ∧ CofixedOn ρ M I) :
    FixedOn ρ N I ∨ CofixedOn ρ N I := by
  obtain ⟨M, hM, hMabs⟩ := habs
  exact fixed_or_cofixed ρ hd I N (fun g _ => hN g) hbot htop M hM hMabs

end DkMath.Lib.RepresentationTheory.AbsorbingSubspace
