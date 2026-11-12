/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Proof strategy informed by S_Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: arbitrary field, actual Representation, line dimension rather than torsion cardinality;
use containment in the absorbing space, without requiring ambient rank two.
-/

import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.Lib.RepresentationTheory.CofixedBranchSwap"

/-!
# NOTE-032-001: 慣性変化量と枝交換によるCofixed直線の排除

同じ表現ρと真部分空間Mについて、局所群Iの変化量がMへ入り、少なくとも一つが非零だとする。
Cofixed直線Lがあれば、その非零変化量はLとMの両方へ入る。
一次元性からL≤M。Mの次元や安定性を別に仮定する必要はない。

さらに枝交換元σがMの外側でρ(σ)x+x∈Mを満たすとする。
Cofixed条件からρ(σ)x−x∈L≤Mなので、差を取って2x∈Mとなる。
2≠0の体ではx∈Mとなり矛盾する。標数2ではこの消去ができない。
慣性の非自明性、Mの真性、枝交換元の存在は算術の入力として明示する。
-/
namespace DkMath.Lib.RepresentationTheory.CofixedBranchSwap
open LocalFixedCofixed
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- [DkMath.Lib] 一次元空間LとMの共通の非零元があればL≤M。
共通の元を生む算術と、ここでの次元の議論を分ける。 -/
theorem line_le_of_common_nonzero {L M : Submodule k V}
    (hline : Module.finrank k L = 1) {x : V} (hx : x ≠ 0) (hxL : x ∈ L) (hxM : x ∈ M) :
    L ≤ M := by
  have hne : L ⊓ M ≠ ⊥ := by
    intro heq
    have hm : x ∈ L ⊓ M := ⟨hxL, hxM⟩
    rw [heq, Submodule.mem_bot] at hm
    exact hx hm
  have hpos := Submodule.one_le_finrank_iff.mpr hne
  have heq : L ⊓ M = L := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  exact heq ▸ inf_le_right

/-- [DkMath.Lib] 局所作用の一つの非零変化量が、Cofixed直線を吸収空間へ含める。
直線の安定性はCofixed条件から従うので重複入力にしない。 -/
theorem line_le_of_cofixed_and_nontrivial (ρ : Representation k G V) (I : Subgroup G)
    {L M : Submodule k V} (hline : Module.finrank k L = 1) (hL : IsCofixedOn ρ L)
    (habs : CofixedOn ρ M I) (hram : ∃ τ ∈ I, ∃ x, ρ τ x ≠ x) : L ≤ M := by
  obtain ⟨τ, hτ, x, hx⟩ := hram
  exact line_le_of_common_nonzero hline (sub_ne_zero.mpr hx) (hL τ x) (habs τ hτ x)

omit [FiniteDimensional k V] in
/-- [DkMath.Lib] 商での+1作用と−1作用の衝突。外側の一点だけで十分。
可逆なスカラー2で割り、Mへの所属に戻す。 -/
theorem not_cofixed_of_swap_at (ρ : Representation k G V) {L M : Submodule k V}
    (hle : L ≤ M) (h2 : (2 : k) ≠ 0) (σ : G) (x : V) (hx : x ∉ M)
    (hswap : ρ σ x + x ∈ M) : ¬ IsCofixedOn ρ L := by
  intro hL
  have hm := M.sub_mem hswap (hle (hL σ x))
  have ht : (ρ σ x + x) - (ρ σ x - x) = (2 : k) • x := by rw [two_smul]; abel
  rw [ht] at hm
  exact hx ((M.smul_mem_iff h2).mp hm)

omit [FiniteDimensional k V] in
/-- [DkMath.Lib] Mの真性から外側の点を取り、枝交換とCofixedの両立を否定する。 -/
theorem not_cofixed_of_branch_swap (ρ : Representation k G V) {L M : Submodule k V}
    (hle : L ≤ M) (hM : M ≠ ⊤) (h2 : (2 : k) ≠ 0)
    (hswap : ∃ σ, ∀ x, x ∉ M → ρ σ x + x ∈ M) : ¬ IsCofixedOn ρ L := by
  obtain ⟨σ, hσ⟩ := hswap
  obtain ⟨x, hx⟩ : ∃ x : V, x ∉ M := by
    by_contra! h
    exact hM (top_unique (fun x _ => h x))
  exact not_cofixed_of_swap_at ρ hle h2 σ x hx (hσ x hx)

/-- [DkMath.Lib] NOTE-032の枝交換ルートの一般核。
周囲の次元2や有限体の位数p²を仮定せず、候補Lの一次元性だけを使う。 -/
theorem no_cofixed_line (ρ : Representation k G V) (I : Subgroup G)
    (M : Submodule k V) (hM : M ≠ ⊤) (h2 : (2 : k) ≠ 0)
    (habs : CofixedOn ρ M I) (hram : ∃ τ ∈ I, ∃ x, ρ τ x ≠ x)
    (hswap : ∃ σ, ∀ x, x ∉ M → ρ σ x + x ∈ M) :
    ¬ ∃ L : Submodule k V, Module.finrank k L = 1 ∧ IsCofixedOn ρ L := by
  rintro ⟨L, hl, hc⟩
  exact not_cofixed_of_branch_swap ρ
    (line_le_of_cofixed_and_nontrivial ρ I hl hc habs hram) hM h2 hswap hc

/-- [DkMath.Lib] 既存hnoが使う「安定かつCofixed」の形への互換入口。 -/
theorem no_stable_cofixed_line (ρ : Representation k G V) (I : Subgroup G)
    (M : Submodule k V) (hM : M ≠ ⊤) (h2 : (2 : k) ≠ 0)
    (habs : CofixedOn ρ M I) (hram : ∃ τ ∈ I, ∃ x, ρ τ x ≠ x)
    (hswap : ∃ σ, ∀ x, x ∉ M → ρ σ x + x ∈ M) :
    ¬ ∃ L : Submodule k V, Module.finrank k L = 1 ∧ IsStable ρ L ∧ IsCofixedOn ρ L := by
  rintro ⟨L, hl, _, hc⟩
  exact no_cofixed_line ρ I M hM h2 habs hram hswap ⟨L, hl, hc⟩

/-- [DkMath.Lib] Cofixed直線と枝交換が両立するなら局所作用は全て自明。
非自明慣性を供給することが残る算術である、と逆向きに観測できる。 -/
theorem inertia_fixed_of_cofixed_and_branch_swap (ρ : Representation k G V) (I : Subgroup G)
    (M : Submodule k V) (hM : M ≠ ⊤) (h2 : (2 : k) ≠ 0)
    (habs : CofixedOn ρ M I) (hswap : ∃ σ, ∀ x, x ∉ M → ρ σ x + x ∈ M)
    {L : Submodule k V} (hline : Module.finrank k L = 1) (hL : IsCofixedOn ρ L) :
    ∀ τ ∈ I, ∀ x, ρ τ x = x := by
  intro τ hτ x
  by_contra h
  exact no_cofixed_line ρ I M hM h2 habs ⟨τ, hτ, x, h⟩ hswap ⟨L, hline, hL⟩

end DkMath.Lib.RepresentationTheory.CofixedBranchSwap
