/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.InvariantLine
import Mathlib.LinearAlgebra.Quotient.Basic

#print "file: DkMath.Lib.RepresentationTheory.FixedCofixed"

/-!
# 固定される直線と、商が固定される直線

`IsFixedOn ρ N` はNの各点を固定すること、`IsCofixedOn ρ N` は作用の差
ρ(g)x − xが常にNへ入ることである。後者はV/Nの各類を固定する条件に等しい。
どちらもNの安定性を含むが、安定性だけからこの二択は従わない。

二次元で可約なら安定直線が存在する。その直線について二択が別に証明され、
かつ非零固定ベクトルが存在しなければcofixed側に絞れる。ここでの二択は明示的な
入力である。行列式、局所還元、慣性群からこの入力を供給する算術は扱わない。
-/

namespace DkMath.Lib.RepresentationTheory
variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- 部分加群の各元が、全ての群元によって固定される。 -/
def IsFixedOn (ρ : Representation R G V) (N : Submodule R V) : Prop :=
  ∀ g, ∀ x ∈ N, ρ g x = x

/-- 商V/Nに自明に作用することを、元の空間内の差で表す。 -/
def IsCofixedOn (ρ : Representation R G V) (N : Submodule R V) : Prop :=
  ∀ g x, ρ g x - x ∈ N

/-- 非零固定ベクトルが存在しないという条件。安定直線の不存在より弱い。 -/
def NoNonzeroFixed (ρ : Representation R G V) : Prop :=
  ∀ x, (∀ g, ρ g x = x) → x = 0

/-- 点ごとの固定は部分加群の安定性を含む。 -/
theorem IsFixedOn.isStable {ρ : Representation R G V} {N : Submodule R V}
    (h : IsFixedOn ρ N) : IsStable ρ N := by
  intro g x hx
  rwa [h g x hx]

/-- cofixed条件も安定性を含む。差と元を足して作用後の元へ戻す。 -/
theorem IsCofixedOn.isStable {ρ : Representation R G V} {N : Submodule R V}
    (h : IsCofixedOn ρ N) : IsStable ρ N := by
  intro g x hx
  simpa only [sub_add_cancel] using N.add_mem (h g x) hx

/-- cofixedの定義は、作用の前後で商の類が変わらないことと同値。 -/
theorem isCofixedOn_iff_mkQ (ρ : Representation R G V) (N : Submodule R V) :
    IsCofixedOn ρ N ↔ ∀ g x, N.mkQ (ρ g x) = N.mkQ x := by
  constructor
  · intro h g x
    exact (Submodule.Quotient.eq N).mpr (h g x)
  · intro h g x
    exact (Submodule.Quotient.eq N).mp (h g x)

/-- 固定ベクトルが零だけなら、点ごとに固定される部分加群は零である。 -/
theorem eq_bot_of_isFixedOn {ρ : Representation R G V} (hzero : NoNonzeroFixed ρ)
    {N : Submodule R V} (h : IsFixedOn ρ N) : N = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact (Submodule.mem_bot R).mpr (hzero x (fun g => h g x hx))

/-- 非零部分加群のfixed/cofixed二択から、固定ベクトルの不存在で後者を選ぶ。
二択を証明したと見なしてしまわないよう、`hcases`を引数に残す。 -/
theorem isCofixedOn_of_fixed_or_cofixed {ρ : Representation R G V}
    (hzero : NoNonzeroFixed ρ) {N : Submodule R V} (hne : N ≠ ⊥)
    (hcases : IsFixedOn ρ N ∨ IsCofixedOn ρ N) : IsCofixedOn ρ N := by
  rcases hcases with h | h
  · exact (hne (eq_bot_of_isFixedOn hzero h)).elim
  · exact h

section Field
variable {k : Type*} [Field k] [Module k V] [FiniteDimensional k V]

/-- 二次元の可約性から、次元を記録した実際の安定部分空間を取り出す。 -/
theorem exists_stable_line_of_not_isIrreducible (ρ : Representation k G V)
    (hd : Module.finrank k V = 2) (hred : ¬ IsIrreducible ρ) :
    ∃ L : Submodule k V, Module.finrank k L = 1 ∧ IsStable ρ L := by
  by_contra h
  exact hred ((isIrreducible_iff_no_stable_line ρ hd).mpr h)

/-- 二択と固定ベクトルの不存在を供給できた場合の、cofixed安定直線の抽出。
これは算術的な二入力を保持した条件付き定理である。 -/
theorem exists_cofixed_line_of_not_isIrreducible (ρ : Representation k G V)
    (hd : Module.finrank k V = 2) (hred : ¬ IsIrreducible ρ)
    (hcases : ∀ L : Submodule k V, Module.finrank k L = 1 → IsStable ρ L →
      IsFixedOn ρ L ∨ IsCofixedOn ρ L) (hzero : NoNonzeroFixed ρ) :
    ∃ L : Submodule k V, Module.finrank k L = 1 ∧ IsStable ρ L ∧ IsCofixedOn ρ L := by
  obtain ⟨L, hdim, hs⟩ := exists_stable_line_of_not_isIrreducible ρ hd hred
  exact ⟨L, hdim, hs, isCofixedOn_of_fixed_or_cofixed hzero
    ((proper_nonzero_iff_finrank_one hd L).mpr hdim).1 (hcases L hdim hs)⟩

/-- 最終的な既約性に必要な三入力を明示する。
cofixed直線の不存在は、非零有理torsionの不存在とは別の算術である。 -/
theorem isIrreducible_of_no_cofixed_line (ρ : Representation k G V)
    (hd : Module.finrank k V = 2)
    (hcases : ∀ L : Submodule k V, Module.finrank k L = 1 → IsStable ρ L →
      IsFixedOn ρ L ∨ IsCofixedOn ρ L) (hzero : NoNonzeroFixed ρ)
    (hno : ¬ ∃ L : Submodule k V, Module.finrank k L = 1 ∧
      IsStable ρ L ∧ IsCofixedOn ρ L) : IsIrreducible ρ := by
  by_contra hred
  exact hno (exists_cofixed_line_of_not_isIrreducible ρ hd hred hcases hzero)

end Field
end DkMath.Lib.RepresentationTheory
