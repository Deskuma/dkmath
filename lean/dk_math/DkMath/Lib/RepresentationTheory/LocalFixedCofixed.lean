/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.FixedCofixed

#print "file: DkMath.Lib.RepresentationTheory.LocalFixedCofixed"

/-!
# NOTE-031-001A: 部分群上のFixed/Cofixedを生成された全群へ輸送する

作用を固定する条件を満たす群元は部分群をなす。従って群を生成する各局所部分群で
同じ側の条件が成立すれば、大域でもその条件が成立する。
FixedはNの各元を固定すること、Cofixedは全Vの変化量がNに入ることである。
Cofixed側の群元も積・逆元で閉じるため、この輸送自体にはNの安定性を追加仮定しない。

重要なのは、全ての局所部分群についてFixed側を選ぶか、全てについてCofixed側を選ぶこと。
各部分群でばらばらに二択を選ぶ条件から、大域の二択を導く定理は置かない。
生成条件はこの純群論の層では明示し、有限ガロア拡大の整数環の慣性群については
NumberFieldInertiaGenerationでMinkowskiから実際に証明する。
-/
namespace DkMath.Lib.RepresentationTheory.LocalFixedCofixed
variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Iの全群元がNの各元を固定するという局所条件。 -/
def FixedOn (ρ : Representation R G V) (N : Submodule R V) (I : Subgroup G) : Prop :=
  ∀ g ∈ I, ∀ x ∈ N, ρ g x = x

/-- Iの全群元によるVの変化量がNに入るという局所条件。商V/Nの固定を表す。 -/
def CofixedOn (ρ : Representation R G V) (N : Submodule R V) (I : Subgroup G) : Prop :=
  ∀ g ∈ I, ∀ x, ρ g x - x ∈ N

/-- Nの各点を固定する群元の部分群。表現ρ自体の作用を使い、別の群作用へ置換しない。 -/
def fixedSubgroup (ρ : Representation R G V) (N : Submodule R V) : Subgroup G where
  carrier := {g | ∀ x ∈ N, ρ g x = x}
  one_mem' := by intro x _; simp
  mul_mem' := by
    intro a b ha hb x hx
    rw [map_mul, Module.End.mul_apply, hb x hx, ha x hx]
  inv_mem' := by
    intro g hg x hx
    have hh := congrArg (ρ g⁻¹) (hg x hx)
    rw [ρ.inv_self_apply] at hh
    exact hh.symm

/-- 商の各類を固定する群元の部分群。
逆元の閉性は、gの条件にg⁻¹xを代入して差を反転することで得る。 -/
def cofixedSubgroup (ρ : Representation R G V) (N : Submodule R V) : Subgroup G where
  carrier := {g | ∀ x, ρ g x - x ∈ N}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    have hh := N.add_mem (ha (ρ b x)) (hb x)
    rw [map_mul, Module.End.mul_apply]
    simpa only [sub_add_sub_cancel] using hh
  inv_mem' := by
    intro g hg x
    have hh := N.neg_mem (hg (ρ g⁻¹ x))
    rw [ρ.self_inv_apply] at hh
    simpa only [neg_sub] using hh

/-- 局所Fixedは局所群が固定部分群へ含まれることに等しい。 -/
theorem fixedOn_iff_le (ρ : Representation R G V) (N : Submodule R V) (I : Subgroup G) :
    FixedOn ρ N I ↔ I ≤ fixedSubgroup ρ N := Iff.rfl

/-- 局所Cofixedは局所群が商固定部分群へ含まれることに等しい。 -/
theorem cofixedOn_iff_le (ρ : Representation R G V) (N : Submodule R V) (I : Subgroup G) :
    CofixedOn ρ N I ↔ I ≤ cofixedSubgroup ρ N := Iff.rfl

/-- 全群を生成する局所部分群でNが点ごとに固定されれば、大域でもFixedとなる。 -/
theorem isFixedOn_of_iSup_eq_top {ι : Sort*} (I : ι → Subgroup G)
    (hgen : (⨆ i, I i) = ⊤) (ρ : Representation R G V) (N : Submodule R V)
    (hlocal : ∀ i, FixedOn ρ N (I i)) : IsFixedOn ρ N := by
  have hh : (⊤ : Subgroup G) ≤ fixedSubgroup ρ N := by
    rw [← hgen]
    exact iSup_le (fun i => (fixedOn_iff_le ρ N (I i)).mp (hlocal i))
  intro g x hx
  exact hh (Subgroup.mem_top g) x hx

/-- 全群を生成する局所部分群で商が固定されれば、大域でもCofixedとなる。 -/
theorem isCofixedOn_of_iSup_eq_top {ι : Sort*} (I : ι → Subgroup G)
    (hgen : (⨆ i, I i) = ⊤) (ρ : Representation R G V) (N : Submodule R V)
    (hlocal : ∀ i, CofixedOn ρ N (I i)) : IsCofixedOn ρ N := by
  have hh : (⊤ : Subgroup G) ≤ cofixedSubgroup ρ N := by
    rw [← hgen]
    exact iSup_le (fun i => (cofixedOn_iff_le ρ N (I i)).mp (hlocal i))
  intro g x
  exact hh (Subgroup.mem_top g) x

/-- 全局所群で同じ側を保った二択なら、大域のFixed/Cofixed二択へ移せる。
前提は(∀i,Fixed)∨(∀i,Cofixed)であり、∀i,(Fixed∨Cofixed)ではない。 -/
theorem fixed_or_cofixed_of_common_side {ι : Sort*} (I : ι → Subgroup G)
    (hgen : (⨆ i, I i) = ⊤) (ρ : Representation R G V) (N : Submodule R V)
    (hside : (∀ i, FixedOn ρ N (I i)) ∨ (∀ i, CofixedOn ρ N (I i))) :
    IsFixedOn ρ N ∨ IsCofixedOn ρ N :=
  hside.elim (fun h => Or.inl (isFixedOn_of_iSup_eq_top I hgen ρ N h))
    (fun h => Or.inr (isCofixedOn_of_iSup_eq_top I hgen ρ N h))

end DkMath.Lib.RepresentationTheory.LocalFixedCofixed
