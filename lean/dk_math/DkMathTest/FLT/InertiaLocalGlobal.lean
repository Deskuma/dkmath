/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.NumberFieldInertiaRepresentation
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic

#print "file: DkMathTest.FLT.InertiaLocalGlobal"

/-!
# NOTE-031-001A: 実際の数体と、局所二択を交換できない境界

3次単位根の体は次数2の実在するガロア拡大であり、非自明な慣性群を持つことを
今回の生成定理から証明する。分岐素数の具体的な同定までは行わない。
後半は二つの局所部分群でFixed/Cofixedの側が異なる有限表現である。
両部分群は全群を生成するが、大域の二択は成立しない。全素点で側をそろえる理由を示す。
-/
namespace InertiaLocalGlobalTest
open scoped NumberField
open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory LocalFixedCofixed

/-- 3次単位根を添加した具体的な数体。次数は3ではなくφ(3)=2である。 -/
abbrev RootField := CyclotomicField 3 ℚ

local instance : IsCyclotomicExtension {3} ℚ RootField := CyclotomicField.isCyclotomicExtension 3 ℚ
local instance : IsGalois ℚ RootField := IsCyclotomicExtension.isGalois {3} ℚ RootField

/-- 実際の円分体の次数2をMathlibの次数公式から得る。 -/
theorem rootField_degree : Module.finrank ℚ RootField = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 RootField]
  decide

/-- 非自明な具体的ガロア拡大で、全有限素点の慣性群が全群を生成する。 -/
theorem rootField_inertia_generates :
    (⨆ P : {P : Ideal (𝓞 RootField) // P.IsMaximal}, P.val.inertia (RootField ≃ₐ[ℚ] RootField)) = ⊤ :=
  NumberFieldInertiaGeneration.iSup_inertia_eq_top

/-- 次数2の拡大では、少なくとも一つの実際の慣性群が非零である。
全てが零なら生成定理からガロア群の位数が1となり、次数2に反する。 -/
theorem rootField_has_nontrivial_inertia :
    ∃ P : Ideal (𝓞 RootField), P.IsMaximal ∧ P.inertia (RootField ≃ₐ[ℚ] RootField) ≠ ⊥ := by
  by_contra! h
  have ht := NumberFieldInertiaGeneration.subgroup_eq_top_of_inertia_le
    (⊥ : Subgroup (RootField ≃ₐ[ℚ] RootField)) (fun P hP => le_of_eq (h P hP))
  have hc := (Subgroup.card_eq_iff_eq_top (⊥ : Subgroup (RootField ≃ₐ[ℚ] RootField))).mpr ht
  rw [Subgroup.card_bot, IsGaloisGroup.card_eq_finrank (RootField ≃ₐ[ℚ] RootField) ℚ RootField,
    rootField_degree] at hc
  omega

/-- 具体的数体の表現でも、全慣性群のFixedから大域Fixedを得る。
生成性を入力に取らず、任意の同じ部分加群Nに適用する。 -/
theorem rootField_fixed_transport {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (RootField ≃ₐ[ℚ] RootField) V) (N : Submodule ℚ V)
    (hlocal : ∀ P : Ideal (𝓞 RootField), P.IsMaximal → FixedOn ρ N (P.inertia (RootField ≃ₐ[ℚ] RootField))) :
    IsFixedOn ρ N := NumberFieldInertiaRepresentation.isFixedOn_of_inertia ρ N hlocal

/-- 同じ具体的数体の商の慣性自明性も大域へ移る。Nの安定性を別入力に要求しない。 -/
theorem rootField_cofixed_transport {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : Representation ℚ (RootField ≃ₐ[ℚ] RootField) V) (N : Submodule ℚ V)
    (hlocal : ∀ P : Ideal (𝓞 RootField), P.IsMaximal → CofixedOn ρ N (P.inertia (RootField ≃ₐ[ℚ] RootField))) :
    IsCofixedOn ρ N := NumberFieldInertiaRepresentation.isCofixedOn_of_inertia ρ N hlocal

namespace SideBoundary
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
/-- 境界例の係数体。 -/
abbrev k := ZMod 5
/-- 二つの独立な可逆スカラーの積群。 -/
abbrev G := kˣ × kˣ
/-- 二つの座標を持つ係数空間。 -/
abbrev V := Fin 2 → k

/-- 二つの独立な指標を対角に置く作用素。Freyや慣性の実例とは同一視しない。 -/
def action (g : G) : V →ₗ[k] V where
  toFun x i := (if i = 0 then (g.1 : k) else (g.2 : k)) * x i
  map_add' x y := by ext i; simp only [Pi.add_apply, mul_add]
  map_smul' a x := by ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- 同じ空間上の実際の有限群表現。 -/
def rho : Representation k G V where
  toFun := action
  map_one' := by ext x i; simp [action]
  map_mul' g h := by
    ext x i
    by_cases hi : i = 0 <;> simp [action, hi, mul_assoc]

/-- 第一座標の直線。 -/
def line : Submodule k V := LinearMap.ker (LinearMap.proj (1 : Fin 2))

/-- 第一軸は非零ベクトル(1,0)が生成する実際の直線である。 -/
theorem line_eq_span : line = Submodule.span k ({![1, 0]} : Set V) := by
  ext x
  constructor
  · intro hx
    change x 1 = 0 at hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i <;> simp [hx]
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change (a • (![1, 0] : V)) 1 = 0
    simp

/-- 境界例の部分加群は次元1であり、零や全空間を使った反例ではない。 -/
theorem line_finrank : Module.finrank k line = 1 := by
  rw [line_eq_span]
  apply finrank_span_singleton (K := k) (v := (![1, 0] : V))
  intro h
  have hh := congrFun h 0
  exact (by decide : (1 : k) ≠ 0) hh

/-- 同じ第一軸は全群によって集合として保存される。 -/
theorem line_stable : IsStable rho line := by
  intro g x hx
  change x 1 = 0 at hx
  change (g.2 : k) * x 1 = 0
  rw [hx, mul_zero]

/-- 第一因子だけが動く局所部分群。 -/
def first : Subgroup G := (MonoidHom.snd kˣ kˣ).ker

/-- 第二因子だけが動く局所部分群。 -/
def second : Subgroup G := (MonoidHom.fst kˣ kˣ).ker

/-- 二つの局所部分群をBoolで添字付けする。 -/
def localGroups : Bool → Subgroup G
  | false => first
  | true => second

/-- (a,b)=(a,1)(1,b)より二つの局所部分群は全群を生成する。 -/
theorem localGroups_generate : (⨆ i, localGroups i) = ⊤ := by
  apply top_unique
  intro g _
  have hf : (g.1, 1) ∈ (⨆ i, localGroups i) :=
    (le_iSup localGroups false) (by change (1 : kˣ) = 1; rfl)
  have hs : (1, g.2) ∈ (⨆ i, localGroups i) :=
    (le_iSup localGroups true) (by change (1 : kˣ) = 1; rfl)
  simpa using (⨆ i, localGroups i).mul_mem hf hs

/-- 第一局所群では第二座標が動かないので、商は固定される。 -/
theorem first_cofixed : CofixedOn rho line first := by
  intro g hg x
  change g.2 = 1 at hg
  change (g.2 : k) * x 1 - x 1 = 0
  rw [hg]
  simp

/-- 第二局所群では第一座標が動かないので、直線は点ごとに固定される。 -/
theorem second_fixed : FixedOn rho line second := by
  intro g hg x hx
  change g.1 = 1 at hg
  change x 1 = 0 at hx
  funext i
  fin_cases i
  · change (g.1 : k) * x 0 = x 0
    rw [hg]; simp
  · change (g.2 : k) * x 1 = x 1
    rw [hx, mul_zero]

/-- 各局所部分群についての二択は実際に成立するが、選ぶ側は異なる。 -/
theorem pointwise_local_alternative : ∀ i, FixedOn rho line (localGroups i) ∨ CofixedOn rho line (localGroups i) := by
  intro i
  cases i
  · exact Or.inr first_cofixed
  · exact Or.inl second_fixed

/-- 全群では第一軸が固定されない。g=(2,1)が反例を与える。 -/
theorem not_global_fixed : ¬ IsFixedOn rho line := by
  intro h
  let g : G := (⟨2, 3, by decide, by decide⟩, 1)
  have he := congrFun (h g (![1, 0] : V) (by change (0 : k) = 0; rfl)) 0
  change (2 : k) * 1 = 1 at he
  exact (by decide : (2 : k) * 1 ≠ 1) he

/-- 全群では商も固定されない。g=(1,2)が反例を与える。 -/
theorem not_global_cofixed : ¬ IsCofixedOn rho line := by
  intro h
  let g : G := (1, ⟨2, 3, by decide, by decide⟩)
  have he := h g (![0, 1] : V)
  change (2 : k) * 1 - 1 = 0 at he
  exact (by decide : (2 : k) * 1 - 1 ≠ 0) he

/-- 群を生成しても、∀i(Fixed∨Cofixed)を大域の二択へ交換することはできない。 -/
theorem inconsistent_side_counterexample :
    Module.finrank k line = 1 ∧ IsStable rho line ∧ (⨆ i, localGroups i) = ⊤ ∧
    (∀ i, FixedOn rho line (localGroups i) ∨ CofixedOn rho line (localGroups i)) ∧
    ¬ (IsFixedOn rho line ∨ IsCofixedOn rho line) :=
  ⟨line_finrank, line_stable, localGroups_generate, pointwise_local_alternative,
    fun h => h.elim not_global_fixed not_global_cofixed⟩

end SideBoundary
end InertiaLocalGlobalTest
