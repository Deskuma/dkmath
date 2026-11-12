/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

#print "file: DkMath.Lib.Algebra.FiniteEigenTorsionBridge"

/-!
# 有限アーベル群の冪商から捩れへの固有条件の消滅移送

自然な写像 `A[p] → A/pA` は単射とは限らない。
まず有限群の自己準同型に Fitting 分解を適用し、商での単射性から
捩れ核の消滅を証明する。その後、有限群作用の重み付き和を用いる。
-/

namespace DkMath.Lib.Algebra.FiniteEigenTorsionBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A : Type*} [AddCommGroup A]

/-- 実際の `p` 倍部分群。 -/
def multiples (p : ℕ) (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (nsmulAddMonoidHom p : A →+ A).range

/-- 自然な実際の商 `A/pA`。 -/
abbrev ModQuotient (p : ℕ) (A : Type*) [AddCommGroup A] := A ⧸ multiples p A

theorem mem_multiples (p : ℕ) (x : A) : x ∈ multiples p A ↔ ∃ y : A, p • y = x := Iff.rfl

/-- 有限群の Fitting 分解を使う核補題。商上の核が零なら、元の核の `p` 捩れも零。
`A[p] → A/pA` の単射性を仮定しない。指数の素数性はこの段階では不要。 -/
theorem torsion_kernel_eq_zero [Finite A] (p : ℕ) (f : A →+ A)
    (hmod : ∀ x : A, f x ∈ multiples p A → x ∈ multiples p A)
    (x : A) (hpx : p • x = 0) (hfx : f x = 0) : x = 0 := by
  let F : Module.End ℤ A := f.toIntLinearMap
  let : IsArtinian ℤ A := isArtinian_of_finite
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp F.eventually_isCompl_ker_pow_range_pow
  let n := k + 1
  have hn := hk n (Nat.le_succ k)
  let K := LinearMap.ker (F ^ n)
  let L := LinearMap.range (F ^ n)
  have hkdiv : ∀ k : ℕ, ∀ a : A, (F ^ k) a = 0 → a ∈ multiples p A := by
    intro k
    induction k with
    | zero =>
      intro a ha
      have ha0 : a = 0 := ha
      rw [ha0]
      exact (multiples p A).zero_mem
    | succ k ih =>
      intro a ha
      apply hmod
      apply ih (f a)
      change (F ^ k) (F a) = 0
      simpa only [pow_succ, Module.End.mul_apply] using ha
  have hpKsurj : Function.Surjective (fun a : K => p • a) := by
    intro a
    obtain ⟨y, hy⟩ := hkdiv n a.val a.property
    change p • y = a.val at hy
    have hymem : y ∈ K ⊔ L := by rw [hn.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hymem
    have hpvK : p • v ∈ K := by
      have he : p • v = a.val - p • u := by rw [← hy, ← huv, nsmul_add]; abel
      rw [he]
      exact K.sub_mem a.property (K.nsmul_mem hu p)
    have hpv : p • v = 0 := (Submodule.disjoint_def.mp hn.disjoint) _ hpvK (L.nsmul_mem hv p)
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    change p • u = a.val
    rw [← hy, ← huv, nsmul_add, hpv, add_zero]
  have hpKinj := (Finite.injective_iff_surjective).mpr hpKsurj
  have hxK : x ∈ K := by
    change (F ^ n) x = 0
    rw [show n = k + 1 from rfl, pow_succ, Module.End.mul_apply]
    change (F ^ k) (f x) = 0
    rw [hfx, map_zero]
  have he : p • (⟨x, hxK⟩ : K) = p • (0 : K) := Subtype.ext (by simpa using hpx)
  exact congrArg Subtype.val (hpKinj he)

/-- 実際の商に値を取る自己準同型。 -/
def quotientMap (p : ℕ) (f : A →+ A) : ModQuotient p A →+ ModQuotient p A :=
  QuotientAddGroup.map _ _ f (by
    rintro _ ⟨a, rfl⟩
    exact ⟨f a, (map_nsmul f p a).symm⟩)

theorem quotientMap_mk (p : ℕ) (f : A →+ A) (a : A) :
    quotientMap p f (a : ModQuotient p A) = (f a : ModQuotient p A) := rfl

instance quotientModule (p : ℕ) : Module (ZMod p) (ModQuotient p A) :=
  AddCommGroup.zmodModule (by
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    rw [← QuotientAddGroup.mk_nsmul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩)

/-- 商の作用も、実際の元の自己同型とその逆から構成する。 -/
def quotientAut (p : ℕ) (f : (A ≃ₗ[ℤ] A)) : (ModQuotient p A ≃ₗ[ℤ] ModQuotient p A) :=
  ({ quotientMap p f.toAddMonoidHom with
    invFun := quotientMap p f.symm.toAddMonoidHom
    left_inv := fun x => Quotient.inductionOn x (fun a => by
      change ((f.symm (f a) : A) : ModQuotient p A) = (a : ModQuotient p A)
      rw [f.symm_apply_apply])
    right_inv := fun x => Quotient.inductionOn x (fun a => by
      change ((f (f.symm a) : A) : ModQuotient p A) = (a : ModQuotient p A)
      rw [f.apply_symm_apply]) } : ModQuotient p A ≃+ ModQuotient p A).toIntLinearEquiv

variable {Γ : Type*} [Group Γ]

/-- 同じ群作用を同じ商へ下ろす。 -/
def quotientAction (p : ℕ) (ρ : Γ →* (A ≃ₗ[ℤ] A)) : Γ →* (ModQuotient p A ≃ₗ[ℤ] ModQuotient p A) where
  toFun g := quotientAut p (ρ g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    change ((ρ 1 a : A) : ModQuotient p A) = (a : ModQuotient p A)
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    refine Quotient.inductionOn x (fun a => ?_)
    change ((ρ (g * h) a : A) : ModQuotient p A) = ((ρ g (ρ h a) : A) : ModQuotient p A)
    rw [map_mul]
    rfl

theorem quotientAction_mk (p : ℕ) (ρ : Γ →* (A ≃ₗ[ℤ] A)) (g : Γ) (a : A) :
    quotientAction p ρ g (a : ModQuotient p A) = (ρ g a : ModQuotient p A) := rfl

/-- 標数 p の加群上の重み付き和。まだ群の位数で割らない。 -/
def weightedSum {p : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [Fintype Γ] (ρ : Γ →* (M ≃ₗ[ℤ] M)) (χ : Γ →* (ZMod p)ˣ) (v : M) : M :=
  ∑ g : Γ, (((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p) • ρ g v

/-- 重み付き和は実際に指標 χ の固有条件を満たす。 -/
theorem weightedSum_eigen {p : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    [Fintype Γ] (ρ : Γ →* (M ≃ₗ[ℤ] M)) (χ : Γ →* (ZMod p)ˣ) (v : M) (h : Γ) :
    ρ h (weightedSum ρ χ v) = (χ h : ZMod p) • weightedSum ρ χ v := by
  unfold weightedSum
  calc
    ρ h (∑ g : Γ, (((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p) • ρ g v) =
        ∑ g : Γ, (((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p) • ρ (h * g) v := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [ZMod.map_smul (ρ h), map_mul]
      rfl
    _ = ∑ g : Γ, (χ h : ZMod p) • ((((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p) • ρ g v) := by
      refine Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun g => ?_)
      have hu : χ h * (χ (h * g))⁻¹ = (χ g)⁻¹ := by
        rw [map_mul, mul_inv_rev]
        simp only [mul_left_comm (χ h), mul_inv_cancel, mul_one]
      rw [smul_smul, ← Units.val_mul, hu]
    _ = (χ h : ZMod p) • ∑ g : Γ, (((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p) • ρ g v :=
      (Finset.smul_sum).symm

/-- 指標の逆元を整数係数へ持ち上げた、元の有限群上の実際の準同型。 -/
def liftedWeightedSum {p : ℕ} [Fintype Γ] (ρ : Γ →* (A ≃ₗ[ℤ] A))
    (χ : Γ →* (ZMod p)ˣ) : A →+ A :=
  ∑ g : Γ, ((((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p).val) • (ρ g).toAddMonoidHom

theorem liftedWeightedSum_apply {p : ℕ} [Fintype Γ] (ρ : Γ →* (A ≃ₗ[ℤ] A))
    (χ : Γ →* (ZMod p)ˣ) (x : A) :
    liftedWeightedSum ρ χ x = ∑ g : Γ,
      ((((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p).val) • ρ g x := by
  simp only [liftedWeightedSum, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
  rfl

theorem liftedWeightedSum_quotient {p : ℕ} [NeZero p] [Fintype Γ]
    (ρ : Γ →* (A ≃ₗ[ℤ] A)) (χ : Γ →* (ZMod p)ˣ) (x : A) :
    (liftedWeightedSum ρ χ x : ModQuotient p A) =
      weightedSum (quotientAction p ρ) χ (x : ModQuotient p A) := by
  rw [liftedWeightedSum_apply]
  change (QuotientAddGroup.mk' (multiples p A)) (∑ g : Γ, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [map_nsmul]
  change _ = (((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p) • (ρ g x : ModQuotient p A)
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  rfl

/-- 同じ群の実際の p 捩れ部分群。 -/
abbrev Torsion (p : ℕ) (A : Type*) [AddCommGroup A] :=
  (nsmulAddMonoidHom p : A →+ A).ker

instance torsionModule (p : ℕ) : Module (ZMod p) (Torsion p A) :=
  AddCommGroup.zmodModule (by
    intro x
    apply Subtype.ext
    exact x.property)

/-- 元の捩れ固有ベクトルに対して、持ち上げた重み付き和は群の位数倍となる。 -/
theorem liftedWeightedSum_torsion {p : ℕ} [NeZero p] [Fintype Γ]
    (ρ : Γ →* (A ≃ₗ[ℤ] A)) (χ : Γ →* (ZMod p)ˣ)
    (x : A) (hpx : p • x = 0) (he : ∀ g : Γ, ρ g x = (χ g : ZMod p).val • x) :
    liftedWeightedSum ρ χ x = Fintype.card Γ • x := by
  rw [liftedWeightedSum_apply]
  have hs (a : ZMod p) (t : Torsion p A) : a.val • t = a • t := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  have ht (g : Γ) :
      ((((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p).val) • ρ g x = x := by
    rw [he]
    have h : ((((χ g)⁻¹ : (ZMod p)ˣ) : ZMod p).val) •
        ((χ g : ZMod p).val • (⟨x, hpx⟩ : Torsion p A)) = (⟨x, hpx⟩ : Torsion p A) := by
      rw [hs, hs, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    exact congrArg Subtype.val h
  simp only [ht, Finset.sum_const, Finset.card_univ]

/-- 有限群作用の固有成分消滅の移送。仮定は同じ実際の商の固有成分の零化である。
群の位数が標数で可逆なことを明示し、自然な捩れから商への写像の単射性は要求しない。 -/
theorem torsion_eigen_eq_zero [Finite A] {p : ℕ} [NeZero p] [Fintype Γ]
    (ρ : Γ →* (A ≃ₗ[ℤ] A)) (χ : Γ →* (ZMod p)ˣ)
    (hcard : IsUnit (Fintype.card Γ : ZMod p))
    (hvanish : ∀ v : ModQuotient p A,
      (∀ g : Γ, quotientAction p ρ g v = (χ g : ZMod p) • v) → v = 0)
    (x : A) (hpx : p • x = 0) (he : ∀ g : Γ, ρ g x = (χ g : ZMod p).val • x) : x = 0 := by
  let S := liftedWeightedSum ρ χ
  let f : A →+ A := Fintype.card Γ • AddMonoidHom.id A - S
  have hS (a : A) : (S a : ModQuotient p A) = 0 := by
    change (liftedWeightedSum ρ χ a : ModQuotient p A) = 0
    rw [liftedWeightedSum_quotient]
    exact hvanish _ (weightedSum_eigen (quotientAction p ρ) χ _)
  refine torsion_kernel_eq_zero p f ?_ x hpx ?_
  · intro a ha
    have hfa : (f a : ModQuotient p A) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ha
    have hq : (Fintype.card Γ : ZMod p) • (a : ModQuotient p A) = 0 := by
      change (QuotientAddGroup.mk' (multiples p A)) (Fintype.card Γ • a - S a) = 0 at hfa
      rw [map_sub, map_nsmul] at hfa
      change Fintype.card Γ • (a : ModQuotient p A) - (S a : ModQuotient p A) = 0 at hfa
      rw [hS, sub_zero] at hfa
      simpa only [Nat.cast_smul_eq_nsmul] using hfa
    exact (QuotientAddGroup.eq_zero_iff _).mp (hcard.smul_eq_zero.mp hq)
  · change Fintype.card Γ • x - liftedWeightedSum ρ χ x = 0
    rw [liftedWeightedSum_torsion ρ χ x hpx he, sub_self]

/-- 有限性を仮定せず、乗法群の同じ自己同型作用を整数線形な加法作用へ読む。 -/
def additiveAction {B : Type*} [CommGroup B] (ρ : Γ →* MulAut B) :
    Γ →* (Additive B ≃ₗ[ℤ] Additive B) where
  toFun g := (MulEquiv.toAdditive (ρ g)).toIntLinearEquiv
  map_one' := by ext x; rw [map_one]; rfl
  map_mul' g h := by ext x; rw [map_mul]; rfl

end
end DkMath.Lib.Algebra.FiniteEigenTorsionBridge
