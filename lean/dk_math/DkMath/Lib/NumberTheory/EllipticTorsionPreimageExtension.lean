/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionPreimageQuotient
import DkMath.Lib.Algebra.PrimePowerCyclicCriterion
import DkMath.Lib.NumberTheory.EllipticStableLine
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard
import Mathlib.GroupTheory.SpecificGroups.Cyclic

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionPreimageExtension"

/-!
# 実際の捩れ逆像商と、次段の二次元 extension

有限の Galois 安定部分群 `K` から、同じ幾何学的点群の商 `V=(p⁻¹K)/K` と
その Galois 表現を構成する。既存の倍写像の全射性と `#E[p]=p²` により、
`#V=p²`, `dim V=2` は追加の算術仮定なしに従う。

`K` が位数 `p^m`, `m≥1` の巡回群なら、元の `E[p]` の像 `C` の濃度は `p`、
次元は1となる。元の Cofixed 直線が `K` に含まれれば、この同じ `C` は点ごとに
Galois 固定である。`K` が `p^m` 倍で消えれば、表現の開核も内部供給する。

ここで構成するのは extension の実際の舞台と固定直線であり、安定な補直線の
存在ではない。局所分裂と大域 extension 消滅から補直線を作る算術は引き続き必要。
-/

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

open DkMath.Lib.Algebra
open DkMath.Lib.RepresentationTheory

noncomputable section

variable (E : WeierstrassCurve ℚ)

/-- 幾何学的な点への座標作用を、加法自己準同型のモノイド準同型として公開する。 -/
def pointActionEndHom : Field.absoluteGaloisGroup ℚ →* AddMonoid.End (Points E) where
  toFun := pointAction E
  map_one' := AddMonoidHom.ext (pointAction_one E)
  map_mul' σ τ := AddMonoidHom.ext (pointAction_mul E σ τ)

/-- 同じ Galois 安定部分群の逆像商に降ろした実際の表現。 -/
def preimageRepresentation (p : ℕ) (K : AddSubgroup (Points E))
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction E σ x ∈ K) :
    Representation (ZMod p) (Field.absoluteGaloisGroup ℚ)
      (TorsionPreimageQuotient.Quotient p K) :=
  TorsionPreimageQuotient.representation p K (pointActionEndHom E) hstable

/-- 商の標準代表に対する作用は、元の同じ点への Galois 作用である。 -/
theorem preimageRepresentation_quotientMap (p : ℕ) (K : AddSubgroup (Points E))
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction E σ x ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) (y : TorsionPreimageQuotient.preimage p K) :
    preimageRepresentation E p K hstable σ (TorsionPreimageQuotient.quotientMap p K y) =
      TorsionPreimageQuotient.quotientMap p K
        (TorsionPreimageQuotient.mapPreimage p K (pointAction E σ) (hstable σ) y) := rfl

variable {p : ℕ} [Fact p.Prime]

/-- `p^m` で消える安定部分群の逆像商表現は開核を持つ。
`E[p^(m+1)]` の実際の開核を含むことから導き、連続性を provider にしない。 -/
theorem preimageRepresentation_kernel_isOpen
    (K : AddSubgroup (Points E))
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction E σ x ∈ K)
    (m : ℕ) (hKtors : ∀ x ∈ K, p ^ m • x = 0) :
    IsOpen ((preimageRepresentation E p K hstable).ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  apply Subgroup.isOpen_mono (H₁ := representationKernel E (p ^ (m + 1))) _
    (representationKernel_isOpen_of_ne_zero E _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))
  intro σ hσ
  change representation E (p ^ (m + 1)) σ = 1 at hσ
  change preimageRepresentation E p K hstable σ = 1
  apply LinearMap.ext
  intro v
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    have hy : p ^ (m + 1) • y.val = 0 := by
      rw [pow_succ, mul_nsmul']
      exact hKtors _ y.property
    have hfix : representation E (p ^ (m + 1)) σ (⟨y.val, hy⟩ : Torsion E (p ^ (m + 1))) =
        ⟨y.val, hy⟩ := by rw [hσ]; rfl
    change TorsionPreimageQuotient.quotientMap p K
      (TorsionPreimageQuotient.mapPreimage p K (pointAction E σ) (hstable σ) y) =
      TorsionPreimageQuotient.quotientMap p K y
    apply congrArg (TorsionPreimageQuotient.quotientMap p K)
    apply Subtype.ext
    exact congrArg (fun z : Torsion E (p ^ (m + 1)) => z.val) hfix

/-- 元の Cofixed 直線を含む `K` の逆像商では、実際の捩れ像 `C` が点ごとに固定される。 -/
theorem preimageRepresentation_fixed_torsionImage_of_cofixed
    (K : AddSubgroup (Points E))
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction E σ x ∈ K)
    (L : Submodule (ZMod p) (Torsion E p))
    (hcofixed : IsCofixedOn (representation E p) L)
    (hLK : pointSubgroup E p L ≤ K) :
    IsFixedOn (preimageRepresentation E p K hstable) (TorsionPreimageQuotient.torsionImage p K) := by
  apply TorsionPreimageQuotient.representation_fixed_on_torsionImage
  intro σ e he
  apply hLK
  exact ⟨representation E p σ (⟨e, he⟩ : Torsion E p) - ⟨e, he⟩,
    hcofixed σ ⟨e, he⟩, rfl⟩

variable [E.IsElliptic]

/-- 楕円曲線の実際の倍写像の全射性と濃度公式により、逆像商の濃度は `p²`。 -/
theorem card_preimageQuotient (K : AddSubgroup (Points E)) [Finite K] :
    Nat.card (TorsionPreimageQuotient.Quotient p K) = p ^ 2 := by
  rw [TorsionPreimageQuotient.card_quotient p K
    (multiplication_surjective E p (Fact.out : p.Prime).ne_zero)]
  exact card_torsion_sq E p (Fact.out : p.Prime).ne_zero

/-- 追加の extension 濃度仮定なしの二次元性。 -/
theorem finrank_preimageQuotient (K : AddSubgroup (Points E)) [Finite K] :
    Module.finrank (ZMod p) (TorsionPreimageQuotient.Quotient p K) = 2 := by
  have hc := card_preimageQuotient E (p := p) K
  let : Finite (TorsionPreimageQuotient.Quotient p K) :=
    Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have h := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := TorsionPreimageQuotient.Quotient p K)
  rw [hc, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm

/-- 巡回 `p^m` 部分群の `p` 捩れ核は `p` 個なので、商の捩れ像 `C` も `p` 個。
巡回性と `m≥1` を保持し、一般の位数 `p^m` の群へ拡張していない。 -/
theorem card_torsionImage_of_cyclic
    (K : AddSubgroup (Points E)) [Finite K] [IsAddCyclic K]
    {m : ℕ} (hm : 1 ≤ m) (hKcard : Nat.card K = p ^ m) :
    Nat.card (TorsionPreimageQuotient.torsionImage p K) = p := by
  have hker : Nat.card (TorsionMultiplication.Kernel K p) = p := by
    change Nat.card (nsmulAddMonoidHom p : K →+ K).ker = p
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker K p, hKcard,
      Nat.gcd_eq_right (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hm))]
  have h := TorsionPreimageQuotient.card_torsionImage_mul_card_kernel p K
  have hg : Nat.card (TorsionMultiplication.Kernel (Points E) p) = p ^ 2 :=
    card_torsion_sq E p (Fact.out : p.Prime).ne_zero
  rw [hker, hg, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h

/-- 同じ実際の像部分加群 `C` の一次元性。 -/
theorem finrank_torsionImage_of_cyclic
    (K : AddSubgroup (Points E)) [Finite K] [IsAddCyclic K]
    {m : ℕ} (hm : 1 ≤ m) (hKcard : Nat.card K = p ^ m) :
    Module.finrank (ZMod p) (TorsionPreimageQuotient.torsionImage p K) = 1 := by
  have hc := card_torsionImage_of_cyclic E K hm hKcard
  let : Finite (TorsionPreimageQuotient.torsionImage p K) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : p.Prime).ne_zero)
  have h := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := TorsionPreimageQuotient.torsionImage p K)
  rw [hc, Nat.card_zmod] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((pow_one p).trans h)).symm

/-- 安定な補部分加群が得られれば、その具体的な逆像から塔の次段を構成できる。
`C'` の存在をここで仮定なしに宣言せず、必要な arithmetic splitting の入力を明示する。
濃度・包含・巡回性・捩れ次数・安定性・底への降下は全て実装済みの商の計算から供給する。 -/
theorem exists_tower_step_of_stable_complement
    (K : AddSubgroup (Points E)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction E σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hKcard : Nat.card K = p ^ m)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (C' : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K))
    (hcompl : IsCompl (TorsionPreimageQuotient.torsionImage p K) C')
    (hCstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ v ∈ C',
      preimageRepresentation E p K hstable σ v ∈ C') :
    ∃ K' : AddSubgroup (Points E), K ≤ K' ∧ Nat.card K' = p ^ (m + 1) ∧ IsAddCyclic K' ∧
      (∀ x ∈ K', p ^ (m + 1) • x = 0) ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K', pointAction E σ x ∈ K') ∧
      (∀ x ∈ K', p • x = 0 → x ∈ K) := by
  have hCcard := card_torsionImage_of_cyclic E K hm hKcard
  have hVcard := card_preimageQuotient E (p := p) K
  have hprod : Nat.card (TorsionPreimageQuotient.torsionImage p K) * Nat.card C' =
      Nat.card (TorsionPreimageQuotient.Quotient p K) :=
    (Nat.card_prod _ _).symm.trans
      (Nat.card_congr (Submodule.prodEquivOfIsCompl _ _ hcompl).toEquiv)
  rw [hCcard, hVcard, pow_two] at hprod
  have hC'card : Nat.card C' = p := Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos hprod
  let J := TorsionPreimageQuotient.liftSubmodule p K C'
  have hJcard : Nat.card J = p ^ (m + 1) := by
    rw [TorsionPreimageQuotient.card_liftSubmodule, hC'card, hKcard, pow_succ']
  have hJtors : ∀ x ∈ J, p ^ (m + 1) • x = 0 := by
    intro x hx
    obtain ⟨hy, _⟩ := (TorsionPreimageQuotient.mem_liftSubmodule_iff p K C' x).mp hx
    rw [pow_succ, mul_nsmul']
    exact hKtors _ hy
  have hdown : ∀ x ∈ J, p • x = 0 → x ∈ K := by
    intro x hx hpx
    exact TorsionPreimageQuotient.torsion_mem_of_lift_disjoint p K C' hcompl.disjoint hx hpx
  let : Finite J := Nat.finite_of_card_ne_zero (by rw [hJcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hker : Nat.card (TorsionMultiplication.Kernel K p) = p := by
    change Nat.card (nsmulAddMonoidHom p : K →+ K).ker = p
    rw [IsAddCyclic.card_nsmulAddMonoidHom_ker K p, hKcard,
      Nat.gcd_eq_right (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hm))]
  let f : {x : J // p • x = 0} → TorsionMultiplication.Kernel K p := fun x =>
    ⟨⟨x.val.val, hdown _ x.val.property (congrArg (fun z : J => z.val) x.property)⟩,
      Subtype.ext (congrArg (fun z : J => z.val) x.property)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : TorsionMultiplication.Kernel K p => z.val.val) hxy
  have hsocle : Nat.card {x : J // p • x = 0} ≤ p := by
    calc
      Nat.card {x : J // p • x = 0} ≤ Nat.card (TorsionMultiplication.Kernel K p) :=
        Nat.card_le_card_of_injective f hf
      _ = p := hker
  have hJcyclic : IsAddCyclic J :=
    (PrimePowerCyclicCriterion.isAddCyclic_and_card_dvd_of_prime_power_exponent
      (Fact.out : p.Prime) (m + 1) (fun x : J => Subtype.ext (hJtors x.val x.property)) hsocle).1
  refine ⟨J, TorsionPreimageQuotient.le_liftSubmodule p K C', hJcard, hJcyclic, hJtors, ?_, hdown⟩
  intro σ x hx
  exact TorsionPreimageQuotient.liftSubmodule_stable p K (pointActionEndHom E) hstable
    C' hCstable σ hx

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
