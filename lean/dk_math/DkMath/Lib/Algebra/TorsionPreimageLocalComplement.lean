/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionPreimageScalar
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod

#print "file: DkMath.Lib.Algebra.TorsionPreimageLocalComplement"

/-!
# 局所部分群の実際の像から補直線を構成する

`K ≤ F ≤ [n]⁻¹K` の同じ商への像を作り、持ち上げ直すと `F` に戻ることを証明する。
この往復から像の濃度を計算する。`F[n] ≤ K` なら像は元の捩れ像と交わらない。
`n=p`, `#V=p²`, `#C=p`, `#F=p^(m+1)`, `#K=p^m` ではこの像が補直線となる。

安定性は指定した作用素ごとに輸送するので、分解群だけの局所安定性にも使える。
局所部分群 `F` 自体の存在や、大域的な補直線の存在はここでは仮定のままである。
-/

namespace DkMath.Lib.Algebra.TorsionPreimageQuotient

variable {G : Type*} [AddCommGroup G] (n : ℕ) (K F : AddSubgroup G)

/-- 同じ部分群を同じ商に送った実際の像。 -/
def imageSubmodule : Submodule (ZMod n) (Quotient n K) :=
  AddSubgroup.toZModSubmodule n
    ((F.addSubgroupOf (preimage n K)).map (quotientMap n K))

/-- 像への所属は、元の部分群内の代表点の存在。 -/
theorem mem_imageSubmodule_iff (v : Quotient n K) :
    v ∈ imageSubmodule n K F ↔
      ∃ y : preimage n K, y.val ∈ F ∧ quotientMap n K y = v := Iff.rfl

/-- `K≤F≤[n]⁻¹K` なら、像を持ち上げて同じ `F` に戻る。 -/
theorem lift_imageSubmodule (hKF : K ≤ F) (hFP : F ≤ preimage n K) :
    liftSubmodule n K (imageSubmodule n K F) = F := by
  ext x
  rw [mem_liftSubmodule_iff]
  constructor
  · rintro ⟨hx, hv⟩
    obtain ⟨y, hyF, heq⟩ := (mem_imageSubmodule_iff n K F _).mp hv
    have hk : x - y.val ∈ K := by
      apply (quotientMap_eq_zero_iff n K (⟨x, hx⟩ - y)).mp
      rw [map_sub, heq, sub_self]
    simpa only [sub_add_cancel] using F.add_mem (hKF hk) hyF
  · intro hx
    exact ⟨hFP hx, (mem_imageSubmodule_iff n K F _).mpr ⟨⟨x, hFP hx⟩, hx, rfl⟩⟩

/-- 底の有限性の下で、像の濃度は元の実際の商の濃度公式に従う。 -/
theorem card_imageSubmodule_mul_card [Finite K] (hKF : K ≤ F) (hFP : F ≤ preimage n K) :
    Nat.card (imageSubmodule n K F) * Nat.card K = Nat.card F := by
  rw [← card_liftSubmodule, lift_imageSubmodule n K F hKF hFP]

/-- `F` の `n` 捩れが底へ戻れば、像は元の捩れ像と交わらない。 -/
theorem disjoint_imageSubmodule (hKF : K ≤ F)
    (hdown : ∀ x ∈ F, n • x = 0 → x ∈ K) :
    Disjoint (torsionImage n K) (imageSubmodule n K F) := by
  apply Submodule.disjoint_def.mpr
  intro v hC hF
  obtain ⟨e, he⟩ := (mem_torsionImage_iff n K v).mp hC
  obtain ⟨y, hyF, hy⟩ := (mem_imageSubmodule_iff n K F v).mp hF
  have hk : y.val - e.val ∈ K := by
    apply (quotientMap_eq_zero_iff n K (y - torsionInclusion n K e)).mp
    rw [map_sub]
    change quotientMap n K y - torsionMap n K e = 0
    rw [hy, he, sub_self]
  have heF : e.val ∈ F := by
    simpa only [sub_sub_cancel] using F.sub_mem hyF (hKF hk)
  have heK := hdown e.val heF e.property
  rw [← he]
  exact (torsionMap_eq_zero_iff n K e).mpr heK

/-- 部分群の安定性を同じ商の像へ運ぶ。全群安定性は要求しない。 -/
theorem imageSubmodule_stable {Γ : Type*} [Monoid Γ]
    (ρ : Γ →* AddMonoid.End G) (hK : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K)
    (g : Γ) (hF : ∀ x ∈ F, ρ g x ∈ F)
    {v : Quotient n K} (hv : v ∈ imageSubmodule n K F) :
    representation n K ρ hK g v ∈ imageSubmodule n K F := by
  obtain ⟨y, hy, rfl⟩ := (mem_imageSubmodule_iff n K F v).mp hv
  exact (mem_imageSubmodule_iff n K F _).mpr
    ⟨mapPreimage n K (ρ g) (hK g) y, hF y.val hy, rfl⟩

/-- 局所部分群から実際の補直線を構成する濃度判定。
分裂そのものを入力にせず、局所部分群の包含・濃度・捩れ降下から証明する。 -/
theorem isCompl_imageSubmodule {p m : ℕ} [Fact p.Prime]
    (K F : AddSubgroup G) [Finite K]
    (hKcard : Nat.card K = p ^ m) (hFcard : Nat.card F = p ^ (m + 1))
    (hV : Nat.card (Quotient p K) = p ^ 2)
    (hC : Nat.card (torsionImage p K) = p)
    (hKF : K ≤ F) (hFP : F ≤ preimage p K)
    (hdown : ∀ x ∈ F, p • x = 0 → x ∈ K) :
    IsCompl (torsionImage p K) (imageSubmodule p K F) := by
  have hp : p.Prime := Fact.out
  have hprod := card_imageSubmodule_mul_card p K F hKF hFP
  rw [hKcard, hFcard, pow_succ'] at hprod
  have hI : Nat.card (imageSubmodule p K F) = p :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos m) hprod
  let : Finite (Quotient p K) := Nat.finite_of_card_ne_zero (hV ▸ pow_ne_zero _ hp.ne_zero)
  have hdV : Module.finrank (ZMod p) (Quotient p K) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Quotient p K)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm
  have rank_one (D : Submodule (ZMod p) (Quotient p K)) (hD : Nat.card D = p) :
      Module.finrank (ZMod p) D = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := D)
    rw [hD, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le ((pow_one p).trans h)).symm
  have hdisj := disjoint_imageSubmodule p K F hKF hdown
  refine ⟨hdisj, codisjoint_iff.mpr ?_⟩
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (torsionImage p K) (imageSubmodule p K F)
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, rank_one _ hC, rank_one _ hI] at hd
  exact Submodule.eq_top_of_finrank_eq (hd.trans hdV.symm)

end DkMath.Lib.Algebra.TorsionPreimageQuotient
