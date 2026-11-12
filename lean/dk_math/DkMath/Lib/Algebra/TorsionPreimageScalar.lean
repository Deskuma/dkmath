/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionPreimageQuotient
import DkMath.Lib.Algebra.CyclicPrimePowerScalar

#print "file: DkMath.Lib.Algebra.TorsionPreimageScalar"

/-!
# 全段の倍写像 `V → K/nK` と、巡回塔の円分商

`V=([n]⁻¹K)/K` から `K` への倍写像は `nK=0` の場合にしか定義できない。
一般の段では、同じ倍写像を実際の商 `K/nK` へ送る。
その核は、元の `G[n]` の `V` における像 `C` に等しい。

巡回 `p^m` 群の底 `K[p]` 上の作用を `K/pK` へ輸送することで、第一段に
制限されない商作用の公式を得る。安定な補直線の存在はこの公式からは従わない。
-/

namespace DkMath.Lib.Algebra.TorsionPreimageQuotient

variable {G : Type*} [AddCommGroup G] (n : ℕ) (K : AddSubgroup G)

/-- 実際の `K` の中の倍写像の像。 -/
def multiples : AddSubgroup K := (nsmulAddMonoidHom n : K →+ K).range

/-- 全段で定義できる倍写像。値域を `K/nK` とすることが不可欠。 -/
def quotientMultiplyMod : Quotient n K →+ K ⧸ multiples n K :=
  QuotientAddGroup.lift _
    ((QuotientAddGroup.mk' (multiples n K)).comp (multiply n K)) (by
      intro y hy
      change QuotientAddGroup.mk' (multiples n K) (multiply n K y) = 0
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨⟨y.val, hy⟩, rfl⟩)

/-- 倍写像の代表公式。 -/
theorem quotientMultiplyMod_quotientMap (y : preimage n K) :
    quotientMultiplyMod n K (quotientMap n K y) =
      QuotientAddGroup.mk' (multiples n K) (multiply n K y) := rfl

/-- 周囲の倍写像が全射なら、同じ `V → K/nK` も全射。 -/
theorem quotientMultiplyMod_surjective
    (hlift : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Function.Surjective (quotientMultiplyMod n K) := by
  intro v
  obtain ⟨k, rfl⟩ := QuotientAddGroup.mk'_surjective (multiples n K) v
  obtain ⟨y, hy⟩ := multiply_surjective n K hlift k
  exact ⟨quotientMap n K y, congrArg (QuotientAddGroup.mk' (multiples n K)) hy⟩

/-- 捩れ像への所属は、代表点の `n` 倍が実際の `nK` に入ることと同値。 -/
theorem quotientMap_mem_torsionImage_iff (y : preimage n K) :
    quotientMap n K y ∈ torsionImage n K ↔
      ∃ k : K, n • y.val = n • k.val := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := (mem_torsionImage_iff n K _).mp h
    have hk : y.val - e.val ∈ K := by
      apply (quotientMap_eq_zero_iff n K
        (y - torsionInclusion n K e)).mp
      rw [map_sub]
      change quotientMap n K y - torsionMap n K e = 0
      rw [he, sub_self]
    refine ⟨⟨y.val - e.val, hk⟩, ?_⟩
    rw [nsmul_sub, show n • e.val = 0 from e.property, sub_zero]
  · rintro ⟨k, hk⟩
    have hkill : n • (y.val - k.val) = 0 := by rw [nsmul_sub, hk, sub_self]
    apply (mem_torsionImage_iff n K _).mpr
    refine ⟨⟨y.val - k.val, hkill⟩, ?_⟩
    let kP : preimage n K := ⟨k.val, K.nsmul_mem k.property n⟩
    change quotientMap n K (y - kP) = quotientMap n K y
    rw [map_sub, (quotientMap_eq_zero_iff n K kP).mpr k.property, sub_zero]

/-- 全段の倍写像の核は、同じ `G[n]` の像 `C`。 -/
theorem mem_torsionImage_iff_quotientMultiplyMod_eq_zero (v : Quotient n K) :
    v ∈ torsionImage n K ↔ quotientMultiplyMod n K v = 0 := by
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    change quotientMap n K y ∈ torsionImage n K ↔
      quotientMultiplyMod n K (quotientMap n K y) = 0
    rw [quotientMap_mem_torsionImage_iff n K y]
    change (∃ k : K, n • y.val = n • k.val) ↔
      QuotientAddGroup.mk' (multiples n K) (multiply n K y) = 0
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, (congrArg (fun z : K => z.val) hk).symm⟩

/-- 倍写像による `V/C ≃ K/nK`。型も写像も同じ実際の群から構成する。 -/
noncomputable def torsionImageQuotientEquiv
    (hlift : Function.Surjective (nsmulAddMonoidHom n : G →+ G)) :
    Quotient n K ⧸ (torsionImage n K).toAddSubgroup ≃+ K ⧸ multiples n K := by
  have hker : (torsionImage n K).toAddSubgroup = (quotientMultiplyMod n K).ker := by
    ext v
    exact mem_torsionImage_iff_quotientMultiplyMod_eq_zero n K v
  rw [hker]
  exact QuotientAddGroup.quotientKerEquivOfSurjective (quotientMultiplyMod n K)
    (quotientMultiplyMod_surjective n K hlift)

/-- 巡回塔の全段で、底の `p` 捩れ上のスカラーから `V/C` のスカラーを得る。
高位の `K` 全体でのスカラー作用を仮定せず、`pK=0` も要求しない。 -/
theorem representation_sub_nsmul_mem_torsionImage_of_cyclic
    {Γ : Type*} [Monoid Γ] {p m : ℕ} (hp : p.Prime)
    (K : AddSubgroup G) [Finite K] [IsAddCyclic K]
    (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (ρ : Γ →* AddMonoid.End G) (hstable : ∀ g : Γ, ∀ x ∈ K, ρ g x ∈ K)
    (χ : Γ → ℕ) (hsocle : ∀ g : Γ, ∀ x ∈ K, p • x = 0 → ρ g x = χ g • x)
    (g : Γ) (v : Quotient p K) :
    representation p K ρ hstable g v - χ g • v ∈ torsionImage p K := by
  induction v using QuotientAddGroup.induction_on with
  | H y =>
    change quotientMap p K (mapPreimage p K (ρ g) (hstable g) y) -
      χ g • quotientMap p K y ∈ torsionImage p K
    rw [← map_nsmul, ← map_sub, quotientMap_mem_torsionImage_iff]
    let f : K →+ K := {
      toFun x := ⟨ρ g x.val, hstable g x.val x.property⟩
      map_zero' := Subtype.ext (map_zero (ρ g))
      map_add' x z := Subtype.ext (map_add (ρ g) x.val z.val) }
    have hf : ∀ x : K, p • x = 0 → f x = χ g • x := by
      intro x hx
      apply Subtype.ext
      exact hsocle g x.val x.property (congrArg (fun z : K => z.val) hx)
    obtain ⟨k, hk⟩ := CyclicPrimePowerScalar.sub_nsmul_mem_range_of_socle
      hp hm hcard f (χ g) hf (multiply p K y)
    refine ⟨k, ?_⟩
    change p • (ρ g y.val - χ g • y.val) = p • k.val
    have hk' := congrArg (fun z : K => z.val) hk
    change p • k.val = ρ g (p • y.val) - χ g • (p • y.val) at hk'
    rw [nsmul_sub, ← map_nsmul, smul_comm p (χ g)]
    exact hk'.symm

end DkMath.Lib.Algebra.TorsionPreimageQuotient
