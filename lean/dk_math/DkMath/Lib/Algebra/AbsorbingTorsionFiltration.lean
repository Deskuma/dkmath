/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
S_WeierstrassCurve_exists_atP_filtration_of_multiplicativeReduction,
blob 125214f2533c1c8fcf1e358ab3d7147cf42d27d9, and
S_AddSubgroup_eq_atP_filtration_of_cyclic_stable_inertia_nontrivial,
blob cf7466796d1f8a4e4a57df2d4471e858379963a6 (both in P2M/Sol).
Modified: arbitrary additive group/actions, actual DkMath torsion kernels,
prime-power cyclic criterion and surjective multiplication replace duplicate counting.
-/

import DkMath.Lib.Algebra.PrimePowerCyclicCriterion
import DkMath.Lib.Algebra.TorsionMultiplication
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic

#print "file: DkMath.Lib.Algebra.AbsorbingTorsionFiltration"

/-!
# 吸収部分群の高次捩れの濃度と一意性

`F_m=G[p^m]∩H` を同じ実際の群に作る。底の濃度上界と非自明な作用があれば、
高次の各 `F_m` は巡回で濃度 `p^m` となる。上界には底の小ささを、下界には
倍写像の全射性と作用差の吸収を使う。濃度や巡回性を入力にしていない。

さらに底で非自明に作用される安定巡回群は、作用差を吸収する部分群に含まれる。
この一意性を、実際の局所還元核と大域安定な巡回段の照合に用いる。
-/

namespace DkMath.Lib.Algebra.AbsorbingTorsionFiltration

open TorsionMultiplication

variable {G : Type*} [AddCommGroup G] (p m : ℕ) (H : AddSubgroup G)

/-- 実際の高次捩れと同じ吸収部分群との交わり。 -/
def stage : AddSubgroup G := Kernel G (p ^ m) ⊓ H

instance finiteStage [Finite (Kernel G (p ^ m))] : Finite (stage p m H) :=
  Finite.of_injective (AddSubgroup.inclusion (show stage p m H ≤ Kernel G (p ^ m) from inf_le_left))
    (AddSubgroup.inclusion_injective _)

/-- 吸収と非自明な底の作用が、各段の正確な濃度と巡回性を強制する。 -/
theorem cyclic_and_card {Γ : Type*} [Monoid Γ] {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (H : AddSubgroup G) [Finite (Kernel G p)] [Finite (Kernel G (p ^ m))]
    (hsocle : Nat.card (Kernel G p ⊓ H : AddSubgroup G) ≤ p)
    (ρ : Γ →* AddMonoid.End G) (I : Set Γ)
    (habs : ∀ g ∈ I, ∀ y : G, p ^ m • y = 0 → ρ g y - y ∈ H)
    (hnontriv : ∃ g ∈ I, ∃ x : G, p • x = 0 ∧ ρ g x ≠ x)
    (hlift : Function.Surjective (nsmulAddMonoidHom (p ^ (m - 1)) : G →+ G)) :
    IsAddCyclic (stage p m H) ∧ Nat.card (stage p m H) = p ^ m := by
  let F := stage p m H
  let : Finite (Kernel G p ⊓ H : AddSubgroup G) :=
    Finite.of_injective (AddSubgroup.inclusion inf_le_left) (AddSubgroup.inclusion_injective _)
  have htors (x : F) : p ^ m • x = 0 := Subtype.ext x.property.1
  let f : {x : F // p • x = 0} → (Kernel G p ⊓ H : AddSubgroup G) := fun x =>
    ⟨x.val.val, ⟨congrArg (fun z : F => z.val) x.property, x.val.property.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : (Kernel G p ⊓ H : AddSubgroup G) => z.val) h))
  have hs : Nat.card {x : F // p • x = 0} ≤ p :=
    (Nat.card_le_card_of_injective f hf).trans hsocle
  obtain ⟨hcyc, hdvd⟩ :=
    PrimePowerCyclicCriterion.isAddCyclic_and_card_dvd_of_prime_power_exponent hp m htors hs
  refine ⟨hcyc, ?_⟩
  obtain ⟨e, hem, he⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  suffices e = m by simpa only [this] using he
  by_contra hne
  have hem' : e ≤ m - 1 := by omega
  obtain ⟨g, hg, x, hx, hmove⟩ := hnontriv
  obtain ⟨y, hy⟩ := hlift x
  have hy' : p ^ (m - 1) • y = x := hy
  have hyt : p ^ m • y = 0 := by
    rw [← Nat.sub_add_cancel hm, pow_succ', mul_nsmul', hy']
    exact hx
  have hd : ρ g y - y ∈ F := by
    refine ⟨?_, habs g hg y hyt⟩
    change p ^ m • (ρ g y - y) = 0
    rw [nsmul_sub, ← map_nsmul, hyt, map_zero, sub_self]
  have hk : p ^ e • (ρ g y - y) = 0 := by
    have h := card_nsmul_eq_zero' (x := (⟨ρ g y - y, hd⟩ : F))
    rw [he] at h
    exact congrArg (fun z : F => z.val) h
  have hk' : p ^ (m - 1) • (ρ g y - y) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      ((addOrderOf_dvd_of_nsmul_eq_zero hk).trans (pow_dvd_pow p hem'))
  apply hmove
  apply sub_eq_zero.mp
  rw [← hy', map_nsmul, ← nsmul_sub]
  exact hk'

/-- 非自明な底の作用を持つ安定巡回群は、作用差の吸収先に含まれる。
非自明性を落とすと、恒等作用では任意の部分群が候補となり偽になる。 -/
theorem le_of_nontrivial_socle {p m : ℕ} (hp : p.Prime)
    (K F : AddSubgroup G) [IsAddCyclic K]
    (hexp : ∀ x ∈ K, p ^ m • x = 0) (f : G →+ G)
    (hstable : ∀ x ∈ K, f x ∈ K)
    (hnontriv : ∃ x ∈ K, p • x = 0 ∧ f x ≠ x)
    (habs : ∀ x ∈ K, f x - x ∈ F) : K ≤ F := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := K)
  have hgen : ∀ x ∈ K, ∃ a : ℤ, a • g.val = x := by
    intro x hx
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
    exact ⟨a, congrArg (fun z : K => z.val) ha⟩
  obtain ⟨a, ha⟩ := hgen (f g.val) (hstable g.val g.property)
  have hdiff : (a - 1) • g.val ∈ F := by
    rw [sub_zsmul, one_zsmul, ha]
    simpa only [sub_eq_add_neg] using habs g.val g.property
  have hnd : ¬ (p : ℤ) ∣ a - 1 := by
    intro h
    obtain ⟨x, hx, hpx, hmove⟩ := hnontriv
    obtain ⟨b, rfl⟩ := hgen x hx
    have hact : f (b • g.val) = a • (b • g.val) := by
      rw [map_zsmul, ← ha, smul_comm]
    obtain ⟨d, hd⟩ := h
    have hz : (a - 1) • (b • g.val) = 0 := by
      rw [hd, mul_comm, mul_zsmul, natCast_zsmul, hpx, zsmul_zero]
    apply hmove
    rw [hact]
    calc a • (b • g.val) = (a - 1) • (b • g.val) + (1 : ℤ) • (b • g.val) := by
          rw [← add_zsmul, sub_add_cancel]
      _ = b • g.val := by rw [hz, zero_add, one_zsmul]
  have hcop : IsCoprime ((p : ℤ) ^ m) (a - 1) :=
    (((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hnd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hk : ((p : ℤ) ^ m) • g.val = 0 := by
    simpa only [← Nat.cast_pow, natCast_zsmul] using hexp g.val g.property
  have hgF : g.val ∈ F := by
    have heq : g.val = v • ((a - 1) • g.val) := by
      calc g.val = (1 : ℤ) • g.val := (one_zsmul _).symm
        _ = (u * (p : ℤ) ^ m + v * (a - 1)) • g.val := by rw [huv]
        _ = v • ((a - 1) • g.val) := by rw [add_zsmul, mul_zsmul, mul_zsmul, hk, zsmul_zero, zero_add]
    exact heq ▸ F.zsmul_mem hdiff v
  intro x hx
  obtain ⟨b, rfl⟩ := hgen x hx
  exact F.zsmul_mem hgF b

end DkMath.Lib.Algebra.AbsorbingTorsionFiltration
