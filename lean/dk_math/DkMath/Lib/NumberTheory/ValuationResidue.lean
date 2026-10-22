/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean,
blob 38bdee599f8b536cb30402a8d1dbef001a3d89da.
Modified: reuse DkMath coordinate integrality, smooth reduction and actual reduction kernel;
separate valuation-residue arithmetic from coordinate and group constructions.
-/

import DkMath.Lib.NumberTheory.ValuationInertia

#print "file: DkMath.Lib.NumberTheory.ValuationResidue"

/-!
# NOTE-031-004 第2部: 単元分母と剰余の座標計算

付値環の単元を分母に持つ式だけを剰余へ移す。非単元分母の除算を剰余へ交換しない。
後続の接線と割線では、分母の単元性をその都度証明して本章の補題へ渡す。
-/
namespace DkMath.Lib.NumberTheory.ValuationResidue
open IsLocalRing
variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- 非単元でない元は非零である。 -/
theorem ne_zero_of_notMem_nonunits {b : L} (hb : b ∉ A.nonunits) : b ≠ 0 := by
  rintro rfl
  exact hb (zero_mem _)

/-- 非単元でない元の逆元は付値環へ入る。 -/
theorem inv_mem_of_notMem_nonunits {b : L} (hb : b ∉ A.nonunits) : b⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or] at hb
  exact Classical.not_not.mp hb.2

/-- 付値環の元が非単元であることは剰余が零であることに等しい。 -/
theorem coe_mem_nonunits_iff_residue_eq_zero (b : A) :
    (b : L) ∈ A.nonunits ↔ residue A b = 0 :=
  ValuationSubring.coe_mem_nonunits_iff.trans (IsLocalRing.residue_eq_zero_iff _).symm

/-- 分母が単元となる商は付値環に入る。 -/
theorem div_mem_of_mem_of_notMem_nonunits {a b : L} (ha : a ∈ A) (hb : b ∉ A.nonunits) :
    a / b ∈ A := by
  rw [div_eq_mul_inv]
  exact A.toSubring.mul_mem ha (inv_mem_of_notMem_nonunits A hb)


/-- 非単元でない整元の剰余は非零である。 -/
theorem residue_ne_zero_of_notMem_nonunits {b : L} (hb : b ∈ A) (hb' : b ∉ A.nonunits) :
    residue A ⟨b, hb⟩ ≠ 0 := fun h =>
  hb' ((coe_mem_nonunits_iff_residue_eq_zero A ⟨b, hb⟩).mpr h)


/-- 同じ体の元を表す付値環の元は同じ剰余を持つ。 -/
theorem residue_eq_of_coe_eq {a : L} (ha : a ∈ A) {v : A} (hav : a = (v : L)) :
    residue A ⟨a, ha⟩ = residue A v :=
  congrArg (residue A) (Subtype.ext hav)


/-- 単元分母の商の剰余は剰余の商となる。 -/
theorem residue_div {a b : L} (ha : a ∈ A) (hb : b ∈ A) (hb' : b ∉ A.nonunits)
    (hq : a / b ∈ A) :
    residue A ⟨a / b, hq⟩ = residue A ⟨a, ha⟩ / residue A ⟨b, hb⟩ := by
  have hb0 : b ≠ 0 := ne_zero_of_notMem_nonunits A hb'
  have hbres : residue A ⟨b, hb⟩ ≠ 0 := residue_ne_zero_of_notMem_nonunits A hb hb'
  rw [eq_div_iff hbres, ← map_mul]
  refine congrArg (residue A) (Subtype.ext ?_)
  push_cast
  exact div_mul_cancel₀ a hb0


/-- 体上の商表示を剰余体上の商表示へ移す。 -/
theorem residue_eq_div_of_eq_div {a c d : L} (ha : a ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hd' : d ∉ A.nonunits) (hacd : a = c / d) :
    residue A ⟨a, ha⟩ = residue A ⟨c, hc⟩ / residue A ⟨d, hd⟩ := by
  rw [residue_eq_of_coe_eq A ha
    (v := ⟨c / d, div_mem_of_mem_of_notMem_nonunits A hc hd'⟩) hacd]
  exact residue_div A hc hd hd' _


/-- 整元の剰余の一致は差の非単元性と同値である。 -/
theorem residue_eq_residue_iff_sub_mem_nonunits {a b : L} (ha : a ∈ A) (hb : b ∈ A) :
    residue A ⟨a, ha⟩ = residue A ⟨b, hb⟩ ↔ a - b ∈ A.nonunits := by
  constructor
  · intro h
    have h0 : residue A (⟨a, ha⟩ - ⟨b, hb⟩) = 0 := by rw [map_sub, h, sub_self]
    have := (coe_mem_nonunits_iff_residue_eq_zero A _).mpr h0
    simpa using this
  · intro h
    have h0 : residue A (⟨a, ha⟩ - ⟨b, hb⟩) = 0 :=
      (coe_mem_nonunits_iff_residue_eq_zero A _).mp (by simpa using h)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end DkMath.Lib.NumberTheory.ValuationResidue
