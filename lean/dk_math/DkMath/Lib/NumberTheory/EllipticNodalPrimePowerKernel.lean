/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Extends DkMath.Lib.NumberTheory.EllipticNodalReductionKernel (its provenance is
recorded there): add prime-power induction in the actual residue point group,
then reuse the same reduction, kernel and critical-centre computations.
-/

import DkMath.Lib.NumberTheory.EllipticNodalReductionKernel

#print "file: DkMath.Lib.NumberTheory.EllipticNodalPrimePowerKernel"

/-!
# 節点還元の `p` 捩れ消滅から、全ての `p^m` 捩れ消滅へ

剰余標数 `p` の滑らかな節点点群で `p` 倍写像が単射なら、その反復も単射。
この事実を実際の還元準同型に適用し、高次の滑らかな捩れ点も還元核へ送る。
一般ファイバーで `p` が単元であるとは仮定しない。
-/

namespace DkMath.Lib.NumberTheory.EllipticNodalReductionKernel

open WeierstrassCurve IsLocalRing EllipticGoodReductionSeparation EllipticSmoothReduction

/-- 同じ剰余節点曲線の滑らかな点群に非零の `p^m` 捩れはない。 -/
theorem eq_zero_of_residue_characteristic_prime_power
    {k : Type*} [Field k] [DecidableEq k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (W : WeierstrassCurve k) (x₀ y₀ : k) (he : W.toAffine.Equation x₀ y₀)
    (hs : ¬ W.toAffine.Nonsingular x₀ y₀) (hnode : W.b₂ + 12 * x₀ ≠ 0)
    (m : ℕ) (P : W.toAffine.Point) (hP : p ^ m • P = 0) : P = 0 := by
  induction m generalizing P with
  | zero => simpa only [pow_zero, one_nsmul] using hP
  | succ m ih =>
    have h : p ^ m • (p • P) = 0 := by rwa [← mul_nsmul', ← pow_succ]
    exact EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion
      W x₀ y₀ he hs hnode P (ih (p • P) h)

/-- 高次捩れの実際の還元が零なら、滑らかな点は実際の還元核へ入る。 -/
theorem mem_kernel_of_smooth_prime_power_torsion
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]
    (x₀ y₀ : ResidueField A) (he : (W.map (residue A)).toAffine.Equation x₀ y₀)
    (hs : ¬ (W.map (residue A)).toAffine.Nonsingular x₀ y₀)
    (hnode : (W.map (residue A)).b₂ + 12 * x₀ ≠ 0)
    {P : (W.map A.subtype).toAffine.Point} (hP : HasSmoothReduction W P)
    (m : ℕ) (ht : p ^ m • P = 0) :
    P ∈ EllipticReductionKernel.reductionKernel A W := by
  classical
  have hz := eq_zero_of_residue_characteristic_prime_power
    (W.map (residue A)) x₀ y₀ he hs hnode m (reducePointSmooth W P)
      (nsmul_reduce_eq_zero W hP _ ht)
  cases P with
  | zero => exact (EllipticReductionKernel.reductionKernel A W).zero_mem
  | some x y h =>
    apply (EllipticReductionKernel.some_mem_iff A W h).mpr
    intro hx
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
    have hns := (hasSmoothReduction_some_iff W h).mp hP hx hy
    rw [reducePointSmooth_some_of_mem W h hx hns] at hz
    exact Affine.Point.some_ne_zero hns hz

/-- 同じ臨界中心で節点を供給し、全ての高次捩れで極または無限遠を結論する。 -/
theorem pole_of_smooth_prime_power_torsion_of_model
    {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
    (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]
    (V : WeierstrassCurve L) (hmodel : W.map A.subtype = V)
    (C : EllipticCriticalCentre.CriticalCentre A V)
    {P : V.toAffine.Point} (hP : HasSmoothReduction W P) (m : ℕ) (ht : p ^ m • P = 0) :
    EllipticDyadicSeparation.PoleOrZero A V P := by
  classical
  subst V
  let xr := residue A (⟨C.x, C.x_mem⟩ : A)
  let yr := residue A (⟨C.y, C.y_mem⟩ : A)
  have hC := C.residue_singular W
  have hnode : (W.map (residue A)).b₂ + 12 * xr ≠ 0 := by
    let n : A := W.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)
    have hn : IsUnit n := (A.valuation_eq_one_iff _).mpr C.node_unit
    have hr := (residue_ne_zero_iff_isUnit n).mpr hn
    simpa only [n, map_add, map_mul, map_ofNat, WeierstrassCurve.map_b₂] using hr
  exact mem_kernel_of_smooth_prime_power_torsion W xr yr hC.1 hC.2 hnode hP m ht

end DkMath.Lib.NumberTheory.EllipticNodalReductionKernel
