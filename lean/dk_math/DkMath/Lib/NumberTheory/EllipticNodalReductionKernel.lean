/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothReduction
import DkMath.Lib.NumberTheory.EllipticNodalTorsion
import DkMath.Lib.NumberTheory.EllipticCriticalCentre

#print "file: DkMath.Lib.NumberTheory.EllipticNodalReductionKernel"

/-!
# NOTE-031-004 第2部: 節点還元の零成分のp-torsionは還元核へ入る

前章で実際に構成した加法準同型により、p倍零性を剰余曲線へ運ぶ。
剰余標数pの節点曲線の滑らかな点群には非零p-torsionがないので、還元は零となる。
従って元の点は無限遠または極の点である。有限整点を仮定すると、
その還元は有限滑らかな点であるため、零という結論と矛盾する。
この論証は一般ファイバーの標数零を仮定せず、除法多項式も使用しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticNodalReductionKernel
open WeierstrassCurve IsLocalRing EllipticGoodReductionSeparation EllipticSmoothReduction
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
  (W : WeierstrassCurve A) [DecidableEq (ResidueField A)]
  {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p]

omit [DecidableEq (ResidueField A)] in
/-- 同じ剰余曲線に節点が存在する場合、滑らかな還元を持つp-torsionは還元核に属する。
節点・非特異接錐・剰余標数は明示的な仮定であり、乗法的還元の適用側で供給する。 -/
theorem mem_kernel_of_smooth_torsion (x₀ y₀ : ResidueField A)
    (he : (W.map (residue A)).toAffine.Equation x₀ y₀)
    (hs : ¬ (W.map (residue A)).toAffine.Nonsingular x₀ y₀)
    (hnode : (W.map (residue A)).b₂ + 12 * x₀ ≠ 0)
    {P : (W.map A.subtype).toAffine.Point}
    (hP : HasSmoothReduction W P) (hp : p • P = 0) :
    P ∈ EllipticReductionKernel.reductionKernel A W := by
  classical
  have hred := nsmul_reduce_eq_zero W hP p hp
  have hzero := EllipticNodalTorsion.eq_zero_of_residue_characteristic_torsion
    (W.map (residue A)) x₀ y₀ he hs hnode (reducePointSmooth W P) hred
  cases P with
  | zero => exact (EllipticReductionKernel.reductionKernel A W).zero_mem
  | some x y h =>
    apply (EllipticReductionKernel.some_mem_iff A W h).mpr
    intro hx
    have hy := EllipticTorsionValuationIntegrality.y_mem_of_x_mem A W _ rfl h.1 hx
    have hns := (hasSmoothReduction_some_iff W h).mp hP hx hy
    rw [reducePointSmooth_some_of_mem W h hx hns] at hzero
    exact Affine.Point.some_ne_zero hns hzero

omit [DecidableEq (ResidueField A)] in
/-- 臨界中心から実際の剰余節点を供給して、元の一般ファイバーで極または無限遠を結論する。
Cの節点量が単元である条件は剰余での接錐の非退化性を保証する。 -/
theorem pole_of_smooth_torsion_of_model (V : WeierstrassCurve L)
    (hmodel : W.map A.subtype = V) (C : EllipticCriticalCentre.CriticalCentre A V)
    {P : V.toAffine.Point} (hP : HasSmoothReduction W P) (hp : p • P = 0) :
    EllipticDyadicSeparation.PoleOrZero A V P := by
  classical
  subst V
  let xr := residue A (⟨C.x, C.x_mem⟩ : A)
  let yr := residue A (⟨C.y, C.y_mem⟩ : A)
  have hC := C.residue_singular W
  have hnode : (W.map (residue A)).b₂ + 12 * xr ≠ 0 := by
    let n : A := W.b₂ + 12 * (⟨C.x, C.x_mem⟩ : A)
    have hn : IsUnit n := (A.valuation_eq_one_iff _).mpr C.node_unit
    have hres := (residue_ne_zero_iff_isUnit n).mpr hn
    simpa only [n, map_add, map_mul, map_ofNat, WeierstrassCurve.map_b₂] using hres
  exact mem_kernel_of_smooth_torsion W xr yr hC.1 hC.2 hnode hP hp

end DkMath.Lib.NumberTheory.EllipticNodalReductionKernel
