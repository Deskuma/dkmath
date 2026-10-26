/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelDivisor
import DkMath.Lib.NumberTheory.WeierstrassPrincipalPushHom

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelHom"

/-!
# 同じ有限核・同じ座標・同じ全点関数の加法準同型

[DkMath.Lib] 前段の同じ全点関数の主因子保存を、アフィンAbel対応へ接続する。
源の基底変換モデルの全点付値を既存pointValuationと一致させ、標的も既存kernelModelを使う。
準同型のtoFunは既存oddKernelPointMapそのものであり、核は同じH、全射性も既存のもの。
安定核では既存K係数モデルへの移送を加法準同型へ昇格し、同じGalois同変性を保持する。

点群の準同型を構成する。スキーム射としてのisogeny、整数モデルや局所還元は含まない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open WeierstrassCurve WeierstrassCurve.Affine
open EllipticTorsionRepresentation WeierstrassFinitePlace WeierstrassPrincipalPushHom
variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance instDecidableEqEllipticFiniteKernelHom {α : Type*} :
    DecidableEq α := Classical.decEq _

omit [CharZero K] in
/-- [DkMath.Lib] 同じ源の基底変換モデルの全点付値は、既存の全点付値そのものである。 -/
theorem geometric_modelPointValuation (P : Points E) :
    modelPointValuation (E.map (algebraMap K (AlgebraicClosure K))) P = pointValuation E P := by
  cases P with
  | zero =>
    change modelPointValuation (E.map (algebraMap K (AlgebraicClosure K))) 0 = pointValuation E 0
    rw [modelPointValuation_zero]
    simp only [pointValuation, ↓reduceDIte]
    rfl
  | some x y hxy =>
    simp only [modelPointValuation, pointValuation, Point.some_ne_zero, ↓reduceDIte]
    rfl

/-- [DkMath.Lib] 同じ全点関数は、同じ二点の実際の加法を保存する。
追加のAbel・Picard・点準同型providerを要求せず、証明済み主因子輸送から導く。 -/
theorem oddKernelPointMap_add (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P Q : Points E) :
    oddKernelPointMap E H hodd (P + Q) =
      oddKernelPointMap E H hodd P + oddKernelPointMap E H hodd Q := by
  let := kernelModel_isElliptic_of_odd_card E H hodd
  apply map_add_of_principal_push (E.map (algebraMap K (AlgebraicClosure K))) (kernelModel E H)
    (oddKernelPointMap E H hodd) ((oddKernelPointMap_eq_zero_iff E H hodd 0).mpr H.zero_mem)
  intro D hD
  have hs : ValuationDivisor.IsPrincipal (pointValuation E) D := by
    obtain ⟨f, hf, hd⟩ := hD
    refine ⟨f, hf, ?_⟩
    change ∀ P : Points E, D P = -WithZero.log (pointValuation E P f)
    intro R
    rw [← geometric_modelPointValuation E R]
    exact hd R
  exact kernelDivisorPush_isPrincipal E H hodd D hs

/-- [DkMath.Lib] 既存全点関数をそのまま保持する、同じ有限核の加法準同型。 -/
noncomputable def oddKernelPointHom (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : Points E →+ (kernelModel E H).toAffine.Point where
  toFun := oddKernelPointMap E H hodd
  map_zero' := (oddKernelPointMap_eq_zero_iff E H hodd 0).mpr H.zero_mem
  map_add' := oddKernelPointMap_add E H hodd

/-- [DkMath.Lib] 準同型の値は構成済みの同じX_H,Y_Hによる全点関数の値である。 -/
theorem oddKernelPointHom_apply (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    oddKernelPointHom E H hodd P = oddKernelPointMap E H hodd P := rfl

/-- [DkMath.Lib] 零ファイバーの判定が、実際の群準同型の核Hの等式へ昇格する。 -/
theorem oddKernelPointHom_ker (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : (oddKernelPointHom E H hodd).ker = H := by
  ext P
  exact oddKernelPointMap_eq_zero_iff E H hodd P

/-- [DkMath.Lib] 同じ実際の加法準同型は全射である。 -/
theorem oddKernelPointHom_surjective (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : Function.Surjective (oddKernelPointHom E H hodd) :=
  oddKernelPointMap_surjective E H hodd

/-- [DkMath.Lib] 同じ幾何学的点群の商E/Hは、同じ標的の点群に加法同型となる。
これは群の商の同型であり、スキームの商の構成とは区別する。 -/
noncomputable def oddKernelQuotientEquiv (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) : (Points E ⧸ H) ≃+ (kernelModel E H).toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (oddKernelPointHom_ker E H hodd).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (oddKernelPointHom E H hodd)
      (oddKernelPointHom_surjective E H hodd))

/-- [DkMath.Lib] 商群の同型も、代表点を同じ既存の全点関数で送る。 -/
theorem oddKernelQuotientEquiv_mk (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (P : Points E) :
    oddKernelQuotientEquiv E H hodd (QuotientAddGroup.mk P) = oddKernelPointMap E H hodd P := rfl

/-- [DkMath.Lib] 同じ安定核の既存K係数モデルへ降下した、実際の加法準同型。 -/
noncomputable def descendedKernelPointHom (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    Points E →+ Points (descendedKernelModel E H hH) :=
  (pointModelEquiv (descendedKernelModel_map E H hH)).symm.toAddMonoidHom.comp (oddKernelPointHom E H hodd)

/-- [DkMath.Lib] 降下準同型も、既存の同じ降下点関数をtoFunに持つ。 -/
theorem descendedKernelPointHom_apply (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) (P : Points E) :
    descendedKernelPointHom E H hodd hH P = descendedKernelPointMap E H hodd hH P := rfl

/-- [DkMath.Lib] 同じK係数標的の準同型の核も、同じHである。 -/
theorem descendedKernelPointHom_ker (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    (descendedKernelPointHom E H hodd hH).ker = H := by
  ext P
  exact descendedKernelPointMap_eq_zero_iff E H hodd hH P

/-- [DkMath.Lib] 同じ降下準同型は全射性を保持する。 -/
theorem descendedKernelPointHom_surjective (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H) :
    Function.Surjective (descendedKernelPointHom E H hodd hH) :=
  descendedKernelPointMap_surjective E H hodd hH

/-- [DkMath.Lib] 同じ降下準同型は、標準実点Galois作用と可換である。 -/
theorem descendedKernelPointHom_equivariant (H : AddSubgroup (Points E)) [Fintype H]
    (hodd : Odd (Nat.card H)) (hH : ∀ σ P, P ∈ H → pointAction E σ P ∈ H)
    (σ : Field.absoluteGaloisGroup K) (P : Points E) :
    descendedKernelPointHom E H hodd hH (pointAction E σ P) =
      pointAction (descendedKernelModel E H hH) σ (descendedKernelPointHom E H hodd hH P) :=
  descendedKernelPointMap_equivariant E H hodd hH σ P

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
