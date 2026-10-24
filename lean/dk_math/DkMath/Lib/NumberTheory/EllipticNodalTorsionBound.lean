/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothTorsionReduction
import DkMath.Lib.NumberTheory.EllipticCriticalCentre
import DkMath.Lib.NumberTheory.EllipticTangentDirections
import DkMath.Lib.NumberTheory.EllipticNodalTorsion

#print "file: DkMath.Lib.NumberTheory.EllipticNodalTorsionBound"

/-!
# NOTE-032-003B: 同じ節点の還元から零成分の捩れ上界を得る

[DkMath.Lib] 既存の中心Cと分離方向Dをそのまま剰余へ写し、節点比のFrameを供給する。
剰余曲線のn捩れは、節点比のn乗根への単射によって高々n個である。
単元位数の滑らかな捩れの還元も単射なので、一般ファイバーのE₀[n]も高々n個となる。

剰余体の代数閉性・完備性・正規化付値は仮定しない。
実際に分離した整な方向Dを使い、剰余での二方向の非等号を保持する。
最後のAPIでは元のモデルとの一致と、同じ点を保つ単射を明示し、consumerでの位数比較へ渡す。
-/
namespace DkMath.Lib.NumberTheory.EllipticNodalTorsionBound
open WeierstrassCurve IsLocalRing EllipticCriticalCentre EllipticTangentDirections
open EllipticGoodReductionSeparation EllipticSmoothReduction
open EllipticNodalTorsion.NodalTorsion
variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

/-- [DkMath.Lib] 同じ中心・方向の剰余は、分離した節点比の実際のFrameを与える。
中心の剰余特異性と、方向の根条件・分離を、同じ剰余曲線へ輸送する。 -/
theorem residue_frame (C : CriticalCentre A (W.map A.subtype)) (D : TangentDirections C) :
    let x₀ := residue A (⟨C.x, C.x_mem⟩ : A)
    let y₀ := residue A (⟨C.y, C.y_mem⟩ : A)
    let α := residue A (⟨D.α, D.α_mem⟩ : A)
    Frame (W.map (residue A)) x₀ y₀ α ∧ α ≠ -(W.map (residue A)).a₁ - α := by
  let x : A := ⟨C.x, C.x_mem⟩
  let y : A := ⟨C.y, C.y_mem⟩
  let a : A := ⟨D.α, D.α_mem⟩
  let b : A := ⟨D.β, D.β_mem⟩
  have hC := C.residue_singular W
  have hs := hC.2
  rw [Affine.nonsingular_iff'] at hs
  push Not at hs
  obtain ⟨hFX, hFY⟩ := hs hC.1
  have hroot : a ^ 2 + W.a₁ * a - (W.a₂ + 3 * x) = 0 := by
    apply Subtype.ext
    exact D.roots.1
  have hα := congrArg (residue A) hroot
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero] at hα
  have hsum : a + b = -W.a₁ := by
    apply Subtype.ext
    exact D.sum_eq
  have hsumr := congrArg (residue A) hsum
  simp only [map_add, map_neg] at hsumr
  refine ⟨⟨?_, hFX, hFY, ?_⟩, ?_⟩
  · exact sub_eq_zero.mpr ((Affine.equation_iff _ _).mp hC.1)
  · simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, add_comm] using hα
  · intro heq
    apply D.residue_ne
    change residue A a = residue A b
    change residue A a = -residue A W.a₁ - residue A a at heq
    linear_combination heq - hsumr

variable [CharZero L] [DecidableEq L]

/-- [DkMath.Lib] 同じ節点の滑らかなn捩れは、n>0かつnが単元なら有限で高々n個。
剰余上の上界と、一般ファイバーから剰余への捩れ還元の単射性をこの順で接続する。 -/
theorem finite_and_ncard_smooth_torsion_le (C : CriticalCentre A (W.map A.subtype))
    (D : TangentDirections C) {n : ℕ} (hn : 0 < n) (hunit : A.valuation (n : L) = 1) :
    {P : (W.map A.subtype).toAffine.Point | HasSmoothReduction W P ∧ n • P = 0}.Finite ∧
      {P : (W.map A.subtype).toAffine.Point | HasSmoothReduction W P ∧ n • P = 0}.ncard ≤ n := by
  classical
  obtain ⟨hd, hsep⟩ := residue_frame W C D
  have hbound := finite_and_ncard_torsion_le hd hsep hn
  exact EllipticSmoothTorsionReduction.finite_and_ncard_le_of_residue_bound W hunit hbound.1 hbound.2

/-- [DkMath.Lib] 元のモデルVの滑らかなn捩れへ単射に写る型の位数は高々n。
Wの一般ファイバーとの一致を明示し、写像の単射性と同じ点の条件を保持する。
剰余側の有限性を先に供給するので、始域の有限性を外部に仮定する必要はない。 -/
theorem card_le_of_injective_smooth_torsion (V : WeierstrassCurve L)
    (hmodel : W.map A.subtype = V) (C : CriticalCentre A V) (D : TangentDirections C)
    {n : ℕ} (hn : 0 < n) (hunit : A.valuation (n : L) = 1)
    {T : Type*} (f : T → V.toAffine.Point) (hf : Function.Injective f)
    (hsmooth : ∀ t, HasSmoothReduction W (f t)) (hkill : ∀ t, n • f t = 0) : Nat.card T ≤ n := by
  classical
  subst V
  let S : Set (W.map A.subtype).toAffine.Point := {P | HasSmoothReduction W P ∧ n • P = 0}
  obtain ⟨hfinite, hbound⟩ := finite_and_ncard_smooth_torsion_le W C D hn hunit
  have : Finite S := hfinite.to_subtype
  let g : T → S := fun t => ⟨f t, hsmooth t, hkill t⟩
  have hinj : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective g hinj).trans hbound

end DkMath.Lib.NumberTheory.EllipticNodalTorsionBound
