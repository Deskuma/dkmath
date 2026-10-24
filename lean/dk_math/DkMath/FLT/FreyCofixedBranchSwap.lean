/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStableLineLocalGlobal
import DkMath.Lib.RepresentationTheory.CofixedBranchSwap
import DkMath.Lib.NumberTheory.EllipticNodalInertia

#print "file: DkMath.FLT.FreyCofixedBranchSwap"

/-!
# NOTE-032-001: 同じFrey Sourceにおける枝交換のhno接続

CofixedBranchSwapの一般核を、既存の同じSourceの実際のE[p]・表現・局所慣性へ特殊化する。
さらに実際の滑らかな零成分E₀との交わりをFₚ部分加群として構成する。
これは031-004の無限遠へ還元する核E₁との交わりとは異なる。両者を同一視しない。

中心・接線方向が与えられ、慣性が中心を固定すれば、既存の幾何から慣性変化量の吸収を供給する。
零成分外のp捩れ点、非自明な慣性作用、枝交換元は明示入力のままである。
とくにa≡3 mod8から枝交換元の存在を証明したとはせず、a≡7 mod8も排除しない。
既約性への接続は031-005を再利用する。一般FLT、isogenyの構成、Mazur理論はこの章の結論ではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
open WeierstrassCurve
private theorem smooth_add_of_model {L : Type*} [Field L] [DecidableEq L]
    {A : ValuationSubring L} (W : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hm : W.map A.subtype = V) {P Q : V.toAffine.Point}
    (hP : HasSmoothReduction W P) (hQ : HasSmoothReduction W Q) :
    HasSmoothReduction W (P + Q) := by
  classical
  subst V
  exact (EllipticSmoothReduction.smooth_add_and_reduce W hP hQ).1

private theorem smooth_neg_of_model {L : Type*} [Field L]
    {A : ValuationSubring L} (W : WeierstrassCurve A) (V : WeierstrassCurve L)
    (hm : W.map A.subtype = V) {P : V.toAffine.Point} (hP : HasSmoothReduction W P) :
    HasSmoothReduction W (-P) := by
  subst V
  exact EllipticSmoothReduction.smooth_neg W hP

variable {p : ℕ} [Fact p.Prime] (S : Source p)

omit [Fact p.Prime] in
/-- mod4の向き付けだけではmod8の3と7の両方が残る。
枝交換元を合同条件から供給する次の工程では、この分岐を保持する。 -/
theorem a_mod_eight_cases_of_oriented (ha4 : (4 : ℤ) ∣ S.a + 1) :
    S.a % 8 = 3 ∨ S.a % 8 = 7 := by
  obtain ⟨k, hk⟩ := ha4
  omega

/-- 同じ実際の残余点のうち、整数モデルで滑らかな還元を持つ点の部分加群。
群の加法・逆元の閉性は031-004の実証明を再利用し、スカラー倍はZMod部分加群化で得る。 -/
noncomputable def residualZeroComponent (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Submodule (ZMod p) S.ResidualSpace := by
  classical
  have := S.rationalCurve_isElliptic
  let W := S.valuationModel A
  let V := S.rationalCurve.baseChange (AlgebraicClosure ℚ)
  have hm : W.map A.subtype = V := S.valuationModel_map A
  let H : AddSubgroup S.ResidualSpace := {
    carrier := {P | HasSmoothReduction W P.val}
    zero_mem' := hasSmoothReduction_zero W V
    add_mem' := by
      intro P Q hP hQ
      change HasSmoothReduction W (P.val + Q.val)
      exact smooth_add_of_model W V hm hP hQ
    neg_mem' := by
      intro P hP
      change HasSmoothReduction W (-P.val)
      exact smooth_neg_of_model W V hm hP }
  exact AddSubgroup.toZModSubmodule p H

/-- 部分加群の所属は、同じSource・同じモデルでの滑らかな還元という条件そのものである。 -/
theorem mem_residualZeroComponent_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : S.ResidualSpace) : P ∈ S.residualZeroComponent A ↔
      HasSmoothReduction (S.valuationModel A) P.val := Iff.rfl

/-- 真性に必要なのは、実際のp捩れに零成分外の点が存在すること。
有理捩れ点の不存在や、無限遠還元核の真性でこの条件を置き換えない。 -/
theorem residualZeroComponent_ne_top_iff (A : ValuationSubring (AlgebraicClosure ℚ)) :
    S.residualZeroComponent A ≠ ⊤ ↔
      ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val := by
  constructor
  · intro h
    by_contra! hall
    exact h (top_unique (fun P _ => (S.mem_residualZeroComponent_iff A P).mpr (hall P)))
  · rintro ⟨P, hP⟩ heq
    apply hP
    exact (S.mem_residualZeroComponent_iff A P).mp (heq ▸ Submodule.mem_top)

/-- 同じモデルの中心を慣性が固定するなら、全慣性変化量が実際のE₀[p]へ入る。
中心・方向・固定性の入力を明示し、2上の存在・固定性を仮定なしで得たとはしない。 -/
theorem residualZeroComponent_absorbs_of_fixed_centre
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x ∧ τ C.y = C.y) :
    CofixedOn S.residualRepresentation (S.residualZeroComponent A) (inertiaSubgroupIn A ℚ) := by
  classical
  intro τ hτ P
  rw [S.mem_residualZeroComponent_iff]
  exact EllipticNodalInertia.inertia_difference_smooth S.rationalCurve A
    (S.valuationModel A) (S.valuationModel_map A) C D τ hτ (hfix τ hτ) P.val

/-- 同じSourceの局所作用・吸収・枝交換からhnoを得る条件付き入口。
モデルの真性、非自明慣性、枝交換元の存在は結論へ紛れ込ませず入力に残す。 -/
theorem residual_no_cofixed_line_of_inertia_and_branch_swap (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : Submodule (ZMod p) S.ResidualSpace) (hM : M ≠ ⊤)
    (habs : CofixedOn S.residualRepresentation M (inertiaSubgroupIn A ℚ))
    (hram : ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P)
    (hswap : ∃ σ, ∀ P, P ∉ M → S.residualRepresentation σ P + P ∈ M) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L := by
  have := S.rationalCurve_isElliptic
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hh : ((2 : ℕ) : ZMod p) ≠ 0 := fun h => hp2
      ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
        ((ZMod.natCast_eq_zero_iff 2 p).mp h))
    exact_mod_cast hh
  exact CofixedBranchSwap.no_stable_cofixed_line S.residualRepresentation
    (inertiaSubgroupIn A ℚ) M hM h2 habs hram hswap

/-- 実際の零成分に特殊化する。吸収は既存の点の幾何から供給し、
零成分外の点、非自明慣性、枝交換だけを残る局所算術として受け取る。 -/
theorem residual_no_cofixed_line_of_zeroComponent_branch_swap (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x ∧ τ C.y = C.y)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hram : ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L := by
  apply S.residual_no_cofixed_line_of_inertia_and_branch_swap hp2 A (S.residualZeroComponent A)
    ((S.residualZeroComponent_ne_top_iff A).mpr hout)
    (S.residualZeroComponent_absorbs_of_fixed_centre A C D hfix) hram
  obtain ⟨σ, hσ⟩ := hswap
  exact ⟨σ, fun P hP => (S.mem_residualZeroComponent_iff A _).mpr
    (hσ P (fun hs => hP ((S.mem_residualZeroComponent_iff A P).mpr hs)))⟩

/-- NOTE-031-005へ実際に接続する条件付き既約性。
同じSourceのb偶数による固定点排除と局所大域二択は再利用する。 -/
theorem residual_isIrreducible_of_inertia_and_branch_swap (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (M : Submodule (ZMod p) S.ResidualSpace) (hM : M ≠ ⊤)
    (habs : CofixedOn S.residualRepresentation M (inertiaSubgroupIn A ℚ))
    (hram : ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P)
    (hswap : ∃ σ, ∀ P, P ∉ M → S.residualRepresentation σ P + P ∈ M) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction hp5 hbe
    (S.residual_no_cofixed_line_of_inertia_and_branch_swap (by omega) A M hM habs hram hswap)

end DkMath.FLT.Frey.Source
