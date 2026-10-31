/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFiniteKernelReduction
import DkMath.FLT.FreyDyadicGeometry
import DkMath.Lib.NumberTheory.EllipticFiniteKernelNodalReduction
import DkMath.Lib.NumberTheory.EllipticFiniteKernelCriticalCentre
import DkMath.Lib.NumberTheory.EllipticNodalSmoothCentre
import DkMath.Lib.NumberTheory.EllipticNodalSmoothTorsionExclusion
import DkMath.Lib.Algebra.FiniteAdditiveTorsionQuotient

#print "file: DkMath.FLT.FreyFiniteKernelNodalReduction"

/-!
# 同じ既存整数商標的の、悪い素数での乗法的還元

前章の二つの局所核の側を両方処理する。滑らかな側は同じ節点商の不変量公式、
特異な側は同じ源との剰余一致を使う。Sourceの実際の位数pと整性・中心・方向を内部供給する。
2上でもp≥5から同じ節点幾何を供給し、既存整数標的の正式な乗法的還元まで閉じる。
良還元の保持、Δ深さ、全点零成分輸送、一般hnoは別の未完了部分である。
-/
namespace DkMath.FLT.Frey.Source
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation EllipticFiniteKernel
open DkMath.Lib.Algebra
open EllipticCriticalCentre EllipticTangentDirections ValuationInertia ValuationPrimeSupport
open ValuationRationalPrimeSupport WeierstrassResidueModel EllipticGoodReductionSeparation
open EllipticSmoothReduction
open EllipticNodalSmoothCard EllipticNodalSmoothCentre
open EllipticNodalTorsion.NodalTorsion
open EllipticNodalSmoothTorsionExclusion
open EllipticSmoothTorsionPrimeExclusion
open DkMath.Lib.RepresentationTheory
noncomputable local instance instDecidableEqFreyFiniteKernelNodalReduction {α : Type*} : DecidableEq α :=
  Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- 同じSourceの中心・方向から、核の分岐によらず同じ整数標的のΔ非単元・c₄単元を得る。
Lと核Hを固定し、前章のDisjoint仮定を追加せずに両側を内部で処理する。 -/
theorem residual_integer_target_nodal_conditions (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C) :
    A.valuation ((S.residualIntegerKernelModel L hl hs).Δ : AlgebraicClosure ℚ) < 1 ∧
      A.valuation ((S.residualIntegerKernelModel L hl hs).c₄ : AlgebraicClosure ℚ) = 1 := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  obtain ⟨F,hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
    (S.valuationModel_map A) C D
  have hi := valuationKernelModel_nodal_invariants S.rationalCurve (pointSubgroup S.rationalCurve p L)
    (card_pointSubgroup S.rationalCurve p L hl) hp2 (S.residual_kernel_killed L) A
    (S.valuationModel A) (S.valuationModel_map A) hp (S.residual_kernel_reduction_cases L hl A) F hsep
  change ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)).Δ = 0 ∧
    ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)).c₄ ≠ 0 at hi
  simp only [map_Δ,map_c₄] at hi
  have hv := S.residual_integer_valuation_kernel_values hp2 L hl hs hq hqp A hA
  rw [hv.1,hv.2]
  exact ⟨(residue_zero_iff A _).mp hi.1,(residue_ne_zero_iff A _).mp hi.2⟩

/-- [DkMath.Lib] The concrete Frey valuation geometry supplies a rational
singular centre on the residue model without lifting that centre to
characteristic zero.  `residue_frame_of_model` provides the equation and the
two vanishing derivatives; `singularCentreOfFrame` packages exactly those
three fields and forgets the auxiliary tangent direction.

This theorem is intentionally about the valuation model itself.  It does not
identify the singular centre with a point of the residual kernel quotient;
that transport remains a separate polynomial-model argument.
-/
noncomputable def valuationModel_residue_singularCentre_of_geometry (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    SingularCentre ((S.valuationModel A).map (residue A)) := by
  obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A (S.valuationModel A) _
    (S.valuationModel_map A) C D
  exact singularCentreOfFrame _ F

/-- [DkMath.Lib] The disjoint branch transports the complete residue frame,
not merely its packaged centre, to the residual valuation-kernel model.
Keeping the two tangent directions in the `Frame` is useful for later slope
and smooth-point arguments; the subsequent `SingularCentre` definition may
forget the chosen direction when only the node is needed.
-/
theorem residualValuationKernelModel_residue_frame_of_disjoint
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    Frame ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A))
        (residue A ⟨C.x, C.x_mem⟩) (residue A ⟨C.y, C.y_mem⟩)
        (residue A ⟨D.α, D.α_mem⟩) ∧
      residue A ⟨D.α, D.α_mem⟩ ≠
        -((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)).a₁ -
          residue A ⟨D.α, D.α_mem⟩ := by
  obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A
    (S.valuationModel A) _ (S.valuationModel_map A) C D
  rw [S.residual_valuation_kernel_residue_eq_of_disjoint L hl hq hqp A hA hd]
  exact ⟨F, hsep⟩

/-- [DkMath.Lib] On the smooth-kernel branch, the nodal quotient theorem
constructs a characteristic-zero `CriticalCentre` for the same valuation
model, and `singularCentreOfCriticalCentre` reduces it to the residue field.
This is the complementary construction to the disjoint-branch transport
above: it uses the smooth-kernel hypotheses, not equality with the source
residue model, and therefore keeps the two local branches mathematically
separate.
-/
noncomputable def residualValuationKernelModel_residue_singularCentre_of_smooth
    (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)) := by
  let := S.finite_residualPointSubgroup L hl
  let := Fintype.ofFinite (pointSubgroup S.rationalCurve p L)
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  have hs : ∀ Q : pointSubgroup S.rationalCurve p L,
      HasSmoothReduction (S.valuationModel A) Q.val :=
    S.residual_kernel_smooth_of_le L A hle
  obtain ⟨F, hsep⟩ := WeierstrassNodalFrame.residue_frame_of_model A
    (S.valuationModel A) _ (S.valuationModel_map A) C D
  let T := Classical.choice (exists_nodal_kernel_criticalCentre S.rationalCurve
    (pointSubgroup S.rationalCurve p L) p
    (card_pointSubgroup S.rationalCurve p L hl) hp2
    (S.residual_kernel_killed L) A (S.valuationModel A) (S.valuationModel_map A) hp hs F hsep)
  let U := S.residualValuationKernelModel L hl hq hqp A hA
  have ho : Odd (Nat.card (pointSubgroup S.rationalCurve p L)) :=
    by simpa only [card_pointSubgroup S.rationalCurve p L hl] using
      (Fact.out : p.Prime).odd_of_ne_two hp2
  have hU : U.map A.subtype = kernelModel S.rationalCurve (pointSubgroup S.rationalCurve p L) := by
    dsimp [U, residualValuationKernelModel]
    exact valuationKernelModel_map S.rationalCurve (pointSubgroup S.rationalCurve p L)
      p (S.residual_kernel_killed L) A (S.valuationModel A) (S.valuationModel_map A) hp ho
  let T' : CriticalCentre A (U.map A.subtype) := hU.symm ▸ T
  exact singularCentreOfCriticalCentre U T'

/-- [DkMath.Lib] On the disjoint (singular-kernel) branch, the residue
singular centre transports from the Frey valuation model to the residual
kernel model by the already established residue-model equality.  No point of
the characteristic-zero curve is introduced: the centre lives entirely over
the residue field, and the equality is the exact bridge supplied by
`residual_valuation_kernel_residue_eq_of_disjoint`.

This is deliberately restricted to the disjoint branch.  The smooth branch
has a different residue model and must use the nodal Vélu invariant formulas
instead of this equality.
-/
noncomputable def residualValuationKernelModel_residue_singularCentre_of_disjoint
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hd : Disjoint L (S.residualZeroComponent A))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C) :
    SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)) := by
  obtain ⟨F, -⟩ := S.residualValuationKernelModel_residue_frame_of_disjoint
    L hl hq hqp A hA hd C D
  exact singularCentreOfFrame _ F

/-- [DkMath.Lib] A residue singular centre immediately gives the finite-point
cardinality bound needed by the component-group argument.  The proof is
branch-independent: callers may supply the centre constructed from either
the smooth or disjoint local branch above.  No identification with a finite
field point set, and no assertion about the characteristic-zero model, is
added here.
-/
theorem residualValuationKernelModel_residue_pointCard_le
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)]
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A))) :
    Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (residue A)).toAffine.Point ≤ Fintype.card (ResidueField A) + 1 := by
  let _ : Finite ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (residue A)).toAffine.Point := finitePoints C
  exact natCard_points_le_card_add_one C

/-- [DkMath.Lib] If the residue field has size at most a prime address
`q < p`, the same centre bound is strictly below `p`.  This is the numerical
form consumed by the prime-divisibility obstruction; it still concerns only
the affine residue point group.
-/
theorem residualValuationKernelModel_residue_pointCard_lt_of_prime_lt
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)]
    (hresidueCard : Fintype.card (ResidueField A) ≤ q) (hqp' : q < p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A))) :
    Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (residue A)).toAffine.Point < p := by
  let : Fact q.Prime := ⟨hq⟩
  calc
    Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
        (residue A)).toAffine.Point ≤ Fintype.card (ResidueField A) + 1 :=
      residualValuationKernelModel_residue_pointCard_le S hq hqp A hA L hl C
    _ ≤ q + 1 := Nat.add_le_add_right hresidueCard 1
    _ < p := add_one_lt_of_prime_lt_of_five_le hp5 hqp'

/-- [DkMath.Lib] Under the preceding strict bound, the residue affine point
group has cardinality not divisible by `p`.  Positivity comes from the same
singular centre, so this is a direct finite-group consequence rather than an
assertion about the component quotient.
-/
theorem residualValuationKernelModel_residue_pointCard_not_dvd_of_prime_lt
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)]
    (hresidueCard : Fintype.card (ResidueField A) ≤ q) (hqp' : q < p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A))) :
    ¬ p ∣ Nat.card ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (residue A)).toAffine.Point := by
  let : Fact q.Prime := ⟨hq⟩
  let _ : Finite ((S.residualValuationKernelModel L hl hq hqp A hA).map
      (residue A)).toAffine.Point := finitePoints C
  apply prime_not_dvd_of_pos_of_lt (natCard_points_pos C)
  exact residualValuationKernelModel_residue_pointCard_lt_of_prime_lt S hp5 hq hqp A hA
    hresidueCard hqp' L hl C

/-- [DkMath.Lib] A residue node and a generic point of exact order `2*p` now
feed directly into the component-quotient obstruction.  The node/cardinality
bound excludes the point from the smooth zero component, while the finite
additive quotient lemma supplies the remaining divisibility
`p ∣ Nat.card (E(A) / E₀(A))`.

The theorem intentionally stops at this divisibility.  It does not identify
the abstract quotient with a Néron component group and does not claim that
the divisibility is impossible.
-/
theorem residualValuationKernelModel_component_prime_dvd_of_residue_centre
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)))
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  let : Fact q.Prime := ⟨hq⟩
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  have hcard := residualValuationKernelModel_residue_pointCard_not_dvd_of_prime_lt S hp5 hq hqp
    A hA hresidueCard hqp' L hl C
  have hnot : ¬ HasSmoothReduction
      (S.residualValuationKernelModel L hl hq hqp A hA) R := by
    intro hRsmooth
    exact (not_addOrder_eq_two_mul_prime_of_smooth_of_nodal_card_bound
      (S.residualValuationKernelModel L hl hq hqp A hA) hp5 hp hresidueCard hqp' C hRsmooth) hR
  have hker : ∀ x : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point,
      x ∈ zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA) →
        p • x = 0 → x = 0 := by
    intro x hx hpx
    have hsmooth := (mem_zeroComponentSubgroup_iff
      (S.residualValuationKernelModel L hl hq hqp A hA)).mp hx
    exact eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard
      (S.residualValuationKernelModel L hl hq hqp A hA) hp hcard hsmooth hpx
  refine ⟨hnot, ?_⟩
  exact prime_dvd_natCard_quotient_of_two_p_torsion
    (zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) R hR hker

/-- [DkMath.Lib] The smooth local branch can now consume the component
obstruction without asking callers to manufacture the residue `SingularCentre`
by hand.  The constructor above is deliberately kept visible in the proof:
this wrapper records that the only extra geometric input is `L ≤ E₀` together
with the original characteristic-zero centre and tangent direction.

The conclusion is still the precise abstract boundary
`¬ HasSmoothReduction R ∧ p ∣ Nat.card (E(A) / E₀(A))`; no Néron component
identification or contradiction is hidden in this specialization.
-/
theorem residualValuationKernelModel_component_prime_dvd_of_smooth_branch
    (hp5 : 5 ≤ p) (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (hle : L ≤ S.residualZeroComponent A)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  let Cres := S.residualValuationKernelModel_residue_singularCentre_of_smooth
    hp2 L hl hq hqp A hA hle C D
  exact S.residualValuationKernelModel_component_prime_dvd_of_residue_centre
    hp5 hq hqp A hA hresidueCard hqp' L hl Cres hR

/-- [DkMath.Lib] The disjoint local branch has the same consumer-facing
component obstruction, but its residue centre is transported through the
residue-model equality rather than through the nodal quotient construction.
This is the branch-separated form useful to later Frey case analyses.

As in the generic theorem, the result stops at divisibility in the abstract
quotient by the smooth zero component.  Any identification with a Néron
component group remains a separate arithmetic-geometric lemma.
-/
theorem residualValuationKernelModel_component_prime_dvd_of_disjoint_branch
    (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (hd : Disjoint L (S.residualZeroComponent A))
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  let Cres := S.residualValuationKernelModel_residue_singularCentre_of_disjoint
    L hl hq hqp A hA hd C D
  exact S.residualValuationKernelModel_component_prime_dvd_of_residue_centre
    hp5 hq hqp A hA hresidueCard hqp' L hl Cres hR

/-- [DkMath.Lib] Branch-free consumer for the component obstruction.  The line
dichotomy selects the smooth or disjoint centre constructor, so callers retain
only the original Frey centre, tangent direction, and exact-order point.
The result remains deliberately abstract: it is divisibility in the quotient
by the smooth zero component, not yet a Néron component-group contradiction.
-/
theorem residualValuationKernelModel_component_prime_dvd_of_geometry
    (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    ¬ HasSmoothReduction (S.residualValuationKernelModel L hl hq hqp A hA) R ∧
      p ∣ Nat.card (((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point ⧸
        zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA)) := by
  rcases S.residual_line_smooth_or_disjoint L hl A with hle | hd
  · exact S.residualValuationKernelModel_component_prime_dvd_of_smooth_branch
      hp5 (by omega) L hl hq hqp A hA hle hresidueCard hqp' C D hR
  · exact S.residualValuationKernelModel_component_prime_dvd_of_disjoint_branch
      hp5 L hl hq hqp A hA hresidueCard hqp' hd C D hR

/-- [DkMath.Lib] The first branch of the component dichotomy is now
explicitly closed at a nodal residue address. If `R` has exact order `2*p`,
then `2 • R` is a nonzero `p`-torsion point. The residue point-cardinality
bound forces every smooth `p`-torsion point to vanish, so the double cannot
belong to the smooth zero-component subgroup.

This theorem is intentionally independent of the component quotient: it is
the reusable geometric input that turns the general two-way quotient lemma
into one-way divisibility. It makes no claim about a Néron model or about the
finiteness of the abstract quotient.
-/
theorem residualValuationKernelModel_two_nsmul_not_mem_zeroComponent_of_geometry
    (hp5 : 5 ≤ p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    [Fintype (ResidueField A)] (hresidueCard : Fintype.card (ResidueField A) ≤ q)
    (hqp' : q < p) (L : Submodule (ZMod p) S.ResidualSpace)
    (hl : Module.finrank (ZMod p) L = 1)
    (C : SingularCentre ((S.residualValuationKernelModel L hl hq hqp A hA).map (residue A)))
    {R : ((S.residualValuationKernelModel L hl hq hqp A hA).map A.subtype).toAffine.Point}
    (hR : addOrderOf R = 2 * p) :
    2 • R ∉ zeroComponentSubgroup (S.residualValuationKernelModel L hl hq hqp A hA) := by
  let : Fact q.Prime := ⟨hq⟩
  have hp : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
    simpa only [pow_one] using prime_power_value_one A (Fact.out : p.Prime) hq
      ((ValuationSubring.mem_nonunits_iff _).mp hA) hqp 1
  have hcard := residualValuationKernelModel_residue_pointCard_not_dvd_of_prime_lt S hp5 hq hqp
    A hA hresidueCard hqp' L hl C
  have hdouble_ne : 2 • R ≠ 0 := by
    intro hzero
    have hdiv : 2 * p ∣ 2 := by
      rw [← hR]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hzero
    have hle : 2 * p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hdouble_p : p • (2 • R) = 0 := by
    have htwoq : (2 * p) • R = 0 := by
      rw [← hR]
      exact addOrderOf_nsmul_eq_zero R
    exact (mul_nsmul R 2 p).symm.trans htwoq
  intro hdouble
  have hsmooth := (mem_zeroComponentSubgroup_iff
    (S.residualValuationKernelModel L hl hq hqp A hA)).mp hdouble
  exact hdouble_ne (eq_zero_of_smooth_prime_torsion_of_residue_not_dvd_natCard
    (S.residualValuationKernelModel L hl hq hqp A hA) hp hcard hsmooth hdouble_p)

/-- 同じ中心・方向から同じ整数標的の正式な乗法的還元へ進む。q=2も除外しない。 -/
theorem residual_integer_target_multiplicative_of_geometry (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  have hi := S.residual_integer_target_nodal_conditions hp2 L hl hs Fact.out hqp A hA C D
  have hqv := (ValuationSubring.mem_nonunits_iff _).mp hA
  apply FreyLocalReduction.hasMultiplicativeReduction_at_prime q _
  · by_contra hn
    exact hi.1.ne (valuation_intCast_eq_one_of_not_dvd A Fact.out hqv hn)
  · intro hn
    have hh := valuation_intCast_lt_one_of_dvd A hqv hn
    rw [hi.2] at hh
    exact lt_irrefl _ hh

/-- 悪い奇素数q≠pで、同じ既存整数標的は乗法的還元を持つ。
住所・中心・方向・核の局所分岐を全て内部供給する。 -/
theorem residual_integer_target_multiplicative_at_bad_prime (hp2 : p ≠ 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hbad : (q : ℤ) ∣ S.a * S.b * S.c) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  obtain ⟨A,hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) (Fact.out : q.Prime)
  obtain ⟨C,D,-,-⟩ := S.exists_criticalCentre_directions_at_bad_prime
    (Nat.Prime.pos (Fact.out : p.Prime)) hq2 hbad A hA
  exact S.residual_integer_target_multiplicative_of_geometry hp2 L hl hs hqp A hA C D

/-- p≥5では同じ既存整数標的が2でも正式な乗法的還元を持つ。
前章の最小性だけの結論を、同じ2進節点幾何から判別式非単元性まで拡張する。 -/
theorem residual_integer_target_multiplicative_at_two (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing 2)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  obtain ⟨A,hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_two
  obtain ⟨C,D,-,-⟩ := S.exists_dyadic_geometry hp5 A hA
  exact S.residual_integer_target_multiplicative_of_geometry (by omega) L hl hs (by omega) A hA C D

/-- 同じSourceの悪い素数住所での一括終点。2またはabcを割るq≠pを同じ整数標的へ運ぶ。
良い素数住所まで含めた大域半安定性や、判別式深さは別の命題である。 -/
theorem residual_integer_target_multiplicative_at_bad_place (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hl : Module.finrank (ZMod p) L = 1)
    (hs : IsStable S.residualRepresentation L) {q : ℕ} [Fact q.Prime] (hqp : q ≠ p)
    (hbad : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) := by
  by_cases hq2 : q = 2
  · subst q
    exact S.residual_integer_target_multiplicative_at_two hp5 L hl hs
  · exact S.residual_integer_target_multiplicative_at_bad_prime (by omega) L hl hs hq2 hqp
      (hbad.resolve_left hq2)

end DkMath.FLT.Frey.Source
