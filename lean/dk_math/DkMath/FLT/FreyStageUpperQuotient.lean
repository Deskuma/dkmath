/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTowerCharacter
import Mathlib.GroupTheory.QuotientGroup.Basic

#print "file: DkMath.FLT.FreyStageUpperQuotient"

/-!
# 元の同じ段による一段上の有限捩れ商と実際の Galois 作用

E[p^(n+2)] の中で元の T を保ち、その商を作る。
非零で p 倍が元の T に入る点は、この商で厳密位数 p を持つ。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 元の段を、一段上の同じ有限捩れ群内の部分群として読む。 -/
def ResidualCyclicStage.upperStage (T : S.ResidualCyclicStage L n) :
    AddSubgroup (Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  T.carrier.comap (torsionGroup S.rationalCurve (p ^ (n + 1 + 1))).subtype

/-- 同じ有限捩れ群による商。 -/
abbrev ResidualCyclicStage.upperQuotient (T : S.ResidualCyclicStage L n) :=
  Torsion S.rationalCurve (p ^ (n + 1 + 1)) ⧸ T.upperStage

/-- 一段上の実際の捩れ群が有限なので、この同じ商も有限。 -/
theorem ResidualCyclicStage.upperQuotient_finite (T : S.ResidualCyclicStage L n) :
    Finite T.upperQuotient := by
  let : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
  let : Finite (Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
    finite_torsion_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  infer_instance

/-- 同じ実際の Galois 作用は元の安定段を保ち、商上の群準同型を与える。 -/
def ResidualCyclicStage.upperQuotientAction (T : S.ResidualCyclicStage L n) :
    Field.absoluteGaloisGroup ℚ →* AddMonoid.End T.upperQuotient where
  toFun σ := QuotientAddGroup.map T.upperStage T.upperStage
    (representation S.rationalCurve (p ^ (n + 1 + 1)) σ).toAddMonoidHom
    (fun x hx => T.stable σ x.val hx)
  map_one' := by
    ext z
    refine QuotientAddGroup.induction_on z ?_
    intro x
    change (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve _ 1 x) =
      (QuotientAddGroup.mk' T.upperStage) x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    ext z
    refine QuotientAddGroup.induction_on z ?_
    intro x
    change (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve _ (σ * τ) x) =
      (QuotientAddGroup.mk' T.upperStage)
        (representation S.rationalCurve _ σ (representation S.rationalCurve _ τ x))
    rw [map_mul]
    rfl

/-- 元の段の外にあり p 倍が段に入る同じ点の剰余類は、厳密位数 p。 -/
theorem ResidualCyclicStage.upperClass_order_eq_prime (T : S.ResidualCyclicStage L n)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : x.val ∉ T.carrier) (hp : p • x.val ∈ T.carrier) :
    addOrderOf ((QuotientAddGroup.mk' T.upperStage) x) = p := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · rw [← map_nsmul]
    apply (QuotientAddGroup.eq_zero_iff (N := T.upperStage) (p • x)).mpr
    exact hp
  · intro h
    exact hx ((QuotientAddGroup.eq_zero_iff (N := T.upperStage) x).mp h)

/-- 同じ有限点の固定性は、同じ商作用の固定性へ降りる。 -/
theorem ResidualCyclicStage.upperClass_fixed (T : S.ResidualCyclicStage L n)
    (σ : Field.absoluteGaloisGroup ℚ) (x : Torsion S.rationalCurve (p ^ (n + 1 + 1)))
    (hx : pointAction S.rationalCurve σ x.val = x.val) :
    T.upperQuotientAction σ ((QuotientAddGroup.mk' T.upperStage) x) =
      (QuotientAddGroup.mk' T.upperStage) x := by
  exact congrArg (QuotientAddGroup.mk' T.upperStage) (Subtype.ext hx)

end
end DkMath.FLT.Frey.Source
