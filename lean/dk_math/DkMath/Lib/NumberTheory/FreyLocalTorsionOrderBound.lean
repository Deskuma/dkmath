/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticSmoothTorsionOrderBound
import DkMath.Lib.NumberTheory.FreyLocalValuationSubring
import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import DkMath.Lib.NumberTheory.WeierstrassVariableChangeGalois

#print "file: DkMath.Lib.NumberTheory.FreyLocalTorsionOrderBound"

/-!
# NOTE-032: 整数 Frey モデルの局所トーション次数上界

良還元モデル上の滑らかな捩れ集合の濃度評価を、`ℤ` 上の Weierstrass モデルへ
直接適用するための教科書的な橋である。素数 `q` が判別式を割らないとき、局所化環
`LocalRing q` へ移し、さらに同じ `q`-進付値を表す `ValuationSubring ℚ` へ移す。
そこで一般定理
`addOrderOf_le_two_mul_residue_card_add_one_of_good` を使い、剰余体が `ZMod q`
であることと、`q ∤ n` による付値単元性を戻す。

ここで得るのは、Frey 曲線の `hno` そのものではなく、任意の整数モデルに対する
局所的な必要条件である。後段の Frey 特殊化では、判別式非可除性を別の補題から
供給し、この上界を残余表現の入口として消費する。
-/

namespace DkMath.Lib.NumberTheory

open WeierstrassCurve
open DkMath.Lib.NumberTheory.FreyLocalReduction
open DkMath.Lib.NumberTheory.ValuationPrimeSupport
open DkMath.Lib.NumberTheory.WeierstrassVariableChange

noncomputable section

noncomputable local instance instDecidableEqFreyLocalTorsionOrderBound :
    DecidableEq ℚ := instDecidableEqEllipticSmoothTorsionOrderBound

/--
For an integral Weierstrass model with good reduction at `q`, every point whose
order is prime to `q` satisfies the elementary local bound `2*q+1`.

The proof is a literal transport diagram:

* `W` is first mapped to `LocalRing q`;
* the DVR equivalence identifies that model with a model over its valuation subring;
* the general smooth-torsion theorem is applied there;
* the residue-field equivalence contributes the cardinality `q`.

No Frey-specific equation, Hasse estimate, or global Galois argument is used.
-/
theorem addOrderOf_le_two_mul_prime_add_one_of_integral_good
    (q : ℕ) [Fact q.Prime]
    (W : WeierstrassCurve ℤ)
    (hΔ : ¬ (q : ℤ) ∣ W.Δ)
    {n : ℕ}
    (hn : ¬ (q : ℤ) ∣ (n : ℤ))
    (Q : (W.map (Int.castRingHom ℚ)).toAffine.Point)
    (hQ : n • Q = 0) :
    addOrderOf Q ≤ 2 * q + 1 := by
  let Wloc : WeierstrassCurve (LocalRing q) :=
    W.map (algebraMap ℤ (LocalRing q))
  let Wv : WeierstrassCurve (localValuationSubring q) :=
    mapModelToValuationSubring q Wloc
  have hbase : Wv.map (localValuationSubring q).subtype =
      W.map (Int.castRingHom ℚ) := by
    ext <;> simp [Wloc, Wv, mapModelToValuationSubring]
  let Qv : (Wv.map (localValuationSubring q).subtype).toAffine.Point :=
    pointEquivOfModelEq hbase.symm Q
  have hQv : n • Qv = 0 := by
    simpa [Qv] using congrArg (pointEquivOfModelEq hbase.symm) hQ
  have hunitLoc : IsUnit Wloc.Δ := by
    simp only [Wloc, WeierstrassCurve.map_Δ]
    exact (isUnit_local_iff q W.Δ).mpr hΔ
  have hgoodLoc :
      (Wloc.map (IsLocalRing.residue (LocalRing q))).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunitLoc
  have hgoodV :
      (Wv.map (IsLocalRing.residue (localValuationSubring q))).Δ ≠ 0 := by
    have hΔmap := mapModelToValuationSubring_residue_discriminant_map q Wloc
    intro hzero
    have : localResidueFieldValuationSubringEquiv q
        ((Wloc.map (IsLocalRing.residue (LocalRing q))).Δ) = 0 := by
      rw [hΔmap, hzero]
    exact hgoodLoc ((localResidueFieldValuationSubringEquiv q).injective (by simpa using this))
  have hnval : (localValuationSubring q).valuation (n : ℚ) = 1 := by
    simpa only [Int.cast_natCast] using
      valuation_intCast_eq_one_of_not_dvd (localValuationSubring q)
        (Fact.out : q.Prime) (by
          exact (localValuationSubring q).mem_nonunits_iff.mp
            (localValuationSubring_liesOverPrime q)) hn
  have hbound := addOrderOf_le_two_mul_residue_card_add_one_of_good
    (localValuationSubring q) Wv hgoodV Qv hnval hQv
  have hord : addOrderOf Qv = addOrderOf Q :=
    (pointEquivOfModelEq hbase.symm).addOrderOf_eq Q
  calc
    addOrderOf Q = addOrderOf Qv := hord.symm
    _ ≤ 2 * q + 1 := by simpa [localValuationSubringResidueField_card q] using hbound

end
end DkMath.Lib.NumberTheory
