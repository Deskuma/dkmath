/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaKUSState

#print "file: DkMath.RH.CFBRC.EtaKUSLimit"

noncomputable section

namespace DkMath.RH.CFBRCProjection

open Filter
open scoped Topology
open DkMath.KUS
open DkMath.RH.Weave.Analytic
open DkMath.RH.Weave.Finite

/--
The unit-rotation eta observations regarded as a sequence of KUS states.
The visible coefficient is the finite eta endpoint; the support retains the
truncation stage and the complex observation point.
-/
noncomputable def etaUnitKUSTrace (s : ℂ) :
    ℕ → GKUS ℂ EtaKUSUnit EtaKUSBlueprint :=
  fun N => etaUnitKUSState N s

@[simp] theorem toCoeff_etaUnitKUSTrace (N : ℕ) (s : ℂ) :
    toCoeff (etaUnitKUSTrace s N) =
      etaPartialEndpoint (N + 1) s := rfl

/-- The complex observation point survives at every stage of the trace. -/
@[simp] theorem etaUnitKUSTrace_point (N : ℕ) (s : ℂ) :
    (etaUnitKUSTrace s N).unit.point = s := rfl

/-- The truncation index is retained rather than erased by endpoint addition. -/
@[simp] theorem etaUnitKUSTrace_index (N : ℕ) (s : ℂ) :
    (etaUnitKUSTrace s N).unit.index = N + 1 := rfl

/-- Unit observation rotation is retained in the structural support. -/
@[simp] theorem etaUnitKUSTrace_rotation (N : ℕ) (s : ℂ) :
    (etaUnitKUSTrace s N).unit.rotation = 1 := rfl

/-- The critical centered coordinate remains queryable at every finite stage. -/
@[simp] theorem etaUnitKUSTrace_storedCenteredCoordinate
    (N : ℕ) (s : ℂ) :
    (etaUnitKUSTrace s N).blueprint.storedCenteredCoordinate =
      centeredSigma s.re := rfl

/--
Every signed eta term remains reconstructible from the retained observation
point, independently of the visible endpoint coefficient.
-/
@[simp] theorem etaUnitKUSTrace_signedVector
    (N i : ℕ) (s : ℂ) :
    etaSignedVector (etaUnitKUSTrace s N).unit.point i =
      etaSignedVector s i := rfl

/--
If ordinary finite eta endpoints tend to zero, then only the visible
coefficients of the KUS trace tend to zero.  No topology on the structural
support is needed for this statement.
-/
theorem toCoeff_etaUnitKUSTrace_tendsto_zero_of_endpoint_tendsto_zero
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s)
        atTop (nhds 0)) :
    Tendsto (fun N : ℕ => toCoeff (etaUnitKUSTrace s N))
      atTop (nhds 0) := by
  have hshift :
      Tendsto (fun N : ℕ => etaPartialEndpoint (N + 1) s)
        atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hzero
  change Tendsto (fun N : ℕ => etaPartialEndpoint (N + 1) s)
    atTop (nhds 0)
  exact hshift

/--
At every nonreal right-half-plane zeta zero, the visible eta coefficient of the
KUS trace vanishes in the limit while its structural fields remain available.
-/
theorem toCoeff_etaUnitKUSTrace_tendsto_zero_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    Tendsto (fun N : ℕ => toCoeff (etaUnitKUSTrace s N))
      atTop (nhds 0) := by
  exact
    toCoeff_etaUnitKUSTrace_tendsto_zero_of_endpoint_tendsto_zero
      (etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
        hre him hz)

/--
The explicitly zeroized trace has coefficient zero at every stage, but still
retains the observation point.
-/
@[simp] theorem etaUnitKUSZeroState_point (N : ℕ) (s : ℂ) :
    (etaUnitKUSZeroState N s).unit.point = s := rfl

/-- The explicitly zeroized trace also retains every signed eta term. -/
@[simp] theorem etaUnitKUSZeroState_signedVector
    (N i : ℕ) (s : ℂ) :
    etaSignedVector (etaUnitKUSZeroState N s).unit.point i =
      etaSignedVector s i := rfl

/--
A compact certificate of the separation between numerical vanishing and
structural persistence.
-/
structure EtaKUSVanishingCertificate (s : ℂ) where
  trace : ℕ → GKUS ℂ EtaKUSUnit EtaKUSBlueprint
  coefficient_tendsto_zero :
    Tendsto (fun N : ℕ => toCoeff (trace N)) atTop (nhds 0)
  point_preserved : ∀ N, (trace N).unit.point = s
  centeredCoordinate_preserved : ∀ N,
    (trace N).blueprint.storedCenteredCoordinate = centeredSigma s.re

/-- Ordinary endpoint convergence constructs a KUS vanishing certificate. -/
noncomputable def etaKUSVanishingCertificate_of_endpoint_tendsto_zero
    {s : ℂ}
    (hzero :
      Tendsto (fun N : ℕ => etaPartialEndpoint N s)
        atTop (nhds 0)) :
    EtaKUSVanishingCertificate s where
  trace := etaUnitKUSTrace s
  coefficient_tendsto_zero :=
    toCoeff_etaUnitKUSTrace_tendsto_zero_of_endpoint_tendsto_zero hzero
  point_preserved := fun N => etaUnitKUSTrace_point N s
  centeredCoordinate_preserved := fun N =>
    etaUnitKUSTrace_storedCenteredCoordinate N s

/-- A nonreal right-half-plane zeta zero supplies a KUS vanishing certificate. -/
noncomputable def etaKUSVanishingCertificate_of_riemannZeta_zero
    {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0)
    (hz : riemannZeta s = 0) :
    EtaKUSVanishingCertificate s :=
  etaKUSVanishingCertificate_of_endpoint_tendsto_zero
    (etaPartialEndpoint_tendsto_zero_of_riemannZeta_eq_zero_of_pos_re_of_im_ne_zero
      hre him hz)

end DkMath.RH.CFBRCProjection
