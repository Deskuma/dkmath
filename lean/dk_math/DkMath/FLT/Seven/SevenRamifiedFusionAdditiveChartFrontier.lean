/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionDirectChartObstruction
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadAddress

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionAdditiveChartFrontier"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open SevenRealCubicInt

namespace RamifiedSignedRootRoutingPacket

/-- Exact provider contract for the first genuinely oriented degree-six
layer above the real cubic order.

The additive equivalence records that `K` is a rank-six integral carrier.
The distinguished unit `zeta` is an oriented primitive seventh root, the
real-cubic generator is its inversion-invariant coordinate, and every
canonical quotient-prime ratio extends to an evaluation of this carrier.

No global seventh-power factorization and no new Fermat chart are fields of
this contract. -/
structure DegreeSixLocalRatioProvider
    (p : RamifiedSignedRootRoutingPacket)
    (K : Type*) [CommRing K] where
  coordinates : K ≃+ (Fin 6 → ℤ)
  cubicMap : SevenRealCubicInt →+* K
  cubicMap_injective : Function.Injective cubicMap
  zeta : Kˣ
  zeta_pow_seven : zeta ^ 7 = 1
  zeta_ne_one : zeta ≠ 1
  cubicMap_alpha :
    cubicMap alpha =
      1 + (zeta : K) + ((zeta⁻¹ : Kˣ) : K)
  localEval :
    ∀ {q : ℕ},
      p.signedDepth.QuotientPrimeMuSevenAddress q →
        K →+* ZMod q
  localEval_cubic :
    ∀ {q : ℕ}
      (a : p.signedDepth.QuotientPrimeMuSevenAddress q)
      (x : SevenRealCubicInt),
      localEval a (cubicMap x) = a.evalAlphaRoot x
  localEval_zeta :
    ∀ {q : ℕ}
      (a : p.signedDepth.QuotientPrimeMuSevenAddress q),
      localEval a (zeta : K) = (a.ratio : ZMod q)

namespace DegreeSixLocalRatioProvider

variable {p : RamifiedSignedRootRoutingPacket}
variable {K : Type*} [CommRing K]

/-- The oriented linear factor selected by `zeta`. -/
def orientedLinearCarrier
    (d : DegreeSixLocalRatioProvider p K) : K :=
  d.cubicMap
      (p.signedDepth.signedRightRoot : SevenRealCubicInt) -
    (d.zeta : K) *
      d.cubicMap
        (p.signedDepth.signedLeftRoot : SevenRealCubicInt)

/-- Its complex-conjugate orientation, obtained by inverting `zeta`. -/
def conjugateLinearCarrier
    (d : DegreeSixLocalRatioProvider p K) : K :=
  d.cubicMap
      (p.signedDepth.signedRightRoot : SevenRealCubicInt) -
    ((d.zeta⁻¹ : Kˣ) : K) *
      d.cubicMap
        (p.signedDepth.signedLeftRoot : SevenRealCubicInt)

/-- The two oriented linear factors multiply exactly to the zeroth real-pair
carrier.  Thus the provider really refines the existing real cubic carrier
rather than adding an unrelated primitive seventh root. -/
theorem oriented_mul_conjugate_eq_realPairCarrier
    (d : DegreeSixLocalRatioProvider p K) :
    d.orientedLinearCarrier * d.conjugateLinearCarrier =
      d.cubicMap (p.signedDepth.realPairCarrier 0) := by
  have hzeta :
      (d.zeta : K) * ((d.zeta⁻¹ : Kˣ) : K) = 1 := by
    simp
  have halpha := d.cubicMap_alpha
  simp only [orientedLinearCarrier, conjugateLinearCarrier,
    RamifiedSignedRootDepthPacket.realPairCarrier,
    SevenRealCubicInt.cyclicAlpha, Fin.isValue,
    ↓reduceIte, map_sub, map_add, map_mul, map_pow,
    map_intCast]
  rw [halpha]
  linear_combination
    (p.signedDepth.signedLeftRoot : K) ^ 2 * hzeta

/-- At every canonical quotient-prime address, the selected orientation
vanishes. -/
theorem localEval_orientedLinearCarrier_zero
    (d : DegreeSixLocalRatioProvider p K)
    {q : ℕ}
    (a : p.signedDepth.QuotientPrimeMuSevenAddress q) :
    d.localEval a d.orientedLinearCarrier = 0 := by
  rw [orientedLinearCarrier, map_sub, map_mul,
    d.localEval_cubic, d.localEval_cubic,
    d.localEval_zeta]
  simp only [map_intCast]
  rw [a.ratio_mul_signedLeftRoot, sub_self]

/-- The conjugate orientation does not vanish at the same address.  This is
the precise local choice that is lost after descending to the real-pair
coordinate `beta`. -/
theorem localEval_conjugateLinearCarrier_ne_zero
    (d : DegreeSixLocalRatioProvider p K)
    {q : ℕ}
    (a : p.signedDepth.QuotientPrimeMuSevenAddress q) :
    d.localEval a d.conjugateLinearCarrier ≠ 0 := by
  letI : Fact (Nat.Prime q) := ⟨a.prime⟩
  intro hzero
  have hconjugate :
      ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) *
          (p.signedDepth.signedLeftRoot : ZMod q) =
        (p.signedDepth.signedRightRoot : ZMod q) := by
    rw [conjugateLinearCarrier, map_sub, map_mul,
      d.localEval_cubic, d.localEval_cubic] at hzero
    have hzetaInv :
        d.localEval a (((d.zeta⁻¹ : Kˣ) : K)) =
          ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
      apply mul_left_cancel₀ a.ratio.ne_zero
      calc
        (a.ratio : ZMod q) *
              d.localEval a (((d.zeta⁻¹ : Kˣ) : K)) =
            d.localEval a (d.zeta : K) *
              d.localEval a (((d.zeta⁻¹ : Kˣ) : K)) := by
                rw [d.localEval_zeta]
        _ = d.localEval a
              ((d.zeta : K) * ((d.zeta⁻¹ : Kˣ) : K)) := by
                rw [map_mul]
        _ = 1 := by simp
        _ = (a.ratio : ZMod q) *
              ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
                exact
                  (congrArg Units.val
                    (mul_inv_cancel a.ratio)).symm
    rw [hzetaInv] at hzero
    simp only [map_intCast] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hleft :
      (p.signedDepth.signedLeftRoot : ZMod q) ≠ 0 :=
    by
      intro hleftZero
      have hrightZero :
          (p.signedDepth.signedRightRoot : ZMod q) = 0 := by
        rw [← a.ratio_mul_signedLeftRoot, hleftZero, mul_zero]
      rcases p.signedDepth.signedRoots_isCoprime with
        ⟨u, v, huv⟩
      have huvq := congrArg (fun z : ℤ => (z : ZMod q)) huv
      push_cast at huvq
      rw [hrightZero, hleftZero, mul_zero, mul_zero,
        zero_add] at huvq
      exact zero_ne_one huvq
  have hratioVal :
      (a.ratio : ZMod q) =
        ((a.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
    apply mul_right_cancel₀ hleft
    exact a.ratio_mul_signedLeftRoot.trans hconjugate.symm
  have hratioUnits :
      a.ratio = a.ratio⁻¹ :=
    Units.ext hratioVal
  have hsq : a.ratio ^ 2 = 1 := by
    rw [pow_two]
    exact
      (congrArg (fun u => a.ratio * u) hratioUnits).trans
        (mul_inv_cancel a.ratio)
  have hpow : a.ratio ^ 7 = a.ratio := by
    calc
      a.ratio ^ 7 = a.ratio ^ (2 * 3 + 1) := by norm_num
      _ = (a.ratio ^ 2) ^ 3 * a.ratio := by
        rw [pow_add, pow_mul, pow_one]
      _ = a.ratio := by rw [hsq]; simp
  apply a.ratio_ne_one
  calc
    a.ratio = a.ratio ^ 7 := hpow.symm
    _ = 1 := a.ratio_pow_seven

private theorem map_associated
    {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) {x y : A}
    (h : Associated x y) :
    Associated (f x) (f y) := by
  rcases h with ⟨u, hu⟩
  refine ⟨Units.map f u, ?_⟩
  change f x * f (u : A) = f y
  simpa only [map_mul] using congrArg f hu

/-- The oriented pair product inherits the complete loaded-core
factorization.  This is the strongest unconditional chart-ready statement:
one real pair has now been refined to an oriented degree-six pair, while its
axis, two scalar loads, and residual seventh power remain exact up to a
mapped unit. -/
theorem orientedPair_associated_loadedCore
    (d : DegreeSixLocalRatioProvider p K)
    (loaded : RamifiedSignedRootRoutingPacket.RealPairLoadedPowerSplit p) :
    Associated
      (d.orientedLinearCarrier * d.conjugateLinearCarrier)
      (d.cubicMap
        (eisensteinAxis *
          (loaded.load21 0 * loaded.load22 0 *
            loaded.residualRoot 0 ^ 7))) := by
  have hloaded :
      Associated
        (eisensteinAxis *
          (loaded.load21 0 * loaded.load22 0 *
            loaded.residualRoot 0 ^ 7))
        (p.signedDepth.realPairCarrier 0) := by
    exact
      (Associated.rfl.mul_mul (loaded.coreAssociated 0)).trans
        (Associated.of_eq
          (p.signedDepth.realPairCarrier_eq_eisensteinAxis_mul_core
            0).symm)
  exact
    (Associated.of_eq d.oriented_mul_conjugate_eq_realPairCarrier).trans
      (map_associated d.cubicMap hloaded.symm)

end DegreeSixLocalRatioProvider

/-- The additive-chart frontier joins a supplied honest degree-six
orientation to the unconditional FUSION-003F loaded-core packet.

It intentionally contains no new integer coordinates and no Fermat
equation.  Those are a later additive reconstruction obligation. -/
structure AdditiveChartFrontierPacket
    (p : RamifiedSignedRootRoutingPacket)
    (K : Type*) [CommRing K] where
  degreeSix : DegreeSixLocalRatioProvider p K
  loaded : RamifiedFusionLoadedCorePacket p

/-- Once a degree-six provider is supplied, all existing unconditional
loaded-core data can be attached without an additional arithmetic
hypothesis. -/
theorem nonempty_additiveChartFrontierPacket
    (p : RamifiedSignedRootRoutingPacket)
    {K : Type*} [CommRing K]
    (degreeSix : DegreeSixLocalRatioProvider p K) :
    Nonempty (AdditiveChartFrontierPacket p K) := by
  rcases p.nonempty_ramifiedFusionLoadedCorePacket with ⟨loaded⟩
  exact ⟨{
    degreeSix := degreeSix
    loaded := loaded }⟩

namespace AdditiveChartFrontierPacket

variable {p : RamifiedSignedRootRoutingPacket}
variable {K : Type*} [CommRing K]

/-- Public synthesis form of the degree-six loaded pair factorization. -/
theorem orientedPair_associated_loadedCore
    (s : AdditiveChartFrontierPacket p K) :
    Associated
      (s.degreeSix.orientedLinearCarrier *
        s.degreeSix.conjugateLinearCarrier)
      (s.degreeSix.cubicMap
        (eisensteinAxis *
          (s.loaded.loadedPowerSplit.load21 0 *
            s.loaded.loadedPowerSplit.load22 0 *
            s.loaded.loadedPowerSplit.residualRoot 0 ^ 7))) :=
  s.degreeSix.orientedPair_associated_loadedCore
    s.loaded.loadedPowerSplit

/-- Quotient-prime chart-ready synthesis: the oriented factor pair carries
the unconditional loaded seventh-power decomposition, and the canonical
local ratio distinguishes exactly one member of that pair. -/
theorem orientedLoadedFactor_chartReadyAt
    (s : AdditiveChartFrontierPacket p K)
    {q : ℕ}
    (a : p.signedDepth.QuotientPrimeMuSevenAddress q) :
    Associated
        (s.degreeSix.orientedLinearCarrier *
          s.degreeSix.conjugateLinearCarrier)
        (s.degreeSix.cubicMap
          (eisensteinAxis *
            (s.loaded.loadedPowerSplit.load21 0 *
              s.loaded.loadedPowerSplit.load22 0 *
              s.loaded.loadedPowerSplit.residualRoot 0 ^ 7))) ∧
      s.degreeSix.localEval a
          s.degreeSix.orientedLinearCarrier = 0 ∧
      s.degreeSix.localEval a
          s.degreeSix.conjugateLinearCarrier ≠ 0 :=
  ⟨s.orientedPair_associated_loadedCore,
    s.degreeSix.localEval_orientedLinearCarrier_zero a,
    s.degreeSix.localEval_conjugateLinearCarrier_ne_zero a⟩

/-- The old signed roots cannot be mistaken for the reconstructed additive
chart even after a degree-six orientation has been supplied. -/
theorem no_direct_signedFermatSevenChart
    (_s : AdditiveChartFrontierPacket p K) :
    ¬ ∃ c : ℤ,
      SignedFermatSevenChart
        p.signedDepth.signedRightRoot
        (-p.signedDepth.signedLeftRoot) c :=
  p.signedDepth.no_direct_signedFermatSevenChart

end AdditiveChartFrontierPacket

end RamifiedSignedRootRoutingPacket


end

end DkMath.FLT.Seven
