/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionAdditiveChartFrontier
import DkMath.FLT.Seven.SevenRamifiedFusionPrimeLoadGalois
import Mathlib.Algebra.QuadraticAlgebra.Basic

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixCarrier"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false
open scoped QuadraticAlgebra

namespace SevenCyclotomicDegreeSixInt

open SevenRealCubicInt

/-- The explicit quadratic algebra over the real cubic order in which
`zeta² = (alpha - 1) zeta - 1`.

Mathlib's `QuadraticAlgebra R a b` uses the convention
`omega² = a + b * omega`, hence the parameters `a = -1` and
`b = alpha - 1`. -/
abbrev Ring : Type :=
  QuadraticAlgebra SevenRealCubicInt (-1) (alpha - 1)

/-- The oriented cyclotomic generator. -/
def zeta : Ring :=
  ⟨0, 1⟩

/-- The canonical inclusion of the real cubic order. -/
def ofReal : SevenRealCubicInt →+* Ring :=
  algebraMap SevenRealCubicInt Ring

/-- The inverse-root conjugate `(alpha - 1) - zeta`. -/
def zetaInv : Ring :=
  ⟨alpha - 1, -1⟩

/-- The defining quadratic relation
`zeta² - (alpha - 1) zeta + 1 = 0`. -/
theorem zeta_quadratic_relation :
    zeta ^ 2 - ofReal (alpha - 1) * zeta + 1 = 0 := by
  rw [pow_two]
  ext <;> simp [zeta, ofReal]

/-- The two displayed roots add to the real trace `alpha - 1`. -/
theorem zeta_add_zetaInv :
    zeta + zetaInv = ofReal (alpha - 1) := by
  ext <;> simp [zeta, zetaInv, ofReal]

/-- The two displayed roots multiply to one. -/
theorem zeta_mul_zetaInv :
    zeta * zetaInv = 1 := by
  ext <;> simp [zeta, zetaInv]

/-- Reverse-order inverse identity. -/
theorem zetaInv_mul_zeta :
    zetaInv * zeta = 1 := by
  rw [mul_comm]
  exact zeta_mul_zetaInv

/-- The oriented seventh root as an explicit unit. -/
def zetaUnit : Ringˣ where
  val := zeta
  inv := zetaInv
  val_inv := zeta_mul_zetaInv
  inv_val := zetaInv_mul_zeta

/-- The real cubic generator is recovered as
`alpha = 1 + zeta + zeta⁻¹`. -/
theorem ofReal_alpha :
    ofReal alpha = 1 + zeta + zetaInv := by
  ext <;> simp [ofReal, zeta, zetaInv]

/-- Cubic relation of the real trace `alpha - 1`. -/
theorem alphaSubOne_cubic_relation :
    (alpha - 1) ^ 3 + (alpha - 1) ^ 2 -
        2 * (alpha - 1) - 1 = 0 := by
  have h :
      alpha ^ 3 - 2 * alpha ^ 2 - alpha + 1 = 0 := by
    rw [alpha_cube]
    ring
  linear_combination h

/-- The same trace relation transported into the quadratic carrier. -/
theorem ofReal_alphaSubOne_cubic_relation :
    ofReal (alpha - 1) ^ 3 +
        ofReal (alpha - 1) ^ 2 -
        2 * ofReal (alpha - 1) - 1 = 0 := by
  have h := congrArg ofReal alphaSubOne_cubic_relation
  simpa only [map_add, map_sub, map_mul, map_pow,
    map_ofNat, map_one, map_zero] using h

private theorem seventh_pow_eq_one_of_quadratic_realTrace
    {S : Type*} [CommRing S]
    (z t : S)
    (hq : z ^ 2 - t * z + 1 = 0)
    (ht : t ^ 3 + t ^ 2 - 2 * t - 1 = 0) :
    z ^ 7 = 1 := by
  linear_combination
    (t ^ 5 + t ^ 4 * z + t ^ 3 * z ^ 2 - 4 * t ^ 3 +
      t ^ 2 * z ^ 3 - 3 * t ^ 2 * z + t * z ^ 4 -
      2 * t * z ^ 2 + 3 * t + z ^ 5 - z ^ 3 + z) * hq +
    (t ^ 3 * z - t ^ 2 * z - t ^ 2 - 2 * t * z +
      t + z + 1) * ht

/-- The explicit quadratic generator is a seventh root of unity. -/
theorem zeta_pow_seven :
    zeta ^ 7 = 1 :=
  seventh_pow_eq_one_of_quadratic_realTrace
    zeta (ofReal (alpha - 1))
    zeta_quadratic_relation ofReal_alphaSubOne_cubic_relation

/-- The selected seventh root is nontrivial. -/
theorem zeta_ne_one :
    zeta ≠ 1 := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  norm_num [zeta] at him

/-- The canonical root has exact order seven. -/
theorem zeta_isPrimitiveRoot :
    IsPrimitiveRoot zeta 7 := by
  refine ⟨zeta_pow_seven, ?_⟩
  intro l hl
  by_contra hnot
  have hcop : Nat.Coprime 7 l :=
    (Nat.Prime.coprime_iff_not_dvd
      (by norm_num : Nat.Prime 7)).mpr hnot
  have hone :
      zeta = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp
      ⟨zeta_pow_seven, hl⟩
  exact zeta_ne_one hone

/-- Unit-valued seventh-power identity used by the provider contract. -/
theorem zetaUnit_pow_seven :
    zetaUnit ^ 7 = 1 := by
  apply Units.ext
  change zeta ^ 7 = 1
  exact zeta_pow_seven

/-- Unit-valued nontriviality used by the provider contract. -/
theorem zetaUnit_ne_one :
    zetaUnit ≠ 1 := by
  intro h
  exact zeta_ne_one (congrArg Units.val h)

/-- The carrier is canonically free of rank two over the real cubic order. -/
theorem rankOverReal_eq_two :
    Module.rank SevenRealCubicInt Ring = 2 :=
  QuadraticAlgebra.rank_eq_two (-1) (alpha - 1)

/-- Explicit six integral coordinates: three real and three oriented
quadratic coordinates. -/
def coordinates : Ring ≃+ (Fin 6 → ℤ) where
  toFun x i :=
    if i = 0 then x.re.fst else
    if i = 1 then x.re.snd else
    if i = 2 then x.re.thd else
    if i = 3 then x.im.fst else
    if i = 4 then x.im.snd else
      x.im.thd
  invFun f :=
    ⟨⟨f 0, f 1, f 2⟩, ⟨f 3, f 4, f 5⟩⟩
  left_inv x := by
    ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp

/-- Consequently the explicit carrier has integral rank six. -/
theorem rankOverIntegers_eq_six :
    Module.rank ℤ Ring = 6 := by
  rw [(coordinates.toIntLinearEquiv).rank_eq]
  exact rank_fin_fun 6

/-- The real-cubic inclusion is injective in the explicit pair model. -/
theorem ofReal_injective :
    Function.Injective ofReal :=
  QuadraticAlgebra.algebraMap_injective

private theorem ratio_quadratic_relation
    {p : RamifiedSignedRootDepthPacket} {q : ℕ}
    (a : p.QuotientPrimeMuSevenAddress q) :
    (a.ratio : ZMod q) ^ 2 =
      -1 +
        (a.evalAlphaRoot alpha - 1) *
          (a.ratio : ZMod q) := by
  let r : ZMod q := (a.ratio : ZMod q)
  let rInv : ZMod q := (a.ratio⁻¹ : ZMod q)
  have hinv : r * rInv = 1 := by
    exact congrArg Units.val (mul_inv_cancel a.ratio)
  have hbeta :
      a.evalAlphaRoot alpha = 1 + r + rInv := by
    rw [a.evalAlphaRoot_alpha]
    rfl
  rw [hbeta]
  change r ^ 2 = -1 + (1 + r + rInv - 1) * r
  linear_combination -hinv

/-- Every canonical quotient-prime real evaluation lifts to the oriented
degree-six carrier by sending `zeta` to the canonical ratio. -/
def localEval
    {p : RamifiedSignedRootDepthPacket} {q : ℕ}
    (a : p.QuotientPrimeMuSevenAddress q) :
    Ring →+* ZMod q where
  toFun x :=
    a.evalAlphaRoot x.re +
      (a.ratio : ZMod q) * a.evalAlphaRoot x.im
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp only [QuadraticAlgebra.re_add,
      QuadraticAlgebra.im_add, map_add]
    ring
  map_mul' x y := by
    have hr := ratio_quadratic_relation a
    simp only [QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, map_add, map_mul, map_neg,
      map_sub, map_one]
    linear_combination
      -(a.evalAlphaRoot x.im * a.evalAlphaRoot y.im) * hr

theorem localEval_ofReal
    {p : RamifiedSignedRootDepthPacket} {q : ℕ}
    (a : p.QuotientPrimeMuSevenAddress q)
    (x : SevenRealCubicInt) :
    localEval a (ofReal x) = a.evalAlphaRoot x := by
  simp [localEval, ofReal, QuadraticAlgebra.algebraMap_eq]

theorem localEval_zeta
    {p : RamifiedSignedRootDepthPacket} {q : ℕ}
    (a : p.QuotientPrimeMuSevenAddress q) :
    localEval a zeta = (a.ratio : ZMod q) := by
  simp [localEval, zeta]

end SevenCyclotomicDegreeSixInt

namespace RamifiedSignedRootDepthPacket

open SevenRealCubicInt SevenCyclotomicDegreeSixInt

/-- The oriented linear factor `R - zeta L`. -/
def cyclotomicDegreeSixCarrier
    (p : RamifiedSignedRootDepthPacket) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal p.signedRightRoot -
    zeta * ofReal p.signedLeftRoot

/-- Its inverse-root conjugate `R - zeta⁻¹ L`. -/
def cyclotomicDegreeSixCarrierConj
    (p : RamifiedSignedRootDepthPacket) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal p.signedRightRoot -
    zetaInv * ofReal p.signedLeftRoot

/-- The oriented degree-six factor and its conjugate multiply exactly to
the image of the zeroth real-pair carrier. -/
theorem cyclotomicDegreeSixCarrier_mul_conj
    (p : RamifiedSignedRootDepthPacket) :
    p.cyclotomicDegreeSixCarrier *
        p.cyclotomicDegreeSixCarrierConj =
      ofReal (p.realPairCarrier 0) := by
  let r : SevenCyclotomicDegreeSixInt.Ring :=
    ofReal p.signedRightRoot
  let l : SevenCyclotomicDegreeSixInt.Ring :=
    ofReal p.signedLeftRoot
  calc
    p.cyclotomicDegreeSixCarrier *
          p.cyclotomicDegreeSixCarrierConj =
        r ^ 2 - (zeta + zetaInv) * (r * l) +
          (zeta * zetaInv) * l ^ 2 := by
      simp only [cyclotomicDegreeSixCarrier,
        cyclotomicDegreeSixCarrierConj, r, l]
      ring
    _ =
        r ^ 2 - ofReal (alpha - 1) * (r * l) +
          l ^ 2 := by
      rw [zeta_add_zetaInv, zeta_mul_zetaInv, one_mul]
    _ = ofReal (p.realPairCarrier 0) := by
      simp only [r, l, realPairCarrier, cyclicAlpha,
        Fin.isValue, ↓reduceIte, map_add, map_sub,
        map_mul, map_pow, map_intCast, map_one, ofReal]
      ring

end RamifiedSignedRootDepthPacket

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt SevenCyclotomicDegreeSixInt

/-- Canonical inhabitant of the additive-frontier degree-six provider
contract.  Its local maps send the oriented root to the already constructed
canonical quotient-prime ratio. -/
def degreeSixLocalRatioProvider
    (p : RamifiedSignedRootRoutingPacket) :
    DegreeSixLocalRatioProvider p SevenCyclotomicDegreeSixInt.Ring where
  coordinates := SevenCyclotomicDegreeSixInt.coordinates
  cubicMap := ofReal
  cubicMap_injective := ofReal_injective
  zeta := zetaUnit
  zeta_pow_seven := zetaUnit_pow_seven
  zeta_ne_one := zetaUnit_ne_one
  cubicMap_alpha := by
    change ofReal alpha = 1 + zeta + zetaInv
    exact ofReal_alpha
  localEval := fun a => SevenCyclotomicDegreeSixInt.localEval a
  localEval_cubic := fun a x =>
    SevenCyclotomicDegreeSixInt.localEval_ofReal a x
  localEval_zeta := fun a =>
    SevenCyclotomicDegreeSixInt.localEval_zeta a

/-- The provider's oriented linear carrier is the concrete carrier above. -/
theorem provider_orientedLinearCarrier_eq
    (p : RamifiedSignedRootRoutingPacket) :
    (p.degreeSixLocalRatioProvider).orientedLinearCarrier =
      p.signedDepth.cyclotomicDegreeSixCarrier := rfl

/-- The provider's conjugate factor is the concrete inverse-root carrier. -/
theorem provider_conjugateLinearCarrier_eq
    (p : RamifiedSignedRootRoutingPacket) :
    (p.degreeSixLocalRatioProvider).conjugateLinearCarrier =
      p.signedDepth.cyclotomicDegreeSixCarrierConj := rfl

/-- At every canonical quotient-prime address, the concrete oriented
degree-six carrier vanishes. -/
theorem localEval_cyclotomicDegreeSixCarrier_zero
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (a : p.signedDepth.QuotientPrimeMuSevenAddress q) :
    SevenCyclotomicDegreeSixInt.localEval a
        p.signedDepth.cyclotomicDegreeSixCarrier = 0 := by
  exact
    DegreeSixLocalRatioProvider.localEval_orientedLinearCarrier_zero
      p.degreeSixLocalRatioProvider a

/-- At the same address, the concrete inverse-root conjugate does not
vanish. -/
theorem localEval_cyclotomicDegreeSixCarrierConj_ne_zero
    (p : RamifiedSignedRootRoutingPacket)
    {q : ℕ}
    (a : p.signedDepth.QuotientPrimeMuSevenAddress q) :
    SevenCyclotomicDegreeSixInt.localEval a
        p.signedDepth.cyclotomicDegreeSixCarrierConj ≠ 0 := by
  exact
    DegreeSixLocalRatioProvider.localEval_conjugateLinearCarrier_ne_zero
      p.degreeSixLocalRatioProvider a

/-- Concrete synthesis of the oriented factor pair with any existing
loaded-core seventh-power split. -/
theorem cyclotomicDegreeSixPair_associated_loadedCore
    (p : RamifiedSignedRootRoutingPacket)
    (loaded : RealPairLoadedPowerSplit p) :
    Associated
      (p.signedDepth.cyclotomicDegreeSixCarrier *
        p.signedDepth.cyclotomicDegreeSixCarrierConj)
      (ofReal
        (eisensteinAxis *
          (loaded.load21 0 * loaded.load22 0 *
            loaded.residualRoot 0 ^ 7))) := by
  exact
    DegreeSixLocalRatioProvider.orientedPair_associated_loadedCore
      p.degreeSixLocalRatioProvider loaded

/-- The FUSION additive-chart frontier is now unconditionally inhabited by
the concrete degree-six carrier and the existing loaded-core packet. -/
theorem nonempty_additiveChartFrontierPacket_degreeSix
    (p : RamifiedSignedRootRoutingPacket) :
    Nonempty
      (AdditiveChartFrontierPacket p
        SevenCyclotomicDegreeSixInt.Ring) :=
  nonempty_additiveChartFrontierPacket p
    p.degreeSixLocalRatioProvider

end RamifiedSignedRootRoutingPacket

end

end DkMath.FLT.Seven
