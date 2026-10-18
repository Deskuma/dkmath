/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealGaloisTransport
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

#print "file: DkMath.Lib.NumberTheory.GaloisPhaseObstructionTransport"

/-!
# IRR-006: ガロア位相輸送と分岐単元補正

整数係数の線形因子は σₐ により i ↦ ai と移る。一方 λ = 1−ζ は固定されず、
σₐ(λ) = cₐ λ（cₐ は単元）となる。そのため正規化因子では
σₐ(Qᵢ) = cₐ⁻¹ Qₐᵢ である。単元を捨ててよいのはイデアルの等式へ移った後だけ。

以下は元の等式、実際のイデアル根の等式、類群の等式を順に証明する。
係数の固定性を明示し、一般の円分整数係数を持つ State に無条件な再索引則を
課さない。正則性、Bernoulli 数と類群を結ぶ定理、類の消滅は仮定しない。
-/

namespace DkMath.Lib.NumberTheory
open scoped NumberField nonZeroDivisors

namespace RamifiedPhasePacket
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {p : ℕ} [Fact p.Prime] (P : RamifiedPhasePacket R p)

/-- 単元 a による全位相の置換。位相0も含め、積を mod p で還元する。 -/
def phaseMul (a : (ZMod p)ˣ) (i : Fin p) : Fin p :=
  ⟨(a.val.val * i.val) % p, Nat.mod_lt _ (Fact.out : p.Prime).pos⟩

/-- 添字を剰余体に埋めると通常の乗法作用になる。 -/
theorem phaseMul_cast (a : (ZMod p)ˣ) (i : Fin p) :
    ((phaseMul a i).val : ZMod p) = (a : ZMod p) * (i.val : ZMod p) := by
  simp [phaseMul, Nat.cast_mul]

private theorem phase_cast_injective :
    Function.Injective (fun i : Fin p => (i.val : ZMod p)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hv

/-- 位相作用の恒等元。 -/
theorem phaseMul_one (i : Fin p) : phaseMul 1 i = i := by
  apply phase_cast_injective
  change ((phaseMul 1 i).val : ZMod p) = (i.val : ZMod p)
  rw [phaseMul_cast]
  simp

/-- 位相作用の合成則。 -/
theorem phaseMul_mul (a b : (ZMod p)ˣ) (i : Fin p) :
    phaseMul (a * b) i = phaseMul a (phaseMul b i) := by
  apply phase_cast_injective
  simp only [phaseMul_cast, Units.val_mul, mul_assoc]

/-- 全位相を保つ本当の置換。逆置換は a⁻¹ で与えられる。 -/
def phasePerm (a : (ZMod p)ˣ) : Equiv.Perm (Fin p) where
  toFun := phaseMul a
  invFun := phaseMul a⁻¹
  left_inv i := by rw [← phaseMul_mul, inv_mul_cancel, phaseMul_one]
  right_inv i := by rw [← phaseMul_mul, mul_inv_cancel, phaseMul_one]

/-- 位相0（Gap）は全ガロア作用で固定される。 -/
theorem phaseMul_zero (a : (ZMod p)ˣ) :
    phaseMul a ⟨0, (Fact.out : p.Prime).pos⟩ = ⟨0, (Fact.out : p.Prime).pos⟩ := by
  apply Fin.ext
  simp [phaseMul]

/-- 冪の mod p 還元が、実際の位相置換と一致する。 -/
theorem zeta_phaseMul (a : (ZMod p)ˣ) (i : Fin p) :
    P.zeta ^ (phaseMul a i).val = (P.zeta ^ a.val.val) ^ i.val := by
  change P.zeta ^ ((a.val.val * i.val) % p) = _
  rw [← pow_mul]
  have h := pow_mod_orderOf P.zeta (a.val.val * i.val)
  rw [← P.primitive.eq_orderOf] at h
  exact h

/-- 正規化した線形因子を運ぶための中心等式。
`x,y` が固定される場合だけ同じ族の位相置換になる。λ は単元倍で動く。 -/
theorem quotient_galois (e : R ≃+* R) (a : (ZMod p)ˣ)
    (hzeta : e P.zeta = P.zeta ^ a.val.val)
    (c : Rˣ) (hc : e P.lambda = c * P.lambda)
    (x y q : R) (hq : x + y = P.lambda * q)
    (hx : e x = x) (hy : e y = y) (i : Fin p) :
    e (P.quotient q y i) = (↑c⁻¹ : R) * P.quotient q y (phaseMul a i) := by
  have source : x + P.zeta ^ i.val * y = P.lambda * P.quotient q y i := by
    have := P.quotient_spec q y i
    linear_combination this + hq
  have target : x + P.zeta ^ (phaseMul a i).val * y =
      P.lambda * P.quotient q y (phaseMul a i) := by
    have := P.quotient_spec q y (phaseMul a i)
    linear_combination this + hq
  have image := congrArg e source
  simp only [map_add, map_mul, map_pow, hx, hy, hzeta, hc] at image
  rw [← P.zeta_phaseMul a i, target] at image
  have he : c * e (P.quotient q y i) = P.quotient q y (phaseMul a i) := by
    apply mul_left_cancel₀ P.lambda_prime.ne_zero
    linear_combination -image
  calc
    e (P.quotient q y i) = (↑c⁻¹ : R) * (c * e (P.quotient q y i)) := by simp
    _ = _ := by rw [he]

/-- 同じ正規化因子族を持つ packet の根は、実際にガロア輸送される。
任意に選んだイデアル根について成り立ち、主イデアル根への置換はしない。 -/
theorem phase_root_galois (C : PhaseClassPacket R p (Fin p))
    (q y x : R) (hf : ∀ i, C.factor i = P.quotient q y i)
    (hq : x + y = P.lambda * q)
    (e : R ≃+* R) (a : (ZMod p)ˣ) (hzeta : e P.zeta = P.zeta ^ a.val.val)
    (c : Rˣ) (hc : e P.lambda = c * P.lambda)
    (hx : e x = x) (hy : e y = y) (i : Fin p) :
    mapNonzeroIdeal e (C.power i).root = (C.power (phaseMul a i)).root := by
  apply IdealPowerObstruction.root_transport_of_unit _ _ e
    (Fact.out : p.Prime).ne_zero c⁻¹
  rw [hf, hf]
  exact P.quotient_galois e a hzeta c hc x y q hq hx hy i

/-- σₐ(ωᵢ) = ωₐᵢ。これは実際の類群同型と実際の根の対応から従う。 -/
theorem phase_obstruction_galois (C : PhaseClassPacket R p (Fin p))
    (q y x : R) (hf : ∀ i, C.factor i = P.quotient q y i)
    (hq : x + y = P.lambda * q)
    (e : R ≃+* R) (a : (ZMod p)ˣ) (hzeta : e P.zeta = P.zeta ^ a.val.val)
    (c : Rˣ) (hc : e P.lambda = c * P.lambda)
    (hx : e x = x) (hy : e y = y) (i : Fin p) :
    ClassGroup.mulEquiv e (C.obstruction i) = C.obstruction (phaseMul a i) := by
  rw [PhaseClassPacket.obstruction, IdealPowerObstruction.obstruction, classGroup_map_mk0,
    P.phase_root_galois C q y x hf hq e a hzeta c hc hx hy i]
  rfl

end RamifiedPhasePacket

namespace CyclotomicPhaseGalois
variable {K : Type*} [Field K] [NumberField K]
  {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

/-- a ∈ (ℤ/pℤ)ˣ に対応する真の有理円分体ガロア自己同型を整数環へ制限する。 -/
noncomputable def sigma (a : (ZMod p)ˣ) : 𝓞 K ≃+* 𝓞 K :=
  NumberField.RingOfIntegers.mapRingEquiv
    (((IsCyclotomicExtension.Rat.galEquivZMod p K).symm a).toRingEquiv)

/-- 恒等ガロア作用は整数環でも恒等写像である。 -/
theorem sigma_one : sigma (K := K) (1 : (ZMod p)ˣ) = RingEquiv.refl (𝓞 K) := by
  ext z
  change ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm 1) (z : K) = (z : K)
  rw [map_one]
  rfl

/-- ガロア群の乗法を整数環の自己同型の合成へ運ぶ。 -/
theorem sigma_mul (a b : (ZMod p)ˣ) :
    sigma (K := K) (a * b) = (sigma b).trans (sigma a) := by
  ext z
  change ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm (a * b)) (z : K) =
    ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm a)
      (((IsCyclotomicExtension.Rat.galEquivZMod p K).symm b) (z : K))
  rw [map_mul]
  rfl

/-- 整数係数は固定される。一般の円分整数係数ではこの前提を省けない。 -/
theorem sigma_int (a : (ZMod p)ˣ) (n : ℤ) : sigma (K := K) a (n : 𝓞 K) = n :=
  map_intCast _ n

/-- 生成元への作用が σₐ(ζ) = ζᵃ であることを、体から整数環へ降ろす。 -/
theorem sigma_zeta {ζ : K} (hζ : IsPrimitiveRoot ζ p) (a : (ZMod p)ˣ) :
    sigma (K := K) a hζ.toInteger = hζ.toInteger ^ a.val.val := by
  apply Subtype.ext
  change ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm a) ζ = ζ ^ a.val.val
  have h := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq p K
    ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm a) hζ.pow_eq_one
  rw [MulEquiv.apply_symm_apply] at h
  exact h

/-- λ の共役は λ の単元倍。その単元は一般に1でも p乗でもない。 -/
theorem exists_ramifier_unit {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    (a : (ZMod p)ˣ) :
    ∃ c : (𝓞 K)ˣ, sigma a (cyclotomicRamifiedPhase hζ hodd).lambda =
      c * (cyclotomicRamifiedPhase hζ hodd).lambda := by
  have h := hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime
    (ZMod.val_coe_unit_coprime a)
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  change sigma a (1 - hζ.toInteger) = (c : 𝓞 K) * (1 - hζ.toInteger)
  rw [map_sub, map_one, sigma_zeta hζ a]
  linear_combination hc

/-- 整数係数に対する主定理。単元補正を供給する前提すら円分体の内部で証明する。
packet のイデアル p乗表示だけを仮定し、類群の torsion-free 条件は要求しない。 -/
theorem obstruction_int {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    (C : PhaseClassPacket (𝓞 K) p (Fin p)) (q : 𝓞 K) (A B : ℤ)
    (hq : (A : 𝓞 K) + B = (cyclotomicRamifiedPhase hζ hodd).lambda * q)
    (hf : ∀ i, C.factor i = (cyclotomicRamifiedPhase hζ hodd).quotient q B i)
    (a : (ZMod p)ˣ) (i : Fin p) :
    ClassGroup.mulEquiv (sigma a) (C.obstruction i) =
      C.obstruction (RamifiedPhasePacket.phaseMul a i) := by
  obtain ⟨c, hc⟩ := exists_ramifier_unit hζ hodd a
  exact (cyclotomicRamifiedPhase hζ hodd).phase_obstruction_galois C q B A hf hq
    (sigma a) a (sigma_zeta hζ a) c hc (sigma_int a A) (sigma_int a B) i

end CyclotomicPhaseGalois
end DkMath.Lib.NumberTheory
