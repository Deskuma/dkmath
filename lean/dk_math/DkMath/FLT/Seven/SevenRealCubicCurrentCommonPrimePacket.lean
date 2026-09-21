import DkMath.FLT.Seven.SevenRealCubicCurrentCyclotomicPhase
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeResidueOne
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquareIdealSupport

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! The quotient-side data used by the current common-prime argument. -/

structure CurrentCommonPrimeResiduePacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (q : ℕ) where
  q_prime : q.Prime
  q_dvd_c : q ∣ h.c
  q_ne_seven : q ≠ 7
  Q : Ideal O
  Q_maximal : Q.IsMaximal
  Q_prime : Q.IsPrime
  Q_liesOver : Q.LiesOver (Ideal.span {(q : ℤ)})
  evalEquiv : Q.ResidueField ≃+* ZMod q
  evalReal : SevenRealCubicInt →+* ZMod q
  evalReal_formula :
    evalReal = evalEquiv.toRingHom.comp
      (@directOrbitCommonPrimeEval Q Q_prime)
  quotientRoot_zero : evalReal h.squareRefinement.quotientSquareRoot = 0
  quotient_zero : evalReal (directOrbitQuotient p) = 0
  rho_ne_zero : evalReal p.rho ≠ 0
  rotate_rho_ne_zero : evalReal (rotateEquiv p.rho) ≠ 0

namespace CurrentCommonPrimeResiduePacket

theorem evalReal_apply
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) (u : SevenRealCubicInt) :
    a.evalReal u = a.evalEquiv
      (@directOrbitCommonPrimeEval a.Q a.Q_prime u) := by
  rw [a.evalReal_formula]
  rfl

end CurrentCommonPrimeResiduePacket

theorem currentCommonPrime_residuePacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    Nonempty (CurrentCommonPrimeResiduePacket h q) := by
  obtain ⟨_, Q, _, hQmax, _, _, _, hQlies, _, hQdiv, _⟩ :=
    directOrbitSquareRefinement_exists_distinct_prime_ideals
      h.squareRefinement hq
      (directOrbitCommonPrime_dvd_data h q hqc).1
      (directOrbitCommonPrime_dvd_data h q hqc).2.1
  let hQprime : Q.IsPrime := hQmax.isPrime
  letI : Q.IsPrime := hQprime
  letI : Q.LiesOver (Ideal.span {(q : ℤ)}) := hQlies
  letI : Fintype Q.ResidueField := Fintype.ofFinite Q.ResidueField
  letI : Fact q.Prime := ⟨hq⟩
  have hsplit := common_norm_prime_complete_split
    h.squareRefinement hq
    (directOrbitCommonPrime_dvd_data h q hqc).1
    (directOrbitCommonPrime_dvd_data h q hqc).2.1
  have hinertia : Q.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span {(q : ℤ)}) Q Gal(Field / ℚ)]
    exact hsplit.2.2.2
  have hcardNat : Nat.card Q.ResidueField = q :=
    residueField_card_of_inertiaDeg_one hinertia
  have hcard : Fintype.card Q.ResidueField = q := by
    rw [Fintype.card_eq_nat_card, hcardNat]
  let e : Q.ResidueField ≃+* ZMod q :=
    FiniteField.ringEquivOfCardEq (K := Q.ResidueField) (K' := ZMod q) (by
      simpa [ZMod.card] using hcard)
  let f : SevenRealCubicInt →+* ZMod q :=
    e.toRingHom.comp (directOrbitCommonPrimeEval Q)
  have hroot : f h.squareRefinement.quotientSquareRoot = 0 := by
    have hmem := directOrbitSquareRefinement_mem_of_principal_dvd hQdiv
    have hmem' : modelToRingOfIntegers
        h.squareRefinement.quotientSquareRoot ∈ Q := by
      simpa only [modelEquivRingOfIntegers_apply] using hmem
    simp [f, directOrbitCommonPrimeEval,
      Ideal.algebraMap_residueField_eq_zero.mpr hmem']
  have hquot : f (directOrbitQuotient p) = 0 := by
    rw [h.squareRefinement.powerSplit.quotient_eq,
      h.squareRefinement.powerSplit.quotientCore_eq,
      h.squareRefinement.quotientRoot_eq]
    simp [hroot]
  have hcop : IsCoprime (rotateEquiv p.rho) p.rho :=
    (directOrbit_roots_isCoprime p).symm
  have hpown : f (rotateEquiv p.rho) ^ 7 = f p.rho ^ 7 := by
    have hzero : f (seventhQuotient (rotateEquiv p.rho) p.rho) = 0 := by
      simpa [directOrbitQuotient] using hquot
    have hf := congrArg f (pow_seven_sub_pow_seven_factorization
      (rotateEquiv p.rho) p.rho)
    simpa only [map_sub, map_pow, map_mul, hzero, mul_zero,
      sub_eq_zero] using hf
  have hrho : f p.rho ≠ 0 := by
    intro hz
    have hrot : f (rotateEquiv p.rho) = 0 := by
      have hpow : f (rotateEquiv p.rho) ^ 7 = 0 := by
        simpa [hz] using hpown
      by_contra hne
      exact (pow_ne_zero 7 hne) hpow
    rcases hcop with ⟨u, v, huv⟩
    have hf := congrArg f huv
    have hf' : f u * f (rotateEquiv p.rho) + f v * f p.rho = 1 := by
      simpa using hf
    rw [hrot, hz, mul_zero, mul_zero, add_zero] at hf'
    norm_num at hf'
  have hrot : f (rotateEquiv p.rho) ≠ 0 := by
    intro hz
    have hrho' : f p.rho = 0 := by
      have hpow : f p.rho ^ 7 = 0 := by
        calc
          f p.rho ^ 7 = f (rotateEquiv p.rho) ^ 7 := hpown.symm
          _ = 0 := by rw [hz]; simp
      by_contra hne
      exact (pow_ne_zero 7 hne) hpow
    exact hrho hrho'
  refine ⟨{
    q_prime := hq
    q_dvd_c := hqc
    q_ne_seven := hsplit.1
    Q := Q
    Q_maximal := hQmax
    Q_prime := hQprime
    Q_liesOver := hQlies
    evalEquiv := e
    evalReal := f
    evalReal_formula := by rfl
    quotientRoot_zero := hroot
    quotient_zero := hquot
    rho_ne_zero := hrho
    rotate_rho_ne_zero := hrot }⟩

def CurrentCommonPrimeResiduePacket.tau
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) : (ZMod q)ˣ := by
  letI : Fact (Nat.Prime q) := ⟨a.q_prime⟩
  exact Units.mk0
    (a.evalReal (rotateEquiv p.rho) / a.evalReal p.rho)
    (div_ne_zero a.rotate_rho_ne_zero a.rho_ne_zero)

theorem CurrentCommonPrimeResiduePacket.evalReal_pow_seven_eq
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) :
    a.evalReal (rotateEquiv p.rho) ^ 7 = a.evalReal p.rho ^ 7 := by
  have hzero : a.evalReal
      (seventhQuotient (rotateEquiv p.rho) p.rho) = 0 := by
    simpa [directOrbitQuotient] using a.quotient_zero
  have hf := congrArg a.evalReal (pow_seven_sub_pow_seven_factorization
    (rotateEquiv p.rho) p.rho)
  simpa only [map_sub, map_pow, map_mul, hzero, mul_zero,
    sub_eq_zero] using hf

theorem CurrentCommonPrimeResiduePacket.tau_pow_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) :
    a.tau ^ 7 = 1 := by
  letI : Fact (Nat.Prime q) := ⟨a.q_prime⟩
  apply Units.ext
  change
    (a.evalReal (rotateEquiv p.rho) / a.evalReal p.rho) ^ 7 = 1
  rw [div_pow, a.evalReal_pow_seven_eq,
    div_self (pow_ne_zero _ a.rho_ne_zero)]

theorem CurrentCommonPrimeResiduePacket.tau_ne_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) :
    a.tau ≠ 1 := by
  letI : Fact (Nat.Prime q) := ⟨a.q_prime⟩
  intro heq
  have hval := congrArg Units.val heq
  change a.evalReal (rotateEquiv p.rho) /
      a.evalReal p.rho = 1 at hval
  have heq' : a.evalReal (rotateEquiv p.rho) =
      a.evalReal p.rho :=
    (div_eq_one_iff_eq a.rho_ne_zero).mp hval
  have hzero : a.evalReal
      (seventhQuotient (rotateEquiv p.rho) p.rho) = 0 := by
    simpa [directOrbitQuotient] using a.quotient_zero
  have hz : (7 : ZMod q) * a.evalReal p.rho ^ 6 = 0 := by
    simp only [seventhQuotient, map_add, map_mul, map_pow, heq'] at hzero
    linear_combination hzero
  have h7 : (7 : ZMod q) ≠ 0 := by
    intro h7
    have hd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).mp h7
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with hq1 | hq7
    · exact a.q_prime.ne_one hq1
    · exact a.q_ne_seven hq7
  exact (mul_ne_zero h7 (pow_ne_zero _ a.rho_ne_zero)) hz

theorem CurrentCommonPrimeResiduePacket.tau_orderOf
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) :
    orderOf a.tau = 7 :=
  orderOf_eq_prime a.tau_pow_seven a.tau_ne_one

theorem CurrentCommonPrimeResiduePacket.q_mod_seven_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeResiduePacket h q) :
    q % 7 = 1 := by
  letI : Fact (Nat.Prime q) := ⟨a.q_prime⟩
  have hdiv : 7 ∣ q - 1 := by
    rw [← a.tau_orderOf]
    exact ZMod.orderOf_units_dvd_card_sub_one a.tau
  have hmod : q ≡ 1 [MOD 7] :=
    ((Nat.modEq_iff_dvd' a.q_prime.one_le).mpr hdiv).symm
  simpa [Nat.ModEq] using hmod

structure CurrentCommonPrimeCyclotomicPacket
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p) (q : ℕ) where
  residue : CurrentCommonPrimeResiduePacket h q
  tau : (ZMod q)ˣ
  tau_eq : tau = residue.tau
  tau_pow_seven : tau ^ 7 = 1
  tau_ne_one : tau ≠ 1
  tau_orderOf : orderOf tau = 7
  phase : Fin 3
  phase_eq : residue.evalReal alpha = currentBeta tau (phase.val + 1)
  ratio : (ZMod q)ˣ
  ratio_eq : ratio = tau ^ (phase.val + 1)
  ratio_pow_seven : ratio ^ 7 = 1
  ratio_ne_one : ratio ≠ 1
  ratio_orderOf : orderOf ratio = 7
  address : CurrentMuSevenResidueAddress q

theorem currentCommonPrime_cyclotomicAddress
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    Nonempty (CurrentCommonPrimeCyclotomicPacket h q) := by
  obtain ⟨a⟩ := currentCommonPrime_residuePacket h q hq hqc
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have halpha : a.evalReal alpha ^ 3 - 2 * a.evalReal alpha ^ 2 -
      a.evalReal alpha + 1 = 0 := by
    have hcube := congrArg a.evalReal alpha_cube
    simp only [map_pow, map_mul, map_add, map_sub, map_one,
      map_ofNat] at hcube
    linear_combination hcube
  obtain ⟨k, hk⟩ := current_phase_alignment a.tau
    a.tau_pow_seven a.tau_ne_one halpha
  let ratio : (ZMod q)ˣ := a.tau ^ (k.val + 1)
  have hratio7 : ratio ^ 7 = 1 := by
    dsimp [ratio]
    calc
      (a.tau ^ (k.val + 1)) ^ 7 =
          a.tau ^ ((k.val + 1) * 7) := by rw [pow_mul]
      _ = a.tau ^ (7 * (k.val + 1)) := by rw [Nat.mul_comm]
      _ = (a.tau ^ 7) ^ (k.val + 1) := by rw [pow_mul]
      _ = 1 := by rw [a.tau_pow_seven, one_pow]
  have hratio1 : ratio ≠ 1 := by
    intro hratio
    have hdiv := orderOf_dvd_of_pow_eq_one hratio
    rw [a.tau_orderOf] at hdiv
    fin_cases k <;> norm_num at hdiv
  have hratioOrder : orderOf ratio = 7 :=
    orderOf_eq_prime hratio7 hratio1
  let address : CurrentMuSevenResidueAddress q := {
    prime := hq
    evalReal := a.evalReal
    ratio := ratio
    ratio_pow_seven := hratio7
    ratio_ne_one := hratio1
    eval_alpha := by
      simpa [ratio, currentBeta, Units.val_inv_eq_inv_val] using hk }
  refine ⟨{
    residue := a
    tau := a.tau
    tau_eq := rfl
    tau_pow_seven := a.tau_pow_seven
    tau_ne_one := a.tau_ne_one
    tau_orderOf := a.tau_orderOf
    phase := k
    phase_eq := hk
    ratio := ratio
    ratio_eq := rfl
    ratio_pow_seven := hratio7
    ratio_ne_one := hratio1
    ratio_orderOf := hratioOrder
    address := address }⟩

theorem CurrentCommonPrimeCyclotomicPacket.ratio_val_ne_inv
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeCyclotomicPacket h q) :
    (a.address.ratio : ZMod q) ≠
      ((a.address.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  letI : Fact (Nat.Prime q) := ⟨a.residue.q_prime⟩
  intro hratioVal
  have hratioUnits : a.address.ratio = a.address.ratio⁻¹ :=
    Units.ext hratioVal
  have hsq : a.address.ratio ^ 2 = 1 := by
    rw [pow_two]
    exact (congrArg (fun u => a.address.ratio * u) hratioUnits).trans
      (mul_inv_cancel a.address.ratio)
  have hdiv := orderOf_dvd_of_pow_eq_one hsq
  rw [a.address.ratio_orderOf] at hdiv
  norm_num at hdiv

theorem CurrentCommonPrimeCyclotomicPacket.currentKernel_isMaximal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeCyclotomicPacket h q) :
    a.address.currentKernel.IsMaximal :=
  a.address.currentKernel_isMaximal

theorem CurrentCommonPrimeCyclotomicPacket.conjugateKernel_isMaximal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeCyclotomicPacket h q) :
    a.address.conjugate.currentKernel.IsMaximal :=
  a.address.conjugate.currentKernel_isMaximal

theorem CurrentCommonPrimeCyclotomicPacket.currentKernel_comap_ofReal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeCyclotomicPacket h q) :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal a.address.currentKernel =
      RingHom.ker a.address.evalReal :=
  a.address.currentKernel_comap_ofReal

theorem CurrentCommonPrimeCyclotomicPacket.conjugateKernel_comap_ofReal
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeCyclotomicPacket h q) :
    Ideal.comap SevenCyclotomicDegreeSixInt.ofReal
        a.address.conjugate.currentKernel = RingHom.ker a.address.evalReal :=
  a.address.currentKernel_conjugate_comap_ofReal

theorem CurrentCommonPrimeCyclotomicPacket.currentKernel_ne_conjugateKernel
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}
    (a : CurrentCommonPrimeCyclotomicPacket h q) :
    a.address.currentKernel ≠ a.address.conjugate.currentKernel := by
  letI : Fact (Nat.Prime q) := ⟨a.residue.q_prime⟩
  let carrier : SevenCyclotomicDegreeSixInt.Ring :=
    zeta - ofReal (a.address.ratio.val.val : SevenRealCubicInt)
  have hmem : carrier ∈ a.address.currentKernel := by
    change a.address.currentLocalEval carrier = 0
    change a.address.currentLocalEval
      (zeta - ofReal (a.address.ratio.val.val : SevenRealCubicInt)) = 0
    rw [map_sub, a.address.currentLocalEval_zeta,
      a.address.currentLocalEval_ofReal, map_natCast]
    exact sub_eq_zero.mpr (ZMod.natCast_zmod_val a.address.ratio.val).symm
  have hnot : carrier ∉ a.address.conjugate.currentKernel := by
    intro hmem
    change a.address.conjugate.currentLocalEval carrier = 0 at hmem
    change a.address.conjugate.currentLocalEval
      (zeta - ofReal (a.address.ratio.val.val : SevenRealCubicInt)) = 0 at hmem
    rw [map_sub, a.address.currentLocalEval_conjugate_zeta,
      a.address.conjugate.currentLocalEval_ofReal, map_natCast] at hmem
    have hzero :
        ((a.address.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) =
          (a.address.ratio : ZMod q) := by
      calc
        ((a.address.ratio⁻¹ : (ZMod q)ˣ) : ZMod q) =
            (↑(a.address.ratio.val).val : ZMod q) :=
          sub_eq_zero.mp hmem
        _ = (a.address.ratio : ZMod q) :=
          ZMod.natCast_zmod_val a.address.ratio.val
    exact a.ratio_val_ne_inv hzero.symm
  intro heq
  exact hnot (heq ▸ hmem)

end SevenRealCubic
end
end DkMath.FLT.Seven
