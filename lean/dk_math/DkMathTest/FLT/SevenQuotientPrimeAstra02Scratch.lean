import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer

/-! Astra-002: use the original orbit roots at a quotient prime, not a gap prime. -/

namespace DkMathTest.FLT.SevenQuotientPrimeAstra02Scratch

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt
open scoped NumberField

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem quotient_eval_mod_seven_one
    {q : ℕ} (hq : q.Prime) (h7 : (7 : ZMod q) ≠ 0)
    (f : SevenRealCubicInt →+* ZMod q) (x y : SevenRealCubicInt)
    (hcop : IsCoprime x y) (hzero : f (seventhQuotient x y) = 0) :
    q % 7 = 1 := by
  let : Fact q.Prime := ⟨hq⟩
  have hp : f x ^ 7 = f y ^ 7 := by
    have hf := congrArg f (pow_seven_sub_pow_seven_factorization x y)
    simpa only [map_sub, map_pow, map_mul, hzero, mul_zero, sub_eq_zero] using hf
  have hy : f y ≠ 0 := by
    intro hy
    have hx : f x = 0 := by simpa [hy] using hp
    rcases hcop with ⟨a, b, hab⟩
    have hf := congrArg f hab
    simp [hx, hy] at hf
  have hx : f x ≠ 0 := by
    intro hx
    have : f y = 0 := by simpa [hx] using hp.symm
    exact hy this
  have hne : f x ≠ f y := by
    intro heq
    have hz : 7 * f y ^ 6 = 0 := by
      simp only [seventhQuotient, map_add, map_mul, map_pow, heq] at hzero
      linear_combination hzero
    exact (mul_ne_zero h7 (pow_ne_zero _ hy)) hz
  let t : (ZMod q)ˣ := Units.mk0 (f x / f y) (div_ne_zero hx hy)
  have ht7 : t ^ 7 = 1 := by
    apply Units.ext
    change (f x / f y) ^ 7 = 1
    rw [div_pow, hp, div_self (pow_ne_zero _ hy)]
  have ht1 : t ≠ 1 := by
    intro ht
    have htval := congrArg Units.val ht
    change f x / f y = 1 at htval
    exact hne ((div_eq_one_iff_eq hy).mp htval)
  have htOrder : orderOf t = 7 := orderOf_eq_prime ht7 ht1
  have hdiv : 7 ∣ q - 1 := by
    rw [← htOrder]
    exact ZMod.orderOf_units_dvd_card_sub_one t
  have hmod : q ≡ 1 [MOD 7] := ((Nat.modEq_iff_dvd' hq.one_le).mpr hdiv).symm
  simpa [Nat.ModEq] using hmod

theorem common_norm_prime_mod_seven_one
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    q % 7 = 1 := by
  obtain ⟨_, Q, _, hQmax, _, _, _, hQlies, _, hQdiv, _⟩ :=
    directOrbitSquareRefinement_exists_distinct_prime_ideals t hq hqR hqS
  let : Q.IsMaximal := hQmax
  let : Q.IsPrime := hQmax.isPrime
  let : Q.LiesOver (Ideal.span {(q : ℤ)}) := hQlies
  let : Fintype Q.ResidueField := Fintype.ofFinite Q.ResidueField
  let : Fact q.Prime := ⟨hq⟩
  have hsplit := common_norm_prime_complete_split t hq hqR hqS
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
  have hroot : f t.quotientSquareRoot = 0 := by
    have hmem := directOrbitSquareRefinement_mem_of_principal_dvd hQdiv
    have hmem' : modelToRingOfIntegers t.quotientSquareRoot ∈ Q := by
      simpa only [modelEquivRingOfIntegers_apply] using hmem
    simp [f, directOrbitCommonPrimeEval,
      Ideal.algebraMap_residueField_eq_zero.mpr hmem']
  have hquot : f (directOrbitQuotient p) = 0 := by
    rw [t.powerSplit.quotient_eq, t.powerSplit.quotientCore_eq, t.quotientRoot_eq]
    simp [hroot]
  have h7 : (7 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).mp hz
    exact hsplit.1
      ((Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd |>.resolve_left hq.ne_one)
  exact quotient_eval_mod_seven_one hq h7 f (rotateEquiv p.rho) p.rho
    (directOrbit_roots_isCoprime p).symm hquot

theorem directOrbitCommonPrime_q_mod_seven_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) : q % 7 = 1 := by
  have hd := directOrbitCommonPrime_dvd_data h q hqc
  exact common_norm_prime_mod_seven_one h.squareRefinement hq hd.1 hd.2.1

#print axioms directOrbitCommonPrime_q_mod_seven_one

theorem twist_ratio_cyclic_product
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    let v := (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt)
    v * rotateEquiv v * rotateEquiv (rotateEquiv v) = -1 := by
  have haxis : norm (directOrbitPairAxisUnitOne : SevenRealCubicInt) = 1 := by
    rw [directOrbitPairAxisUnitOne_val, norm_pairAxisUnit_one]
  have h1 : norm (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) = 1 := by
    rw [directOrbit_squareTwist_coeff1_transport, Units.val_mul,
      Units.val_pow_eq_pow_val, norm_mul, SevenRealCubicInt.norm_pow,
      directOrbitRotateUnit_val, norm_rotateEquiv, haxis,
      directOrbit_squareTwist_coeff0_norm_eq_one]
    simp
  have h2 : norm (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt) = 1 := by
    rw [directOrbit_squareTwist_coeff2_transport, Units.val_mul,
      Units.val_pow_eq_pow_val, norm_mul, SevenRealCubicInt.norm_pow,
      directOrbitRotateUnit_val, norm_rotateEquiv, haxis, h1]
    simp
  have hi : norm (((directOrbitSquareTwistCoeff1 t)⁻¹ : SevenRealCubicIntˣ) :
      SevenRealCubicInt) = 1 := by
    have hh : norm ((directOrbitSquareTwistCoeff1 t : SevenRealCubicInt) *
        (((directOrbitSquareTwistCoeff1 t)⁻¹ : SevenRealCubicIntˣ) :
          SevenRealCubicInt)) = 1 := by simp [SevenRealCubicInt.norm]
    rw [SevenRealCubicInt.norm_mul, h1, one_mul] at hh
    exact hh
  have hn : norm (directOrbitCommonPrimeTwistRatio21 t : SevenRealCubicInt) = -1 := by
    simp only [directOrbitCommonPrimeTwistRatio21, Units.val_mul, SevenRealCubicInt.norm_mul,
      h2, hi, mul_one]
    norm_num [SevenRealCubicInt.norm]
  dsimp only
  rw [mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm, hn]
  rfl

#print axioms twist_ratio_cyclic_product

end DkMathTest.FLT.SevenQuotientPrimeAstra02Scratch
