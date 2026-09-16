/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor

#print "file: DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport"

namespace DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport

open scoped BigOperators

open DkMath.CosmicFormula
open DkMath.NumberTheory.CyclotomicQRProduct
open DkMath.NumberTheory.CyclotomicQRGaloisAction
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.CyclotomicQRUniversalTransport
open DkMath.NumberTheory.CyclotomicQRUniversalTraceOneAnchor
open DkMath.NumberTheory.PrimeQuadraticDiscriminant
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private theorem eval_intCast_to_zmod
    {q z y : ℕ} (T : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        ![(z : ZMod q), (y : ZMod q)] T =
      ((MvPolynomial.eval ![(z : ℤ), (y : ℤ)] T : ℤ) : ZMod q) := by
  have h := MvPolynomial.map_eval (Int.castRingHom (ZMod q))
    ![(z : ℤ), (y : ℤ)] T
  have hv : (Int.castRingHom (ZMod q) : ℤ → ZMod q) ∘
      ![(z : ℤ), (y : ℤ)] =
      ![(z : ZMod q), (y : ZMod q)] := by
    funext i
    fin_cases i <;> simp
  rw [hv] at h
  simpa [MvPolynomial.eval_map] using h.symm

private theorem shell_cast_eq_zero_of_coordinate_dvd
    {L : Type*} [Field L] [Algebra ℚ L]
    {p q z y : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (hA : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ)
    (hS : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ) :
    GTailCyclotomicShell p
        ((z : ZMod q) - (y : ZMod q)) (y : ZMod q) = 0 := by
  let A : ℤ := MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ
  let S : ℤ := MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ
  have hnorm : (q : ℤ) ∣
      norm (P.coord (z : ℤ) (y : ℤ)) := by
    change (q : ℤ) ∣ A ^ 2 + A * S - signedPrimeParameter p * S ^ 2
    exact dvd_sub
      (dvd_add (dvd_pow hA (by norm_num))
        (dvd_mul_of_dvd_left hA S))
      (dvd_mul_of_dvd_right (dvd_pow hS (by norm_num))
        (signedPrimeParameter p))
  have hnorm_shell : (q : ℤ) ∣
      GTailCyclotomicShell p ((z : ℤ) - (y : ℤ)) (y : ℤ) := by
    rw [← P.coord_norm_eq (z : ℤ) (y : ℤ)]
    exact hnorm
  have hzero_int :
      ((GTailCyclotomicShell (R := ℤ) p ((z : ℤ) - (y : ℤ)) (y : ℤ) : ℤ) : ZMod q) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod q) q
      (GTailCyclotomicShell (R := ℤ) p ((z : ℤ) - (y : ℤ)) (y : ℤ))).2 hnorm_shell
  have hcast_shell :
      ((GTailCyclotomicShell (R := ℤ) p ((z : ℤ) - (y : ℤ)) (y : ℤ) : ℤ) : ZMod q) =
        GTailCyclotomicShell (R := ZMod q) p
          ((z : ZMod q) - (y : ZMod q)) (y : ZMod q) := by
    simp [GTailCyclotomicShell]
  rw [hcast_shell] at hzero_int
  exact hzero_int

private theorem shell_zero_implies_y_ne_zero
    {p q z y : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hshell : GTailCyclotomicShell p
      ((z : ZMod q) - (y : ZMod q)) (y : ZMod q) = 0)
    (hcop : Nat.Coprime z y) :
    (y : ZMod q) ≠ 0 := by
  intro hy
  have hpow : (z : ZMod q) ^ p = 0 := by
    have h := add_pow_eq_mul_GTailCyclotomicShell_add_gap p
      ((z : ZMod q) - (y : ZMod q)) (y : ZMod q)
    rw [sub_add_cancel, hshell, hy, mul_zero,
      zero_pow (Fact.out : Nat.Prime p).ne_zero, add_zero] at h
    exact h
  have hz : (z : ZMod q) = 0 := eq_zero_of_pow_eq_zero hpow
  have hqz : q ∣ z := (ZMod.natCast_eq_zero_iff z q).mp hz
  have hqy : q ∣ y := (ZMod.natCast_eq_zero_iff y q).mp hy
  exact (Nat.not_coprime_of_dvd_of_dvd (Fact.out : Nat.Prime q).one_lt
    hqz hqy) hcop

private theorem shell_zero_implies_primitive_root_ratio
    {p q z y : ℕ} [Fact p.Prime] [Fact q.Prime]
    (_hq2 : q ≠ 2) (hpq : q ≠ p)
    (hshell : GTailCyclotomicShell p
      ((z : ZMod q) - (y : ZMod q)) (y : ZMod q) = 0)
    (hcop : Nat.Coprime z y) :
    ∃ t : ZMod q, IsPrimitiveRoot t p ∧
      t = (z : ZMod q) / (y : ZMod q) := by
  have hy : (y : ZMod q) ≠ 0 := shell_zero_implies_y_ne_zero hshell hcop
  let t : ZMod q := (z : ZMod q) / (y : ZMod q)
  have hpow_zy : (z : ZMod q) ^ p = (y : ZMod q) ^ p := by
    have h := add_pow_eq_mul_GTailCyclotomicShell_add_gap p
      ((z : ZMod q) - (y : ZMod q)) (y : ZMod q)
    rw [sub_add_cancel, hshell, mul_zero, zero_add] at h
    exact h
  have ht_pow : t ^ p = 1 := by
    simp only [t, div_pow, hpow_zy, div_self (pow_ne_zero p hy)]
  have ht_ne_one : t ≠ 1 := by
    intro ht
    have hzy : (z : ZMod q) = (y : ZMod q) :=
      (div_eq_one_iff_eq hy).mp ht
    have hzero_shell :
        GTailCyclotomicShell p (0 : ZMod q) (y : ZMod q) = 0 := by
      simpa [hzy] using hshell
    have hsingle :
        GTailCyclotomicShell p (0 : ZMod q) (y : ZMod q) =
          (p : ZMod q) * (y : ZMod q) ^ (p - 1) := by
      rw [GTailCyclotomicShell]
      calc
        (∑ b ∈ Finset.range p,
            (0 + (y : ZMod q)) ^ b * (y : ZMod q) ^ (p - 1 - b)) =
            ∑ b ∈ Finset.range p, (y : ZMod q) ^ (p - 1) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb_lt : b < p := Finset.mem_range.mp hb
          have hb_le : b ≤ p - 1 := Nat.le_pred_of_lt hb_lt
          rw [zero_add, ← pow_add, Nat.add_sub_of_le hb_le]
        _ = (p : ZMod q) * (y : ZMod q) ^ (p - 1) := by simp
    rw [hsingle] at hzero_shell
    have hp0 : (p : ZMod q) ≠ 0 :=
      (neZero_primeCast_of_charPrime hpq).out
    exact (mul_ne_zero hp0 (pow_ne_zero (p - 1) hy)) hzero_shell
  have htprim : IsPrimitiveRoot t p :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime ht_pow ht_ne_one)
  exact ⟨t, htprim, rfl⟩

private theorem shell_mod_two_case_zero_one
    {p : ℕ} (hp : 3 ≤ p) :
    GTailCyclotomicShell p ((0 : ZMod 2) - (1 : ZMod 2)) (1 : ZMod 2) = 1 := by
  rw [GTailCyclotomicShell, Finset.sum_eq_single 0]
  · norm_num
  · intro b hb hb0
    have htwo : (1 : ZMod 2) + 1 = 0 := by
      change ((2 : ℤ) : ZMod 2) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      norm_num
    have hzero : (0 : ZMod 2) - 1 + 1 = 0 := by ring
    rw [hzero, zero_pow hb0, zero_mul]
  · intro hnot
    exfalso
    apply hnot
    exact Finset.mem_range.mpr (by omega)

private theorem shell_mod_two_case_one_zero
    {p : ℕ} (hp : 3 ≤ p) :
    GTailCyclotomicShell p ((1 : ZMod 2) - (0 : ZMod 2)) (0 : ZMod 2) = 1 := by
  rw [GTailCyclotomicShell, Finset.sum_eq_single (p - 1)]
  · norm_num
  · intro b hb hne
    have hlt : b < p := Finset.mem_range.mp hb
    have hle : b ≤ p - 1 := Nat.le_pred_of_lt hlt
    have hlt' : b < p - 1 := Nat.lt_of_le_of_ne hle hne
    have hne' : p - 1 - b ≠ 0 := (Nat.sub_ne_zero_iff_lt).2 hlt'
    norm_num [hne']
  · intro hnot
    exfalso
    apply hnot
    exact Finset.mem_range.mpr (by omega)

private theorem shell_mod_two_case_one_one
    {p : ℕ} (hpodd : Odd p) :
    GTailCyclotomicShell p ((1 : ZMod 2) - (1 : ZMod 2)) (1 : ZMod 2) = 1 := by
  simp only [GTailCyclotomicShell, sub_self, zero_add, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rcases hpodd with ⟨k, hk⟩
  rw [hk]
  push_cast
  have htwo : (2 : ZMod 2) = 0 := by
    change ((2 : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  rw [htwo, zero_mul, zero_add]

private theorem shell_mod_two_ne_zero_of_coprime
    {p z y : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcop : Nat.Coprime z y) :
    GTailCyclotomicShell p
        ((z : ZMod 2) - (y : ZMod 2)) (y : ZMod 2) ≠ 0 := by
  have hp3 : 3 ≤ p := by
    have hpp := (Fact.out : Nat.Prime p).two_le
    omega
  have hzcases : (z : ZMod 2) = 0 ∨ (z : ZMod 2) = 1 := by
    have hv := ZMod.val_lt (z : ZMod 2)
    have hv' : (z : ZMod 2).val = 0 ∨ (z : ZMod 2).val = 1 := by omega
    rcases hv' with hv' | hv'
    · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
    · exact Or.inr ((ZMod.val_eq_one (by norm_num) _).mp hv')
  have hycases : (y : ZMod 2) = 0 ∨ (y : ZMod 2) = 1 := by
    have hv := ZMod.val_lt (y : ZMod 2)
    have hv' : (y : ZMod 2).val = 0 ∨ (y : ZMod 2).val = 1 := by omega
    rcases hv' with hv' | hv'
    · exact Or.inl ((ZMod.val_eq_zero _).mp hv')
    · exact Or.inr ((ZMod.val_eq_one (by norm_num) _).mp hv')
  intro hshell
  rcases hzcases with hz | hz <;> rcases hycases with hy | hy
  · have hqz : 2 ∣ z := (ZMod.natCast_eq_zero_iff z 2).mp hz
    have hqy : 2 ∣ y := (ZMod.natCast_eq_zero_iff y 2).mp hy
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) hqz hqy) hcop
  · rw [hz, hy] at hshell
    rw [shell_mod_two_case_zero_one hp3] at hshell
    norm_num at hshell
  · rw [hz, hy] at hshell
    rw [shell_mod_two_case_one_zero hp3] at hshell
    norm_num at hshell
  · rw [hz, hy] at hshell
    have hpodd : Odd p := by
      rcases Nat.even_or_odd p with hpe | hpodd
      · exfalso
        apply hp2
        have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero (Nat.even_iff.mp hpe)
        have heq : 2 = p :=
          ((Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd).resolve_left
            (by norm_num)
        exact heq.symm
      · exact hpodd
    rw [shell_mod_two_case_one_one hpodd] at hshell
    norm_num at hshell

/-! ## Odd common-prime support -/

/-- For an odd prime `q` different from the exponent prime, the two retained
TraceOne coordinates cannot have a common `q`-divisor. -/
theorem not_common_coordinate_prime_of_odd_ne
    {L : Type*} [Field L] [Algebra ℚ L]
    {p q z y : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hq2 : q ≠ 2) (hpq : q ≠ p)
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (hcop : Nat.Coprime z y)
    (hA : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ)
    (hS : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ) :
    False := by
  have hshell := shell_cast_eq_zero_of_coordinate_dvd P hA hS
  obtain ⟨t, htprim, rfl⟩ :=
    shell_zero_implies_primitive_root_ratio hq2 hpq hshell hcop
  let U : ZMod q := MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
      (qrFactorPoly (p := p) ((z : ZMod q) / (y : ZMod q)))
  let V : ZMod q := MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
      (qnrFactorPoly (p := p) ((z : ZMod q) / (y : ZMod q)))
  have hRzero :
      MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
          (Rpoly (p := p) ((z : ZMod q) / (y : ZMod q))) = 0 := by
    have hmap := packet_RZ_map_eq_Rpoly_of_primitive_root
      (P := P) hpq ((z : ZMod q) / (y : ZMod q)) htprim
    have hA0 : ((MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ : ℤ) : ZMod q) = 0 :=
      (CharP.intCast_eq_zero_iff (ZMod q) q _).2 hA
    have hS0 : ((MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ : ℤ) : ZMod q) = 0 :=
      (CharP.intCast_eq_zero_iff (ZMod q) q _).2 hS
    have hR0 :
        ((MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.RZ : ℤ) : ZMod q) = 0 := by
      have hhalf := congrArg
        (MvPolynomial.eval ![(z : ℤ), (y : ℤ)]) P.half_relation
      have hcast := congrArg (Int.castRingHom (ZMod q)) hhalf
      simpa [map_add, map_mul, hA0, hS0] using hcast
    calc
      MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
          (Rpoly (p := p) ((z : ZMod q) / (y : ZMod q))) =
          MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
            (MvPolynomial.map (Int.castRingHom (ZMod q)) P.RZ) := by
        rw [hmap]
      _ = ((MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.RZ : ℤ) : ZMod q) := by
        rw [MvPolynomial.eval_map]
        exact eval_intCast_to_zmod P.RZ
      _ = 0 := hR0
  have hUV : U + V = 0 := by
    simpa [Rpoly, U, V] using hRzero
  have hU : U = 0 := by
    have hone : (1 : ZMod p) ∈ qrFinset p := by
      simp [qrFinset, nonzeroResidues, IsSquare.one]
    change MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
        (qrFactorPoly (p := p) ((z : ZMod q) / (y : ZMod q))) = 0
    rw [eval_qrFactorPoly]
    apply (Finset.prod_eq_zero_iff).2
    refine ⟨1, hone, ?_⟩
    have hY : (y : ZMod q) ≠ 0 := shell_zero_implies_y_ne_zero hshell hcop
    simp only [rootFactor, ZMod.val_one, pow_one]
    exact sub_eq_zero.mpr (div_mul_cancel₀ _ hY).symm
  have hV : V = 0 := by
    rw [hU, zero_add] at hUV
    exact hUV
  obtain ⟨b, hb, hbfactor⟩ := by
    have hV_eval :
        MvPolynomial.eval ![(z : ZMod q), (y : ZMod q)]
          (qnrFactorPoly (p := p) ((z : ZMod q) / (y : ZMod q))) = 0 := by
      simpa [V] using hV
    rw [eval_qnrFactorPoly] at hV_eval
    exact (Finset.prod_eq_zero_iff).mp hV_eval
  have hY : (y : ZMod q) ≠ 0 := shell_zero_implies_y_ne_zero hshell hcop
  have hpow :
      ((z : ZMod q) / (y : ZMod q)) ^ b.val =
        ((z : ZMod q) / (y : ZMod q)) := by
    have hz_b : (z : ZMod q) =
        ((z : ZMod q) / (y : ZMod q)) ^ b.val * (y : ZMod q) := by
      exact sub_eq_zero.mp (by simpa [rootFactor] using hbfactor)
    apply mul_right_cancel₀ hY
    calc
      ((z : ZMod q) / (y : ZMod q)) ^ b.val * (y : ZMod q) =
          (z : ZMod q) := hz_b.symm
      _ = ((z : ZMod q) / (y : ZMod q)) * (y : ZMod q) :=
        (div_mul_cancel₀ _ hY).symm
  have hbval : b.val = 1 := by
    apply htprim.pow_inj b.val_lt (Fact.out : Nat.Prime p).one_lt
    simpa [pow_one] using hpow
  have hb_one : b = 1 := (ZMod.val_eq_one (Fact.out : Nat.Prime p).one_lt b).mp hbval
  exact (Finset.mem_filter.mp hb).2 (by simp [hb_one])

/-- Characteristic two cannot divide both retained coordinates when the
exponent prime is odd. -/
theorem not_common_coordinate_prime_two
    {L : Type*} [Field L] [Algebra ℚ L]
    {p z y : ℕ} [Fact p.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2)
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (hcop : Nat.Coprime z y)
    (hA : (2 : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ)
    (hS : (2 : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ) :
    False := by
  have hshell := shell_cast_eq_zero_of_coordinate_dvd
    (q := 2) P hA hS
  exact (shell_mod_two_ne_zero_of_coprime hp2 hcop) hshell

/-- Under the odd-exponent hypothesis, every common coordinate prime is the
exponent prime itself. -/
theorem common_coordinate_prime_eq_exponent
    {L : Type*} [Field L] [Algebra ℚ L]
    {p q z y : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    (hp2 : p ≠ 2)
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (hcop : Nat.Coprime z y)
    (hA : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ)
    (hS : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ) :
    q = p := by
  by_cases hqp : q = p
  · exact hqp
  by_cases hq2 : q = 2
  · exact False.elim (not_common_coordinate_prime_two hp2 P hcop
      (by simpa [hq2] using hA) (by simpa [hq2] using hS))
  exact False.elim (not_common_coordinate_prime_of_odd_ne
    hq2 hqp P hcop hA hS)

/-- A common coordinate prime is either the exponent prime or the separately
handled characteristic-two prime. -/
theorem common_coordinate_prime_eq_exponent_or_two
    {L : Type*} [Field L] [Algebra ℚ L]
    {p q z y : ℕ} [Fact p.Prime] [Fact q.Prime]
    [IsCyclotomicExtension {p} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ p}
    (P : PrimeTraceOneCoordinatePacket L p ζ hζ)
    (hcop : Nat.Coprime z y)
    (hA : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.AZ)
    (hS : (q : ℤ) ∣
      MvPolynomial.eval ![(z : ℤ), (y : ℤ)] P.SZ) :
    q = p ∨ q = 2 := by
  by_cases hqp : q = p
  · exact Or.inl hqp
  by_cases hq2 : q = 2
  · exact Or.inr hq2
  exact False.elim (not_common_coordinate_prime_of_odd_ne
    hq2 hqp P hcop hA hS)

end

end DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
