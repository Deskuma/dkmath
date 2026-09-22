/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Prime.PrimeCyclotomicTraceOne

#print "file: DkMathTest.FLT.Prime.PrimeCyclotomicTraceOne"

namespace DkMathTest.FLT.Prime

open DkMath.CFBRC
open DkMath.CosmicFormula
open DkMath.FLT.Prime
open DkMath.NumberTheory.CyclotomicQRTraceOneBridge
open DkMath.NumberTheory.TraceOneQuadratic

noncomputable section

private abbrev cycloField (p : ℕ) := CyclotomicField p ℚ

private instance cycloField_isCyclotomicExtension (p : ℕ) [Fact p.Prime] :
    IsCyclotomicExtension {p} ℚ (cycloField p) := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let : NeZero (p : ℚ) := ⟨by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension p ℚ

private def cycloZeta (p : ℕ) [Fact p.Prime] : cycloField p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta p ℚ (cycloField p)

private theorem cycloZeta_isPrimitiveRoot (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (cycloZeta p) p := by
  let : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  exact IsCyclotomicExtension.zeta_spec p ℚ (cycloField p)

private instance factPrime3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance factPrime5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ## Unconditional Nat/Int shell bridge -/

example :
    ((GTail 3 1 0 0 : ℕ) : ℤ) =
      GTailCyclotomicShell 3 (0 : ℤ) (0 : ℤ) :=
  DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell

example (u : ℕ) :
    ((GTail 5 1 0 u : ℕ) : ℤ) =
      GTailCyclotomicShell 5 (0 : ℤ) (u : ℤ) :=
  DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell

example (g : ℕ) :
    ((GTail 7 1 g 0 : ℕ) : ℤ) =
      GTailCyclotomicShell 7 (g : ℤ) (0 : ℤ) :=
  DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell

/-! ## Canonical p = 3, 5, 7 coordinate calibration -/

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 3) 3
        (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3),
      norm (P.coord ((2 + 1 : ℕ) : ℤ) (1 : ℤ)) =
        (Ideal.absNorm
          (cyclotomicLinearFactorIdeal (cycloZeta_isPrimitiveRoot 3) 2 1) : ℤ) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 3) (p := 3) (by norm_num)
    (cycloZeta 3) (cycloZeta_isPrimitiveRoot 3)
  exact ⟨P, TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm P 2 1⟩

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 5) 5
        (cycloZeta 5) (cycloZeta_isPrimitiveRoot 5),
      Int.natAbs (norm (P.coord ((0 + 0 : ℕ) : ℤ) (0 : ℤ))) =
        Ideal.absNorm
          (cyclotomicLinearFactorIdeal (cycloZeta_isPrimitiveRoot 5) 0 0) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 5) (p := 5) (by norm_num)
    (cycloZeta 5) (cycloZeta_isPrimitiveRoot 5)
  exact ⟨P, TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P 0 0⟩

example :
    ∃ P : PrimeTraceOneCoordinatePacket (cycloField 7) 7
        (cycloZeta 7) (cycloZeta_isPrimitiveRoot 7),
      padicValNat 7
          (Int.natAbs (norm (P.coord ((3 + 2 : ℕ) : ℤ) (2 : ℤ)))) =
        padicValNat 7
          (Ideal.absNorm
            (cyclotomicLinearFactorIdeal (cycloZeta_isPrimitiveRoot 7) 3 2)) := by
  obtain ⟨P⟩ := exists_prime_traceOne_coordinate_packet
    (L := cycloField 7) (p := 7) (by norm_num)
    (cycloZeta 7) (cycloZeta_isPrimitiveRoot 7)
  exact ⟨P, TraceOneScalar.padicValNat_coord_natAbs_norm_eq_ideal_absNorm P 3 2⟩

/-! ## Generic FLT packet and ramified split projections -/

section Packet

variable {L : Type*} [Field L] [NumberField L] [CharZero L]
variable {p g u x : ℕ} [Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ L]
variable {ζ : L} {hζ : IsPrimitiveRoot ζ p}
variable (P0 : PrimeAdicFactorPacket p g u x)
variable (P : PrimeTraceOneCoordinatePacket L p ζ hζ)

example :
    norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)) =
      (Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) : ℤ) :=
  PrimeAdicFactorPacket.coord_norm_eq_cyclotomicIdeal_absNorm P0 P

example :
    Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) =
      Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) :=
  TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm P g u

example (q : ℕ) :
    padicValNat q (Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)))) =
      padicValNat q (Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u)) :=
  TraceOneScalar.padicValNat_coord_natAbs_norm_eq_ideal_absNorm P g u

example (q : ℕ) :
    q ∣ Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) ↔
      q ∣ Ideal.absNorm (cyclotomicLinearFactorIdeal hζ g u) :=
  TraceOneScalar.dvd_coord_natAbs_norm_iff_dvd_ideal_absNorm P g u

example :
    g * Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) = x ^ p :=
  PrimeAdicFactorPacket.gap_mul_coord_natAbs_norm_eq_pow P0 P

variable (S : PrimeAdicPowerSplit p g u x)

example :
    Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ))) = p * S.b ^ p :=
  PrimeAdicPowerSplit.coord_natAbs_norm_eq_prime_mul_pow S P

example :
    padicValNat p (Int.natAbs (norm (P.coord ((g + u : ℕ) : ℤ) (u : ℤ)))) = 1 :=
  PrimeAdicPowerSplit.padicValNat_coord_natAbs_norm_eq_one S P

end Packet

/-! ## Public theorem axiom audit -/

#print axioms DkMath.CosmicFormula.natCast_GTail_one_eq_GTailCyclotomicShell
#print axioms DkMath.FLT.Prime.TraceOneScalar.coord_norm_eq_cyclotomicIdeal_absNorm
#print axioms DkMath.FLT.Prime.TraceOneScalar.coord_natAbs_norm_eq_cyclotomicIdeal_absNorm
#print axioms DkMath.FLT.Prime.TraceOneScalar.padicValNat_coord_natAbs_norm_eq_ideal_absNorm
#print axioms DkMath.FLT.Prime.TraceOneScalar.dvd_coord_natAbs_norm_iff_dvd_ideal_absNorm
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.coord_norm_eq_cyclotomicIdeal_absNorm
#print axioms DkMath.FLT.Prime.PrimeAdicFactorPacket.gap_mul_coord_natAbs_norm_eq_pow
#print axioms DkMath.FLT.Prime.PrimeAdicPowerSplit.coord_natAbs_norm_eq_prime_mul_pow
#print axioms DkMath.FLT.Prime.PrimeAdicPowerSplit.padicValNat_coord_natAbs_norm_eq_one

end

end DkMathTest.FLT.Prime
