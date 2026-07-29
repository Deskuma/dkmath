import DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic
open DkMath.FLT.Seven

example {z y q : ℕ} (hq : Nat.Prime q)
    (hA : (q : ℤ) ∣ cyclotomicSevenFst (z : ℤ) (y : ℤ))
    (hB : (q : ℤ) ∣ cyclotomicSevenSnd (z : ℤ) (y : ℤ)) :
    q ∣ z ∧ q ∣ y :=
  prime_dvd_both_cyclotomicSeven_coordinates hq hA hB

example {z y : ℕ} (hcop : Nat.Coprime z y) :
    IsCoprime (cyclotomicSevenFst (z : ℤ) (y : ℤ))
      (cyclotomicSevenSnd (z : ℤ) (y : ℤ)) :=
  cyclotomicSeven_coordinates_isCoprime hcop

example (w : TraceOneInt (-2)) :
    w - conj w = (w.snd : TraceOneInt (-2)) * sevenAxis :=
  sub_conj_eq_snd_mul_sevenAxis w

example (w : TraceOneInt (-2)) :
    sevenAxis * w - tau (-2) * (w - conj w) =
      (w.fst : TraceOneInt (-2)) * sevenAxis :=
  sevenAxis_mul_sub_tau_mul_sub_conj w

example {w d : TraceOneInt (-2)} (hcoords : IsCoprime w.fst w.snd)
    (hdw : d ∣ w) (hdc : d ∣ conj w) : d ∣ sevenAxis :=
  common_divisor_dvd_sevenAxis_of_coordinate_coprime hcoords hdw hdc

example : Irreducible (sevenAxis : TraceOneInt (-2)) := irreducible_sevenAxis

example : Prime (sevenAxis : TraceOneInt (-2)) := prime_sevenAxis

example {d r : TraceOneInt (-2)} (hdAxis : d ∣ sevenAxis)
    (hdr : d ∣ r) (hterminal : ¬ sevenAxis ∣ r) : IsUnit d :=
  isUnit_of_dvd_sevenAxis_of_dvd_terminal hdAxis hdr hterminal

#print axioms prime_dvd_both_cyclotomicSeven_coordinates
#print axioms cyclotomicSeven_coordinates_isCoprime
#print axioms sub_conj_eq_snd_mul_sevenAxis
#print axioms sevenAxis_mul_sub_tau_mul_sub_conj
#print axioms common_divisor_dvd_sevenAxis_of_coordinate_coprime
#print axioms common_divisor_cyclotomic_conj_dvd_sevenAxis
#print axioms irreducible_sevenAxis
#print axioms prime_sevenAxis
#print axioms isUnit_of_dvd_sevenAxis_of_dvd_terminal
