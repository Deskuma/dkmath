import DkMath

#print "file: RootSmokeNOTE006Legendre"

open DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Legendre.FreyC4CentralSeat

example (n : ℕ) : (rationalCurve n).c₄ = (centralSeat n : ℚ) := rationalCurve_c4 n

example {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    (q : ℤ) ∣ (curve n).c₄ ∧ ¬ (q : ℤ) ∣ (curve n).Δ ∧ (q = 3 ∨ q % 3 = 1) :=
  prime_bridge hq hd

example {q n : ℕ} (h : q ∈ squareOffsetPrimeSupport n (n + 1)) : q ≤ n :=
  (prime_bridge_of_mem_support h).1

example : ((curve 4).map (Int.castRingHom (ZMod 7))).IsElliptic :=
  reduction_isElliptic (by decide) (by decide)

example {p : ℕ} (S : DkMath.FLT.Frey.Source p) : S.rationalCurve.IsElliptic :=
  S.rationalCurve_isElliptic
example : FermatLastTheoremFor 11 := DkMath.FLT.Kummer.fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := DkMath.FLT.Kummer.fermatLastTheoremFor_thirteen

#print axioms rationalCurve_c4
#print axioms reduction_isElliptic
#print axioms prime_mod_three
#print axioms prime_bridge_of_mem_support
