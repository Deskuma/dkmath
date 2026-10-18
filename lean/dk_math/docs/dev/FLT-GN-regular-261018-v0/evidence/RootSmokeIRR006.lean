import DkMath

#print "file: RootSmokeIRR006"

open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open scoped NumberField nonZeroDivisors
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

example {R : Type*} [CommRing R] [IsDedekindDomain R] (w : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) w = w := classGroup_map_refl w

example {m : ℕ} (E : RegularDescent.State IrregularPrime37.phase37 (m + 1))
    (A B : ℤ) (hx : E.x = A) (hy : E.y = B) (a : (ZMod 37)ˣ) (i : Fin 37) :
    ClassGroup.mulEquiv (IrregularPrime37.sigma37 a)
        ((IrregularPrime37.observe E).phases.obstruction i) =
      (IrregularPrime37.observe E).phases.obstruction (RamifiedPhasePacket.phaseMul a i) :=
  (IrregularPrime37.observe_galois E A B hx hy a i).2

example : FermatLastTheoremFor 11 := fermatLastTheoremFor_eleven
example : FermatLastTheoremFor 13 := fermatLastTheoremFor_thirteen

#print axioms IdealPowerObstruction.root_transport_of_unit
#print axioms RamifiedPhasePacket.quotient_galois
#print axioms CyclotomicPhaseGalois.obstruction_int
#print axioms IrregularPrime37.observe_galois
