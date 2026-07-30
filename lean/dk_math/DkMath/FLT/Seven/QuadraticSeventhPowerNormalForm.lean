/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.QuadraticConjugateCoprime

#print "file: DkMath.FLT.Seven.QuadraticSeventhPowerNormalForm"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

structure SevenQuadraticSeventhPowerPacket (x y z : ℕ) : Type where
  residual : SevenQuadraticResidualPacket x y z
  root : TraceOneInt (-2)
  residual_eq : residual.residualCore = root ^ 7
  coordinate_eq :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = sevenAxis * root ^ 7

theorem nonempty_sevenQuadraticSeventhPowerPacket_of_residual
    {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    Nonempty (SevenQuadraticSeventhPowerPacket x y z) := by
  rcases q.exists_residualCore_eq_seventh_power with ⟨root, hroot⟩
  exact ⟨{
    residual := q
    root := root
    residual_eq := hroot
    coordinate_eq := by rw [q.coordinate_eq, hroot] }⟩

noncomputable def sevenQuadraticSeventhPowerPacket_of_residual
    {x y z : ℕ} (q : SevenQuadraticResidualPacket x y z) :
    SevenQuadraticSeventhPowerPacket x y z :=
  Classical.choice (nonempty_sevenQuadraticSeventhPowerPacket_of_residual q)

noncomputable def sevenQuadraticSeventhPowerPacket_of_counterexample
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : 7 ∣ z - y) : SevenQuadraticSeventhPowerPacket x y z :=
  sevenQuadraticSeventhPowerPacket_of_residual
    (sevenQuadraticResidualPacket_of_counterexample hPack hBranch)

inductive QuadraticCounterexampleRoute (x y z : ℕ) : Type
  | away (seven_not_dvd_gap : ¬ 7 ∣ z - y)
      (root : TraceOneInt (-2))
      (coordinate_eq :
        cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7)
  | ramified (packet : SevenQuadraticSeventhPowerPacket x y z)

theorem quadraticCounterexampleRoute_of_pack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nonempty (QuadraticCounterexampleRoute x y z) := by
  by_cases hBranch : 7 ∣ z - y
  · exact ⟨.ramified
      (sevenQuadraticSeventhPowerPacket_of_counterexample hPack hBranch)⟩
  · rcases exists_cyclotomicSeven_eq_seventh_power_of_away hPack hBranch with
      ⟨root, hroot⟩
    exact ⟨.away hBranch root hroot⟩

end DkMath.FLT.Seven
