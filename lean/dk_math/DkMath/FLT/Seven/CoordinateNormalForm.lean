/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SeventhPowerCoordinates

#print "file: DkMath.FLT.Seven.CoordinateNormalForm"

namespace DkMath.FLT.Seven

open DkMath.NumberTheory.TraceOneQuadratic

structure AwayCoordinateNormalForm (x y z : ℕ) : Type where
  counterexample : CounterexamplePack x y z
  seven_not_dvd_gap : ¬ 7 ∣ z - y
  root : TraceOneInt (-2)
  coordinate_eq :
    cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7
  fst_eq :
    cyclotomicSevenFst (z : ℤ) (y : ℤ) =
      seventhPowerFst root.fst root.snd
  snd_eq :
    cyclotomicSevenSnd (z : ℤ) (y : ℤ) =
      seventhPowerSnd root.fst root.snd

def awayCoordinateNormalForm_of_route {x y z : ℕ}
    (hPack : CounterexamplePack x y z) (hgap : ¬ 7 ∣ z - y)
    (root : TraceOneInt (-2))
    (hcoordinate : cyclotomicSevenToTraceOne (z : ℤ) (y : ℤ) = root ^ 7) :
    AwayCoordinateNormalForm x y z where
  counterexample := hPack
  seven_not_dvd_gap := hgap
  root := root
  coordinate_eq := hcoordinate
  fst_eq := by
    have h := congrArg TraceOneInt.fst hcoordinate
    calc
      _ = (root ^ 7).fst := h
      _ = _ := by
        rcases root with ⟨u, v⟩
        exact traceOne_pow_seven_fst u v
  snd_eq := by
    have h := congrArg TraceOneInt.snd hcoordinate
    calc
      _ = (root ^ 7).snd := h
      _ = _ := by
        rcases root with ⟨u, v⟩
        exact traceOne_pow_seven_snd u v

structure RamifiedCoordinateNormalForm (x y z : ℕ) : Type where
  seventhPower : SevenQuadraticSeventhPowerPacket x y z
  fst_eq :
    cyclotomicSevenFst (z : ℤ) (y : ℤ) =
      ramifiedSeventhFst seventhPower.root.fst seventhPower.root.snd
  snd_eq :
    cyclotomicSevenSnd (z : ℤ) (y : ℤ) =
      ramifiedSeventhSnd seventhPower.root.fst seventhPower.root.snd

def ramifiedCoordinateNormalForm_of_packet {x y z : ℕ}
    (packet : SevenQuadraticSeventhPowerPacket x y z) :
    RamifiedCoordinateNormalForm x y z where
  seventhPower := packet
  fst_eq := by
    have h := congrArg TraceOneInt.fst packet.coordinate_eq
    calc
      _ = (sevenAxis * packet.root ^ 7).fst := h
      _ = _ := by
        rcases packet.root with ⟨u, v⟩
        exact congrArg TraceOneInt.fst (sevenAxis_mul_pow_seven_eq u v)
  snd_eq := by
    have h := congrArg TraceOneInt.snd packet.coordinate_eq
    calc
      _ = (sevenAxis * packet.root ^ 7).snd := h
      _ = _ := by
        rcases packet.root with ⟨u, v⟩
        exact congrArg TraceOneInt.snd (sevenAxis_mul_pow_seven_eq u v)

inductive CoordinateCounterexampleRoute (x y z : ℕ) : Type
  | away (packet : AwayCoordinateNormalForm x y z)
  | ramified (packet : RamifiedCoordinateNormalForm x y z)

theorem coordinateCounterexampleRoute_of_pack {x y z : ℕ}
    (hPack : CounterexamplePack x y z) :
    Nonempty (CoordinateCounterexampleRoute x y z) := by
  rcases quadraticCounterexampleRoute_of_pack hPack with ⟨route⟩
  cases route with
  | away hgap root hcoordinate =>
      exact ⟨.away (awayCoordinateNormalForm_of_route hPack hgap root hcoordinate)⟩
  | ramified packet =>
      exact ⟨.ramified (ramifiedCoordinateNormalForm_of_packet packet)⟩

end DkMath.FLT.Seven
