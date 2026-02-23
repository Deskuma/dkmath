/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PhaseLift
import DkMath.FLT.PetalCoreUnit

namespace DkMath.FLT

open DkMath.FLT.PetalDetect

/-- 反例パターン抽出器の入力。 -/
structure CounterexampleInput where
  c : ℕ
  b : ℕ
  q : ℕ

/--
原始素因子ゲート:
`q` が差の立方を割り、境界差を割らない。
-/
def primitivePrimeGate (x : CounterexampleInput) : Prop :=
  Nat.Prime x.q ∧ x.q ∣ x.c ^ 3 - x.b ^ 3 ∧ ¬ x.q ∣ x.c - x.b

/--
square 回避ゲート:
`q^2` が `S0_nat c b` を割らない。
-/
def noSquareGate (x : CounterexampleInput) : Prop :=
  ¬ x.q ^ 2 ∣ S0_nat x.c x.b

/-- OctagonCore 由来の位相ゲート（現段階では存在証明のみ使用）。 -/
def phaseGate (_x : CounterexampleInput) : Prop :=
  HasPhaseUnitInfrastructure
    ∧ ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u

lemma phaseGate_default (x : CounterexampleInput) : phaseGate x := by
  refine ⟨hasPhaseUnitInfrastructure, ?_⟩
  refine ⟨ofNP DkMath.zero, ?_⟩
  exact ⟨harmonicPoint_ofNP DkMath.zero, notExceptional_ofNP_zero⟩

/--
例外相ゲート（phase-03 skeleton）:
例外相の調和点 witness が存在する場合。
-/
def exceptionalPhaseGate (_x : CounterexampleInput) : Prop :=
  ∃ u : PetalCoreUnit, HarmonicPoint u ∧ isExceptionalPhase u

/-- `lift` 判定の現在値。 -/
inductive LiftStatus where
  | possible
  | impossible
  | undecided
  deriving DecidableEq, Repr

/--
反例抽出器の最小判定器。

- `primitivePrimeGate` が閉じない場合は `undecided`
- 閉じていて `noSquareGate` が成り立つなら `impossible`
- 閉じていて `noSquareGate` が崩れるなら `possible`
-/
noncomputable def classifyLift (x : CounterexampleInput) : LiftStatus := by
  classical
  exact if hexc : exceptionalPhaseGate x then
    LiftStatus.undecided
  else if hprim : primitivePrimeGate x then
    if hnosq : noSquareGate x then LiftStatus.impossible else LiftStatus.possible
  else
    LiftStatus.undecided

lemma classifyLift_impossible_of_gates {x : CounterexampleInput}
    (hexc : ¬ exceptionalPhaseGate x)
    (hprim : primitivePrimeGate x)
    (hnosq : noSquareGate x) :
    classifyLift x = LiftStatus.impossible := by
  classical
  simp [classifyLift, hexc, hprim, hnosq]

lemma classifyLift_possible_of_primitive_and_sq {x : CounterexampleInput}
    (hexc : ¬ exceptionalPhaseGate x)
    (hprim : primitivePrimeGate x)
    (hsq : x.q ^ 2 ∣ S0_nat x.c x.b) :
    classifyLift x = LiftStatus.possible := by
  classical
  have hnosq : ¬ noSquareGate x := by
    intro h
    exact h hsq
  have hnosq' : (if h : noSquareGate x then LiftStatus.impossible else LiftStatus.possible)
      = LiftStatus.possible := by
    simp [hnosq]
  simp [classifyLift, hexc, hprim, hnosq']

lemma classifyLift_undecided_of_not_primitive {x : CounterexampleInput}
    (hexc : ¬ exceptionalPhaseGate x)
    (hprim : ¬ primitivePrimeGate x) :
    classifyLift x = LiftStatus.undecided := by
  classical
  simp [classifyLift, hexc, hprim]

lemma classifyLift_undecided_of_exceptional {x : CounterexampleInput}
    (hexc : exceptionalPhaseGate x) :
    classifyLift x = LiftStatus.undecided := by
  classical
  simp [classifyLift, hexc]

/--
`primitivePrimeGate` が成り立つ入力で `classifyLift = impossible` なら、
`noSquareGate` が成り立つ。
-/
lemma noSquareGate_of_classifyLift_impossible {x : CounterexampleInput}
    (hprim : primitivePrimeGate x)
    (hclass : classifyLift x = LiftStatus.impossible) :
    noSquareGate x := by
  classical
  have hexc : ¬ exceptionalPhaseGate x := by
    intro hexc
    have hundec : classifyLift x = LiftStatus.undecided := by
      simp [classifyLift, hexc]
    have : LiftStatus.undecided = LiftStatus.impossible := hundec.symm.trans hclass
    cases this
  by_cases hnosq : noSquareGate x
  · exact hnosq
  · have hpossible : classifyLift x = LiftStatus.possible := by
      simp [classifyLift, hexc, hprim, hnosq]
    have : LiftStatus.possible = LiftStatus.impossible := hpossible.symm.trans hclass
    cases this

end DkMath.FLT
