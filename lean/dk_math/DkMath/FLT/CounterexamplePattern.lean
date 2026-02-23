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

lemma phaseGate_of_harmonicEnvelope {x : CounterexampleInput}
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u) :
    phaseGate x := by
  exact ⟨hInfra, hHarm⟩

lemma phaseGate_all_of_harmonicEnvelope
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u) :
    ∀ x : CounterexampleInput, phaseGate x := by
  intro x
  exact phaseGate_of_harmonicEnvelope (x := x) hInfra hHarm

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

/--
`PrimitiveOnS0` から `primitivePrimeGate` への持ち上げ。
-/
lemma primitivePrimeGate_of_PrimitiveOnS0 {c b q : ℕ}
    (hbc : b < c)
    (hprim : PrimitiveOnS0 c b q) :
    primitivePrimeGate ({ c := c, b := b, q := q } : CounterexampleInput) := by
  rcases hprim with ⟨hq, hqS0, hq_ndvd⟩
  have hdiff : c ^ 3 - b ^ 3 = (c - b) * (c ^ 2 + c * b + b ^ 2) := by
    have h_pow : b ^ 3 ≤ c ^ 3 := Nat.pow_le_pow_left hbc.le 3
    zify [hbc, h_pow]
    ring_nf
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b := by
    simpa [S0_nat] using hdiff
  have hq_diff : q ∣ c ^ 3 - b ^ 3 := by
    rw [hfact]
    exact dvd_mul_of_dvd_right hqS0 (c - b)
  exact ⟨hq, hq_diff, hq_ndvd⟩

/--
`classifyLift = impossible` が得られれば、対応する `q` は `NonLiftableS0` となる。
-/
lemma nonLiftableS0_of_classifyLift_impossible {c b q : ℕ}
    (hbc : b < c)
    (hclass :
      classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible) :
    NonLiftableS0 c b q := by
  intro hprim
  let x : CounterexampleInput := { c := c, b := b, q := q }
  have hprimGate : primitivePrimeGate x := by
    simpa [x] using primitivePrimeGate_of_PrimitiveOnS0 hbc hprim
  have hnosq : noSquareGate x :=
    noSquareGate_of_classifyLift_impossible hprimGate (by simpa [x] using hclass)
  simpa [x, noSquareGate] using hnosq

/--
phase-04 接続補題:
Harmonic witness と分類器の impossible 判定群から `AllNonLiftableOnS0` を作る。
-/
lemma allNonLiftableOnS0_of_harmonicClassifier {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hClass :
      ∀ {q : ℕ}, PrimitiveOnS0 c b q →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    AllNonLiftableOnS0 c b := by
  -- 位相入口は x 非依存なので、全入力に持ち上がる
  have _hphaseAll : ∀ x : CounterexampleInput, phaseGate x :=
    phaseGate_all_of_harmonicEnvelope hInfra hHarm
  have hNonLift : ∀ q : ℕ, NonLiftableS0 c b q := by
    intro q hprim
    exact nonLiftableS0_of_classifyLift_impossible hbc (hClass hprim) hprim
  exact AllNonLiftableOnS0_of_exceptThree_mod3_separated hSuppEx3 hNonLift hc_nz hb_nz hsep

end DkMath.FLT
