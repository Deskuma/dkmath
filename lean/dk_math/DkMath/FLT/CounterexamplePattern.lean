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

/--
phase-04 で使う「非例外・調和側」判定。
-/
def HarmonicNonExceptionalSide (x : CounterexampleInput) : Prop :=
  phaseGate x ∧ ¬ exceptionalPhaseGate x

lemma harmonicNonExceptionalSide_of_envelope {x : CounterexampleInput}
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExc : ¬ exceptionalPhaseGate x) :
    HarmonicNonExceptionalSide x := by
  exact ⟨phaseGate_of_harmonicEnvelope hInfra hHarm, hNoExc⟩

lemma harmonicNonExceptionalSide_all_of_envelope
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x) :
    ∀ x : CounterexampleInput, HarmonicNonExceptionalSide x := by
  intro x
  exact harmonicNonExceptionalSide_of_envelope hInfra hHarm (hNoExcAll x)

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

lemma classifyLift_impossible_of_harmonicNonExceptional {x : CounterexampleInput}
    (hside : HarmonicNonExceptionalSide x)
    (hprim : primitivePrimeGate x)
    (hnosq : noSquareGate x) :
    classifyLift x = LiftStatus.impossible := by
  exact classifyLift_impossible_of_gates hside.2 hprim hnosq

/--
`PrimitiveOnS0` から `primitivePrimeGate` への持ち上げ。
-/
lemma primitivePrimeGate_of_PrimitiveOnS0 {c b q : ℕ}
    (hbc : b < c)
    (hprim : PrimitiveOnS0 c b q) :
    primitivePrimeGate ({ c := c, b := b, q := q } : CounterexampleInput) := by
  rcases hprim with ⟨hq, hqS0, hq_ndvd⟩
  have hfact : c ^ 3 - b ^ 3 = (c - b) * S0_nat c b :=
    cube_sub_eq_mul_sub_S0 hbc
  have hq_diff : q ∣ c ^ 3 - b ^ 3 := by
    rw [hfact]
    exact dvd_mul_of_dvd_right hqS0 (c - b)
  exact ⟨hq, hq_diff, hq_ndvd⟩

/--
`PhaseLift.two_gap_xy_dvd_cube_bridge` を Counterexample 入力側へ持ち上げる補助補題。
-/
lemma two_gap_xy_dvd_cube_bridge_for_input {c b : ℕ}
    (hbc : b < c) :
    (c - b) * b ∣ c ^ 3 - (c - b) ^ 3 - b ^ 3 := by
  exact two_gap_xy_dvd_cube_bridge hbc.le

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
`PrimitiveOnS0` 上での `classifyLift = impossible` family から、
`q` 全域の `NonLiftableS0` family を生成する。
-/
lemma nonLiftableS0_family_of_classifyLift_impossible {c b : ℕ}
    (hbc : b < c)
    (hClass :
      ∀ {q : ℕ}, PrimitiveOnS0 c b q →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  intro q hprim
  exact nonLiftableS0_of_classifyLift_impossible hbc (hClass hprim) hprim

/--
非例外・調和側の入力で、`PrimitiveOnS0` と `NonLiftableS0` から
`classifyLift = impossible` を得るテンプレート。
-/
lemma classifyLift_impossible_of_harmonicNonExceptional_nonLiftable {c b q : ℕ}
    (hbc : b < c)
    (hside : HarmonicNonExceptionalSide ({ c := c, b := b, q := q } : CounterexampleInput))
    (hprim : PrimitiveOnS0 c b q)
    (hNonLift : NonLiftableS0 c b q) :
    classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible := by
  let x : CounterexampleInput := { c := c, b := b, q := q }
  have hprimGate : primitivePrimeGate x := by
    simpa [x] using primitivePrimeGate_of_PrimitiveOnS0 hbc hprim
  have hnosq : noSquareGate x := by
    exact hNonLift hprim
  exact classifyLift_impossible_of_harmonicNonExceptional
    (by simpa [x] using hside) hprimGate (by simpa [x] using hnosq)

/--
`q` 全域のテンプレート版。
-/
lemma classifyLift_impossible_family_of_harmonicNonExceptional_nonLiftable {c b : ℕ}
    (hbc : b < c)
    (hsideAll :
      ∀ q : ℕ, HarmonicNonExceptionalSide ({ c := c, b := b, q := q } : CounterexampleInput))
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q) :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q →
      classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible := by
  intro q hprim
  exact classifyLift_impossible_of_harmonicNonExceptional_nonLiftable
    hbc (hsideAll q) hprim (hNonLiftAll q)

/--
`NoSqOnS0` と harmonic envelope 仮定から、
primitive 因子に対する `classifyLift = impossible` family を作る。
-/
lemma classifyLift_impossible_family_of_harmonicEnvelope_NoSq {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hNoSq : NoSqOnS0 c b) :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q →
      classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible := by
  have hsideAll :
      ∀ q : ℕ, HarmonicNonExceptionalSide ({ c := c, b := b, q := q } : CounterexampleInput) := by
    intro q
    exact harmonicNonExceptionalSide_of_envelope hInfra hHarm (hNoExcAll { c := c, b := b, q := q })
  have hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_all_of_NoSqOnS0 hNoSq
  intro q hprim
  exact classifyLift_impossible_family_of_harmonicNonExceptional_nonLiftable
    hbc hsideAll hNonLiftAll hprim

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

/--
phase-04 接続補題（non-exceptional ∧ harmonic 側のテンプレート利用版）。
-/
lemma allNonLiftableOnS0_of_harmonicNonExceptional_nonLiftable {c b : ℕ}
    (hbc : b < c)
    (hsideAll :
      ∀ q : ℕ, HarmonicNonExceptionalSide ({ c := c, b := b, q := q } : CounterexampleInput))
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    AllNonLiftableOnS0 c b := by
  have hClass :
      ∀ {q : ℕ}, PrimitiveOnS0 c b q →
        classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible :=
    classifyLift_impossible_family_of_harmonicNonExceptional_nonLiftable hbc hsideAll hNonLiftAll
  exact allNonLiftableOnS0_of_harmonicClassifier
    hbc hasPhaseUnitInfrastructure
    (by
      -- `hsideAll` の 0 番目成分から位相 witness を回収する
      have h0 : HarmonicNonExceptionalSide ({ c := c, b := b, q := 0 } : CounterexampleInput) :=
        hsideAll 0
      exact h0.1.2)
    hSuppEx3 hClass hc_nz hb_nz hsep

/--
phase-04 接続補題（envelope 入力版）:
`hsideAll` を外部で組み立てずに
`hInfra + hHarm + hNoExcAll + hNonLiftAll` から `AllNonLiftableOnS0` を作る。
-/
lemma allNonLiftableOnS0_of_harmonicEnvelope_nonLiftable {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hSuppEx3 : S0PrimeSupportExceptThree c b)
    (hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q)
    (hc_nz : c % 3 ≠ 0)
    (hb_nz : b % 3 ≠ 0)
    (hsep : c % 3 ≠ b % 3) :
    AllNonLiftableOnS0 c b := by
  have hsideAll :
      ∀ q : ℕ, HarmonicNonExceptionalSide ({ c := c, b := b, q := q } : CounterexampleInput) := by
    intro q
    exact harmonicNonExceptionalSide_of_envelope hInfra hHarm (hNoExcAll { c := c, b := b, q := q })
  exact allNonLiftableOnS0_of_harmonicNonExceptional_nonLiftable
    hbc hsideAll hSuppEx3 hNonLiftAll hc_nz hb_nz hsep

end DkMath.FLT
