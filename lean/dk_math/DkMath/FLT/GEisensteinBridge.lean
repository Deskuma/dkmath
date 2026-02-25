/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PetalDetect
import DkMath.FLT.CounterexamplePattern
import DkMath.NumberTheory.ZsigmondyCyclotomic
import DkMath.CosmicFormula.CosmicFormulaBinom

set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.FLT.PetalDetect
open DkMath.NumberTheory.GcdNext
open DkMath.CosmicFormulaBinom

/-- Eisenstein ノルム形（係数表示 x + yω の標準形）: x^2 - xy + y^2 -/
def eisensteinNormNat (x y : ℕ) : ℕ := x ^ 2 - x * y + y ^ 2

/-- S0 = a^2 + ab + b^2 は、平行移動した Eisenstein ノルム形に一致する。 -/
lemma S0_eq_eisensteinNorm_shift (a b : ℕ) :
    S0_nat a b = eisensteinNormNat (a + b) b := by
  unfold S0_nat eisensteinNormNat
  calc
    a ^ 2 + a * b + b ^ 2
        = (a + b) * a + b ^ 2 := by ring
    _ = (a + b) * ((a + b) - b) + b ^ 2 := by rw [Nat.add_sub_cancel]
    _ = ((a + b) * (a + b) - (a + b) * b) + b ^ 2 := by
      rw [Nat.mul_sub_left_distrib]
    _ = (a + b) ^ 2 - (a + b) * b + b ^ 2 := by
      simp [pow_two, Nat.add_comm]

/-- d = 3 の G 多項式は、(a-b,b) 代入で S0 に落ちる。 -/
lemma GN3_sub_eq_S0 (a b : ℕ) (hab : b ≤ a) :
    GN 3 (a - b) b = S0_nat a b := by
  set x : ℕ := a - b
  have hx : x + b = a := by
    unfold x
    exact Nat.sub_add_cancel hab
  rw [GN_three_explicit (a - b) b]
  change x ^ 2 + 3 * x * b + 3 * b ^ 2 = S0_nat a b
  unfold S0_nat
  rw [← hx]
  ring

/-- d = 3 の G 多項式は、(a-b,b) 代入で Eisenstein ノルム形に落ちる。 -/
lemma GN3_sub_eq_eisensteinNorm_shift (a b : ℕ) (hab : b ≤ a) :
    GN 3 (a - b) b = eisensteinNormNat (a + b) b := by
  rw [GN3_sub_eq_S0 a b hab, S0_eq_eisensteinNorm_shift]

/--
GEisenstein 層で供給する下降法コア。
将来はこの構造体に追加データ（縮小写像・単調減少証明など）を積む。
-/
structure GEisensteinDescentFrame (c b : ℕ) where
  State : Type
  measure : State → ℕ
  step : (s : State) → measure s > 0 → State
  step_decreases : ∀ (s : State) (hs : measure s > 0), measure (step s hs) < measure s

/--
下降法枠の最小実装（空状態）。
現在のブリッジ層では、この枠を保持して API を先行固定する。
-/
def emptyGEisensteinDescentFrame (c b : ℕ) : GEisensteinDescentFrame c b where
  State := PEmpty
  measure := by
    intro s
    cases s
  step := by
    intro s hs
    cases s
  step_decreases := by
    intro s hs
    cases s

/--
非空状態を持つトイ下降フレーム。
`State = ℕ`, `measure = id`, `step = pred`。
-/
def toyNatGEisensteinDescentFrame (c b : ℕ) : GEisensteinDescentFrame c b where
  State := ℕ
  measure := id
  step := by
    intro s hs
    exact Nat.pred s
  step_decreases := by
    intro s hs
    simpa using Nat.pred_lt (Nat.ne_of_gt hs)

/--
GEisenstein 下降で扱う反例候補の最小状態。
将来はここに `(a,b,c)` 側の情報や整合条件を追加する。
-/
structure GEisensteinCandidate where
  q : ℕ

/-- 反例候補の測度（暫定: `q`）。 -/
def GEisensteinCandidate.measure (s : GEisensteinCandidate) : ℕ := s.q

/-- 反例候補の 1-step 縮小（暫定: `q := pred q`）。 -/
def GEisensteinCandidate.step (s : GEisensteinCandidate)
    (_hs : GEisensteinCandidate.measure s > 0) : GEisensteinCandidate :=
  { q := Nat.pred s.q }

lemma GEisensteinCandidate.step_decreases (s : GEisensteinCandidate)
    (hs : GEisensteinCandidate.measure s > 0) :
    GEisensteinCandidate.measure (GEisensteinCandidate.step s hs) <
      GEisensteinCandidate.measure s := by
  simpa [GEisensteinCandidate.measure, GEisensteinCandidate.step]
    using Nat.pred_lt (Nat.ne_of_gt hs)

/--
反例候補レコードを使う暫定下降フレーム。
`toyNat` より本実装に近い状態表現。
-/
def candidateGEisensteinDescentFrame (c b : ℕ) : GEisensteinDescentFrame c b where
  State := GEisensteinCandidate
  measure := GEisensteinCandidate.measure
  step := GEisensteinCandidate.step
  step_decreases := GEisensteinCandidate.step_decreases

/--
GEisenstein 層で供給する下降法コア。
`classifyImpossible` に加えて、将来拡張用の descent frame を持つ。
-/
structure GEisensteinDescentCore (c b : ℕ) where
  classifyImpossible :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q →
      classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible
  frame : GEisensteinDescentFrame c b

/--
GEisenstein 下降法コアから `descent` インターフェースへ戻す。
-/
lemma descentClassifyImpossibleOnPrimitive_of_GEisensteinCore {c b : ℕ}
    (hCore : GEisensteinDescentCore c b) :
    DescentClassifyImpossibleOnPrimitive c b := by
  exact hCore.classifyImpossible

/--
既存の `DescentClassifyImpossibleOnPrimitive` から GEisenstein コアを作る。
-/
def GEisensteinDescentCore_of_descentClassify_withFrame {c b : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b)
    (hFrame : GEisensteinDescentFrame c b) :
    GEisensteinDescentCore c b := by
  exact ⟨hDescent, hFrame⟩

/--
既存の `DescentClassifyImpossibleOnPrimitive` から GEisenstein コアを作る。
フレームは暫定的に `empty` を採用する。
-/
def GEisensteinDescentCore_of_descentClassify {c b : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b) :
    GEisensteinDescentCore c b := by
  exact GEisensteinDescentCore_of_descentClassify_withFrame
    hDescent (emptyGEisensteinDescentFrame c b)

/--
GEisenstein 層から下降法インターフェースへ接続する橋。
現段階では `NoSq + harmonic envelope` 供給版を再公開する。
-/
lemma descentClassifyImpossibleOnPrimitive_via_GEisenstein {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hNoSq : NoSqOnS0 c b) :
    DescentClassifyImpossibleOnPrimitive c b := by
  exact descentClassifyImpossibleOnPrimitive_of_GEisensteinCore
    (hCore := GEisensteinDescentCore_of_descentClassify
      (descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_NoSq
        hbc hInfra hHarm hNoExcAll hNoSq))

/-- 旧層Bの平方耐性主張が一般には成り立たないことの具体反例。 -/
theorem exists_counterexample_S0_square_resistance :
    ∃ a b q : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ Nat.Prime q ∧
      q ∣ S0_nat a b ∧ ¬ q ∣ a + b ∧ q ^ 2 ∣ S0_nat a b := by
  refine ⟨18, 1, 7, ?_⟩
  decide

end DkMath.FLT
