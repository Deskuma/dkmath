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

namespace GEisensteinDescentFrame

/--
下降ステップの有界反復。
`measure = 0` に到達したらその場で停止する。
-/
def descend {c b : ℕ} (F : GEisensteinDescentFrame c b) :
    F.State → ℕ → F.State
  | s, 0 => s
  | s, n + 1 =>
      if hs : F.measure s > 0 then
        descend F (F.step s hs) n
      else
        s

/--
任意回数反復しても、測度は初期値を超えない。
-/
lemma measure_descend_le {c b : ℕ} (F : GEisensteinDescentFrame c b) :
    ∀ (s : F.State) (n : ℕ), F.measure (descend F s n) ≤ F.measure s := by
  intro s n
  induction n generalizing s with
  | zero =>
      simp [descend]
  | succ n ih =>
      by_cases hs : F.measure s > 0
      · have hstep : F.measure (F.step s hs) < F.measure s := F.step_decreases s hs
        have hrec : F.measure (descend F (F.step s hs) n) ≤ F.measure (F.step s hs) :=
          ih (F.step s hs)
        have hdesc :
            F.measure (descend F s (n + 1)) = F.measure (descend F (F.step s hs) n) := by
          simp [descend, hs]
        rw [hdesc]
        exact Nat.le_trans hrec (Nat.le_of_lt hstep)
      · simp [descend, hs]

/--
1-step 反復で `measure > 0` なら厳密減少。
-/
lemma measure_descend_one_lt_of_pos {c b : ℕ}
    (F : GEisensteinDescentFrame c b)
    (s : F.State) (hs : F.measure s > 0) :
    F.measure (descend F s 1) < F.measure s := by
  simpa [descend, hs] using F.step_decreases s hs

/--
`step` が測度を `pred` にするフレームでは、`measure s` 回の反復で測度 0 に到達する。
-/
lemma measure_descend_eq_zero_of_step_pred {c b : ℕ}
    (F : GEisensteinDescentFrame c b)
    (hpred : ∀ (s : F.State) (hs : F.measure s > 0),
      F.measure (F.step s hs) = Nat.pred (F.measure s)) :
    ∀ s : F.State, F.measure (descend F s (F.measure s)) = 0 := by
  have hmain :
      ∀ n : ℕ, ∀ s : F.State, F.measure s = n → F.measure (descend F s n) = 0 := by
    intro n
    induction n with
    | zero =>
        intro s hs
        simpa [descend] using hs
    | succ n ih =>
        intro s hsEq
        have hsPos : F.measure s > 0 := by omega
        have hdesc :
            F.measure (descend F s (n + 1)) =
              F.measure (descend F (F.step s hsPos) n) := by
          simp [descend, hsPos]
        rw [hdesc]
        have hstepEq : F.measure (F.step s hsPos) = n := by
          calc
            F.measure (F.step s hsPos) = Nat.pred (F.measure s) := hpred s hsPos
            _ = n := by simp [hsEq]
        exact ih (F.step s hsPos) hstepEq
  intro s
  exact hmain (F.measure s) s rfl

end GEisensteinDescentFrame

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
GEisenstein 下降で扱う反例候補状態。
`prim?` は `PrimitiveOnS0 c b q` 証拠の保持スロット（保持できない段で `none` を許容）。
-/
structure GEisensteinCandidate (c b : ℕ) where
  q : ℕ
  primEvidence : Prop
  hPrimEvidence : primEvidence

/-- `PrimitiveOnS0` 証拠つき候補のコンストラクタ。 -/
def GEisensteinCandidate.ofPrimitive {c b q : ℕ}
    (hPrim : PrimitiveOnS0 c b q) : GEisensteinCandidate c b :=
  { q := q, primEvidence := PrimitiveOnS0 c b q, hPrimEvidence := hPrim }

/-- 反例候補の測度（暫定: `q`）。 -/
def GEisensteinCandidate.measure {c b : ℕ} (s : GEisensteinCandidate c b) : ℕ := s.q

/--
反例候補の 1-step 縮小（暫定: `q := pred q`）。
この段階では primitive 証拠の保存は要求せず、`prim? := none` とする。
-/
def GEisensteinCandidate.step {c b : ℕ} (s : GEisensteinCandidate c b)
    (_hs : GEisensteinCandidate.measure s > 0) : GEisensteinCandidate c b :=
  { q := Nat.pred s.q, primEvidence := True, hPrimEvidence := trivial }

lemma GEisensteinCandidate.step_decreases {c b : ℕ} (s : GEisensteinCandidate c b)
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
  State := GEisensteinCandidate c b
  measure := GEisensteinCandidate.measure
  step := GEisensteinCandidate.step
  step_decreases := GEisensteinCandidate.step_decreases

/--
`PrimitiveOnS0` 証拠を保持し続ける候補状態。
`q` は固定し、下降は `fuel` を減らして表現する。
-/
structure GEisensteinPrimitiveCandidate (c b : ℕ) where
  q : ℕ
  hPrim : PrimitiveOnS0 c b q
  fuel : ℕ

/-- 証拠保持型候補の測度（`fuel`）。 -/
def GEisensteinPrimitiveCandidate.measure {c b : ℕ}
    (s : GEisensteinPrimitiveCandidate c b) : ℕ := s.fuel

/--
証拠保持型候補の 1-step 縮小（`fuel := pred fuel`）。
`q` と `hPrim` は保存する。
-/
def GEisensteinPrimitiveCandidate.step {c b : ℕ}
    (s : GEisensteinPrimitiveCandidate c b)
    (_hs : GEisensteinPrimitiveCandidate.measure s > 0) :
    GEisensteinPrimitiveCandidate c b :=
  { q := s.q, hPrim := s.hPrim, fuel := Nat.pred s.fuel }

lemma GEisensteinPrimitiveCandidate.step_decreases {c b : ℕ}
    (s : GEisensteinPrimitiveCandidate c b)
    (hs : GEisensteinPrimitiveCandidate.measure s > 0) :
    GEisensteinPrimitiveCandidate.measure (GEisensteinPrimitiveCandidate.step s hs) <
      GEisensteinPrimitiveCandidate.measure s := by
  simpa [GEisensteinPrimitiveCandidate.measure, GEisensteinPrimitiveCandidate.step]
    using Nat.pred_lt (Nat.ne_of_gt hs)

/--
`PrimitiveOnS0` 証拠保持型の下降フレーム。
-/
def primitiveCandidateGEisensteinDescentFrame (c b : ℕ) : GEisensteinDescentFrame c b where
  State := GEisensteinPrimitiveCandidate c b
  measure := GEisensteinPrimitiveCandidate.measure
  step := GEisensteinPrimitiveCandidate.step
  step_decreases := GEisensteinPrimitiveCandidate.step_decreases

/--
`PrimitiveOnS0` 証拠保持に加えて、候補サイズ `size` を明示する状態。
`size ≤ q` を不変量として保持する。
-/
structure GEisensteinPrimitiveSizedCandidate (c b : ℕ) where
  q : ℕ
  hPrim : PrimitiveOnS0 c b q
  size : ℕ
  hsize : size ≤ q

/-- 証拠つき候補から初期サイズを与えて構成する。 -/
def GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize {c b q : ℕ}
    (hPrim : PrimitiveOnS0 c b q) (size : ℕ) (hsize : size ≤ q) :
    GEisensteinPrimitiveSizedCandidate c b :=
  { q := q, hPrim := hPrim, size := size, hsize := hsize }

/-- sized 候補の測度は `size`。 -/
def GEisensteinPrimitiveSizedCandidate.measure {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b) : ℕ := s.size

/--
sized 候補の 1-step 縮小（`size := pred size`）。
`q`, `hPrim`, `size ≤ q` は保持。
-/
def GEisensteinPrimitiveSizedCandidate.step {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b)
    (_hs : GEisensteinPrimitiveSizedCandidate.measure s > 0) :
    GEisensteinPrimitiveSizedCandidate c b :=
  { q := s.q
    hPrim := s.hPrim
    size := Nat.pred s.size
    hsize := by
      exact Nat.le_trans (Nat.pred_le _) s.hsize }

lemma GEisensteinPrimitiveSizedCandidate.step_decreases {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b)
    (hs : GEisensteinPrimitiveSizedCandidate.measure s > 0) :
    GEisensteinPrimitiveSizedCandidate.measure (GEisensteinPrimitiveSizedCandidate.step s hs) <
      GEisensteinPrimitiveSizedCandidate.measure s := by
  simpa [GEisensteinPrimitiveSizedCandidate.measure, GEisensteinPrimitiveSizedCandidate.step]
    using Nat.pred_lt (Nat.ne_of_gt hs)

/--
候補サイズ `size` を測度に使う証拠保持型の下降フレーム。
-/
def primitiveSizedCandidateGEisensteinDescentFrame (c b : ℕ) : GEisensteinDescentFrame c b where
  State := GEisensteinPrimitiveSizedCandidate c b
  measure := GEisensteinPrimitiveSizedCandidate.measure
  step := GEisensteinPrimitiveSizedCandidate.step
  step_decreases := GEisensteinPrimitiveSizedCandidate.step_decreases

/-- `toyNat` フレームは `measure` 回の反復で測度 0 に到達する。 -/
lemma toyNat_measure_descend_eq_zero (c b : ℕ) :
    ∀ n : ℕ,
      (toyNatGEisensteinDescentFrame c b).measure
        (GEisensteinDescentFrame.descend (toyNatGEisensteinDescentFrame c b) n
          ((toyNatGEisensteinDescentFrame c b).measure n)) = 0 := by
  intro n
  exact GEisensteinDescentFrame.measure_descend_eq_zero_of_step_pred
    (F := toyNatGEisensteinDescentFrame c b)
    (hpred := by
      intro s hs
      simp [toyNatGEisensteinDescentFrame])
    n

/-- `primitiveSized` フレームは `measure` 回の反復で測度 0 に到達する。 -/
lemma primitiveSized_measure_descend_eq_zero (c b : ℕ) :
    ∀ s : GEisensteinPrimitiveSizedCandidate c b,
      (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        (GEisensteinDescentFrame.descend (primitiveSizedCandidateGEisensteinDescentFrame c b) s
          ((primitiveSizedCandidateGEisensteinDescentFrame c b).measure s)) = 0 := by
  intro s
  exact GEisensteinDescentFrame.measure_descend_eq_zero_of_step_pred
    (F := primitiveSizedCandidateGEisensteinDescentFrame c b)
    (hpred := by
      intro t ht
      simp [primitiveSizedCandidateGEisensteinDescentFrame,
        GEisensteinPrimitiveSizedCandidate.measure,
        GEisensteinPrimitiveSizedCandidate.step])
    s

/--
`PrimitiveOnS0` なら `S0_nat c b ≠ 0`。
（`S0=0` なら `c=b=0` となり `q ∣ c-b` に矛盾）
-/
lemma S0_nat_ne_zero_of_PrimitiveOnS0 {c b q : ℕ}
    (hPrim : PrimitiveOnS0 c b q) :
    S0_nat c b ≠ 0 := by
  intro hS0
  have hsum : (c ^ 2 + c * b) + b ^ 2 = 0 := by
    simpa [S0_nat, Nat.add_assoc] using hS0
  have hb2_eq0 : b ^ 2 = 0 := Nat.eq_zero_of_add_eq_zero_left hsum
  have hcb_eq0 : c ^ 2 + c * b = 0 := Nat.eq_zero_of_add_eq_zero_right hsum
  have hc2_eq0 : c ^ 2 = 0 := Nat.eq_zero_of_add_eq_zero_right hcb_eq0
  have hc0 : c = 0 := (Nat.pow_eq_zero.mp hc2_eq0).1
  have hb0 : b = 0 := (Nat.pow_eq_zero.mp hb2_eq0).1
  have hq_dvd_diff : q ∣ c - b := by simp [hc0, hb0]
  exact hPrim.2.2 hq_dvd_diff

/-- `PrimitiveOnS0` な `q` は `S0_nat c b` 以下。 -/
lemma q_le_S0_nat_of_PrimitiveOnS0 {c b q : ℕ}
    (hPrim : PrimitiveOnS0 c b q) :
    q ≤ S0_nat c b := by
  have hS0_pos : 0 < S0_nat c b :=
    Nat.pos_of_ne_zero (S0_nat_ne_zero_of_PrimitiveOnS0 hPrim)
  exact Nat.le_of_dvd hS0_pos hPrim.2.1

/--
`size ≤ q` 不変量つき候補の測度は、`S0_nat c b` でも上から抑えられる。
-/
lemma primitiveSizedCandidate_measure_le_S0 {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b) :
    GEisensteinPrimitiveSizedCandidate.measure s ≤ S0_nat c b := by
  have hq_le : s.q ≤ S0_nat c b := q_le_S0_nat_of_PrimitiveOnS0 s.hPrim
  exact Nat.le_trans s.hsize hq_le

/--
`step` 後も `size ≤ q` 不変量は保持される（構造体フィールド経由）。
-/
lemma GEisensteinPrimitiveSizedCandidate.hsize_step {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b)
    (hs : GEisensteinPrimitiveSizedCandidate.measure s > 0) :
    (GEisensteinPrimitiveSizedCandidate.step s hs).size ≤
      (GEisensteinPrimitiveSizedCandidate.step s hs).q := by
  simpa [GEisensteinPrimitiveSizedCandidate.step]
    using (GEisensteinPrimitiveSizedCandidate.step s hs).hsize

/--
`step` 後も測度上界 `measure ≤ S0_nat c b` は保持される。
-/
lemma primitiveSizedCandidate_measure_le_S0_step {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b)
    (hs : GEisensteinPrimitiveSizedCandidate.measure s > 0) :
    GEisensteinPrimitiveSizedCandidate.measure (GEisensteinPrimitiveSizedCandidate.step s hs) ≤
      S0_nat c b := by
  exact primitiveSizedCandidate_measure_le_S0 (GEisensteinPrimitiveSizedCandidate.step s hs)

/--
`step` は厳密減少なので、弱単調性 `measure(step) ≤ measure` も成り立つ。
-/
lemma primitiveSizedCandidate_measure_step_le {c b : ℕ}
    (s : GEisensteinPrimitiveSizedCandidate c b)
    (hs : GEisensteinPrimitiveSizedCandidate.measure s > 0) :
    GEisensteinPrimitiveSizedCandidate.measure (GEisensteinPrimitiveSizedCandidate.step s hs) ≤
      GEisensteinPrimitiveSizedCandidate.measure s := by
  exact Nat.le_of_lt (GEisensteinPrimitiveSizedCandidate.step_decreases s hs)

/--
GEisenstein 層で供給する下降法コア。
`classifyImpossible` に加えて、将来拡張用の descent frame を持つ。
-/
structure GEisensteinDescentCore (c b : ℕ) where
  classifyImpossible :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q →
      classifyLift ({ c := c, b := b, q := q } : CounterexampleInput) = LiftStatus.impossible
  frame : GEisensteinDescentFrame c b
  step_pred :
    ∀ (s : frame.State) (hs : frame.measure s > 0),
      frame.measure (frame.step s hs) = Nat.pred (frame.measure s)

/--
コアに載っている frame が `pred` 型の縮小を満たすとき、
任意状態は `measure` 回の反復で測度 0 に到達する。
-/
lemma GEisensteinDescentCore.measure_descend_eq_zero_of_step_pred {c b : ℕ}
    (hCore : GEisensteinDescentCore c b) :
    ∀ s : hCore.frame.State,
      hCore.frame.measure
        (GEisensteinDescentFrame.descend hCore.frame s (hCore.frame.measure s)) = 0 := by
  exact GEisensteinDescentFrame.measure_descend_eq_zero_of_step_pred hCore.frame hCore.step_pred

/--
停止到達の存在版（回数 `n` の存在）。
-/
lemma GEisensteinDescentCore.exists_descend_measure_eq_zero_of_step_pred {c b : ℕ}
    (hCore : GEisensteinDescentCore c b)
    (s : hCore.frame.State) :
    ∃ n : ℕ,
      hCore.frame.measure (GEisensteinDescentFrame.descend hCore.frame s n) = 0 := by
  refine ⟨hCore.frame.measure s, ?_⟩
  exact GEisensteinDescentCore.measure_descend_eq_zero_of_step_pred hCore s

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
    (hFrame : GEisensteinDescentFrame c b)
    (hFrameStepPred : ∀ (s : hFrame.State) (hs : hFrame.measure s > 0),
      hFrame.measure (hFrame.step s hs) = Nat.pred (hFrame.measure s)) :
    GEisensteinDescentCore c b := by
  exact ⟨hDescent, hFrame, hFrameStepPred⟩

/--
既存の `DescentClassifyImpossibleOnPrimitive` から GEisenstein コアを作る。
フレームは暫定的に `empty` を採用する。
-/
def GEisensteinDescentCore_of_descentClassify {c b : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b) :
    GEisensteinDescentCore c b := by
  exact GEisensteinDescentCore_of_descentClassify_withFrame
    hDescent (emptyGEisensteinDescentFrame c b)
    (by
      intro s hs
      cases s)

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
