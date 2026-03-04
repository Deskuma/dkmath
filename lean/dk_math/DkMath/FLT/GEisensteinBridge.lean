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

/--
`primitiveSized` フレームの `step_pred` 版。
-/
lemma primitiveSizedCandidate_frame_step_pred (c b : ℕ) :
    ∀ (s : (primitiveSizedCandidateGEisensteinDescentFrame c b).State)
      (hs : (primitiveSizedCandidateGEisensteinDescentFrame c b).measure s > 0),
      (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        ((primitiveSizedCandidateGEisensteinDescentFrame c b).step s hs)
        = Nat.pred ((primitiveSizedCandidateGEisensteinDescentFrame c b).measure s) := by
  intro s hs
  simp [primitiveSizedCandidateGEisensteinDescentFrame,
    GEisensteinPrimitiveSizedCandidate.measure,
    GEisensteinPrimitiveSizedCandidate.step]

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
`PrimitiveOnS0` な素数で平方持ち上げが起きる witness。
phase-11 ではこの witness 集合を下降法で空にする。
-/
def PrimitiveSquareWitness (c b : ℕ) : Prop :=
  ∃ q : ℕ, PrimitiveOnS0 c b q ∧ q ^ 2 ∣ S0_nat c b

/--
`PrimitiveOnS0` な平方持ち上げ witness を、より小さい `q` へ送る strict descent 条件。
-/
def PrimitiveSquareDescentStep (c b : ℕ) : Prop :=
  ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
    ∃ q' : ℕ, PrimitiveOnS0 c b q' ∧ q' ^ 2 ∣ S0_nat c b ∧ q' < q

/--
phase-11 の実体降下写像を束ねる入力構造。
`step` は平方持ち上げ witness をより小さい witness に送る。
-/
structure PrimitiveSquareDescentEngine (c b : ℕ) where
  step :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      {q' : ℕ // PrimitiveOnS0 c b q' ∧ q' ^ 2 ∣ S0_nat c b ∧ q' < q}

/--
`q` 固定の 1-step 縮小証明をまとめたレコード。
具体実装ではこのレコードを与える補題を `q` ごとに構成していく。
-/
structure PrimitiveSquareReduction (c b q : ℕ) where
  q' : ℕ
  hPrim : PrimitiveOnS0 c b q'
  hSq : q' ^ 2 ∣ S0_nat c b
  hlt : q' < q

/--
`PrimitiveSquareReduction` から engine の `step` 形式へ変換する。
-/
def PrimitiveSquareReduction.toStep {c b q : ℕ}
    (r : PrimitiveSquareReduction c b q) :
    {q' : ℕ // PrimitiveOnS0 c b q' ∧ q' ^ 2 ∣ S0_nat c b ∧ q' < q} :=
  ⟨r.q', r.hPrim, r.hSq, r.hlt⟩

/--
局所縮小関数 `reduce` から engine を組み立てるコンストラクタ。
-/
def primitiveSquareDescentEngine_of_reduce {c b : ℕ}
    (reduce : ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q) :
    PrimitiveSquareDescentEngine c b where
  step := by
    intro q hPrim hSq
    exact (PrimitiveSquareReduction.toStep (reduce hPrim hSq))

/--
`PrimitiveSquareDescentStep` から、局所縮小関数 `reduce` を直接取り出す。
phase-11 の最小実装として、まずこの形で `reduce` API を実運用できる。
-/
noncomputable def primitiveSquareReduce_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q := by
  classical
  intro q hPrim hSq
  let w : ∃ q' : ℕ, PrimitiveOnS0 c b q' ∧ q' ^ 2 ∣ S0_nat c b ∧ q' < q :=
    hStep hPrim hSq
  refine ⟨Classical.choose w, ?_, ?_, ?_⟩
  · exact (Classical.choose_spec w).1
  · exact (Classical.choose_spec w).2.1
  · exact (Classical.choose_spec w).2.2

/--
`PrimitiveSquareDescentStep` から engine を組み立てる最小コンストラクタ。
-/
noncomputable def primitiveSquareDescentEngine_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    PrimitiveSquareDescentEngine c b := by
  exact primitiveSquareDescentEngine_of_reduce (primitiveSquareReduce_of_step hStep)

/--
`reduce` 候補（数論系）を表す別名。
-/
abbrev NumberTheoryReduce (c b : ℕ) :=
  ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
    PrimitiveSquareReduction c b q

/--
`reduce` 候補（トロミノ/幾何系）を表す別名。
現時点では型は同じで、証明供給源のみを分離する。
-/
abbrev TrominoReduce (c b : ℕ) :=
  ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
    PrimitiveSquareReduction c b q

/--
数論系 `step` から `NumberTheoryReduce` を生成する。
-/
noncomputable def numberTheoryReduce_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    NumberTheoryReduce c b :=
  primitiveSquareReduce_of_step hStep

/--
数論系 `reduce` の最小実装（phase-11 first concrete）。
現段階では `step` を通じて `reduce` を供給する。
-/
noncomputable def numberTheoryReduce_basic {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    NumberTheoryReduce c b :=
  numberTheoryReduce_of_step hStep

/--
数論系 `step` から `PrimitiveSquareDescentEngine` を生成する。
-/
noncomputable def numberTheoryEngine_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    PrimitiveSquareDescentEngine c b :=
  primitiveSquareDescentEngine_of_step hStep

/--
数論系 `reduce` から `PrimitiveSquareDescentEngine` を生成する。
-/
def numberTheoryEngine_of_reduce {c b : ℕ}
    (reduceNT : NumberTheoryReduce c b) :
    PrimitiveSquareDescentEngine c b :=
  primitiveSquareDescentEngine_of_reduce reduceNT

/--
`numberTheoryReduce_basic` から engine を得る補助定義。
-/
noncomputable def numberTheoryEngine_basic {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    PrimitiveSquareDescentEngine c b :=
  numberTheoryEngine_of_reduce (numberTheoryReduce_basic hStep)

/--
phase-11 本実装に向けた数論側の状態。
`c,b,q` を状態として持ち、`PrimitiveOnS0` と平方持ち上げ witness を同時に保持する。
-/
structure NumberTheoryDescentState where
  c : ℕ
  b : ℕ
  q : ℕ
  hbc : b < c
  hcop : Nat.Coprime c b
  hPrim : PrimitiveOnS0 c b q
  hSq : q ^ 2 ∣ S0_nat c b

namespace NumberTheoryDescentState

/-- 数論降下で使う測度（第2版）: `q`。 -/
def measure (s : NumberTheoryDescentState) : ℕ := s.q

/--
`PrimitiveSquareReduction` から次状態を組み立てる。
`c,b` とその付随証明は保持し、`q` を `q'` に更新する。
-/
def nextOfReduction (s : NumberTheoryDescentState)
    (red : PrimitiveSquareReduction s.c s.b s.q) :
    NumberTheoryDescentState :=
  { c := s.c
    b := s.b
    q := red.q'
    hbc := s.hbc
    hcop := s.hcop
    hPrim := red.hPrim
    hSq := red.hSq }

/--
数論降下の中核条件（構成の正当性）。
`t` がある `PrimitiveSquareReduction` から生成された状態であることを要求する。
-/
def IsStepCore (s t : NumberTheoryDescentState) : Prop :=
  ∃ red : PrimitiveSquareReduction s.c s.b s.q, t = nextOfReduction s red

/--
次状態 `t` が `s` からの数論降下ステップであることを表す関係。
本実装ではこの関係に具体的な構成条件を追加していく。
-/
def IsStep (s t : NumberTheoryDescentState) : Prop :=
  IsStepCore s t ∧ measure t < measure s

/-- phase-11 の最初の固定点: 降下ステップ存在性の型。 -/
def StepExists : Prop :=
  ∀ s : NumberTheoryDescentState, ∃ t : NumberTheoryDescentState, IsStep s t

/-- `IsStep` から `Core 条件` を取り出す。 -/
lemma core_of_isStep {s t : NumberTheoryDescentState}
    (h : IsStep s t) :
    IsStepCore s t := h.1

/-- 降下ステップは測度を厳密減少させる。 -/
lemma measure_lt_of_isStep {s t : NumberTheoryDescentState}
    (h : IsStep s t) :
    measure t < measure s := h.2

/-- `PrimitiveSquareReduction` から `IsStep` を作る。 -/
lemma isStep_of_reduction (s : NumberTheoryDescentState)
    (red : PrimitiveSquareReduction s.c s.b s.q) :
    IsStep s (nextOfReduction s red) := by
  refine ⟨⟨red, rfl⟩, ?_⟩
  simpa [measure, nextOfReduction] using red.hlt

/-- 数論降下の次状態関数。 -/
abbrev StepFunction : Type := NumberTheoryDescentState → NumberTheoryDescentState

/-- 次状態関数が測度を厳密減少させる条件。 -/
def StepDecreases (next : StepFunction) : Prop :=
  ∀ s : NumberTheoryDescentState, IsStep s (next s)

/--
`next` が測度を厳密減少させるなら、`StepExists` は直ちに得られる。
-/
lemma stepExists_of_stepFunction (next : StepFunction)
    (hdec : StepDecreases next) :
    StepExists := by
  intro s
  exact ⟨next s, hdec s⟩

/--
phase-11 本実装向けの数論ステップ仕様。
`next` とその厳密減少証明をひとまとめにする。
-/
structure StepSpec where
  next : StepFunction
  decreases : StepDecreases next

/-- `StepSpec` から `StepExists` を得る。 -/
lemma stepExists_of_spec (spec : StepSpec) : StepExists := by
  exact stepExists_of_stepFunction spec.next spec.decreases

/-- 全状態で reduction を与えるローカル降下入力。 -/
abbrev LocalReduce : Type :=
  ∀ s : NumberTheoryDescentState, PrimitiveSquareReduction s.c s.b s.q

/-- `LocalReduce` から次状態関数を作る。 -/
def stepFunction_of_localReduce (reduce : LocalReduce) : StepFunction :=
  fun s => nextOfReduction s (reduce s)

/-- `LocalReduce` は `StepDecreases` を満たす。 -/
lemma stepDecreases_of_localReduce (reduce : LocalReduce) :
    StepDecreases (stepFunction_of_localReduce reduce) := by
  intro s
  exact isStep_of_reduction s (reduce s)

/-- `LocalReduce` から `StepSpec` を作る。 -/
def stepSpec_of_localReduce (reduce : LocalReduce) : StepSpec where
  next := stepFunction_of_localReduce reduce
  decreases := stepDecreases_of_localReduce reduce

/-- `LocalReduce` から `StepExists` を得る。 -/
lemma stepExists_of_localReduce (reduce : LocalReduce) : StepExists := by
  exact stepExists_of_spec (stepSpec_of_localReduce reduce)

/--
`StepExists` から `StepSpec` を（選択公理で）構成する。
本実装の局所構成が揃うまでの間、仕様オブジェクト経由で接続できる。
-/
noncomputable def spec_of_stepExists (hex : StepExists) : StepSpec where
  next := fun s => Classical.choose (hex s)
  decreases := by
    intro s
    exact (Classical.choose_spec (hex s))

/--
`StepExists` と `StepSpec` の同値（仕様化レイヤー）。
-/
lemma stepExists_iff_exists_stepSpec : StepExists ↔ Nonempty StepSpec := by
  constructor
  · intro hex
    exact ⟨spec_of_stepExists hex⟩
  · intro hs
    rcases hs with ⟨spec⟩
    exact stepExists_of_spec spec

/--
`StepExists` が成り立つと、任意状態は矛盾する。
（測度 `measure : ℕ` に関する強い帰納法）
-/
lemma false_of_state_of_stepExists (hex : StepExists)
    (s : NumberTheoryDescentState) :
    False := by
  have hmain : ∀ n : ℕ, ∀ s : NumberTheoryDescentState, measure s = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro s hs
        rcases hex s with ⟨t, ht⟩
        have ht' : measure t < n := by
          simpa [hs] using (measure_lt_of_isStep ht)
        exact ih (measure t) ht' t rfl
  exact hmain (measure s) s rfl

/-- `StepExists` が成り立つなら、状態は存在しない。 -/
lemma not_nonempty_of_stepExists (hex : StepExists) :
    ¬ Nonempty NumberTheoryDescentState := by
  intro hs
  rcases hs with ⟨s⟩
  exact false_of_state_of_stepExists hex s

end NumberTheoryDescentState

/-
固定 `(c,b)` 上での数論降下状態。
global 版より前提を狭くし、ローカルに降下仕様を扱う。
-/
namespace NumberTheoryDescentOn

structure State (c b : ℕ) where
  q : ℕ
  hbc : b < c
  hcop : Nat.Coprime c b
  hPrim : PrimitiveOnS0 c b q
  hSq : q ^ 2 ∣ S0_nat c b

/-- 局所降下の測度: `q`。 -/
def measure {c b : ℕ} (s : State c b) : ℕ := s.q

/--
`PrimitiveSquareReduction` から次状態を組み立てる（固定 `(c,b)` 版）。
-/
def nextOfReduction {c b : ℕ} (s : State c b)
    (red : PrimitiveSquareReduction c b s.q) :
    State c b :=
  { q := red.q'
    hbc := s.hbc
    hcop := s.hcop
    hPrim := red.hPrim
    hSq := red.hSq }

/--
局所降下ステップの中核条件（固定 `(c,b)` 版）。
`t` が `s` の `PrimitiveSquareReduction` から生成されることを要求する。
-/
def IsStepCore {c b : ℕ} (s t : State c b) : Prop :=
  ∃ red : PrimitiveSquareReduction c b s.q, t = nextOfReduction s red

/-- 局所降下ステップ（固定 `(c,b)` 版）。 -/
def IsStep {c b : ℕ} (s t : State c b) : Prop :=
  IsStepCore s t ∧ measure t < measure s

/-- 固定 `(c,b)` での降下ステップ存在性。 -/
def StepExists (c b : ℕ) : Prop :=
  ∀ s : State c b, ∃ t : State c b, IsStep s t

/-- `IsStep` から `Core` 条件を取り出す。 -/
lemma core_of_isStep {c b : ℕ} {s t : State c b}
    (h : IsStep s t) :
    IsStepCore s t := h.1

/-- `IsStep` から測度減少を取り出す。 -/
lemma measure_lt_of_isStep {c b : ℕ} {s t : State c b}
    (h : IsStep s t) :
    measure t < measure s := h.2

/-- `PrimitiveSquareReduction` から `IsStep` を作る（固定 `(c,b)` 版）。 -/
lemma isStep_of_reduction {c b : ℕ} (s : State c b)
    (red : PrimitiveSquareReduction c b s.q) :
    IsStep s (nextOfReduction s red) := by
  refine ⟨⟨red, rfl⟩, ?_⟩
  simpa [measure, nextOfReduction] using red.hlt

/-- 局所降下の次状態関数。 -/
abbrev StepFunction (c b : ℕ) : Type := State c b → State c b

/-- 次状態関数が測度を厳密減少させる条件。 -/
def StepDecreases {c b : ℕ} (next : StepFunction c b) : Prop :=
  ∀ s : State c b, IsStep s (next s)

/-- `next` が測度を厳密減少させるなら `StepExists`。 -/
lemma stepExists_of_stepFunction {c b : ℕ}
    (next : StepFunction c b)
    (hdec : StepDecreases next) :
    StepExists c b := by
  intro s
  exact ⟨next s, hdec s⟩

/-- 固定 `(c,b)` での `StepSpec`。 -/
structure StepSpec (c b : ℕ) where
  next : StepFunction c b
  decreases : StepDecreases next

/-- `StepSpec` から `StepExists`。 -/
lemma stepExists_of_spec {c b : ℕ} (spec : StepSpec c b) :
    StepExists c b := by
  exact stepExists_of_stepFunction spec.next spec.decreases

/--
`StepExists` が成り立つと、任意状態は矛盾する（固定 `(c,b)` 版）。
-/
lemma false_of_state_of_stepExists {c b : ℕ}
    (hex : StepExists c b)
    (s : State c b) :
    False := by
  have hmain : ∀ n : ℕ, ∀ s : State c b, measure s = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro s hs
        rcases hex s with ⟨t, ht⟩
        have ht' : measure t < n := by
          simpa [hs] using (measure_lt_of_isStep ht)
        exact ih (measure t) ht' t rfl
  exact hmain (measure s) s rfl

/-- `StepExists` が成り立つなら局所状態は存在しない。 -/
lemma not_nonempty_of_stepExists {c b : ℕ}
    (hex : StepExists c b) :
    ¬ Nonempty (State c b) := by
  intro hs
  rcases hs with ⟨s⟩
  exact false_of_state_of_stepExists hex s

/-- 固定 `(c,b)` 上のローカル `reduce` 入力。 -/
abbrev LocalReduce (c b : ℕ) :=
  ∀ s : State c b, PrimitiveSquareReduction c b s.q

/-- ローカル `reduce` から次状態関数を作る。 -/
def stepFunction_of_localReduce {c b : ℕ}
    (reduce : LocalReduce c b) : StepFunction c b :=
  fun s => nextOfReduction s (reduce s)

/-- ローカル `reduce` は測度厳密減少を与える。 -/
lemma stepDecreases_of_localReduce {c b : ℕ}
    (reduce : LocalReduce c b) :
    StepDecreases (stepFunction_of_localReduce reduce) := by
  intro s
  exact isStep_of_reduction s (reduce s)

/-- ローカル `reduce` から `StepExists`。 -/
lemma stepExists_of_localReduce {c b : ℕ}
    (reduce : LocalReduce c b) :
    StepExists c b := by
  exact stepExists_of_stepFunction
    (stepFunction_of_localReduce reduce)
    (stepDecreases_of_localReduce reduce)

/--
`IsStep s t` から、`s` を始点とする `PrimitiveSquareReduction` を再構成する。
`hlt` は `IsStep` の測度減少成分から復元する。
-/
noncomputable def reduction_of_isStep {c b : ℕ} {s t : State c b}
    (h : IsStep s t) :
    PrimitiveSquareReduction c b s.q := by
  let hcore : IsStepCore s t := h.1
  let red : PrimitiveSquareReduction c b s.q := Classical.choose hcore
  let hred : t = nextOfReduction s red := Classical.choose_spec hcore
  refine
    { q' := red.q'
      hPrim := red.hPrim
      hSq := red.hSq
      hlt := ?_ }
  have hlt_meas : measure t < measure s := h.2
  simpa [measure, nextOfReduction, hred] using hlt_meas

/--
`StepExists`（固定 `(c,b)`）から `LocalReduce` を（選択公理で）構成する。
-/
noncomputable def localReduce_of_stepExists {c b : ℕ}
    (hex : StepExists c b) :
    LocalReduce c b := by
  intro s
  let t : State c b := Classical.choose (hex s)
  let ht : IsStep s t := Classical.choose_spec (hex s)
  exact reduction_of_isStep ht

/--
`StepExists` と `LocalReduce` の同値（固定 `(c,b)` 版）。
-/
lemma stepExists_iff_nonempty_localReduce {c b : ℕ} :
    StepExists c b ↔ Nonempty (LocalReduce c b) := by
  constructor
  · intro hex
    exact ⟨localReduce_of_stepExists hex⟩
  · intro hreduce
    rcases hreduce with ⟨reduce⟩
    exact stepExists_of_localReduce reduce

/--
固定 `(c,b)` の数論局所縮小カーネル。
`nextQ` と、primitive/平方因子の保存、および strict 減少を1束にする。
-/
structure ReductionKernel (c b : ℕ) where
  nextQ :
    ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b → ℕ
  preserves_prim :
    ∀ {q : ℕ} (hPrim : PrimitiveOnS0 c b q) (hSq : q ^ 2 ∣ S0_nat c b),
      PrimitiveOnS0 c b (nextQ hPrim hSq)
  preserves_sq :
    ∀ {q : ℕ} (hPrim : PrimitiveOnS0 c b q) (hSq : q ^ 2 ∣ S0_nat c b),
      (nextQ hPrim hSq) ^ 2 ∣ S0_nat c b
  decreases :
    ∀ {q : ℕ} (hPrim : PrimitiveOnS0 c b q) (hSq : q ^ 2 ∣ S0_nat c b),
      nextQ hPrim hSq < q

/--
`ReductionKernel` から固定 `(c,b)` 版 `LocalReduce` を構成する。
-/
def localReduce_of_kernel {c b : ℕ}
    (ker : ReductionKernel c b) :
    LocalReduce c b := by
  intro s
  refine
    { q' := ker.nextQ s.hPrim s.hSq
      hPrim := ker.preserves_prim s.hPrim s.hSq
      hSq := ker.preserves_sq s.hPrim s.hSq
      hlt := ker.decreases s.hPrim s.hSq }

/--
固定 `(c,b)` とその不変量 `hbc/hcop` があるとき、
`LocalReduce` から `ReductionKernel` を作れる。
-/
def kernel_of_localReduce {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (reduce : LocalReduce c b) :
    ReductionKernel c b where
  nextQ := by
    intro q hPrim hSq
    exact (reduce ⟨q, hbc, hcop, hPrim, hSq⟩).q'
  preserves_prim := by
    intro q hPrim hSq
    exact (reduce ⟨q, hbc, hcop, hPrim, hSq⟩).hPrim
  preserves_sq := by
    intro q hPrim hSq
    exact (reduce ⟨q, hbc, hcop, hPrim, hSq⟩).hSq
  decreases := by
    intro q hPrim hSq
    exact (reduce ⟨q, hbc, hcop, hPrim, hSq⟩).hlt

/--
`StepExists` と `ReductionKernel` の同値（固定 `(c,b)` 版）。
`StepExists -> kernel` 方向では、`hbc/hcop` を使って `LocalReduce` を kernel 化する。
-/
lemma stepExists_iff_nonempty_kernel {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    StepExists c b ↔ Nonempty (ReductionKernel c b) := by
  constructor
  · intro hex
    let reduce : LocalReduce c b := localReduce_of_stepExists hex
    exact ⟨kernel_of_localReduce hbc hcop reduce⟩
  · intro hker
    rcases hker with ⟨ker⟩
    exact stepExists_of_localReduce (localReduce_of_kernel ker)

/-- `ReductionKernel` から `StepExists` を得る。 -/
lemma stepExists_of_kernel {c b : ℕ}
    (ker : ReductionKernel c b) :
    StepExists c b := by
  exact stepExists_of_localReduce (localReduce_of_kernel ker)

end NumberTheoryDescentOn

/--
`PrimitiveSquareDescentStep` から、固定 `(c,b)` 版 `LocalReduce` を作る。
-/
noncomputable def numberTheoryLocalReduceOn_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    NumberTheoryDescentOn.LocalReduce c b :=
  fun s => (numberTheoryReduce_of_step hStep) s.hPrim s.hSq

/--
`NumberTheoryReduce` から、固定 `(c,b)` 版 `LocalReduce` を作る。
-/
def numberTheoryLocalReduceOn_of_reduce {c b : ℕ}
    (reduceNT : NumberTheoryReduce c b) :
    NumberTheoryDescentOn.LocalReduce c b :=
  fun s => reduceNT s.hPrim s.hSq

/--
`NumberTheoryReduce` から固定 `(c,b)` の `ReductionKernel` を作る。
-/
def numberTheoryKernel_of_reduce {c b : ℕ}
    (reduceNT : NumberTheoryReduce c b) :
    NumberTheoryDescentOn.ReductionKernel c b where
  nextQ := fun hPrim hSq => (reduceNT hPrim hSq).q'
  preserves_prim := by
    intro q hPrim hSq
    exact (reduceNT hPrim hSq).hPrim
  preserves_sq := by
    intro q hPrim hSq
    exact (reduceNT hPrim hSq).hSq
  decreases := by
    intro q hPrim hSq
    exact (reduceNT hPrim hSq).hlt

/--
`PrimitiveSquareDescentStep` から固定 `(c,b)` の `ReductionKernel` を作る。
-/
noncomputable def numberTheoryKernel_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    NumberTheoryDescentOn.ReductionKernel c b :=
  numberTheoryKernel_of_reduce (numberTheoryReduce_of_step hStep)

/--
`PrimitiveSquareDescentStep` から、固定 `(c,b)` 版 `StepExists` を得る。
-/
lemma numberTheoryStepExistsOn_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    NumberTheoryDescentOn.StepExists c b := by
  exact NumberTheoryDescentOn.stepExists_of_kernel
    (numberTheoryKernel_of_step hStep)

/--
`NumberTheoryReduce` から、固定 `(c,b)` 版 `StepExists` を得る。
-/
lemma numberTheoryStepExistsOn_of_reduce {c b : ℕ}
    (reduceNT : NumberTheoryReduce c b) :
    NumberTheoryDescentOn.StepExists c b := by
  exact NumberTheoryDescentOn.stepExists_of_kernel
    (numberTheoryKernel_of_reduce reduceNT)

/--
固定 `(c,b)` の `ReductionKernel` から `StepExistsOn` を得る。
-/
lemma numberTheoryStepExistsOn_of_kernel {c b : ℕ}
    (ker : NumberTheoryDescentOn.ReductionKernel c b) :
    NumberTheoryDescentOn.StepExists c b := by
  exact NumberTheoryDescentOn.stepExists_of_kernel ker

/--
固定 `(c,b)` の `StepExistsOn` から `ReductionKernel` 存在を得る。
-/
lemma numberTheoryHasKernel_of_stepExistsOn {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hex : NumberTheoryDescentOn.StepExists c b) :
    Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  exact (NumberTheoryDescentOn.stepExists_iff_nonempty_kernel hbc hcop).1 hex

/--
固定 `(c,b)` の `ReductionKernel` 存在から `StepExistsOn` を得る。
-/
lemma numberTheoryStepExistsOn_of_hasKernel {c b : ℕ}
    (hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    NumberTheoryDescentOn.StepExists c b := by
  rcases hker with ⟨ker⟩
  exact numberTheoryStepExistsOn_of_kernel ker

/--
`PrimitiveSquareDescentStep` から固定 `(c,b)` の `ReductionKernel` 存在を得る。
-/
lemma numberTheoryHasKernel_of_step {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  exact ⟨numberTheoryKernel_of_step hStep⟩

/--
`NumberTheoryReduce` から固定 `(c,b)` の `ReductionKernel` 存在を得る。
-/
lemma numberTheoryHasKernel_of_reduce {c b : ℕ}
    (reduceNT : NumberTheoryReduce c b) :
    Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  exact ⟨numberTheoryKernel_of_reduce reduceNT⟩

/--
`LocalReduce` と `hbc/hcop` から固定 `(c,b)` の `ReductionKernel` 存在を得る。
-/
lemma numberTheoryHasKernel_of_localReduce {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (reduce : NumberTheoryDescentOn.LocalReduce c b) :
    Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  exact ⟨NumberTheoryDescentOn.kernel_of_localReduce hbc hcop reduce⟩

/--
下降エンジンから `PrimitiveSquareDescentStep` 条件を回収する。
-/
lemma primitiveSquareDescentStep_of_engine {c b : ℕ}
    (hEngine : PrimitiveSquareDescentEngine c b) :
    PrimitiveSquareDescentStep c b := by
  intro q hPrim hSq
  rcases hEngine.step hPrim hSq with ⟨q', hq'⟩
  exact ⟨q', hq'.1, hq'.2.1, hq'.2.2⟩

/--
局所縮小関数 `reduce` から、直接 `PrimitiveSquareDescentStep` を得る補助補題。
-/
lemma primitiveSquareDescentStep_of_reduce {c b : ℕ}
    (reduce : ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q) :
    PrimitiveSquareDescentStep c b := by
  exact primitiveSquareDescentStep_of_engine
    (primitiveSquareDescentEngine_of_reduce reduce)

/--
strict descent 条件があるなら、`PrimitiveOnS0` 上の平方持ち上げ witness は存在しない。
（最小反例 `q0` を取り、strict descent で `q' < q0` を得て矛盾）
-/
lemma not_primitiveSquareWitness_of_descentStep {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    ¬ PrimitiveSquareWitness c b := by
  classical
  intro hWitness
  let q0 : ℕ := Nat.find hWitness
  have hq0 : PrimitiveOnS0 c b q0 ∧ q0 ^ 2 ∣ S0_nat c b := by
    simpa [q0] using (Nat.find_spec hWitness)
  have hq0_min :
      ∀ q : ℕ, PrimitiveOnS0 c b q ∧ q ^ 2 ∣ S0_nat c b → q0 ≤ q := by
    intro q hq
    simpa [q0] using (Nat.find_min' hWitness hq)
  rcases hStep (q := q0) hq0.1 hq0.2 with ⟨q1, hq1Prim, hq1Sq, hq1Lt⟩
  have hq0_le_q1 : q0 ≤ q1 := hq0_min q1 ⟨hq1Prim, hq1Sq⟩
  exact (Nat.not_lt_of_ge hq0_le_q1) hq1Lt

/--
下降エンジン入力版: `PrimitiveOnS0` 上の平方持ち上げ witness は存在しない。
-/
lemma not_primitiveSquareWitness_of_descentEngine {c b : ℕ}
    (hEngine : PrimitiveSquareDescentEngine c b) :
    ¬ PrimitiveSquareWitness c b := by
  exact not_primitiveSquareWitness_of_descentStep
    (primitiveSquareDescentStep_of_engine hEngine)

/--
局所縮小関数 `reduce` 入力版: `PrimitiveOnS0` 上の平方持ち上げ witness は存在しない。
-/
lemma not_primitiveSquareWitness_of_reduce {c b : ℕ}
    (reduce : ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q) :
    ¬ PrimitiveSquareWitness c b := by
  exact not_primitiveSquareWitness_of_descentStep
    (primitiveSquareDescentStep_of_reduce reduce)

/--
strict descent 条件から `q` 全域の `NonLiftableS0` family を回収する。
-/
lemma nonLiftableS0_family_of_descentStep {c b : ℕ}
    (hStep : PrimitiveSquareDescentStep c b) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  intro q hPrim hqSq
  have hWitness : PrimitiveSquareWitness c b := ⟨q, hPrim, hqSq⟩
  exact (not_primitiveSquareWitness_of_descentStep hStep) hWitness

/--
下降エンジン入力版: `q` 全域の `NonLiftableS0` family を回収する。
-/
lemma nonLiftableS0_family_of_descentEngine {c b : ℕ}
    (hEngine : PrimitiveSquareDescentEngine c b) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  exact nonLiftableS0_family_of_descentStep (primitiveSquareDescentStep_of_engine hEngine)

/--
局所縮小関数 `reduce` 入力版: `q` 全域の `NonLiftableS0` family を回収する。
-/
lemma nonLiftableS0_family_of_reduce {c b : ℕ}
    (reduce : ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  exact nonLiftableS0_family_of_descentStep
    (primitiveSquareDescentStep_of_reduce reduce)

/--
`strict descent` と `coprime(c,b)` から `NoSqOnS0` を直接回復する。
-/
lemma NoSqOnS0_of_descentStep_coprime {c b : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (hStep : PrimitiveSquareDescentStep c b) :
    NoSqOnS0 c b := by
  have hNonLift : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_family_of_descentStep hStep
  intro q hq hqS0
  exact NoSqOnS0_of_support_nonLiftable_coprime hbc hcop hNonLift hq hqS0

/--
`descent engine` と `coprime(c,b)` から `NoSqOnS0` を直接回復する。
-/
lemma NoSqOnS0_of_descentEngine_coprime {c b : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (hEngine : PrimitiveSquareDescentEngine c b) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_descentStep_coprime hbc hcop
    (primitiveSquareDescentStep_of_engine hEngine)

/--
局所縮小関数 `reduce` 入力版: `NoSqOnS0` を直接回復する。
-/
lemma NoSqOnS0_of_reduce_coprime {c b : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (reduce : ∀ {q : ℕ}, PrimitiveOnS0 c b q → q ^ 2 ∣ S0_nat c b →
      PrimitiveSquareReduction c b q) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_descentStep_coprime hbc hcop
    (primitiveSquareDescentStep_of_reduce reduce)

/--
数論系 `reduce` 候補から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryReduce_coprime {c b : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (reduceNT : NumberTheoryReduce c b) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_reduce_coprime hbc hcop reduceNT

/--
トロミノ/幾何系 `reduce` 候補から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_trominoReduce_coprime {c b : ℕ}
    (hbc : b ≤ c)
    (hcop : Nat.Coprime c b)
    (reduceGeom : TrominoReduce c b) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_reduce_coprime hbc hcop reduceGeom

/--
状態遷移仕様 `StepExists`（global）から、固定 `c,b,q` での `NonLiftableS0` を得る。
-/
lemma nonLiftableS0_of_numberTheoryStepExists {c b q : ℕ}
    (hex : NumberTheoryDescentState.StepExists)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NonLiftableS0 c b q := by
  intro hPrim hSq
  exact NumberTheoryDescentState.false_of_state_of_stepExists hex
    ⟨c, b, q, hbc, hcop, hPrim, hSq⟩

/--
`StepExists`（global）から、固定 `c,b` 上の `NonLiftableS0` family を得る。
-/
lemma nonLiftableS0_family_of_numberTheoryStepExists {c b : ℕ}
    (hex : NumberTheoryDescentState.StepExists)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  intro q
  exact nonLiftableS0_of_numberTheoryStepExists (c := c) (b := b) (q := q) hex hbc hcop

/--
`StepExists`（global）と `coprime(c,b)` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryStepExists_coprime {c b : ℕ}
    (hex : NumberTheoryDescentState.StepExists)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hNonLift : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_family_of_numberTheoryStepExists hex hbc hcop
  intro q hq hqS0
  exact NoSqOnS0_of_support_nonLiftable_coprime hbc.le hcop hNonLift hq hqS0

/--
固定 `(c,b)` の `StepExists` から、固定 `q` の `NonLiftableS0` を得る。
-/
lemma nonLiftableS0_of_numberTheoryStepExistsOn {c b q : ℕ}
    (hex : NumberTheoryDescentOn.StepExists c b)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NonLiftableS0 c b q := by
  intro hPrim hSq
  exact NumberTheoryDescentOn.false_of_state_of_stepExists hex
    ⟨q, hbc, hcop, hPrim, hSq⟩

/--
固定 `(c,b)` の `StepExists` から `NonLiftableS0` family を得る。
-/
lemma nonLiftableS0_family_of_numberTheoryStepExistsOn {c b : ℕ}
    (hex : NumberTheoryDescentOn.StepExists c b)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    ∀ q : ℕ, NonLiftableS0 c b q := by
  intro q
  exact nonLiftableS0_of_numberTheoryStepExistsOn (c := c) (b := b) (q := q) hex hbc hcop

/--
固定 `(c,b)` の `StepExists` と `coprime(c,b)` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryStepExistsOn_coprime {c b : ℕ}
    (hex : NumberTheoryDescentOn.StepExists c b)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hNonLift : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_family_of_numberTheoryStepExistsOn hex hbc hcop
  intro q hq hqS0
  exact NoSqOnS0_of_support_nonLiftable_coprime hbc.le hcop hNonLift hq hqS0

/--
固定 `(c,b)` の `ReductionKernel` と `coprime(c,b)` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryKernel_coprime {c b : ℕ}
    (ker : NumberTheoryDescentOn.ReductionKernel c b)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hex : NumberTheoryDescentOn.StepExists c b :=
    numberTheoryStepExistsOn_of_kernel ker
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryStepExistsOn_coprime hex hbc hcop hq hqS0

/--
固定 `(c,b)` の数論 kernel の存在と `coprime(c,b)` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasKernel_coprime {c b : ℕ}
    (hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b))
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  rcases hker with ⟨ker⟩
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryKernel_coprime ker hbc hcop hq hqS0

/--
`hasKernel` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasKernelFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasKernel :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime
    (hasKernel hbc hcop) hbc hcop

/--
`hasStep` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasStepFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasStep :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        PrimitiveSquareDescentStep c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_step (hasStep hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`hasReduce` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasReduceFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryReduce c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_reduce (hasReduce hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`hasStepExists` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasStepExistsFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasStepExists :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.StepExists c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_stepExistsOn hbc hcop (hasStepExists hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`hasLocalReduce` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasLocalReduceFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasLocalReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.LocalReduce c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_localReduce hbc hcop (hasLocalReduce hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`hasStep` family から `hasKernel` family を作る。
-/
def numberTheoryHasKernelFamily_of_hasStep
    (hasStep :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        PrimitiveSquareDescentStep c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  intro c b hbc hcop
  exact numberTheoryHasKernel_of_step (hasStep hbc hcop)

/--
`hasReduce` family から `hasKernel` family を作る。
-/
def numberTheoryHasKernelFamily_of_hasReduce
    (hasReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryReduce c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  intro c b hbc hcop
  exact numberTheoryHasKernel_of_reduce (hasReduce hbc hcop)

/--
`hasStepExists` family から `hasKernel` family を作る。
-/
def numberTheoryHasKernelFamily_of_hasStepExists
    (hasStepExists :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.StepExists c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  intro c b hbc hcop
  exact numberTheoryHasKernel_of_stepExistsOn hbc hcop (hasStepExists hbc hcop)

/--
`hasLocalReduce` family から `hasKernel` family を作る。
-/
def numberTheoryHasKernelFamily_of_hasLocalReduce
    (hasLocalReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.LocalReduce c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b) := by
  intro c b hbc hcop
  exact numberTheoryHasKernel_of_localReduce hbc hcop (hasLocalReduce hbc hcop)

/--
`hasKernel` family から `hasReduce` family を作る。
-/
noncomputable def numberTheoryHasReduceFamily_of_hasKernel
    (hasKernel :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      NumberTheoryReduce c b := by
  intro c b hbc hcop
  let ker : NumberTheoryDescentOn.ReductionKernel c b := Classical.choice (hasKernel hbc hcop)
  intro q hPrim hSq
  exact (NumberTheoryDescentOn.localReduce_of_kernel ker)
    ⟨q, hbc, hcop, hPrim, hSq⟩

/--
`hasKernel` family から `hasStep` family を作る。
-/
noncomputable def numberTheoryHasStepFamily_of_hasKernel
    (hasKernel :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      PrimitiveSquareDescentStep c b := by
  intro c b hbc hcop
  intro q hPrim hSq
  let red : PrimitiveSquareReduction c b q :=
    (numberTheoryHasReduceFamily_of_hasKernel hasKernel hbc hcop) hPrim hSq
  exact ⟨red.q', red.hPrim, red.hSq, red.hlt⟩

/--
`hasNonLiftable` family から `hasStep` family を作る。
各 `(c,b,q)` で平方持ち上げが起きないため、`PrimitiveSquareDescentStep` は空前提で成立する。
-/
def numberTheoryHasStepFamily_of_nonLiftableFamily
    (hasNonLift :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        ∀ q : ℕ, NonLiftableS0 c b q) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      PrimitiveSquareDescentStep c b := by
  intro c b hbc hcop q hPrim hSq
  exact False.elim (hasNonLift hbc hcop q hPrim hSq)

/--
`hasNonLiftable` family から `hasKernel` family を作る。
-/
def numberTheoryHasKernelFamily_of_nonLiftableFamily
    (hasNonLift :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        ∀ q : ℕ, NonLiftableS0 c b q) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
  numberTheoryHasKernelFamily_of_hasStep
    (numberTheoryHasStepFamily_of_nonLiftableFamily hasNonLift)

/--
`hasNoSq` family から `hasNonLiftable` family を作る。
-/
def numberTheoryHasNonLiftableFamily_of_hasNoSqFamily
    (hasNoSq :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NoSqOnS0 c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      ∀ q : ℕ, NonLiftableS0 c b q := by
  intro c b hbc hcop q
  exact nonLiftableS0_all_of_NoSqOnS0 (hasNoSq hbc hcop) q

/--
`hasNoSq` family から `hasStep` family を作る。
-/
def numberTheoryHasStepFamily_of_hasNoSqFamily
    (hasNoSq :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NoSqOnS0 c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      PrimitiveSquareDescentStep c b :=
  numberTheoryHasStepFamily_of_nonLiftableFamily
    (numberTheoryHasNonLiftableFamily_of_hasNoSqFamily hasNoSq)

/--
`hasNoSq` family から `hasKernel` family を作る。
-/
def numberTheoryHasKernelFamily_of_hasNoSqFamily
    (hasNoSq :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NoSqOnS0 c b) :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
  numberTheoryHasKernelFamily_of_nonLiftableFamily
    (numberTheoryHasNonLiftableFamily_of_hasNoSqFamily hasNoSq)

/--
`hasNoSq` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を取り出す。
-/
lemma NoSqOnS0_of_numberTheoryHasNoSqFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasNoSq :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NoSqOnS0 c b) :
    NoSqOnS0 c b :=
  hasNoSq hbc hcop

/--
`hasNonLiftable` family 仮定から、固定 `(c,b)` の `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryHasNonLiftableFamily {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hasNonLift :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        ∀ q : ℕ, NonLiftableS0 c b q) :
    NoSqOnS0 c b := by
  exact NoSqOnS0_of_numberTheoryHasStepFamily hbc hcop
    (numberTheoryHasStepFamily_of_nonLiftableFamily hasNonLift)

/--
phase-11 本実装ターゲット:
固定 `(c,b)` ごとに `ReductionKernel` を供給する数論 provider。
-/
structure NumberTheoryKernelProvider where
  hasKernel :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      Nonempty (NumberTheoryDescentOn.ReductionKernel c b)

/--
固定 `(c,b)` ごとに `StepExistsOn` を供給する数論 provider。
-/
structure NumberTheoryStepExistsProvider where
  hasStepExists :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      NumberTheoryDescentOn.StepExists c b

/--
固定 `(c,b)` ごとに `LocalReduce` を供給する数論 provider。
-/
structure NumberTheoryLocalReduceProvider where
  hasLocalReduce :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      NumberTheoryDescentOn.LocalReduce c b

/--
固定 `(c,b)` ごとに `NumberTheoryReduce` を供給する数論 provider。
-/
structure NumberTheoryReduceProvider where
  hasReduce :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      NumberTheoryReduce c b

/--
固定 `(c,b)` ごとに `PrimitiveSquareDescentStep` を供給する数論 provider。
`KernelProvider` より弱い実装目標として用意する。
-/
structure NumberTheoryStepProvider where
  hasStep :
    ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
      PrimitiveSquareDescentStep c b

/--
`hasKernel` 関数から `NumberTheoryKernelProvider` を作る。
-/
def numberTheoryKernelProvider_of_hasKernel
    (hasKernel :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    NumberTheoryKernelProvider where
  hasKernel := by
    intro c b hbc hcop
    exact hasKernel hbc hcop

/--
`hasStepExists` 関数から `NumberTheoryStepExistsProvider` を作る。
-/
def numberTheoryStepExistsProvider_of_hasStepExists
    (hasStepExists :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.StepExists c b) :
    NumberTheoryStepExistsProvider where
  hasStepExists := by
    intro c b hbc hcop
    exact hasStepExists hbc hcop

/--
`hasLocalReduce` 関数から `NumberTheoryLocalReduceProvider` を作る。
-/
def numberTheoryLocalReduceProvider_of_hasLocalReduce
    (hasLocalReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryDescentOn.LocalReduce c b) :
    NumberTheoryLocalReduceProvider where
  hasLocalReduce := by
    intro c b hbc hcop
    exact hasLocalReduce hbc hcop

/--
`hasReduce` 関数から `NumberTheoryReduceProvider` を作る。
-/
def numberTheoryReduceProvider_of_hasReduce
    (hasReduce :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        NumberTheoryReduce c b) :
    NumberTheoryReduceProvider where
  hasReduce := by
    intro c b hbc hcop
    exact hasReduce hbc hcop

/--
`hasStep` 関数から `NumberTheoryStepProvider` を作る。
-/
def numberTheoryStepProvider_of_hasStep
    (hasStep :
      ∀ {c b : ℕ}, b < c → Nat.Coprime c b →
        PrimitiveSquareDescentStep c b) :
    NumberTheoryStepProvider where
  hasStep := by
    intro c b hbc hcop
    exact hasStep hbc hcop

/--
`NumberTheoryLocalReduceProvider` から `NumberTheoryStepExistsProvider` を得る。
-/
def numberTheoryStepExistsProvider_of_localReduceProvider
    (provLocal : NumberTheoryLocalReduceProvider) :
    NumberTheoryStepExistsProvider where
  hasStepExists := by
    intro c b hbc hcop
    exact NumberTheoryDescentOn.stepExists_of_localReduce
      (provLocal.hasLocalReduce hbc hcop)

/--
`NumberTheoryLocalReduceProvider` から `NumberTheoryKernelProvider` を得る。
-/
def numberTheoryKernelProvider_of_localReduceProvider
    (provLocal : NumberTheoryLocalReduceProvider) :
    NumberTheoryKernelProvider where
  hasKernel := by
    intro c b hbc hcop
    exact numberTheoryHasKernel_of_localReduce hbc hcop
      (provLocal.hasLocalReduce hbc hcop)

/--
`NumberTheoryLocalReduceProvider` から `NumberTheoryReduceProvider` を得る。
-/
def numberTheoryReduceProvider_of_localReduceProvider
    (provLocal : NumberTheoryLocalReduceProvider) :
    NumberTheoryReduceProvider where
  hasReduce := by
    intro c b hbc hcop
    let reduceLocal : NumberTheoryDescentOn.LocalReduce c b :=
      provLocal.hasLocalReduce hbc hcop
    intro q hPrim hSq
    exact reduceLocal ⟨q, hbc, hcop, hPrim, hSq⟩

/--
`NumberTheoryLocalReduceProvider` から `NumberTheoryStepProvider` を得る。
-/
def numberTheoryStepProvider_of_localReduceProvider
    (provLocal : NumberTheoryLocalReduceProvider) :
    NumberTheoryStepProvider where
  hasStep := by
    intro c b hbc hcop
    exact primitiveSquareDescentStep_of_reduce
      ((numberTheoryReduceProvider_of_localReduceProvider provLocal).hasReduce hbc hcop)

/--
`NumberTheoryStepExistsProvider` から `NumberTheoryKernelProvider` を得る。
-/
def numberTheoryKernelProvider_of_stepExistsProvider
    (provExists : NumberTheoryStepExistsProvider) :
    NumberTheoryKernelProvider where
  hasKernel := by
    intro c b hbc hcop
    exact numberTheoryHasKernel_of_stepExistsOn hbc hcop
      (provExists.hasStepExists hbc hcop)

/--
`NumberTheoryStepExistsProvider` から `NumberTheoryReduceProvider` を得る。
-/
noncomputable def numberTheoryReduceProvider_of_stepExistsProvider
    (provExists : NumberTheoryStepExistsProvider) :
    NumberTheoryReduceProvider where
  hasReduce := by
    intro c b hbc hcop
    let reduceLocal : NumberTheoryDescentOn.LocalReduce c b :=
      NumberTheoryDescentOn.localReduce_of_stepExists
        (provExists.hasStepExists hbc hcop)
    intro q hPrim hSq
    exact reduceLocal ⟨q, hbc, hcop, hPrim, hSq⟩

/--
`NumberTheoryStepExistsProvider` から `NumberTheoryStepProvider` を得る。
-/
noncomputable def numberTheoryStepProvider_of_stepExistsProvider
    (provExists : NumberTheoryStepExistsProvider) :
    NumberTheoryStepProvider where
  hasStep := by
    intro c b hbc hcop
    exact primitiveSquareDescentStep_of_reduce
      ((numberTheoryReduceProvider_of_stepExistsProvider provExists).hasReduce hbc hcop)

/--
`NumberTheoryStepProvider` から `NumberTheoryReduceProvider` を得る。
-/
noncomputable def numberTheoryReduceProvider_of_stepProvider
    (provStep : NumberTheoryStepProvider) :
    NumberTheoryReduceProvider where
  hasReduce := by
    intro c b hbc hcop
    exact numberTheoryReduce_of_step (provStep.hasStep hbc hcop)

/--
`NumberTheoryReduceProvider` から `NumberTheoryStepProvider` を得る。
-/
def numberTheoryStepProvider_of_reduceProvider
    (provReduce : NumberTheoryReduceProvider) :
    NumberTheoryStepProvider where
  hasStep := by
    intro c b hbc hcop
    exact primitiveSquareDescentStep_of_reduce (provReduce.hasReduce hbc hcop)

/--
`NumberTheoryReduceProvider` から `NumberTheoryKernelProvider` を得る。
-/
def numberTheoryKernelProvider_of_reduceProvider
    (provReduce : NumberTheoryReduceProvider) :
    NumberTheoryKernelProvider where
  hasKernel := by
    intro c b hbc hcop
    exact numberTheoryHasKernel_of_reduce (provReduce.hasReduce hbc hcop)

/--
固定 `(c,b)` の `ReductionKernel` 存在（`hbc/hcop` 付き）から
`NumberTheoryReduce c b` を（選択公理で）構成する。
-/
noncomputable def numberTheoryReduce_of_hasKernel {c b : ℕ}
    (hbc : b < c)
    (hcop : Nat.Coprime c b)
    (hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b)) :
    NumberTheoryReduce c b := by
  let ker : NumberTheoryDescentOn.ReductionKernel c b := Classical.choice hker
  intro q hPrim hSq
  exact (NumberTheoryDescentOn.localReduce_of_kernel ker)
    ⟨q, hbc, hcop, hPrim, hSq⟩

/--
`NumberTheoryKernelProvider` から `NumberTheoryReduceProvider` を得る。
-/
noncomputable def numberTheoryReduceProvider_of_kernelProvider
    (provKernel : NumberTheoryKernelProvider) :
    NumberTheoryReduceProvider where
  hasReduce := by
    intro c b hbc hcop
    exact numberTheoryReduce_of_hasKernel hbc hcop (provKernel.hasKernel hbc hcop)

/--
`NumberTheoryKernelProvider` から `NumberTheoryStepProvider` を得る。
-/
noncomputable def numberTheoryStepProvider_of_kernelProvider
    (provKernel : NumberTheoryKernelProvider) :
    NumberTheoryStepProvider where
  hasStep := by
    intro c b hbc hcop
    exact primitiveSquareDescentStep_of_reduce
      (numberTheoryReduce_of_hasKernel hbc hcop (provKernel.hasKernel hbc hcop))

/--
`NumberTheoryStepProvider` から `NumberTheoryKernelProvider` を得る。
-/
def numberTheoryKernelProvider_of_stepProvider
    (provStep : NumberTheoryStepProvider) :
    NumberTheoryKernelProvider where
  hasKernel := by
    intro c b hbc hcop
    exact numberTheoryHasKernel_of_step (provStep.hasStep hbc hcop)

/--
`NumberTheoryStepProvider` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryStepProvider {c b : ℕ}
    (provStep : NumberTheoryStepProvider)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_step (provStep.hasStep hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`NumberTheoryReduceProvider` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryReduceProvider {c b : ℕ}
    (provReduce : NumberTheoryReduceProvider)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_reduce (provReduce.hasReduce hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`NumberTheoryStepExistsProvider` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryStepExistsProvider {c b : ℕ}
    (provExists : NumberTheoryStepExistsProvider)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_stepExistsOn hbc hcop
      (provExists.hasStepExists hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`NumberTheoryLocalReduceProvider` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryLocalReduceProvider {c b : ℕ}
    (provLocal : NumberTheoryLocalReduceProvider)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have hker : Nonempty (NumberTheoryDescentOn.ReductionKernel c b) :=
    numberTheoryHasKernel_of_localReduce hbc hcop
      (provLocal.hasLocalReduce hbc hcop)
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime hker hbc hcop hq hqS0

/--
`NumberTheoryKernelProvider` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryKernelProvider {c b : ℕ}
    (prov : NumberTheoryKernelProvider)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryHasKernel_coprime
    (prov.hasKernel hbc hcop) hbc hcop hq hqS0

/--
固定 `(c,b)` の `LocalReduce` から `NoSqOnS0` を回復する。
-/
lemma NoSqOnS0_of_numberTheoryLocalReduceOn_coprime {c b : ℕ}
    (reduce : NumberTheoryDescentOn.LocalReduce c b)
    (hbc : b < c)
    (hcop : Nat.Coprime c b) :
    NoSqOnS0 c b := by
  have ker : NumberTheoryDescentOn.ReductionKernel c b :=
    NumberTheoryDescentOn.kernel_of_localReduce hbc hcop reduce
  intro q hq hqS0
  exact NoSqOnS0_of_numberTheoryKernel_coprime ker hbc hcop hq hqS0

/--
phase-11 接続補題:
`harmonic envelope` と `strict descent` から
`DescentClassifyImpossibleOnPrimitive` を構成する。
-/
lemma descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentStep {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hStep : PrimitiveSquareDescentStep c b) :
    DescentClassifyImpossibleOnPrimitive c b := by
  have hNonLiftAll : ∀ q : ℕ, NonLiftableS0 c b q :=
    nonLiftableS0_family_of_descentStep hStep
  have hsideAll :
      ∀ q : ℕ, HarmonicNonExceptionalSide ({ c := c, b := b, q := q } : CounterexampleInput) := by
    intro q
    exact harmonicNonExceptionalSide_of_envelope hInfra hHarm
      (hNoExcAll { c := c, b := b, q := q })
  intro q hPrim
  exact classifyLift_impossible_family_of_harmonicNonExceptional_nonLiftable
    hbc hsideAll hNonLiftAll hPrim

/--
phase-11 接続補題（engine 入力版）。
-/
lemma descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentEngine {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hEngine : PrimitiveSquareDescentEngine c b) :
    DescentClassifyImpossibleOnPrimitive c b := by
  exact descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentStep
    hbc hInfra hHarm hNoExcAll (primitiveSquareDescentStep_of_engine hEngine)

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
`primitiveSized` フレームを使う非empty版 core コンストラクタ。
-/
def GEisensteinDescentCore_of_descentClassify_primitiveSized {c b : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b) :
    GEisensteinDescentCore c b := by
  exact GEisensteinDescentCore_of_descentClassify_withFrame
    hDescent (primitiveSizedCandidateGEisensteinDescentFrame c b)
    (primitiveSizedCandidate_frame_step_pred c b)

/--
phase-15 canonical constructor（step 版）:
`harmonic envelope + strict descent step` から、`primitiveSized` frame つきの
`GEisensteinDescentCore` を組み立てる。
-/
def GEisensteinDescentCore_of_harmonicEnvelope_descentStep {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hStep : PrimitiveSquareDescentStep c b) :
    GEisensteinDescentCore c b := by
  exact GEisensteinDescentCore_of_descentClassify_primitiveSized
    (descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentStep
      hbc hInfra hHarm hNoExcAll hStep)

/--
phase-15 canonical constructor（engine 版）:
`harmonic envelope + descent engine` から、`GEisenstein` 側の descent kernel を
直接組み立てる。
-/
def GEisensteinDescentCore_of_harmonicEnvelope_descentEngine {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hEngine : PrimitiveSquareDescentEngine c b) :
    GEisensteinDescentCore c b := by
  exact GEisensteinDescentCore_of_harmonicEnvelope_descentStep
    hbc hInfra hHarm hNoExcAll (primitiveSquareDescentStep_of_engine hEngine)

/--
`primitiveSized` 非empty core を使った停止到達橋補題。
`PrimitiveOnS0` を持つ初期状態から、有限反復で測度 0 に到達する。
-/
lemma exists_descend_measure_eq_zero_of_descentClassify_primitiveSized
    {c b q : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b)
    (hPrim : PrimitiveOnS0 c b q)
    (size : ℕ)
    (hsize : size ≤ q) :
    ∃ n : ℕ,
      (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        (GEisensteinDescentFrame.descend
          (primitiveSizedCandidateGEisensteinDescentFrame c b)
          (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize)
          n) = 0 := by
  let hCore : GEisensteinDescentCore c b :=
    GEisensteinDescentCore_of_descentClassify_primitiveSized hDescent
  let s0 : hCore.frame.State :=
    GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize
  simpa [hCore, s0] using
    GEisensteinDescentCore.exists_descend_measure_eq_zero_of_step_pred hCore s0

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

/--
phase-11 版 bridge:
`NoSqOnS0` 仮定なしで、`strict descent` を入口にして
`DescentClassifyImpossibleOnPrimitive` を構成する。
-/
lemma descentClassifyImpossibleOnPrimitive_via_GEisenstein_descentStep {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hStep : PrimitiveSquareDescentStep c b) :
    DescentClassifyImpossibleOnPrimitive c b := by
  exact descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentStep
    hbc hInfra hHarm hNoExcAll hStep

/--
phase-11 版 bridge（engine 入力版）。
-/
lemma descentClassifyImpossibleOnPrimitive_via_GEisenstein_descentEngine {c b : ℕ}
    (hbc : b < c)
    (hInfra : HasPhaseUnitInfrastructure)
    (hHarm : ∃ u : PetalCoreUnit, HarmonicPoint u ∧ ¬ isExceptionalPhase u)
    (hNoExcAll : ∀ x : CounterexampleInput, ¬ exceptionalPhaseGate x)
    (hEngine : PrimitiveSquareDescentEngine c b) :
    DescentClassifyImpossibleOnPrimitive c b := by
  exact descentClassifyImpossibleOnPrimitive_of_harmonicEnvelope_descentEngine
    hbc hInfra hHarm hNoExcAll hEngine

/-- 旧層Bの平方耐性主張が一般には成り立たないことの具体反例。 -/
theorem exists_counterexample_S0_square_resistance :
    ∃ a b q : ℕ,
      0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ Nat.Prime q ∧
      q ∣ S0_nat a b ∧ ¬ q ∣ a + b ∧ q ^ 2 ∣ S0_nat a b := by
  refine ⟨18, 1, 7, ?_⟩
  decide

end DkMath.FLT
