/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveGNSameBeta
import DkMath.FLT.Five.SignedGoldenClosure

/-!
# GN・Kummer と黄金比降下による FLT5 再形式化

最初の同じ β の五乗根を新しい円分イデアル・単元・相対ノルム経路で供給する。
その根の第二座標、ノルム、原始性、十分な5進深度を既存の零セクター降下へ渡す。
厳密減少を新しい強帰納法で閉じ、既存の完成済み FLT5 終点は呼ばない。

降下内部の二次 lift の再五乗抽出と黄金比単元分類は既存証明を再利用する。
この依存を「単元分類を全廃した」と取り違えないことが研究上の境界となる。
-/

namespace DkMath.FLT.Kummer

open DkMath.FLT.Five

/-- 指定された同じ β の根から、既存の厳密降下が必要とする全算術データを作る。
単に型を定義するのではなく、ノルム・第二座標・互いに素性から構成する。 -/
theorem nonempty_gnGoldenZeroSectorCandidate {u v w : ℕ}
    (q : SignedGoldenRamifierStrippedPacket u v w) {θ : GoldenInt} (hθ : q.beta = θ ^ 5) :
    Nonempty GoldenZeroSectorCandidate := by
  obtain ⟨c, d, hc, hd⟩ := q.zeroSector_tenthPower_split hθ
  exact ⟨goldenZeroSectorCandidate_of_raw θ.fst θ.snd
    q.exceptional.powerSplit.a q.exceptional.powerSplit.b
    q.exceptional.powerSplit.a_pos q.exceptional.powerSplit.b_pos
    q.exceptional.powerSplit.coprime_a_b q.five_not_dvd_b
    (q.zeroSector_gamma_norm_eq_or_eq_neg hθ)
    (q.zeroSector_snd_factor_eq hθ) (q.zeroSector_coprime_coords hθ) c d hc hd⟩

/-- 既存の一段の厳密降下を、第二座標の絶対値に関する新しい強帰納法で閉じる。
lift の再五乗抽出は既存の零セクター機構を使う。 -/
theorem goldenZeroSectorDescentPacket_false_via_GN (p : GoldenZeroSectorDescentPacket) : False := by
  have noAt : ∀ n : ℕ, ∀ q : GoldenZeroSectorDescentPacket,
      goldenZeroSectorDescentMeasure q = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hq
      obtain ⟨step⟩ := q.strictDescent
      exact ih (goldenZeroSectorDescentMeasure step.next)
        (by simpa [hq] using step.measure_lt) step.next rfl
  exact noAt (goldenZeroSectorDescentMeasure p) p rfl

/-- 同じ β の GN 五乗根から降下へ実際に到達する接続。 -/
theorem signedGoldenRamifierStripped_false_via_GN {u v w : ℕ}
    (q : SignedGoldenRamifierStrippedPacket u v w) : False := by
  obtain ⟨θ, hθ⟩ := exists_fifth_eq_stripped_beta_via_GN q
  obtain ⟨candidate⟩ := nonempty_gnGoldenZeroSectorCandidate q hθ
  exact goldenZeroSectorDescentPacket_false_via_GN
    (goldenZeroSectorDescentPacket_of_candidate candidate)

/-- 二つの signed orientation の入力パケットを、新しい GN 経路へ渡す。 -/
theorem signedBranchARefuter_via_GN : SignedBranchARefuter :=
  signedBranchARefuter_of_goldenRamifierStrippedCore
    (fun q => signedGoldenRamifierStripped_false_via_GN q)

/-- 元の原始解を向き付けし、GN・Kummer と黄金比降下で反駁する。 -/
theorem counterexamplePack_false_via_GN {x y z : ℕ} (p : CounterexamplePack x y z) : False := by
  rcases p.branchB_orientation with hy | hx
  · exact branchB_false_of_signedBranchARefuter signedBranchARefuter_via_GN p hy
  · exact branchB_false_of_signedBranchARefuter signedBranchARefuter_via_GN p.swap hx

/-- 追加仮定のない GN 経由の FLT5。既存の gcd 正規化だけを使い、
不可能性の結論は今回の同じ β の五乗根と新しい強帰納法により供給する。 -/
theorem fermatFive_no_positive_solution_via_GN (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 5 + b ^ 5 ≠ c ^ 5 := by
  intro heq
  obtain ⟨a', b', c', p⟩ := exists_counterexamplePack_of_positive_fermat5 ha hb hc heq
  exact counterexamplePack_false_via_GN p

end DkMath.FLT.Kummer
