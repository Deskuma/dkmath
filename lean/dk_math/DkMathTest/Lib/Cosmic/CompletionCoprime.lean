/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.CompletionCoprime
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.Cosmic.CompletionCoprime"

/-!
# GN-LIB-002: 非原始完成と素数支持の境界

下位所有者だけをimportし、共通因子の保存・零次数・零座標を検査する。
原始性を落とした素数排除と、正次数を落とした支持一致には具体的な反例を置く。
合成数の完成根91は、完成が素数生成ではなく付値の倍化であることを示す。
-/

namespace DkMathTest.Lib.Cosmic.CompletionCoprime

open DkMath.CosmicFormula DkMath.Lib.Cosmic

/-- 最初の完成例。Bodyの積表示を含めて960+1=961を確認する。 -/
example : (30 * GTail 2 1 30 1 : ℕ) = 960 ∧ (30 + 1) ^ 2 = 961 := by decide

example : (30 * GTail 2 1 30 1 : ℕ) + 1 ^ 2 = (30 + 1) ^ 2 :=
  completion_body_add_gap 2 30 1

/-- 非原始対では共通因子2の3乗が三者に残り、gcdを1へ置換しない。 -/
example : Nat.gcd ((6 + 4) ^ 3) (4 ^ 3) = 8 ∧
    Nat.gcd (6 * GTail 3 1 6 4) (4 ^ 3) = 8 ∧
    Nat.gcd (6 * GTail 3 1 6 4) ((6 + 4) ^ 3) = 8 := by
  rw [completion_gcd_big_gap, completion_gcd_body_gap, completion_gcd_body_big]
  decide

/-- 次数0は、非原始対を含めて三つのgcdが全て1になる。 -/
example (g u : ℕ) : Nat.gcd ((g + u) ^ 0) (u ^ 0) = 1 ∧
    Nat.gcd (g * GTail 0 1 g u) (u ^ 0) = 1 ∧
    Nat.gcd (g * GTail 0 1 g u) ((g + u) ^ 0) = 1 := by
  rw [completion_gcd_big_gap, completion_gcd_body_gap, completion_gcd_body_big]
  exact ⟨rfl, rfl, rfl⟩

example : Nat.gcd (0 * GTail 3 1 0 7) (7 ^ 3) = 343 := by
  rw [completion_gcd_body_gap]
  decide

example : Nat.gcd (3 * GTail 2 1 3 0) ((3 + 0) ^ 2) = 9 := by
  rw [completion_gcd_body_big]
  decide

example : Nat.gcd (0 * GTail 3 1 0 0) ((0 + 0) ^ 3) = 0 := by
  rw [completion_gcd_body_big]
  decide

/-- 原始対の三者はpairwise coprime。次数0も同じ公開APIで扱う。 -/
example : (0 * GTail 0 1 0 1).Coprime (1 ^ 0) ∧
    (0 * GTail 0 1 0 1).Coprime ((0 + 1) ^ 0) ∧
    ((0 + 1) ^ 0).Coprime (1 ^ 0) :=
  completion_pairwise_coprime 0 0 1 (by decide)

/-- 完成根91は合成数だが、7と13はBigのみに現れる。 -/
example : ¬Nat.Prime (90 + 1) := by decide

example : ¬7 ∣ 90 * GTail 2 1 90 1 ∧ ¬7 ∣ 1 ^ 2 :=
  completion_prime_not_dvd_body_gap_of_dvd_sum 2 90 1 (by decide) (by decide)
    (by decide) (by decide)

example : ¬13 ∣ 90 * GTail 2 1 90 1 ∧ ¬13 ∣ 1 ^ 2 :=
  completion_prime_not_dvd_body_gap_of_dvd_big 2 90 1 (by decide) (by decide)
    (by decide)

/-- 次数側を2にしても素数3を排除でき、奇素数次数の仮定は不要。 -/
example : ¬3 ∣ 2 * GTail 2 1 2 1 ∧ ¬3 ∣ 1 ^ 2 :=
  completion_prime_not_dvd_body_gap_of_dvd_sum 2 2 1 (by decide) (by decide)
    (by decide) (by decide)

/-- 非原始対では三者を割る素数が残る。原始性を外せない反例。 -/
example : 2 ∣ (2 + 2) ^ 2 ∧ 2 ∣ 2 * GTail 2 1 2 2 ∧ 2 ∣ 2 ^ 2 := by decide

/-- 次数0の完成根は素数を持ち得るが、Big=1は持たず、Body=0は全素数で割れる。 -/
example : 2 ∣ (1 + 1) ∧ ¬2 ∣ (1 + 1) ^ 0 ∧ 2 ∣ 1 * GTail 0 1 1 1 := by decide

/-- 正次数なら完成根が0でも支持一致は成立する。 -/
example : 2 ∣ ((0 + 0) ^ 3 : ℕ) ↔ 2 ∣ (0 + 0 : ℕ) :=
  completion_prime_dvd_big_iff_dvd_sum 3 0 0 (by decide) (by decide)

/-- 原始性なしでもBigの付値は倍化する。 -/
example : padicValNat 2 ((6 + 4) ^ 3) = 3 := by
  rw [completion_padicValNat_big 3 6 4 (by decide) (by decide)]
  change 3 * padicValNat 2 (2 * 5) = 3
  rw [padicValNat_base_mul (by decide) (by decide),
    padicValNat.eq_zero_of_not_dvd (by decide)]

example : padicValNat 7 ((90 + 1) ^ 2) = 2 := by
  rw [completion_padicValNat_big 2 90 1 (by decide) (by decide)]
  change 2 * padicValNat 7 (7 * 13) = 2
  rw [padicValNat_base_mul (by decide) (by decide),
    padicValNat.eq_zero_of_not_dvd (by decide)]

example : padicValNat 13 ((90 + 1) ^ 0) = 0 := by
  rw [completion_padicValNat_big 0 90 1 (by decide) (by decide)]
  exact Nat.zero_mul _

/-- 現れない素数の付値は0。次数が付値を割るだけでは出現を保証しない。 -/
example : 3 ∣ padicValNat 7 ((6 + 4) ^ 3) :=
  completion_degree_dvd_padicValNat_big 3 6 4 (by decide) (by decide)

end DkMathTest.Lib.Cosmic.CompletionCoprime

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``DkMath.Lib.Cosmic.completion_body_add_gap,
    ``DkMath.Lib.Cosmic.completion_gcd_big_gap,
    ``DkMath.Lib.Cosmic.completion_gcd_body_gap,
    ``DkMath.Lib.Cosmic.completion_gcd_body_big,
    ``DkMath.Lib.Cosmic.completion_coprime_big_gap,
    ``DkMath.Lib.Cosmic.completion_coprime_body_gap,
    ``DkMath.Lib.Cosmic.completion_coprime_body_big,
    ``DkMath.Lib.Cosmic.completion_pairwise_coprime,
    ``DkMath.Lib.Cosmic.completion_prime_not_dvd_body_gap_of_dvd_big,
    ``DkMath.Lib.Cosmic.completion_prime_dvd_big_iff_dvd_sum,
    ``DkMath.Lib.Cosmic.completion_prime_not_dvd_body_gap_of_dvd_sum,
    ``DkMath.Lib.Cosmic.completion_padicValNat_big,
    ``DkMath.Lib.Cosmic.completion_degree_dvd_padicValNat_big]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {n}: {ax}"
  logInfo m!"GN-LIB-002: {names.size} declarations use standard logical axioms only."
