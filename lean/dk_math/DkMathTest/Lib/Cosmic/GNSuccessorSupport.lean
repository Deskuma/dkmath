/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNSupport
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

#print "file: DkMathTest.Lib.Cosmic.GNSuccessorSupport"

/-!
# GN-LIB-001: 下位importからの境界回帰

旧GapFocusingモジュールをimportせず、Libだけから旧全修飾名を使用する。
零次数、零座標、非原始対、負座標、零因子を含む係数環を確認する。
17個の昇格宣言について、標準論理公理以外への依存をエラーにする。
旧importの回帰は既存の `GapFocusingSupport` と successorテストが担う。
-/

namespace DkMathTest.Lib.Cosmic.GNSuccessorSupport

open DkMath.CosmicFormula DkMath.NumberTheory.GapFocusing

/-- 再帰は零次数でも成立し、gapでの約分を要求しない。 -/
example {R : Type*} [CommSemiring R] (x u : R) :
    GTail (0 + 1) 1 x u = u * GTail 0 1 x u + (x + u) ^ 0 :=
  GN_succ_right 0 x u

example {R : Type*} [CommSemiring R] (d : ℕ) (u : R) :
    GTail (d + 1) 1 0 u = (0 + u) * GTail d 1 0 u + u ^ d :=
  GN_succ_left d 0 u

/-- 零gapと単位anchorの原始対は全次数で互いに素である。 -/
example (d : ℕ) : (GTail d 1 0 1).Coprime (GTail (d + 1) 1 0 1) :=
  nat_coprime_adjacent_GN d 0 1 (by decide)

example (d : ℕ) : (GTail d 1 1 0).Coprime (GTail (d + 1) 1 1 0) :=
  nat_coprime_adjacent_GN d 1 0 (by decide)

/-- 原始性の逆向きは次数2以上。次数1のGN=1には適用しない。 -/
example : (GTail 1 1 2 2 : ℕ).Coprime (GTail 2 1 2 2) := by decide

example : ¬(GTail 2 1 2 2 : ℕ).Coprime (GTail 3 1 2 2) := by
  rw [nat_coprime_adjacent_GN_iff 0 2 2]
  decide

example : (2 : ℕ) ∣ GTail 2 1 2 2 ∧ 2 ∣ GTail 3 1 2 2 :=
  (nat_prime_dvd_adjacent_GN_iff 0 2 2 (by decide)).mpr ⟨by decide, by decide⟩

/-- 整数版は負座標と零次数を保持する。 -/
example : Int.gcd (GTail 0 1 (-3) 2) (GTail 1 1 (-3) 2) = 1 :=
  int_gcd_adjacent_GN_eq_one 0 (-3) 2 (by decide)

/-- ZMod 6には零因子があるが、座標のBézout関係から同じ結論が得られる。 -/
example (d : ℕ) : IsCoprime (GTail d 1 (2 : ZMod 6) 3)
    (GTail (d + 1) 1 (2 : ZMod 6) 3) :=
  isCoprime_adjacent_GN d 2 3 ⟨-1, 1, by decide⟩

/-- 後続項の素数は直前にはない。過去全体への非出現は主張しない。 -/
example : ∃ p : ℕ, p.Prime ∧ p ∣ GTail 6 1 1 1 ∧ ¬p ∣ GTail 5 1 1 1 :=
  nat_exists_prime_dvd_GN_succ_not_dvd_GN 5 1 1 (by decide) (by decide)
    (by decide) (by decide)

end DkMathTest.Lib.Cosmic.GNSuccessorSupport

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``DkMath.NumberTheory.GapFocusing.GN_succ_right,
    ``DkMath.NumberTheory.GapFocusing.GN_succ_left,
    ``DkMath.NumberTheory.GapFocusing.GN_succ_unit_anchor,
    ``DkMath.NumberTheory.GapFocusing.GN_succ_bezout,
    ``DkMath.NumberTheory.GapFocusing.GN_succ_isCoprime_unit_anchor,
    ``DkMath.NumberTheory.GapFocusing.dvd_anchor_pow_of_dvd_adjacent_GN,
    ``DkMath.NumberTheory.GapFocusing.dvd_sum_pow_of_dvd_adjacent_GN,
    ``DkMath.NumberTheory.GapFocusing.nat_dvd_powers_of_dvd_adjacent_GN,
    ``DkMath.NumberTheory.GapFocusing.nat_prime_dvd_coordinates_of_dvd_adjacent_GN,
    ``DkMath.NumberTheory.GapFocusing.nat_coprime_adjacent_GN,
    ``DkMath.NumberTheory.GapFocusing.nat_one_lt_GN_succ,
    ``DkMath.NumberTheory.GapFocusing.nat_exists_prime_dvd_GN_succ_not_dvd_GN,
    ``DkMath.NumberTheory.GapFocusing.dvd_GN_of_dvd_coordinates,
    ``DkMath.NumberTheory.GapFocusing.nat_prime_dvd_adjacent_GN_iff,
    ``DkMath.NumberTheory.GapFocusing.nat_coprime_adjacent_GN_iff,
    ``DkMath.NumberTheory.GapFocusing.isCoprime_adjacent_GN,
    ``DkMath.NumberTheory.GapFocusing.int_gcd_adjacent_GN_eq_one]
  for n in names do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {n}: {ax}"
  logInfo m!"GN-LIB-001: {names.size} promoted declarations use standard logical axioms only."
