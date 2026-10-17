/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenDescentStep

#print "file: DkMath.FLT.Kummer.SevenGNDescent"

/-! # FLT7教科書：GNによる七位相降下の閉包
深度1の排除と実際に構成した一段遷移を自然数帰納法で反復する。
元の自然数反例を毎回作り直さず、同じ七乗方程式の型を保つ。
最後にMathlibのgcd正規化で、原始性の仮定も取り除く。
-/

namespace DkMath.FLT.Kummer.SevenDescent

open DkMath.FLT.Seven

/-- 正深度の状態は存在しない。底とstepはいずれも前章で証明済みである。 -/
theorem no_state (m : ℕ) (hm : 1 ≤ m) : ¬ Nonempty (State m) := by
  induction m, hm using Nat.le_induction with
  | base => exact no_state_one
  | succ m _ ih => exact fun h => ih (descent_step m h)

/-- 任意の正の原始FLT7反例から初期状態へ入り、分岐深度降下で矛盾する。 -/
theorem no_counterexample {a b c : ℕ} (source : CounterexamplePack a b c) : False := by
  obtain ⟨m, hm, hE⟩ := initial_state_of_counterexample source
  exact no_state m hm hE

/-- 三端点のgcd=1と七乗方程式から二端点の原始性を回復する。 -/
theorem coprime_of_gcd_triple_eq_one {a b c : ℕ}
    (hgcd : ({a, b, c} : Finset ℕ).gcd id = 1) (he : a ^ 7 + b ^ 7 = c ^ 7) :
    Nat.Coprime a b := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  by_contra hne
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hqa := hqd.trans (Nat.gcd_dvd_left a b)
  have hqb := hqd.trans (Nat.gcd_dvd_right a b)
  have hqc : q ∣ c := by
    apply hq.dvd_of_dvd_pow
    rw [← he]
    exact dvd_add (hqa.trans (dvd_pow_self _ (by decide : 7 ≠ 0)))
      (hqb.trans (dvd_pow_self _ (by decide : 7 ≠ 0)))
  apply hq.not_dvd_one
  rw [← hgcd]
  apply Finset.dvd_gcd_iff.mpr
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact hqa
  · exact hqb
  · exact hqc

/-- **GN七位相降下によるFLT7**。
既存の七次PID・具体的Kummer単元補題を用い、外部FLT終点や降下providerを仮定しない。
自然数の原始性はMathlibのgcd正規化で除去する。 -/
theorem fermatLastTheoremFor_seven : FermatLastTheoremFor 7 := by
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hgcd he
  exact no_counterexample {
    hx := Nat.pos_of_ne_zero ha
    hy := Nat.pos_of_ne_zero hb
    hz := Nat.pos_of_ne_zero hc
    hxy := coprime_of_gcd_triple_eq_one hgcd he
    hEq := he }

/-- 正値引数を用いる自然数版の読みやすい入口。 -/
theorem seventh_sum_ne_seventh {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 7 + b ^ 7 ≠ c ^ 7 :=
  fermatLastTheoremFor_seven a b c (Nat.ne_of_gt ha) (Nat.ne_of_gt hb) (Nat.ne_of_gt hc)

end DkMath.FLT.Kummer.SevenDescent
