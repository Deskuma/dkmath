/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyHnoSmallGoodPrime
import DkMath.FLT.Five.Main
import DkMath.FLT.Kummer.SevenGNDescent
import DkMath.FLT.Kummer.ElevenThirteenFLT

#print "file: DkMath.FLT.FreyHnoSmallIndex"

/-!
# 小指数を既存の FLT から除く

この章の論理の向きは **既存 FLT → Source の不存在 → hno** である。
残余表現の既約性からこれらの FLT を証明する経路へ、この章を戻してはならない。
低層の Frey・Kummer・FLT5 の証明は本章を import しない。

まず、正の自然数について完成済みの FLT5 を標準 `FermatLastTheoremFor 5`
へ接続する。Mathlib の整数版同値は符号を処理するため、`Source` の座標を
正と仮定したり、`natAbs` を方程式へ無条件に適用したりする必要はない。
次に FLT7/11/13 の既存終点と合流し、小指数の Source 自体を排除する。
-/

namespace DkMath.FLT.Five

/-- 正の自然数での完成済み FLT5 を Mathlib の標準述語へ接続する。 -/
theorem fermatLastTheoremFor_five : FermatLastTheoremFor 5 := by
  intro a b c ha hb hc he
  exact fermatFive_no_positive_solution a b c
    (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc) he

end DkMath.FLT.Five

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.RepresentationTheory

/-- 同じ指数の標準 FLT が成立すれば、非零整数解を持つ Source は存在しない。
原始性や向き付けを弱めず、Source の既存方程式に整数版 FLT を適用する。 -/
theorem false_of_fermatLastTheoremFor {p : ℕ} (S : Source p)
    (hFLT : FermatLastTheoremFor p) : False :=
  (fermatLastTheoremFor_iff_int.mp hFLT) S.a S.b S.c S.a_ne S.b_ne S.c_ne S.equation

/-- 完成済み FLT5/7/11/13 による小指数 Source の排除。 -/
theorem false_of_small_prime_index {p : ℕ} (S : Source p)
    (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13) : False := by
  rcases hp with rfl | rfl | rfl | rfl
  · exact S.false_of_fermatLastTheoremFor Five.fermatLastTheoremFor_five
  · exact S.false_of_fermatLastTheoremFor Kummer.SevenDescent.fermatLastTheoremFor_seven
  · exact S.false_of_fermatLastTheoremFor Kummer.fermatLastTheoremFor_eleven
  · exact S.false_of_fermatLastTheoremFor Kummer.fermatLastTheoremFor_thirteen

/-- 素数指数が5以上なら、小指数の既存 FLT により残る Source は17以上。
これは Source が与えられた場合の必要条件であり、Source の存在を主張しない。 -/
theorem seventeen_le_of_five_le {p : ℕ} [Fact p.Prime] (S : Source p)
    (hp5 : 5 ≤ p) : 17 ≤ p := by
  by_contra hp17
  have hp : p.Prime := Fact.out
  interval_cases p <;> norm_num at hp <;>
    exact S.false_of_small_prime_index (by simp)

/-- 小指数の `hno`。証明は残余表現の算術ではなく Source の不存在による。 -/
theorem residual_hno_of_small_prime_index {p : ℕ} [Fact p.Prime] (S : Source p)
    (hp : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L := by
  exact (S.false_of_small_prime_index hp).elim

end DkMath.FLT.Frey.Source
