/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDyadicBranchSwap
import DkMath.Lib.NumberTheory.ValuationPrimeExistence

#print "file: DkMath.FLT.FreyModEightIrreducibility"

/-!
# NOTE-032-004: 3側の直接hnoと既約性の公開入口

032-003Cの局所定理は、指定した任意の2上の付値環で成立する。
本章では標数0の体上の住所の存在を内部供給し、公開終点からA,hAを取り除く。
残る入力は同じSource、素数p≥5、a≡3 mod8である。

証明は、同じE[p]上の慣性変化量のE₀[p]への吸収、非自明慣性、
Frobeniusによる商上の符号反転を使う。Cofixed直線があれば、
非自明な慣性変化量からその直線はE₀[p]に含まれる。
外側の点の商ではCofixed性が+1、枝交換が−1を与え、奇素数pでは矛盾する。
既約性への接続には031-005の同じSourceの大域二択と有理捩れ排除を使う。

mod4の向き付けからはa≡3,7 mod8が残る。今回の3側の排除により、
可約性を仮定した同じ向き付きSourceは7側に属する。
この最後の文は可約性の仮定下の絞込みであり、7側の存在・排除を意味しない。
整数反例の入口では、共通因子を保持したPrimitiveReductionとOrientationTraceも残す。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeExistence ValuationFrobenius
open EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 2上の住所と同じ点群上の枝交換元を同時に構成する。
任意のFrobeniusの存在だけでなく、その同じ元で全ての外側の点の和がE₀[p]に入る。 -/
theorem residual_exists_dyadic_frobenius_branch_swap_of_a_mod_eight
    (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 2 ∧
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), IsFrobeniusAt A σ 2 ∧
        ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
          HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val := by
  obtain ⟨A, hA⟩ := exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_two
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  exact ⟨A, hA, σ, hσ, S.residual_frobenius_branch_swap_of_a_mod_eight hp5 ha8 A hA hσ⟩

/-- 3側の直接hno。住所・中心・方向・外側の点・非自明慣性・枝交換は内部供給する。
素数性、p≥5、a≡3 mod8を保ち、一般のCofixed直線排除とは区別する。 -/
theorem residual_no_cofixed_line_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L := by
  obtain ⟨A, hA⟩ := exists_liesOverPrime (L := AlgebraicClosure ℚ) Nat.prime_two
  exact S.residual_no_cofixed_line_of_a_mod_eight_at_two hp5 ha8 A hA

/-- 3側の同じFrey残余表現は既約。b偶数は合同条件と正規化から供給済み。
既存の大域分類へ上の直接hnoを渡すので、hcasesやhnoを外部仮定にしない。 -/
theorem residual_isIrreducible_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction hp5 (S.b_even_of_a_mod_eight ha8)
    (S.residual_no_cofixed_line_of_a_mod_eight hp5 ha8)

/-- 同じSourceにおける全ガロア安定直線の不存在。
既存の次元2の判定基準で、座標や曲線を変更せず既約性を言い換える。 -/
theorem residual_no_stable_line_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L :=
  S.residual_isIrreducible_iff_no_stable_line.mp (S.residual_isIrreducible_of_a_mod_eight hp5 ha8)

/-- 向き付きSourceが可約なら、未解決の7側に限られる。
mod4だけで3側を選べず、可約性から7側の実例を構成したとも主張しない。 -/
theorem residual_a_mod_eight_eq_seven_of_not_irreducible (hp5 : 5 ≤ p)
    (ha4 : (4 : ℤ) ∣ S.a + 1) (hred : ¬ S.ResidualIsIrreducible) : S.a % 8 = 7 := by
  rcases S.a_mod_eight_cases_of_oriented ha4 with h3 | h7
  · exact (hred (S.residual_isIrreducible_of_a_mod_eight hp5 h3)).elim
  · exact h7

/-- 非零整数反例から選んだ同じSourceは、既約であるか7側に属する。
元との共通因子・符号付き置換の証拠を結論へ残す。反例の存在や一般FLTを証明しない。 -/
theorem ofCounterexample_residual_irreducible_or_seven (hp5 : 5 ≤ p)
    (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (he : a ^ p + b ^ p = c ^ p) :
    let S := Source.ofCounterexample p Fact.out hp5 a b c ha hb hc he
    4 ∣ S.a + 1 ∧ Even S.b ∧
      (∃ R : PrimitiveReduction p a b c, OrientationTrace R.A R.B R.C S.a S.b S.c) ∧
      (S.ResidualIsIrreducible ∨ S.a % 8 = 7) := by
  classical
  let S := Source.ofCounterexample p Fact.out hp5 a b c ha hb hc he
  obtain ⟨ha4, hbe, htrace⟩ := Source.ofCounterexample_spec p Fact.out hp5 a b c ha hb hc he
  refine ⟨ha4, hbe, htrace, ?_⟩
  by_cases hirr : S.ResidualIsIrreducible
  · exact Or.inl hirr
  · exact Or.inr (S.residual_a_mod_eight_eq_seven_of_not_irreducible hp5 ha4 hirr)

end DkMath.FLT.Frey.Source
