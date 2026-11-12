/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTorsionAllCard
import DkMathTest.FLT.FreyResidualRepresentation

#print "file: DkMathTest.FLT.FreyTorsionAllCard"

/-!
# NOTE-019: 合成数・素数冪・同変な短完全列と全射性の必要性

実在するSource 2の曲線でE[4], E[36], E[37²]を調べる。6と6は互いに素ではないが、
E[6]→E[36]→E[6]は有限短完全列をなす。全射性を省けないことは、可除でない群ZMod 2で
同じ制限写像が全射でなくなる反例で検査する。Weil対や仮想Source 37は必要としない。
-/
namespace FreyTorsionAllCardTest
open DkMath.Lib.Algebra
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open FreyResidualRepresentationTest
local instance : sample.rationalCurve.IsElliptic := sample.rationalCurve_isElliptic

/-- 帰納法の単位元。1-torsionには零点だけがある。 -/
theorem actual1_card : Nat.card (Torsion sample.rationalCurve 1) = 1 := card_torsion_one _

/-- 以前は下界16だけだった合成数4の位数が、ちょうど16に確定する。 -/
theorem actual4_card : Nat.card (Torsion sample.rationalCurve 4) = 16 :=
  card_torsion_sq _ 4 (by decide)

/-- 複数の素因子を持つ合成数にも一般の位数公式を適用する。 -/
theorem actual36_card : Nat.card (Torsion sample.rationalCurve 36) = 1296 :=
  sample.curve_torsion_card_sq 36 (by decide)

/-- 同じ実在する曲線の37²-torsion。pの一次だけの定理に留まらない。 -/
theorem actual37square_card : Nat.card (Torsion sample.rationalCurve (37 ^ 2)) = 1874161 :=
  card_torsion_pow _ 37 2 (by decide)

/-- 冪指数0はE[1]へ戻る。 -/
theorem actual37pow_zero : Nat.card (Torsion sample.rationalCurve (37 ^ 0)) = 1 :=
  card_torsion_pow _ 37 0 (by decide)

/-- 標準torsionBy表示も同じ位数16を保持する。 -/
theorem standard4_card : Nat.card (StandardTorsion sample.rationalCurve 4) = 16 :=
  card_standardTorsion_sq _ 4 (by decide)

/-- 6と6が互いに素でないことを明示する。 -/
theorem six_six_not_coprime : ¬ Nat.Coprime 6 6 := by decide

/-- 互いに素でない因子でも、同じ実際の点群の有限短完全列が得られる。 -/
theorem actual6_6_short_exact :
    Finite (Torsion sample.rationalCurve (6 * 6)) ∧
      Function.Injective (torsionInclusion sample.rationalCurve 6 6) ∧
      Function.Exact (torsionInclusion sample.rationalCurve 6 6) (torsionMultiply sample.rationalCurve 6 6) ∧
      Function.Surjective (torsionMultiply sample.rationalCurve 6 6) :=
  sample.curve_torsion_finite_short_exact 6 6 (by decide) (by decide)

/-- 制限写像の核はE[6]と同型なので、その位数は36である。 -/
theorem actual6_6_kernel_card : Nat.card (torsionMultiply sample.rationalCurve 6 6).ker = 36 := by
  rw [← Nat.card_congr (torsionMultiplyKernelEquiv sample.rationalCurve 6 6).toEquiv]
  exact card_torsion_sq _ 6 (by decide)

/-- 商は同じ曲線のE[6]になる。商・核の乗法性の経路を確認する。 -/
theorem actual6_6_quotient_card :
    Nat.card (Torsion sample.rationalCurve (6 * 6) ⧸ (torsionMultiply sample.rationalCurve 6 6).ker) = 36 := by
  have h : Nat.card (Torsion sample.rationalCurve (6 * 6) ⧸
      (torsionMultiply sample.rationalCurve 6 6).ker) = Nat.card (Torsion sample.rationalCurve 6) :=
    Nat.card_congr (TorsionMultiplication.quotientEquiv (Points sample.rationalCurve) 6 6
      (multiplication_surjective sample.rationalCurve 6 (by decide))).toEquiv
  exact h.trans (card_torsion_sq _ 6 (by decide))

/-- 端の1を含む制限写像も短完全列をなす。 -/
theorem actual1_4_short_exact :
    Function.Injective (torsionInclusion sample.rationalCurve 1 4) ∧
      Function.Exact (torsionInclusion sample.rationalCurve 1 4) (torsionMultiply sample.rationalCurve 1 4) ∧
      Function.Surjective (torsionMultiply sample.rationalCurve 1 4) :=
  torsion_short_exact _ 1 4 (by decide)

/-- 列の完全性だけなら右因子0も扱える。全射性とは区別する。 -/
theorem zero_factor_exact_pair :
    Function.Exact (torsionInclusion sample.rationalCurve 6 0) (torsionMultiply sample.rationalCurve 6 0) :=
  torsion_exact_pair _ 6 0

/-- 同じ実際の点に対する包含はガロア作用と可換する。 -/
theorem actual6_6_inclusion_equivariant (σ : Field.absoluteGaloisGroup ℚ)
    (P : Torsion sample.rationalCurve 6) :
    torsionInclusion sample.rationalCurve 6 6 (representation sample.rationalCurve 6 σ P) =
      representation sample.rationalCurve (6 * 6) σ (torsionInclusion sample.rationalCurve 6 6 P) :=
  torsionInclusion_equivariant _ _ _ σ P

/-- 制限倍写像も同じ作用を保つ。 -/
theorem actual6_6_multiply_equivariant (σ : Field.absoluteGaloisGroup ℚ)
    (P : Torsion sample.rationalCurve (6 * 6)) :
    torsionMultiply sample.rationalCurve 6 6 (representation sample.rationalCurve (6 * 6) σ P) =
      representation sample.rationalCurve 6 σ (torsionMultiply sample.rationalCurve 6 6 P) :=
  torsionMultiply_equivariant _ _ _ σ P

/-- 可除性を持たない群では、完全な組でも右側の全射性は出ない。
ZMod 2上の2倍写像は零なので、標的の非零元1を像に持たない。 -/
theorem nondivisible_multiply_not_surjective :
    ¬ Function.Surjective (TorsionMultiplication.multiply (ZMod 2) 2 2) := by
  intro h
  let q : TorsionMultiplication.Kernel (ZMod 2) 2 := ⟨1, by
    change 2 • (1 : ZMod 2) = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]⟩
  obtain ⟨x, hx⟩ := h q
  have hv := congrArg (fun z : TorsionMultiplication.Kernel (ZMod 2) 2 => z.val) hx
  change 2 • x.val = (1 : ZMod 2) at hv
  have hz : 2 • x.val = (0 : ZMod 2) := by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  exact (by decide : (1 : ZMod 2) ≠ 0) (hv.symm.trans hz)

/-- 位数と有限レベルを同じ実在する曲線の合成数指数で同時に得る。 -/
theorem actual36_card_finite_level :
    Nat.card (Torsion sample.rationalCurve 36) = 36 ^ 2 ∧ FactorsThroughFiniteLevel sample.rationalCurve 36 :=
  sample.curve_torsion_card_finite_level 36 (by decide)

/-- 任意のSource 37からも、torsion指数nの素数性を仮定せず一般公式を供給する。 -/
theorem source37_all_card (S : DkMath.FLT.Frey.Source 37) (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion S.rationalCurve n) = n ^ 2 := S.curve_torsion_card_sq n hn

end FreyTorsionAllCardTest
