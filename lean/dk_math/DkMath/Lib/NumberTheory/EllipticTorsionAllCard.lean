/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.TorsionMultiplication
import DkMath.Lib.NumberTheory.EllipticMultiplicationSurjective
import Mathlib.Data.Nat.Factorization.Induction

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionAllCard"

/-!
# 全ての正整数nに対する実際のねじれ点の位数n²

既存のTorsion E nは代数閉包上の実際の点群のn倍写像の核である。
一般の可換群の短完全列を同じ点群へ適用し、証明済みの倍写像全射性を供給する。
E[n]→E[mn]→E[m]はガロア作用とも可換であり、形式的な別の有限群へ置き換えない。
この列の濃度公式は互いに素性を要求しないので、素数の位数p²と乗法的帰納法だけで
全ての非零nの位数n²を得る。Weil対・円分行列式・Tate加群の自由性は必要としない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 同じ点を保持するE[n]→E[mn]の包含。 -/
noncomputable def torsionInclusion (m n : ℕ) : Torsion E n →+ Torsion E (m * n) :=
  TorsionMultiplication.inclusion (Points E) m n

/-- 実際の点のn倍を取るE[mn]→E[m]。 -/
noncomputable def torsionMultiply (m n : ℕ) : Torsion E (m * n) →+ Torsion E m :=
  TorsionMultiplication.multiply (Points E) m n

/-- 制限倍写像の核と実際のE[n]との加法同型。 -/
noncomputable def torsionMultiplyKernelEquiv (m n : ℕ) :
    Torsion E n ≃+ (torsionMultiply E m n).ker :=
  TorsionMultiplication.kernelEquiv (Points E) m n

/-- 完全性自体には楕円曲線性も非零指数も不要である。 -/
theorem torsion_exact_pair (m n : ℕ) :
    Function.Exact (torsionInclusion E m n) (torsionMultiply E m n) :=
  TorsionMultiplication.exact_pair (Points E) m n

/-- 自然な包含は、既存の点へのガロア作用を保つ。 -/
theorem torsionInclusion_equivariant (m n : ℕ) (σ : Field.absoluteGaloisGroup K) (P : Torsion E n) :
    torsionInclusion E m n (representation E n σ P) =
      representation E (m * n) σ (torsionInclusion E m n P) := by
  apply Subtype.ext
  rfl

/-- 制限倍写像も同じガロア作用と可換する。 -/
theorem torsionMultiply_equivariant (m n : ℕ) (σ : Field.absoluteGaloisGroup K)
    (P : Torsion E (m * n)) :
    torsionMultiply E m n (representation E (m * n) σ P) =
      representation E m σ (torsionMultiply E m n P) := by
  apply Subtype.ext
  change n • pointAction E σ P.val = pointAction E σ (n • P.val)
  exact (map_nsmul (pointAction E σ) n P.val).symm

variable [CharZero K] [E.IsElliptic]

/-- 全射な倍写像を供給して短完全列を得る。m=0も許すが、有限群として使うにはm≠0が必要。 -/
theorem torsion_short_exact (m n : ℕ) (hn : n ≠ 0) :
    Function.Injective (torsionInclusion E m n) ∧
      Function.Exact (torsionInclusion E m n) (torsionMultiply E m n) ∧
      Function.Surjective (torsionMultiply E m n) :=
  TorsionMultiplication.short_exact (Points E) m n (multiplication_surjective E n hn)

/-- 非零のm,nでは中央も有限であり、有限群の短完全列として位数を取れる。 -/
theorem torsion_finite_short_exact (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    Finite (Torsion E (m * n)) ∧ Function.Injective (torsionInclusion E m n) ∧
      Function.Exact (torsionInclusion E m n) (torsionMultiply E m n) ∧
      Function.Surjective (torsionMultiply E m n) :=
  ⟨finite_torsion_of_ne_zero E (m * n) (mul_ne_zero hm hn), torsion_short_exact E m n hn⟩

/-- 濃度の乗法性。互いに素性は不要で、右因子が非零なら一般のNat.card公式が使える。
両因子が非零なら既存の幾何学的有限性により通常の有限群の位数公式になる。 -/
theorem card_torsion_mul (m n : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion E (m * n)) = Nat.card (Torsion E m) * Nat.card (Torsion E n) :=
  TorsionMultiplication.card_mul (Points E) m n (multiplication_surjective E n hn)

omit [CharZero K] [E.IsElliptic] in
/-- 1倍写像の核には零点だけがある。帰納法の単位元の場合。 -/
theorem card_torsion_one : Nat.card (Torsion E 1) = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨0, torsion_one_eq_zero E⟩

/-- 全ての正整数指数の無条件の位数公式。素数の幾何学的位数公式と短完全列を結ぶ。
n=0は点群全体の核になるため、この定理の対象から明示的に除く。 -/
theorem card_torsion_sq (n : ℕ) (hn : n ≠ 0) : Nat.card (Torsion E n) = n ^ 2 := by
  revert hn
  refine Nat.recOnMul ?_ ?_ ?_ ?_ n
  · intro h
    exact (h rfl).elim
  · intro _
    simpa only [one_pow] using card_torsion_one E
  · intro p hp _
    have : Fact p.Prime := ⟨hp⟩
    exact card_torsion_prime_sq E p
  · intro a b ha hb hab
    have ha0 := (mul_ne_zero_iff.mp hab).1
    have hb0 := (mul_ne_zero_iff.mp hab).2
    rw [card_torsion_mul E a b hb0, ha ha0, hb hb0, mul_pow]

/-- 素数冪にも同じ公式を適用できる。pに限らず非零底の自然数冪を許す。 -/
theorem card_torsion_pow (n k : ℕ) (hn : n ≠ 0) :
    Nat.card (Torsion E (n ^ k)) = n ^ (2 * k) := by
  rw [card_torsion_sq E _ (pow_ne_zero _ hn), ← pow_mul, Nat.mul_comm k 2]

/-- 標準torsionBy表示にも、同じ点を保持する加法同型で全指数の位数を運ぶ。 -/
theorem card_standardTorsion_sq (n : ℕ) (hn : n ≠ 0) :
    Nat.card (StandardTorsion E n) = n ^ 2 := by
  rw [← Nat.card_congr (torsionByLinearEquiv E n).toEquiv]
  exact card_torsion_sq E n hn

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
