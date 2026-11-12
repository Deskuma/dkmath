import DkMath.Lib.NumberTheory.EllipticFiniteKernelGalois
import DkMath.Lib.NumberTheory.EllipticFixedTorsion

#print "file: Note032FiniteKernelBoundary"

/-!
005C₂aの実例。曲線y²=x³−xと実際の有理2捩れ点Q=(1,0)からH={O,Q}を構成する。
次数2、正規化補正1、平行移動・ガロア不変性を同じ関数体で確認する。
-/
namespace EllipticFiniteKernelTest
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation EllipticFunctionField
open WeierstrassCurve WeierstrassCurve.Affine
open scoped BigOperators
noncomputable section
local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

/-- 非特異な具体曲線y²=x³−x。 -/
def curve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

/-- 判別式64から楕円曲線性を供給する。 -/
theorem curve_discriminant : curve.Δ = 64 := by
  norm_num [curve, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]

local instance : curve.IsElliptic := ⟨by rw [curve_discriminant]; norm_num⟩

/-- 基礎体上の実際の点(1,0)。 -/
def rationalQ : curve.toAffine.Point :=
  .some 1 0 (by norm_num [curve, nonsingular_iff', equation_iff])

/-- 同じ有理点を代数閉包へ基底変換する。 -/
def Q : Points curve := baseChangePoint curve rationalQ

local instance : DecidableEq (Points curve) := Classical.decEq _

/-- Qは非零の2捩れ点で、ガロア群がその点自身を固定する。 -/
theorem point_data : Q ≠ 0 ∧ Q + Q = 0 ∧ ∀ σ, pointAction curve σ Q = Q := by
  refine ⟨Point.some_ne_zero _, ?_, fun σ => pointAction_baseChange curve σ rationalQ⟩
  apply Point.add_self_of_Y_eq
  norm_num [curve, negY]

/-- 実点群内の同じ二元部分群。 -/
def kernel : AddSubgroup (Points curve) where
  carrier := {P | P = 0 ∨ P = Q}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro P R hP hR
    rcases hP with rfl | rfl <;> rcases hR with rfl | rfl <;> simp [point_data.2.1]
  neg_mem' := by
    intro P hP
    rcases hP with rfl | rfl
    · exact Or.inl neg_zero
    · exact Or.inr (neg_eq_of_add_eq_zero_left point_data.2.1)

local instance : Fintype kernel :=
  Fintype.ofFinset {0, Q} (fun P => by simp [kernel])

/-- 同じ核の列挙を、実点の部分型の値を保ったまま確定する。 -/
theorem kernel_univ : (Finset.univ : Finset kernel) = {0, ⟨Q, Or.inr rfl⟩} := by
  ext P
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  rcases P.property with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

/-- 二元核上の任意の加法的な有限和を、同じ二つの点で展開する。 -/
theorem sum_kernel {M : Type*} [AddCommMonoid M] (f : kernel → M) :
    (∑ P : kernel, f P) = f 0 + f ⟨Q, Or.inr rfl⟩ := by
  have hn : (0 : kernel) ≠ ⟨Q, Or.inr rfl⟩ := by
    intro he
    exact point_data.1 (congrArg Subtype.val he).symm
  rw [kernel_univ, Finset.sum_pair hn]

/-- 同じ核の位数2と、その固定体に対する関数体の次数2。 -/
theorem degree_two : Nat.card kernel = 2 ∧
    Module.finrank (kernelFixedField curve kernel)
      (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField = 2 := by
  have hc : Nat.card kernel = 2 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, kernel_univ, Finset.card_pair]
    intro he
    exact point_data.1 (congrArg Subtype.val he).symm
  exact ⟨hc, (finrank_kernelFixedField curve kernel).trans hc⟩

/-- 二元核の正規化x座標和には補正定数1が必要である。
一般点は実際の群法で移動し、Oの便宜的な定数座標0は補正和へ寄与しない。 -/
theorem normalized_coordinates :
    veluX curve kernel = genericX curve (AlgebraicClosure ℚ) +
      transEquiv curve (AlgebraicClosure ℚ) Q (genericX curve (AlgebraicClosure ℚ)) - 1 ∧
    veluY curve kernel = genericY curve (AlgebraicClosure ℚ) +
      transEquiv curve (AlgebraicClosure ℚ) Q (genericY curve (AlgebraicClosure ℚ)) := by
  have h0 : transEquiv curve (AlgebraicClosure ℚ) (0 : Points curve) = AlgEquiv.refl :=
    transEquiv_zero curve (AlgebraicClosure ℚ)
  have hx0 : (0 : Points curve).xc = 0 := rfl
  have hy0 : (0 : Points curve).yc = 0 := rfl
  have hxQ : Q.xc = 1 := rfl
  have hyQ : Q.yc = 0 := by
    change algebraMap ℚ (AlgebraicClosure ℚ) (0 : ℚ) = 0
    exact map_zero _
  constructor
  · simp [veluX, kernelTrace, sum_kernel, h0, hx0, hxQ]
  · simp [veluY, kernelTrace, sum_kernel, h0, hy0, hyQ]

/-- 同じ二元核を全ガロア元が保存する。位数pの仮想的な核を入力しない。 -/
theorem kernel_stable : ∀ σ P, P ∈ kernel → pointAction curve σ P ∈ kernel := by
  intro σ P hP
  rcases hP with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (point_data.2.2 σ)

/-- 実際の同じ核の平行移動と係数ガロア作用の双方で、構成済み二関数は不変である。 -/
theorem same_kernel_invariance (σ : Field.absoluteGaloisGroup ℚ) :
    transEquiv curve (AlgebraicClosure ℚ) Q (veluX curve kernel) = veluX curve kernel ∧
    transEquiv curve (AlgebraicClosure ℚ) Q (veluY curve kernel) = veluY curve kernel ∧
    galFunctionFieldEquiv curve σ (veluX curve kernel) = veluX curve kernel ∧
    galFunctionFieldEquiv curve σ (veluY curve kernel) = veluY curve kernel :=
  ⟨veluX_translation curve kernel ⟨Q, Or.inr rfl⟩,
    veluY_translation curve kernel ⟨Q, Or.inr rfl⟩,
    veluX_galois curve kernel kernel_stable σ, veluY_galois curve kernel kernel_stable σ⟩

/-- 総和は平均ではない。二元核の定数1の和は2となる。 -/
theorem trace_not_average : kernelTrace curve kernel 1 = 2 ∧
    kernelTrace curve kernel 1 ≠ 1 := by
  have h : kernelTrace curve kernel 1 = 2 := by
    simp [kernelTrace, ← Nat.card_eq_fintype_card, degree_two.1]
  refine ⟨h, ?_⟩
  rw [h]
  intro he
  have hc : (2 : AlgebraicClosure ℚ) ≠ 1 := by norm_num
  apply hc
  apply (algebraMap (AlgebraicClosure ℚ) (curve.toAffine⁄(AlgebraicClosure ℚ)).FunctionField).injective
  simpa only [map_ofNat, map_one] using he

/-- 自明核なら正規化座標和は元の一般座標に戻る。 -/
theorem trivial_kernel :
    letI : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
    veluX curve ⊥ = genericX curve (AlgebraicClosure ℚ) ∧
      veluY curve ⊥ = genericY curve (AlgebraicClosure ℚ) := by
  let : Fintype (⊥ : AddSubgroup (Points curve)) := Fintype.ofFinite _
  have hd : ((default : (⊥ : AddSubgroup (Points curve))) : Points curve) = 0 :=
    (default : (⊥ : AddSubgroup (Points curve))).property
  have h0 : transEquiv curve (AlgebraicClosure ℚ) (0 : Points curve) = AlgEquiv.refl :=
    transEquiv_zero curve (AlgebraicClosure ℚ)
  have hx0 : (0 : Points curve).xc = 0 := rfl
  have hy0 : (0 : Points curve).yc = 0 := rfl
  constructor <;> simp [veluX, veluY, kernelTrace, hd, h0, hx0, hy0]

end
end EllipticFiniteKernelTest
