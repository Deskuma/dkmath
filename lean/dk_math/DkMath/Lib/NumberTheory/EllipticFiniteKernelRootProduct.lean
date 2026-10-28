/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.Lib.NumberTheory.EllipticFiniteKernelDepthProduct
import DkMath.Lib.NumberTheory.EllipticFiniteKernelRationalFiber
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantRoots
import DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelRootProduct"

/-!
# 奇数核の接線分母と2捩れ三根

[DkMath.Lib] 幾何学的点群の同じ半核について、接線分母の積を2捩れ三根への
距離の積に分解する。奇数位数の核では半核点は2捩れでないので、各因子は非零。
この恒等式は局所付値や商判別式の積公式を仮定しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open EllipticFunctionField EllipticTorsionRepresentation WeierstrassDiscriminantRoots
open DkMath.Lib.Algebra.RationalPolynomialFiber
open DkMath.Lib.NumberTheory.WeierstrassDiscriminantAssembly
open scoped BigOperators
noncomputable local instance instDecidableEqEllipticFiniteKernelRootProduct {α : Type*} : DecidableEq α := Classical.decEq _

variable {K : Type*} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  (H : AddSubgroup (Points E)) [Fintype H]

omit [CharZero K] [E.IsElliptic] [Fintype H] in
/-- [DkMath.Lib] 奇数位数の核の非零点の接線式は非零である。
零なら反転固定点となり、奇数位数の核に非零2捩れが生じる。 -/
theorem odd_kernel_tangent_ne_zero (ho : Odd (Nat.card H)) (Q : H) (hQ : Q ≠ 0) :
    2 * Q.val.yc + (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃ ≠ 0 := by
  intro h
  have hQ0 : Q.val ≠ 0 := fun hz => hQ (Subtype.ext hz)
  have hf := point_neg_eq_of_tangent_zero (E.map (algebraMap K (AlgebraicClosure K))) Q.val hQ0 h
  exact neg_ne_self_of_odd_kernel E H ho Q hQ (Subtype.ext hf)

omit [E.IsElliptic] in
/-- [DkMath.Lib] 半核の実際の接線分母の積は、三根それぞれへの距離の積と4の冪に分かれる。
根は源曲線の2捩れ三次式の根であり、商側の根ではない。 -/
theorem half_tangent_product_eq_root_products (r₁ r₂ r₃ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) :
    (∏ Q : halfKernel E H, (2 * Q.val.val.yc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₁ * Q.val.val.xc +
      (E.map (algebraMap K (AlgebraicClosure K))).a₃) ^ 2) =
      (4 : AlgebraicClosure K) ^ (halfKernel E H).card *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₁)) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₂)) *
        (∏ Q : halfKernel E H, (Q.val.val.xc - r₃)) := by
  have hpoint (Q : halfKernel E H) : Q.val.val ≠ 0 :=
    fun hz => ((mem_halfKernel E H Q.val).mp Q.property).1 (Subtype.ext hz)
  calc
    _ = ∏ Q : halfKernel E H, (4 : AlgebraicClosure K) * (Q.val.val.xc - r₁) *
        (Q.val.val.xc - r₂) * (Q.val.val.xc - r₃) := by
      apply Finset.prod_congr rfl
      intro Q _
      exact tangent_square_eq_root_product _ (by norm_num) r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
        _ _ (Point.nonsingular_xc_yc (hpoint Q)).1
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_coe]

omit [E.IsElliptic] in
/-- [DkMath.Lib] 奇数核の半核点のx座標は、源曲線の2捩れ三根のいずれとも一致しない。
ここで必要な非零性は、接線分母が非零であることと三根分解から得られる。 -/
theorem half_x_sub_root_ne_zero (ho : Odd (Nat.card H)) (r₁ r₂ r₃ : AlgebraicClosure K)
    (h₁ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₁ = 0)
    (h₂ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₂ = 0)
    (h₃ : (E.map (algebraMap K (AlgebraicClosure K))).twoTorsionPolynomial.toPoly.eval r₃ = 0)
    (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) (Q : halfKernel E H) :
    Q.val.val.xc - r₁ ≠ 0 ∧ Q.val.val.xc - r₂ ≠ 0 ∧ Q.val.val.xc - r₃ ≠ 0 := by
  have hQ : Q.val ≠ 0 := ((mem_halfKernel E H Q.val).mp Q.property).1
  have hQ0 : Q.val.val ≠ 0 := fun hz => hQ (Subtype.ext hz)
  have ht := odd_kernel_tangent_ne_zero E H ho Q.val hQ
  have hf := tangent_square_eq_root_product (E.map (algebraMap K (AlgebraicClosure K)))
    (by norm_num) r₁ r₂ r₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ _ _
    (Point.nonsingular_xc_yc hQ0).1
  have hn : 4 * (Q.val.val.xc - r₁) * (Q.val.val.xc - r₂) *
      (Q.val.val.xc - r₃) ≠ 0 := by rw [← hf]; exact pow_ne_zero _ ht
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2, (mul_ne_zero_iff.mp hn).2⟩

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 半核を添字にしたファイバー因子の次数は、元の核の位数に一致する。

`fiberFactor` は一本の単純根と半核各点の二重根から作るため、次数は
`2 * |halfKernel| + 1` である。半核分割公式をここで接続すると、
実際の奇数核の有限ファイバーに期待される次数 `|H|` を得る。 -/
theorem halfKernel_fiberFactor_natDegree (ho : Odd (Nat.card H))
    (e : AlgebraicClosure K) (ξ : halfKernel E H → AlgebraicClosure K) :
    (fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ).natDegree = Nat.card H := by
  rw [fiberFactor_natDegree]
  have hc := card_halfKernel E H ho
  rw [Finset.card_univ, Fintype.card_coe]
  omega

/-- [DkMath.Lib] 半核の各添字を明示した二捩れ根輸送。

`halfKernel` は反転対から一方だけを選ぶ有限集合である。ここではその選択を
隠さず、各 `Q : halfKernel E H` について `P + Q` の特殊化座標が標的
二捩れ多項式の根になることを直接記録する。これは `fiberFactor` の根包含を
作る幾何学側の入力であり、二重根（多重度）の主張は別の層に残す。 -/
theorem kernelAt_twoTorsion_root_halfKernel
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (Q : halfKernel E H) :
    (kernelModel E H).twoTorsionPolynomial.toPoly.eval
      (kernelXAt E H (P + Q.val.val)
        (add_not_mem_kernel E H P hP Q.val)) = 0 := by
  exact kernelAt_twoTorsion_root_translation E H P hP hneg Q.val

omit [CharZero K] in
/-- [DkMath.Lib] 反転固定点の核軌道は、半核添字の反転にも不変である。

`P=-P` と既存の `kernelXAt_neg` を組み合わせると、`P+(-Q)` と `P+Q`
の特殊化 x 値が一致する。これは幾何学的な反転対を、有限積定理が要求する
`ξ(-Q)=ξ(Q)` の形へ直接変換する橋である。 -/
theorem kernelXAt_neg_translation_eq
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : H) :
    kernelXAt E H (P + (-Q).val)
        (add_not_mem_kernel E H P hP (-Q)) =
      kernelXAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q) := by
  have hR : -(P + (-Q).val) = P + Q.val := by
    calc
      -(P + (-Q).val) = -P + -(-Q).val := by abel
      _ = P + Q.val := by rw [hneg]; simp
  have h := kernelXAt_neg E H (P + (-Q).val)
    (add_not_mem_kernel E H P hP (-Q))
  simpa only [hR] using h.symm

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 反転不変な有限ファイバーの全核因子は、無限遠点の根と
半核因子の平方へ分解する。

`hneg` は `ξ(-Q)=ξ(Q)` という幾何学的な反転不変性だけを入力に取る。
半核分割を有限積へ写すことで、各半核根が全核側では二重に現れることを
多項式恒等式として記録する。`kernelXAt` の分子へ適用する際には、
`ξ Q = kernelXAt (P + Q)` と置き、先に根の多重度をこの形へ供給する。 -/
theorem fullKernel_factor_eq_root_and_half_square
    (ho : Odd (Nat.card H)) (ξ : H → AlgebraicClosure K)
    (hneg : ∀ Q : H, ξ (-Q) = ξ Q) :
    (∏ Q : H, (Polynomial.X - Polynomial.C (ξ Q))) =
      (Polynomial.X - Polynomial.C (ξ 0)) *
        (∏ Q ∈ halfKernel E H, (Polynomial.X - Polynomial.C (ξ Q))) ^ 2 := by
  classical
  obtain ⟨hu, hd⟩ := halfKernel_partition E H ho
  let f : H → Polynomial (AlgebraicClosure K) :=
    fun Q => Polynomial.X - Polynomial.C (ξ Q)
  have hprod : (∏ Q : H, f Q) = f 0 * ∏ Q ∈ (Finset.univ : Finset H).erase 0, f Q := by
    rw [← Finset.prod_erase_mul (Finset.univ : Finset H) f (Finset.mem_univ 0)]
    ac_rfl
  calc
    (∏ Q : H, (Polynomial.X - Polynomial.C (ξ Q))) =
        f 0 * ∏ Q ∈ (Finset.univ : Finset H).erase 0, f Q := hprod
    _ = f 0 * ((∏ Q ∈ halfKernel E H, f Q) *
        (∏ Q ∈ (halfKernel E H).image Neg.neg, f Q)) := by
      rw [← hu, Finset.prod_union hd]
    _ = f 0 * (∏ Q ∈ halfKernel E H, f Q) ^ 2 := by
      have himage :
          (∏ Q ∈ (halfKernel E H).image Neg.neg, f Q) =
            ∏ Q ∈ halfKernel E H, f Q := by
        rw [Finset.prod_image]
        · apply Finset.prod_congr rfl
          intro Q hQ
          simp only [f, hneg]
        · exact neg_injective.injOn
      rw [himage]
      ring
    _ = (Polynomial.X - Polynomial.C (ξ 0)) *
        (∏ Q ∈ halfKernel E H, (Polynomial.X - Polynomial.C (ξ Q))) ^ 2 := by
      rfl

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 反転固定点の x 軌道積を、単純根と半核積の平方へ分解する。

`ξ Q = (P + Q).xc` と置いた全核積分解の幾何学的特殊化である。`P=-P` なら
`P+(-Q)=-(P+Q)` なので x 座標は反転で変わらず、半核の各 x 根が全核側で
二重に現れる。これは `kernelXAt=c` の有限ファイバー分子を組み立てる際に、
根の重複度を明示的に供給するための直接の入口である。 -/
theorem orbit_x_factor_eq_root_and_half_square
    (ho : Odd (Nat.card H)) (P : Points E) (hneg : -P = P) :
    (∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val : Points E).xc))) =
      (Polynomial.X - Polynomial.C P.xc) *
        (∏ Q ∈ halfKernel E H,
          (Polynomial.X - Polynomial.C ((P + Q.val : Points E).xc))) ^ 2 := by
  let ξ : H → AlgebraicClosure K := fun Q => (P + Q.val : Points E).xc
  have hξ : ∀ Q : H, ξ (-Q) = ξ Q := by
    intro Q
    have hsum : -(P + Q.val) = P + (-Q).val := by
      calc
        -(P + Q.val) = -P + -Q.val := by abel
        _ = P + (-Q).val := by rw [hneg, AddSubgroup.coe_neg]
    dsimp [ξ]
    have hcoord :
        (P + (-Q).val : Points E).xc = (P + Q.val).xc := by
      calc
        (P + (-Q).val : Points E).xc = (-(P + Q.val)).xc := by rw [hsum]
        _ = (P + Q.val).xc := by
          cases hR : (P + Q.val : Points E) <;> rfl
    simpa only [AddSubgroup.coe_neg] using hcoord
  have hfactor := fullKernel_factor_eq_root_and_half_square E H ho ξ hξ
  have hzero : ξ 0 = P.xc := by
    dsimp [ξ]
    simp only [add_zero]
  simpa only [ξ, hzero] using hfactor

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 核外の反転固定点から半核への x 軌道は単射である。

`x(P+Q)=x(P+R)` なら、有限点の x 座標判定により
`P+Q=P+R` または `P+Q=-(P+R)` となる。前者は `Q=R` を与え、後者は
`Q=-R` を与えるが、半核が反転対を一方だけ選ぶことに反する。従って、
`fiberFactor` の半核根は添字の衝突なしに扱える。 -/
theorem orbit_x_injective_on_halfKernel
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) :
    Function.Injective (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  intro Q R hQR
  have hQ0 : P + Q.val.val ≠ 0 := by
    intro hz
    exact hP (by
      rw [eq_neg_of_add_eq_zero_left hz]
      exact H.neg_mem Q.val.property)
  have hR0 : P + R.val.val ≠ 0 := by
    intro hz
    exact hP (by
      rw [eq_neg_of_add_eq_zero_left hz]
      exact H.neg_mem R.val.property)
  rcases point_eq_or_eq_neg_of_xc_eq E (P + Q.val.val) (P + R.val.val)
      hQ0 hR0 hQR with hsame | hneg'
  · apply Subtype.ext
    apply Subtype.ext
    exact add_left_cancel hsame
  · have hQRneg : Q.val.val = -R.val.val := by
      calc
        Q.val.val = (P + Q.val.val) - P := by abel
        _ = (-(P + R.val.val)) - P := by rw [hneg']
        _ = -P - R.val.val - P := by rw [neg_add]; abel
        _ = -R.val.val := by rw [hneg]; abel
    have hQRneg' : Q.val = -R.val := by
      apply Subtype.ext
      exact hQRneg
    have hmem : -Q.val ∈ halfKernel E H := by
      rw [hQRneg', neg_neg]
      exact R.property
    exact (neg_not_mem_halfKernel E H Q.val Q.property hmem).elim

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 単純根 `P.xc` は半核軌道の x 根とは衝突しない。

`P` 自身と `P+Q` の x 座標が等しければ、二点判定から両者が等しいか
反転関係にある。`P=-P` を使うと、どちらの場合も `Q=0` に帰着するが、
半核は零元を含まない。この補題は `fiberFactor` の単純根と二重根の分離を
実座標側で供給する。 -/
theorem orbit_x_root_ne_halfKernel
    (P : Points E) (hP : P ∉ H) (hneg : -P = P) (Q : halfKernel E H) :
    P.xc ≠ (P + Q.val.val).xc := by
  intro hxe
  have hP0 : P ≠ 0 := fun hz => hP (hz ▸ H.zero_mem)
  have hPQ0 : P + Q.val.val ≠ 0 := by
    intro hz
    exact hP (by
      rw [eq_neg_of_add_eq_zero_left hz]
      exact H.neg_mem Q.val.property)
  rcases point_eq_or_eq_neg_of_xc_eq E P (P + Q.val.val) hP0 hPQ0 hxe with heq | hneg'
  · have hz : Q.val.val = 0 := by
      calc
        Q.val.val = (P + Q.val.val) - P := by abel
        _ = P - P := by rw [← heq]
        _ = 0 := by abel
    exact ((mem_halfKernel E H Q.val).mp Q.property).1 (Subtype.ext hz)
  · have hz : Q.val.val = 0 := by
      have hsum : P + Q.val.val = -P := by
        have h := congrArg Neg.neg hneg'
        simpa only [neg_neg] using h.symm
      calc
        Q.val.val = (P + Q.val.val) - P := by abel
        _ = (-P) - P := by rw [hsum]
        _ = 0 := by rw [hneg]; abel
    exact ((mem_halfKernel E H Q.val).mp Q.property).1 (Subtype.ext hz)

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 実軌道の局所多重度から半核ファイバー因子の可除性を得る。

`orbit_x_injective_on_halfKernel` と `orbit_x_root_ne_halfKernel` が、単純根
`P.xc` と半核の二重根を相互に分離する。従って、分子多項式 `p` が単純根で
少なくとも一重、各半核軌道根で少なくとも二重なら、一般の
`fiberFactor_dvd_of_rootMultiplicity` をそのまま適用できる。ここでは
この局所多重度条件を幾何学から自動生成されたものとは扱わず、Vélu 分子の
接線・局所評価から供給されるべき入力として明示する。
-/
theorem orbit_x_fiberFactor_dvd_of_rootMultiplicity
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (p : Polynomial (AlgebraicClosure K)) (hp : p ≠ 0)
    (hsimple : 1 ≤ p.rootMultiplicity P.xc)
    (hdouble : ∀ Q : halfKernel E H,
      2 ≤ p.rootMultiplicity ((P + Q.val.val).xc)) :
    fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
      (fun Q : halfKernel E H => (P + Q.val.val).xc) ∣ p := by
  apply fiberFactor_dvd_of_rootMultiplicity P.xc
    (fun Q : halfKernel E H => (P + Q.val.val).xc) p hp
    (orbit_x_injective_on_halfKernel E H P hP hneg)
  · intro Q
    exact orbit_x_root_ne_halfKernel E H P hP hneg Q
  · exact hsimple
  · exact hdouble

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 軌道根の値零点と微分零点からファイバー因子の可除性を得る。

各半核軌道根で `p` と `p.derivative` が同時に消えるなら、一般補題
`two_le_rootMultiplicity_of_isRoot_of_derivative_isRoot` が二重性を供給する。
単純根 `P.xc` の値零点は非零多項式の根多重度正性へ変換し、前定理へ渡す。
この定理は、未実装の幾何学的分岐計算を「微分零点を示す」という一つの
明確な入力へ縮約する教科書入口である。
-/
theorem orbit_x_fiberFactor_dvd_of_derivative_roots
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (p : Polynomial (AlgebraicClosure K)) (hp : p ≠ 0)
    (hroot : p.IsRoot P.xc)
    (hderiv : ∀ Q : halfKernel E H,
      p.IsRoot ((P + Q.val.val).xc) ∧
        p.derivative.IsRoot ((P + Q.val.val).xc)) :
    fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
      (fun Q : halfKernel E H => (P + Q.val.val).xc) ∣ p := by
  apply orbit_x_fiberFactor_dvd_of_rootMultiplicity E H P hP hneg p hp
  · have hpos : 0 < p.rootMultiplicity P.xc :=
      (Polynomial.rootMultiplicity_pos hp).mpr hroot
    omega
  · intro Q
    exact two_le_rootMultiplicity_of_isRoot_of_derivative_isRoot p hp _
      (hderiv Q).1 (hderiv Q).2

/-- [DkMath.Lib] 有限ファイバー分子の一重根を、同じ核の全軌道へ輸送する。

`exists_veluX_fiber_polynomial_with_rootMultiplicity` が評価零点から一重根を
供給し、`kernelXAt_translation` が `P+Q` でも同じ値 `c` を保つ。従って、
核外の一点 `P` を選ぶだけで、全核軌道の x 座標が分子の根になることを
一つの存在定理にまとめられる。ここでは各根が一重以上であることだけを
確定し、半核根の二重性は次の幾何学層へ残す。
-/
theorem exists_veluX_fiber_polynomial_with_orbit_rootMultiplicity
    (P : Points E) (hP : P ∉ H) (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    ∃ p : Polynomial (AlgebraicClosure K), p ≠ 0 ∧
      p.natDegree ≤ Nat.card H ∧ 1 ≤ p.rootMultiplicity P.xc ∧
      ∀ Q : H, 1 ≤ p.rootMultiplicity ((P + Q.val).xc) := by
  obtain ⟨p, hp, hd, hroot⟩ :=
    exists_veluX_fiber_polynomial_with_rootMultiplicity E H c
  refine ⟨p, hp, hd, hroot P hP hPc, ?_⟩
  intro Q
  apply hroot (P + Q.val) (add_not_mem_kernel E H P hP Q)
  rw [kernelXAt_translation E H P hP Q, hPc]

/-- [DkMath.Lib] モニック化した有限ファイバー分子の一重根を全核軌道へ輸送する。

前定理のモニック化版であり、`eq_orbit_x_fiberFactor_of_monic_of_rootMultiplicity`
へ直接渡せる形を用意する。ここでも供給されるのは各軌道根の一重性だけで、
半核の二重性は依然として別の幾何学的入力である。
-/
theorem exists_veluX_monic_fiber_polynomial_with_orbit_rootMultiplicity
    (P : Points E) (hP : P ∉ H) (c : AlgebraicClosure K)
    (hPc : kernelXAt E H P hP = c) :
    ∃ p : Polynomial (AlgebraicClosure K), p.Monic ∧
      p.natDegree ≤ Nat.card H ∧ 1 ≤ p.rootMultiplicity P.xc ∧
      ∀ Q : H, 1 ≤ p.rootMultiplicity ((P + Q.val).xc) := by
  obtain ⟨p, hp, hd, hroot⟩ :=
    exists_veluX_monic_fiber_polynomial_with_rootMultiplicity E H c
  refine ⟨p, hp, hd, hroot P hP hPc, ?_⟩
  intro Q
  apply hroot (P + Q.val) (add_not_mem_kernel E H P hP Q)
  rw [kernelXAt_translation E H P hP Q, hPc]

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] x 軌道積を標準の `fiberFactor` 表記へ正規化する。

前定理の積分解を、判別式組立で使う `fiberFactor` にそのまま同定する。
単純根は `P.xc`、半核の添字 `Q` に対応する移動根は `(P+Q).xc` である。
この同定により、以後は一般の根多重度 API と x 軌道の幾何学 API を混在させずに
接続できる。 -/
theorem orbit_x_factor_eq_fiberFactor
    (ho : Odd (Nat.card H)) (P : Points E) (hneg : -P = P) :
    (∏ Q : H, (Polynomial.X - Polynomial.C ((P + Q.val : Points E).xc))) =
      fiberFactor (halfKernel E H) P.xc
        (fun Q : H => (P + Q.val : Points E).xc) := by
  rw [orbit_x_factor_eq_root_and_half_square E H ho P hneg]
  unfold fiberFactor
  rw [← Finset.prod_pow]

omit [CharZero K] in
/-- [DkMath.Lib] 反転固定点 `P` の `kernelXAt` 軌道積を半核因子へ分解する。

`kernelXAt_neg_translation_eq` が供給する軌道の反転不変性を
`fullKernel_factor_eq_root_and_half_square` へ渡した特殊化版である。右辺の
単純根は `Q=0` の軌道点であり、`kernelXAt_translation` により `P` 自身へ
簡約できる。以後の根差計算では、この因子を標的2捩れ根ごとに評価する。 -/
theorem kernelXAt_fullKernel_factor_eq_root_and_half_square
    (ho : Odd (Nat.card H)) (P : Points E) (hP : P ∉ H) (hneg : -P = P) :
    (∏ Q : H, (Polynomial.X - Polynomial.C
      (kernelXAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q)))) =
      (Polynomial.X - Polynomial.C (kernelXAt E H P hP)) *
        (∏ Q ∈ halfKernel E H, (Polynomial.X - Polynomial.C
          (kernelXAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q)))) ^ 2 := by
  let ξ : H → AlgebraicClosure K := fun Q =>
    kernelXAt E H (P + Q.val) (add_not_mem_kernel E H P hP Q)
  have hξ : ∀ Q : H, ξ (-Q) = ξ Q := by
    intro Q
    exact kernelXAt_neg_translation_eq E H P hP hneg Q
  have hfactor := fullKernel_factor_eq_root_and_half_square E H ho ξ hξ
  have hzero : ξ 0 = kernelXAt E H P hP := by
    dsimp [ξ]
    exact kernelXAt_translation E H P hP (0 : H)
  simpa only [ξ, hzero] using hfactor

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 半核ファイバー因子の根包含と次数上界から、実際のモニック分子を
`fiberFactor` へ同定する。

幾何学側は `kernelAt_twoTorsion_root_halfKernel` で各根の存在を供給するが、
各根が二重に現れることは自動ではない。そのため `hroots` は多重集合として
明示的に要求し、ここでは半核の次数公式だけを加えて、同定の代数部分を閉じる。 -/
theorem eq_halfKernel_fiberFactor_of_monic_of_roots_le
    (ho : Odd (Nat.card H))
    (e : AlgebraicClosure K) (ξ : halfKernel E H → AlgebraicClosure K)
    (p : Polynomial (AlgebraicClosure K)) (hp : p.Monic)
    (hroots : (fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ).roots ≤ p.roots)
    (hdeg : p.natDegree ≤ Nat.card H) :
    p = fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ := by
  apply eq_fiberFactor_of_monic_of_roots_le (Finset.univ : Finset (halfKernel E H))
    e ξ p hp hroots
  rw [halfKernel_fiberFactor_natDegree E H ho e ξ]
  exact hdeg

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 半核ファイバー因子が分子を割り、次数が尽きていれば同一である。

根の多重集合を直接構成する代わりに、幾何学側で得た可除性
`fiberFactor ∣ p` を入力に取る。`Polynomial.roots.le_of_dvd` が根の多重度を
自動的に持ち上げるため、平行移動根の二重性を分子の根 API へ接続する際の
教科書的な短い入口になる。 -/
theorem eq_halfKernel_fiberFactor_of_monic_of_dvd_of_degree
    (ho : Odd (Nat.card H))
    (e : AlgebraicClosure K) (ξ : halfKernel E H → AlgebraicClosure K)
    (p : Polynomial (AlgebraicClosure K)) (hp : p.Monic)
    (hdiv : fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ ∣ p)
    (hdeg : p.natDegree ≤ Nat.card H) :
    p = fiberFactor (Finset.univ : Finset (halfKernel E H)) e ξ := by
  apply eq_halfKernel_fiberFactor_of_monic_of_roots_le E H ho e ξ p hp
    (Polynomial.roots.le_of_dvd hp.ne_zero hdiv)
  exact hdeg

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 実軌道の根多重度と次数上界からファイバー因子を同定する。

前定理の可除性に、`p` のモニック性と `natDegree p ≤ |H|` を加えると、
半核ファイバー因子と `p` は等しい。これは「局所的な根の重複度を示す」
幾何学的作業と、「有限次数のモニック多項式を一意化する」代数的作業を
分離した教科書形の終端である。実際の `kernelXAt = c` 分子へ進むには、
残る仕事はこの二つの局所多重度を評価から供給することである。
-/
theorem eq_orbit_x_fiberFactor_of_monic_of_rootMultiplicity
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (p : Polynomial (AlgebraicClosure K)) (hp : p.Monic)
    (hsimple : 1 ≤ p.rootMultiplicity P.xc)
    (hdouble : ∀ Q : halfKernel E H,
      2 ≤ p.rootMultiplicity ((P + Q.val.val).xc))
    (hdeg : p.natDegree ≤ Nat.card H) :
    p = fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
      (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  apply eq_halfKernel_fiberFactor_of_monic_of_dvd_of_degree E H ho P.xc
    (fun Q : halfKernel E H => (P + Q.val.val).xc) p hp
  · exact orbit_x_fiberFactor_dvd_of_rootMultiplicity E H P hP hneg p hp.ne_zero
      hsimple hdouble
  · exact hdeg

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] 値・微分の軌道零点と次数上界からファイバー因子を同定する。

`orbit_x_fiberFactor_dvd_of_derivative_roots` が値零点・微分零点を根多重度へ
変換し、`eq_halfKernel_fiberFactor_of_monic_of_dvd_of_degree` がモニック性と
次数上界から等号を回収する。従って、Vélu 分子の幾何学的仕事を「全軌道で
値と微分が消える」の一命題へ集約できる。ここでも、その微分零点自体を
自動生成したとは主張せず、明示的な入力として保持する。
-/
theorem eq_orbit_x_fiberFactor_of_monic_of_derivative_roots
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (p : Polynomial (AlgebraicClosure K)) (hp : p.Monic)
    (hroot : p.IsRoot P.xc)
    (hderiv : ∀ Q : halfKernel E H,
      p.IsRoot ((P + Q.val.val).xc) ∧
        p.derivative.IsRoot ((P + Q.val.val).xc))
    (hdeg : p.natDegree ≤ Nat.card H) :
    p = fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
      (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  apply eq_halfKernel_fiberFactor_of_monic_of_dvd_of_degree E H ho P.xc
    (fun Q : halfKernel E H => (P + Q.val.val).xc) p hp
  · exact orbit_x_fiberFactor_dvd_of_derivative_roots E H P hP hneg p hp.ne_zero
      hroot hderiv
  · exact hdeg

omit [CharZero K] [E.IsElliptic] in
/-- [DkMath.Lib] Wronskian の軌道零点から実軌道因子を同定する。

`p = F - cG` を有理関数のファイバー多項式とし、分子・分母の互いに素性を
仮定する。各半核移動点で `p` と Wronskian が同時に消えるなら、前段の
`fiberPolynomial_derivative_isRoot_iff_wronskian_isRoot` が微分零点を供給し、
軌道の二重根条件へ自動的に変換する。従って、モニック性と次数上界を加えれば
既存の軌道 `fiberFactor` と多項式等号が得られる。

ここで Wronskian の零点性自体は幾何学から供給すべき入力として残している。
この分離により、関数体の有理式計算と有限核の根配置の証明を独立に再利用できる。
-/
theorem eq_orbit_x_fiberFactor_of_monic_of_wronskian_roots
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (F G : Polynomial (AlgebraicClosure K))
    (hcoprime : IsCoprime F G) (c : AlgebraicClosure K)
    (hp : (fiberPolynomial F G c).Monic)
    (hroot : (fiberPolynomial F G c).IsRoot P.xc)
    (horbit : ∀ Q : halfKernel E H,
      (fiberPolynomial F G c).IsRoot ((P + Q.val.val).xc))
    (hwronskian : ∀ Q : halfKernel E H,
      (wronskian F G).IsRoot ((P + Q.val.val).xc))
    (hdeg : (fiberPolynomial F G c).natDegree ≤ Nat.card H) :
    fiberPolynomial F G c = fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
      (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  apply eq_orbit_x_fiberFactor_of_monic_of_derivative_roots E H ho P hP hneg
    (fiberPolynomial F G c) hp hroot ?_ hdeg
  intro Q
  refine ⟨horbit Q, ?_⟩
  exact (fiberPolynomial_derivative_isRoot_iff_wronskian_isRoot hcoprime (horbit Q)).mpr
    (hwronskian Q)

omit [CharZero K] in
/-- [DkMath.Lib] Vélu 有理式の点評価から実軌道因子同定へ進む終端。

`fiberPolynomial_isRoot_of_veluX_eq_quotient` は、同じ係数対 `F,G` を使った
`X_H = F/G` の表示から、`kernelXAt P = c` を `F-cG` の根へ変換する。
`kernelXAt_translation` によってこの根を `P+Q` の全半核軌道へ輸送し、最後に
Wronskian の軌道零点を微分零点へ変換する。従って、モニック性・次数上界・
Wronskian 軌道零点が別途与えられれば、有限ファイバー多項式は標準の
`fiberFactor` と一致する。

この定理は幾何学的な Wronskian 零点を自動生成したとは主張しない。その入力を
明示的に残すことで、Vélu 有理式の評価、核平行移動、代数的因子同定の三段を
独立に再利用できる教科書構成を保つ。
-/
theorem eq_orbit_x_fiberFactor_of_monic_of_veluX_quotient_of_wronskian_roots
    (ho : Odd (Nat.card H))
    (P : Points E) (hP : P ∉ H) (hneg : -P = P)
    (F G : Polynomial (AlgebraicClosure K)) (hcoprime : IsCoprime F G) (hG : G ≠ 0)
    (hrel : veluX E H =
      aeval (genericX E (AlgebraicClosure K)) F /
        aeval (genericX E (AlgebraicClosure K)) G)
    (c : AlgebraicClosure K)
    (hp : (fiberPolynomial F G c).Monic)
    (hPc : kernelXAt E H P hP = c)
    (hwronskian : ∀ Q : halfKernel E H,
      (wronskian F G).IsRoot ((P + Q.val.val).xc))
    (hdeg : (fiberPolynomial F G c).natDegree ≤ Nat.card H) :
    fiberPolynomial F G c = fiberFactor (Finset.univ : Finset (halfKernel E H)) P.xc
      (fun Q : halfKernel E H => (P + Q.val.val).xc) := by
  have hroot : (fiberPolynomial F G c).IsRoot P.xc :=
    fiberPolynomial_isRoot_of_veluX_eq_quotient E H F G hG hrel c P hP hPc
  have horbit : ∀ Q : halfKernel E H,
      (fiberPolynomial F G c).IsRoot ((P + Q.val.val).xc) := by
    intro Q
    apply fiberPolynomial_isRoot_of_veluX_eq_quotient E H F G hG hrel c
      (P + Q.val.val) (add_not_mem_kernel E H P hP Q.val)
    rw [kernelXAt_translation E H P hP Q.val, hPc]
  exact eq_orbit_x_fiberFactor_of_monic_of_wronskian_roots E H ho P hP hneg F G
    hcoprime c hp hroot horbit hwronskian hdeg

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
