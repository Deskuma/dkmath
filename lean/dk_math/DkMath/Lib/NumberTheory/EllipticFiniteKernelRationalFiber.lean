/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelSpecialization
import Mathlib.FieldTheory.RatFunc.IntermediateField

#print "file: DkMath.Lib.NumberTheory.EllipticFiniteKernelRationalFiber"

/-!
# 同じX_Hを元のxの有理式として読み、有限ファイバーの次数を制御する

[DkMath.Lib] 反転固定体はk(x)。既存の関数体次数2|H|を次数2で割ると、
k(x)/k(X_H)の次数は|H|になる。RatFuncの分子分母次数公式へ輸送すれば、
実点でX_H=cとなるx座標は、次数高々|H|の非零多項式の根となる。
明示的Vélu係数を選び直さず、同じ関数と同じ実点評価を保つ。
-/
namespace DkMath.Lib.NumberTheory.EllipticFiniteKernel
open Polynomial IntermediateField WeierstrassCurve WeierstrassCurve.Affine WithZero
open EllipticFunctionField EllipticTorsionRepresentation EllipticPointEvaluation
open DkMath.Lib.Algebra
variable {K : Type*} [Field K] [NeZero (2 : K)] (E : WeierstrassCurve K) [E.IsElliptic]
noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 自明核の同じ二関数は、元の一般座標へ戻る。 -/
theorem velu_bot_coordinates :
    letI : Fintype (⊥ : AddSubgroup (Points E)) := Fintype.ofFinite _
    veluX E ⊥ = genericX E (AlgebraicClosure K) ∧ veluY E ⊥ = genericY E (AlgebraicClosure K) := by
  let : Fintype (⊥ : AddSubgroup (Points E)) := Fintype.ofFinite _
  have hd : ((default : (⊥ : AddSubgroup (Points E))) : Points E) = 0 :=
    (default : (⊥ : AddSubgroup (Points E))).property
  have h0 : transEquiv E (AlgebraicClosure K) (0 : Points E) = AlgEquiv.refl :=
    transEquiv_zero E (AlgebraicClosure K)
  have hx0 : (0 : Points E).xc = 0 := rfl
  have hy0 : (0 : Points E).yc = 0 := rfl
  constructor <;> simp [veluX, veluY, kernelTrace, hd, h0, hx0, hy0]

omit [NeZero (2 : K)] in
/-- [DkMath.Lib] 元の一般x座標の単純体上で、同じ楕円関数体の次数は2。 -/
theorem finrank_over_genericX :
    Module.finrank (AlgebraicClosure K)⟮genericX E (AlgebraicClosure K)⟯
      (E.toAffine⁄(AlgebraicClosure K)).FunctionField = 2 := by
  let : Fintype (⊥ : AddSubgroup (Points E)) := Fintype.ofFinite _
  have h := (velu_ambient_degrees E ⊥).1
  rw [velu_bot_coordinates E |>.1] at h
  simpa using h

/-- [DkMath.Lib] 反転で固定される同じX_Hは、元のxの有理関数である。 -/
theorem veluX_mem_genericX (H : AddSubgroup (Points E)) [Fintype H] :
    veluX E H ∈ (AlgebraicClosure K)⟮genericX E (AlgebraicClosure K)⟯ := by
  let : Fintype (⊥ : AddSubgroup (Points E)) := Fintype.ofFinite _
  have hmove := negEquiv_veluY_ne E ⊥
  rw [(velu_bot_coordinates E).2] at hmove
  apply QuadraticFixedField.mem_of_fixed
    ((AlgebraicClosure K)⟮genericX E (AlgebraicClosure K)⟯) ⊤ le_top
    (by rw [relfinrank_top_right]; exact finrank_over_genericX E)
    (negEquiv E (AlgebraicClosure K)) ?_ (genericY E (AlgebraicClosure K))
    mem_top hmove mem_top (negEquiv_veluX E H)
  intro a ha
  obtain ⟨p, q, he⟩ := (mem_adjoin_simple_iff (AlgebraicClosure K) a).mp ha
  rw [he, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, negEquiv_genericX]

/-- [DkMath.Lib] 反転固定体内での同じX_Hの次数は、同じ核の位数|H|。 -/
theorem genericX_relative_degree (H : AddSubgroup (Points E)) [Fintype H] :
    ((AlgebraicClosure K)⟮veluX E H⟯).relfinrank
      ((AlgebraicClosure K)⟮genericX E (AlgebraicClosure K)⟯) = Nat.card H := by
  have ht := relfinrank_mul_finrank_top
    (adjoin_simple_le_iff.mpr (veluX_mem_genericX E H))
  rw [finrank_over_genericX, (velu_ambient_degrees E H).1] at ht
  omega

/-- [DkMath.Lib] 同じX_Hを既約有理関数rとして実現し、分子分母の最大次数|H|を供給する。 -/
theorem exists_veluX_rational (H : AddSubgroup (Points E)) [Fintype H] :
    ∃ r : RatFunc (AlgebraicClosure K),
      max r.num.natDegree r.denom.natDegree = Nat.card H ∧
      veluX E H = aeval (genericX E (AlgebraicClosure K)) r.num /
        aeval (genericX E (AlgebraicClosure K)) r.denom := by
  let k := AlgebraicClosure K
  let F := (E.toAffine⁄k).FunctionField
  let x := genericX E k
  have hx : Transcendental k x := transcendental_of_point_pole E 0 x (by
    change 1 < pointValuation E (0 : (E⁄(AlgebraicClosure K)).Point)
      (genericX E (AlgebraicClosure K))
    rw [pointValuation_zero_genericX, ← exp_zero, exp_lt_exp]; decide)
  let A := k⟮x⟯
  let e := RatFunc.algEquivOfTranscendental x hx
  let r := e.symm ⟨veluX E H, veluX_mem_genericX E H⟩
  let φ : RatFunc k →ₐ[k] F := A.val.comp e.toAlgHom
  have hr : φ r = veluX E H := congrArg Subtype.val (e.apply_symm_apply _)
  have hφ : φ.fieldRange = A := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩; exact (e a).property
    · intro hz
      obtain ⟨a, ha⟩ := e.surjective ⟨z, hz⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hmap : (k⟮r⟯).map φ = k⟮veluX E H⟯ := by
    rw [adjoin_map, Set.image_singleton, hr]
  have htop : (⊤ : IntermediateField k (RatFunc k)).map φ = A := by
    rw [show (⊤ : IntermediateField k (RatFunc k)).map φ = φ.fieldRange from by ext z; simp, hφ]
  have ht := relfinrank_map_map (k⟮r⟯) ⊤ φ
  rw [hmap, htop, genericX_relative_degree E H, relfinrank_top_right,
    RatFunc.finrank_eq_max_natDegree] at ht
  refine ⟨r, ht.symm, ?_⟩
  calc veluX E H = (e r : F) := hr.symm
    _ = _ := RatFunc.algEquivOfTranscendental_apply x hx r

/-- [DkMath.Lib] X_H=cの有限ファイバーのx座標を、次数高々|H|の非零多項式の根へ送る。
分母が評価点で非零という追加仮定は不要。恒等式を先に払ってから正則評価する。 -/
theorem exists_veluX_fiber_polynomial (H : AddSubgroup (Points E)) [Fintype H]
    (c : AlgebraicClosure K) :
    ∃ p : (AlgebraicClosure K)[X], p ≠ 0 ∧ p.natDegree ≤ Nat.card H ∧
      ∀ (P : Points E) (hP : P ∉ H), kernelXAt E H P hP = c → p.eval P.xc = 0 := by
  let k := AlgebraicClosure K
  let F := (E.toAffine⁄k).FunctionField
  let x := genericX E k
  have hx : Transcendental k x := transcendental_of_point_pole E 0 x (by
    change 1 < pointValuation E (0 : (E⁄k).Point) (genericX E k)
    rw [pointValuation_zero_genericX, ← exp_zero, exp_lt_exp]; decide)
  obtain ⟨r, hrdeg, hr⟩ := exists_veluX_rational E H
  change veluX E H = aeval x r.num / aeval x r.denom at hr
  have hq : aeval x r.denom ≠ 0 := fun h => r.denom_ne_zero ((transcendental_iff.mp hx) _ h)
  let p := r.num - C c * r.denom
  have hid : aeval x p = (veluX E H - algebraMap k F c) * aeval x r.denom := by
    dsimp only [p]
    rw [map_sub, map_mul, aeval_C, hr]
    field_simp [hq]
    ring
  have hp : p ≠ 0 := by
    intro h0
    have hv : aeval x p ≠ 0 := by
      rw [hid]
      exact mul_ne_zero (sub_ne_zero.mpr (veluX_ne_const E H c)) hq
    exact hv (by rw [h0, map_zero])
  refine ⟨p, hp, ?_, ?_⟩
  · exact (natDegree_sub_le r.num (C c * r.denom)).trans
      ((max_le_max le_rfl (natDegree_C_mul_le c r.denom)).trans_eq hrdeg)
  · intro P hP hval
    have hP0 : P ≠ 0 := fun hz => hP (hz ▸ H.zero_mem)
    have hc (a : k) := pointValuation_const_le_one E P a
    have hX := (kernelAt_congr E H P hP).1
    rw [hval] at hX
    have hqreg := ValuationRationalPolynomial.aeval_le_one (pointValuation E P) hc x
      (pointValuation_genericX_le_one E P hP0) r.denom
    have hv : pointValuation E P (aeval x p) < 1 := by
      rw [hid, map_mul]
      exact lt_of_le_of_lt ((mul_le_mul' le_rfl hqreg).trans_eq (mul_one _)) hX
    have hxc := value_spec E P x (pointValuation_genericX_le_one E P hP0)
    rw [value_genericX E P hP0] at hxc
    have hcong := (Valuation.Cong.eval₂ (algebraMap k F) hc hxc (hc P.xc) p).1
    rw [eval₂_at_apply] at hcong
    have hcval : pointValuation E P (algebraMap k F (p.eval P.xc)) < 1 :=
      hcong.lt_one_iff.mp hv
    by_contra hn
    rw [pointValuation_const_eq_one E P hn] at hcval
    exact lt_irrefl _ hcval

/-- [DkMath.Lib] 有限ファイバー多項式の評価零点を根多重度へ変換する。

`exists_veluX_fiber_polynomial` は、`kernelXAt = c` となる点の x 座標で
`p.eval = 0` を供給する。非零多項式ではこれは `rootMultiplicity ≥ 1` と
同値なので、評価 API と多項式の重複度 API の間の教科書的な変換をここで
固定する。二重根までは主張せず、単純根の確実な層だけを公開する。
-/
theorem exists_veluX_fiber_polynomial_with_rootMultiplicity
    (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    ∃ p : (AlgebraicClosure K)[X], p ≠ 0 ∧ p.natDegree ≤ Nat.card H ∧
      ∀ (P : Points E) (hP : P ∉ H),
        kernelXAt E H P hP = c → 1 ≤ p.rootMultiplicity P.xc := by
  obtain ⟨p, hp, hd, hroot⟩ := exists_veluX_fiber_polynomial E H c
  refine ⟨p, hp, hd, ?_⟩
  intro P hP hval
  apply (Polynomial.rootMultiplicity_pos hp).mpr
  exact hroot P hP hval

/-- [DkMath.Lib] 有限ファイバー分子をモニック化しても、根・次数・一重根情報は
そのまま保たれる。

`Polynomial.normalize` は非零多項式を最高係数で割るだけなので、根の多重集合を
変えずに `Monic` を供給する。以後の `fiberFactor` 同定定理へ渡す分子は、この
標準モニック化を使えばよく、係数の正規化を幾何学側へ持ち込む必要がない。
-/
theorem exists_veluX_monic_fiber_polynomial_with_rootMultiplicity
    (H : AddSubgroup (Points E)) [Fintype H] (c : AlgebraicClosure K) :
    ∃ p : (AlgebraicClosure K)[X], p.Monic ∧ p.natDegree ≤ Nat.card H ∧
      ∀ (P : Points E) (hP : P ∉ H),
        kernelXAt E H P hP = c → 1 ≤ p.rootMultiplicity P.xc := by
  obtain ⟨p, hp, hd, hroot⟩ :=
    exists_veluX_fiber_polynomial_with_rootMultiplicity E H c
  let q := normalize p
  have hroots : q.roots = p.roots := by
    exact Polynomial.roots_normalize
  have hdeg : q.natDegree ≤ Nat.card H := by
    rw [Polynomial.natDegree_normalize]
    exact hd
  refine ⟨q, Polynomial.monic_normalize hp, hdeg, ?_⟩
  intro P hP hval
  have hmult : q.rootMultiplicity P.xc = p.rootMultiplicity P.xc := by
    rw [← Polynomial.count_roots q, ← Polynomial.count_roots p, hroots]
  rw [hmult]
  exact hroot P hP hval

/-- [DkMath.Lib] 同じ有限値cへ移る相異なるx座標は、同じ核の位数以下である。 -/
theorem card_veluX_fiber_le (H : AddSubgroup (Points E)) [Fintype H]
    (c : AlgebraicClosure K) (T : Finset (AlgebraicClosure K))
    (hT : ∀ a ∈ T, ∃ (P : Points E) (hP : P ∉ H), P.xc = a ∧ kernelXAt E H P hP = c) :
    T.card ≤ Nat.card H := by
  obtain ⟨p, hp, hd, hroot⟩ := exists_veluX_fiber_polynomial E H c
  have hsub : T ⊆ p.roots.toFinset := by
    intro a ha
    obtain ⟨P, hP, he, hv⟩ := hT a ha
    rw [Multiset.mem_toFinset, mem_roots hp]
    rw [← he]
    exact hroot P hP hv
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans hd))

end DkMath.Lib.NumberTheory.EllipticFiniteKernel
