/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.DiscreteValuationPullback
import Mathlib.RingTheory.Ideal.Quotient.Operations

#print "file: DkMath.Lib.NumberTheory.DedekindLocalParameter"

/-!
# 有限個の相異なる素点で、一点だけの一様化元を作る

[DkMath.Lib] 一点で位数1、他の指定点では単元となる座標環元を中国剰余定理で構成する。
素イデアルの二乗を法として一様化元と1を貼り合わせる。
環の類群が自明であるとの仮定や、素イデアルが主であるとの仮定は不要。
-/
namespace DkMath.Lib.NumberTheory.DedekindLocalParameter
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Function
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- [DkMath.Lib] 有限個の相異なる素点の中で、一点のみを一次で消す元が存在する。
局所的一様化元の存在と、相異なる極大イデアルの二乗の互いに素性から従う。 -/
theorem exists_parameter {ι : Type*} [Finite ι] [DecidableEq ι]
    (w : ι → HeightOneSpectrum R) (hinj : Function.Injective w) (i : ι) :
    ∃ a : R, a ≠ 0 ∧ ∀ j, (w j).intValuation a = if j = i then exp (-1 : ℤ) else 1 := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨π, hπ⟩ := (w i).intValuation_exists_uniformizer
  have hcop : Pairwise (IsCoprime on (fun j => (w j).asIdeal ^ 2)) := by
    intro j l hjl
    let : (w j).asIdeal.IsMaximal := (w j).isMaximal
    let : (w l).asIdeal.IsMaximal := (w l).isMaximal
    have hne : (w j).asIdeal ≠ (w l).asIdeal := fun he => hjl (hinj (HeightOneSpectrum.ext he))
    exact (Ideal.isCoprime_of_isMaximal hne).pow
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun j => if j = i then π else 1)
  have hv (j : ι) : (w j).intValuation a = if j = i then exp (-1 : ℤ) else 1 := by
    have hdiff := ((w j).intValuation_le_pow_iff_mem _ 2).mpr (ha j)
    by_cases hj : j = i
    · subst j
      simp only [ite_true] at hdiff ⊢
      have hlt : (w i).intValuation (a - π) < (w i).intValuation π := by
        rw [hπ]
        exact hdiff.trans_lt (by rw [exp_lt_exp]; norm_num)
      have he : a = π + (a - π) := by ring
      rw [he, (w i).intValuation.map_add_eq_of_lt_left hlt]
      exact hπ
    · simp only [ite_eq_right hj] at hdiff ⊢
      have hc : ((w j).intValuation).Cong a 1 :=
        hdiff.trans_lt (by rw [← exp_zero, exp_lt_exp]; norm_num)
      exact hc.eq_of_eq_one (map_one _)
  refine ⟨a, ?_, hv⟩
  intro hz
  have hi := hv i
  simp only [hz, map_zero, ite_true] at hi
  exact exp_ne_zero hi.symm

end DkMath.Lib.NumberTheory.DedekindLocalParameter
