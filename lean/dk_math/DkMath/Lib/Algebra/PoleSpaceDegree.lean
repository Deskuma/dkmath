/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
The integral-basis growth argument is reconstructed from
P2M/Sol/S_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean,
blob 3c0bfbe2ef83931a739635809490b5a7f4db654e.
Modified: use one discrete valuation and a proved pole-space bound, no curve/divisor packages.
-/

import DkMath.Lib.Algebra.ValuationPoleSpace
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Algebra.Polynomial.Basis

#print "file: DkMath.Lib.Algebra.PoleSpaceDegree"

/-!
# 整基底の増大から関数体次数を抑える

[DkMath.Lib] E=k(f)、F/Eは有限とする。整基底u_iとfʲの積はk上一次独立。
fの極位数dと、Rの極空間の上界n+1を比較すると[F:E]≤dとなる。
Rへの整元の所属は数学的な仮定として保持し、任意の部分代数には拡張しない。
-/
namespace DkMath.Lib.Algebra.PoleSpaceDegree
open Polynomial IntermediateField WithZero Module
open ValuationPoleSpace
variable {k E F : Type*} [Field k] [Field E] [Field F]
  [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]

/-- [DkMath.Lib] 同じ生成表示E=k(f)から、k[f]の分数体がEであることを供給する。 -/
theorem isFractionRing_adjoin_of_eq_top (f : E) (hgen : adjoin k {f} = ⊤) :
    IsFractionRing (Algebra.adjoin k {f}) E := by
  apply IsFractionRing.of_field
  intro z
  have hz : z ∈ adjoin k {f} := by rw [hgen]; trivial
  obtain ⟨p, q, he⟩ := (mem_adjoin_simple_iff k z).mp hz
  refine ⟨⟨aeval f p, ?_⟩, ⟨aeval f q, ?_⟩, he⟩ <;>
    exact Algebra.adjoin_singleton_eq_range_aeval k f ▸ ⟨_, rfl⟩

/-- [DkMath.Lib] 単純生成体の同じ生成元は、その体自身を生成する。 -/
theorem adjoin_gen_eq_top {L : Type*} [Field L] [Algebra k L] (x : L) :
    adjoin k {AdjoinSimple.gen k x} = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨p, q, he⟩ := (mem_adjoin_simple_iff k (z : L)).mp z.2
  apply (mem_adjoin_simple_iff k z).mpr
  refine ⟨p, q, Subtype.ext ?_⟩
  simpa only [IntermediateField.coe_div, AdjoinSimple.coe_aeval_gen_apply] using he

/-- [DkMath.Lib] 超越元の冪と上の体の独立族の積は、下の係数体でも独立である。 -/
theorem linearIndependent_pow_mul (f : E) (hf : Transcendental k f)
    {ι : Type*} (u : ι → F) (hu : LinearIndependent E u) :
    LinearIndependent k (fun p : ℕ × ι => algebraMap E F f ^ p.1 * u p.2) := by
  have hp : LinearIndependent k (fun n : ℕ => f ^ n) := by
    have h := (Polynomial.basisMonomials k).linearIndependent.map'
      (aeval (R := k) f).toLinearMap (LinearMap.ker_eq_bot.mpr
        (transcendental_iff_injective.mp hf))
    simpa only [Function.comp_def, AlgHom.toLinearMap_apply, Polynomial.coe_basisMonomials,
      aeval_monomial, map_one, one_mul] using h
  simpa only [Algebra.smul_def, map_pow] using linearIndependent_smul hp hu

/-- [DkMath.Lib] 単一の極フィルトレーションの成長上界から、実際の関数体次数を抑える。
整基底をRへ入れ、r個の基底とm個の冪の独立性を、極上界c+dmに比較する。
これは次数を入力し直す包装ではなく、有限次元性から数値の上界を証明する。 -/
theorem finrank_le (f : E) (hf : Transcendental k f) (hgen : adjoin k {f} = ⊤)
    [FiniteDimensional E F] (R : Subalgebra k F) (v : Valuation F ℤᵐ⁰)
    (hc : ∀ c : k, v (algebraMap k F c) ≤ 1)
    (hregular : ∀ g ∈ R, v g ≤ 1 → ∃ c : k, g = algebraMap k F c)
    (hcancel : ∀ {g h : F}, h ≠ 0 → v g = v h → ∃ c : k, v (g - c • h) < v h)
    (hint : ∀ g : F, IsIntegral (Algebra.adjoin k {f}) g → g ∈ R)
    (hfm : algebraMap E F f ∈ R) (d : ℕ)
    (hfv : v (algebraMap E F f) = exp (d : ℤ)) : Module.finrank E F ≤ d := by
  classical
  let := isFractionRing_adjoin_of_eq_top f hgen
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (Algebra.adjoin k {f}) E F
  have hcard : Fintype.card s = Module.finrank E F := (Module.finrank_eq_card_basis b).symm
  have hmem : ∀ i, b i ∈ R := fun i => hint _ (hb i)
  let c : ℕ := Finset.univ.sup fun i : s => (log (v (b i))).toNat
  have hbound : ∀ i, v (b i) ≤ exp (c : ℤ) := by
    intro i
    rw [← exp_log (v.ne_zero_iff.mpr (b.ne_zero i)), exp_le_exp]
    exact (Int.self_le_toNat _).trans (by exact_mod_cast
      (Finset.le_sup (f := fun i : s => (log (v (b i))).toNat) (Finset.mem_univ i)))
  have hli := linearIndependent_pow_mul f hf b b.linearIndependent
  have hdim : ∀ m : ℕ, m * Module.finrank E F ≤ c + d * m + 1 := by
    intro m
    let n := c + d * m
    let P := poleSpace R v hc n
    let := (finiteDimensional_finrank_poleSpace R v hc hregular hcancel n).1
    have hpmem : ∀ p : Fin m × s,
        algebraMap E F f ^ (p.1 : ℕ) * b p.2 ∈ P := by
      intro p
      refine ⟨R.mul_mem (R.pow_mem hfm _) (hmem p.2), ?_⟩
      change v (algebraMap E F f ^ (p.1 : ℕ) * b p.2) ≤ exp (n : ℤ)
      rw [map_mul, map_pow, hfv, ← exp_nsmul]
      simp only [nsmul_eq_mul]
      calc exp ((p.1 : ℕ) * (d : ℤ)) * v (b p.2)
          ≤ exp ((p.1 : ℕ) * (d : ℤ)) * exp (c : ℤ) := mul_le_mul' le_rfl (hbound p.2)
        _ = exp ((p.1 : ℕ) * (d : ℤ) + c) := (exp_add _ _).symm
        _ ≤ exp (n : ℤ) := exp_le_exp.mpr (by dsimp [n]; nlinarith [p.1.isLt])
    have hli' : LinearIndependent k (fun p : Fin m × s =>
        (⟨algebraMap E F f ^ (p.1 : ℕ) * b p.2, hpmem p⟩ : P)) := by
      apply LinearIndependent.of_comp P.subtype
      exact hli.comp (fun p : Fin m × s => ((p.1 : ℕ), p.2))
        (fun p q h => Prod.ext (Fin.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2)
    have hlow := hli'.fintype_card_le_finrank
    have hhigh := (finiteDimensional_finrank_poleSpace R v hc hregular hcancel n).2
    simp only [Fintype.card_prod, Fintype.card_fin, hcard] at hlow
    exact hlow.trans hhigh
  by_contra! hlarge
  have htest := hdim (c + 2)
  have hgap : d + 1 ≤ Module.finrank E F := hlarge
  nlinarith

end DkMath.Lib.Algebra.PoleSpaceDegree
