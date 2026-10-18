/-
Adapted from leanprover-community/flt-regular, commit
b8a5f23ab44a7be9fd49f6e3c831da54573c3c89,
FltRegular/NumberTheory/Cyclotomic/CyclRat.lean.
Licensed under Apache-2.0; see RegularKummer/LICENSE.
DkMath additions: arbitrary-modulus coefficient differences and support obstruction.
-/

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

#print "file: DkMath.Lib.NumberTheory.CyclotomicPhaseCoefficientRigidity"

/-!
# 円分位相の係数剛性

素数 p の円分整数環では、p 個の位相の唯一の整数関係は
`1 + ζ + … + ζ^(p-1) = 0` である。整数冪基底での座標は
`f i - f (p-1)` なので、整数 m による評価値の可除性は全係数の
合同に等しい。m は p に限らず、0 や負の整数でもよい。

ここでの可除性は整数 m の像による可除性である。
分岐素元 `1-ζ` による可除性とは区別しなければならない。
-/

namespace DkMath.Lib.NumberTheory

open Finset Polynomial Nat
open scoped NumberField

variable {p : ℕ} {L : Type*} [Field L] [CharZero L]
  [IsCyclotomicExtension {p} ℚ L]

/-- 係数0の位相を持つ関係では、評価値の整数 m による可除性が
各係数へ戻る。整数冪基底で最後の位相を消去し、座標の可除性を使う。
原典の補題を FLT に依存しない任意の円分体上へ切り出したもの。 -/
theorem dvd_phase_coefficients_of_zero (hp : p.Prime) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ p)
    {f : Fin p → ℤ} (hf : ∃ i, f i = 0) {m : ℤ}
    (hdiv : ↑m ∣ ∑ j, f j • ζ ^ (j : ℕ)) : ∀ j, m ∣ f j := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p.pred, (succ_pred_prime hp).symm⟩
  have hζ' : IsPrimitiveRoot (ζ : L) (n + 1) := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  set b := hζ'.integralPowerBasis with hb
  have hdim : b.dim = n := by rw [hb, hζ'.integralPowerBasis_dim, totient_prime hp,
    Nat.add_sub_cancel]
  have hbasis (i : Fin b.dim) : b.basis i = ζ ^ (i : ℕ) := by
    rw [PowerBasis.basis_eq_pow, show b.gen = hζ'.toInteger from hζ'.integralPowerBasis_gen]
    rfl
  have hgeom : ∑ i : Fin n, ζ ^ (i : ℕ) = -ζ ^ n := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ ζ ^ i) n]
    exact eq_neg_of_add_eq_zero_left
      (by simpa [sum_range_succ] using hζ.geom_sum_eq_zero hp.one_lt)
  -- Since `ζ ^ n = -(1 + ζ + ⋯ + ζ ^ (n - 1))`, the sum `∑ j, f j • ζ ^ j` has
  -- coordinates `f j - f (Fin.last n)` in the integral power basis `1, ζ, …, ζ ^ (n - 1)`.
  have hsum : (∑ j, f j • ζ ^ (j : ℕ)) = b.basis.equivFun.symm
      fun i ↦ f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n) := by
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_equiv (finCongr hdim)
      (fun i : Fin b.dim ↦
        (f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n)) • b.basis i)
      (fun i : Fin n ↦ (f ⟨i, i.2.trans n.lt_succ_self⟩ - f (Fin.last n)) • ζ ^ (i : ℕ))
      fun i ↦ by
        rw [hbasis]
        rfl]
    simp only [sub_smul, sum_sub_distrib, ← Finset.smul_sum, hgeom, smul_neg, sub_neg_eq_add]
    exact Fin.sum_univ_castSucc fun j : Fin (n + 1) ↦ f j • ζ ^ (j : ℕ)
  -- 評価値 = m*y を整数冪基底の各座標へ射影する。
  obtain ⟨y, hy⟩ := hdiv
  rw [hsum, ← zsmul_eq_mul] at hy
  have key (i : Fin b.dim) :
      m ∣ f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n) := by
    have h1 : f ⟨i, (i.2.trans_le hdim.le).trans n.lt_succ_self⟩ - f (Fin.last n) =
        b.basis.coord i (m • y) := by rw [← hy, b.basis.coord_equivFun_symm]
    rw [h1]
    exact b.basis.dvd_coord_smul i y m
  -- 係数0の位相により、共通の剰余類が0であると決まる。
  have hlast : m ∣ f (Fin.last n) := by
    obtain ⟨i, hi⟩ := hf
    rcases (Nat.lt_succ_iff.mp i.2).eq_or_lt with h | h
    · rw [← show i = Fin.last n from Fin.ext h, hi]
      exact dvd_zero m
    · simpa [hi] using key ⟨i, hdim.symm ▸ h⟩
  intro j
  rcases (Nat.lt_succ_iff.mp j.2).eq_or_lt with h | h
  · exact (show j = Fin.last n from Fin.ext h) ▸ hlast
  · simpa using (key ⟨j, hdim.symm ▸ h⟩).add hlast


/-- 評価値が m で割れるなら、任意の二つの位相係数は mod m で一致する。
係数を `f j` だけ平行移動しても、全位相和が0なので評価値は変わらない。 -/
theorem dvd_phase_coefficient_sub (hp : p.Prime) {ζ : 𝓞 L}
    (hζ : IsPrimitiveRoot ζ p) {f : Fin p → ℤ} {m : ℤ}
    (hdiv : (m : 𝓞 L) ∣ ∑ i, f i • ζ ^ (i : ℕ)) (i j : Fin p) :
    m ∣ f i - f j := by
  have hsum : ∑ k : Fin p, ζ ^ (k : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hζ.geom_sum_eq_zero hp.one_lt
  apply dvd_phase_coefficients_of_zero hp hζ (f := fun k => f k - f j) ⟨j, sub_self _⟩
  simpa only [sub_smul, sum_sub_distrib, ← Finset.smul_sum, hsum, smul_zero,
    sub_zero] using hdiv

/-- 円分評価値の可除性と、全係数の合同は同値。
後向きは任意の基準位相 j を引き、各項の m 可除性を足し合わせる。
NOTE-002 の固定契約：名前・引数・任意整数 m・双方向同値を維持する。
GN への一般化は別の定理として追加し、この円分特化を弱めない。 -/
theorem phase_sum_dvd_iff (hp : p.Prime) {ζ : 𝓞 L}
    (hζ : IsPrimitiveRoot ζ p) (f : Fin p → ℤ) (m : ℤ) :
    (m : 𝓞 L) ∣ ∑ i, f i • ζ ^ (i : ℕ) ↔ ∀ i j, m ∣ f i - f j := by
  refine ⟨fun h i j => dvd_phase_coefficient_sub hp hζ h i j, fun h => ?_⟩
  let j : Fin p := ⟨0, hp.pos⟩
  have hsum : ∑ k : Fin p, ζ ^ (k : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hζ.geom_sum_eq_zero hp.one_lt
  have hd : (m : 𝓞 L) ∣ ∑ i : Fin p, (f i - f j) • ζ ^ (i : ℕ) := by
    apply Finset.dvd_sum
    intro i _
    rw [zsmul_eq_mul]
    exact dvd_mul_of_dvd_left (map_dvd (Int.castRingHom (𝓞 L)) (h i j)) _
  simpa only [sub_smul, sum_sub_distrib, ← Finset.smul_sum, hsum, smul_zero,
    sub_zero] using hd

/-- 位相の合同剛性を `Int.ModEq` として読む API。 -/
theorem phase_coefficients_modEq (hp : p.Prime) {ζ : 𝓞 L}
    (hζ : IsPrimitiveRoot ζ p) {f : Fin p → ℤ} {m : ℤ}
    (hdiv : (m : 𝓞 L) ∣ ∑ i, f i • ζ ^ (i : ℕ)) (i j : Fin p) :
    Int.ModEq m (f i) (f j) := by
  rw [Int.modEq_iff_dvd]
  exact (dvd_phase_coefficient_sub hp hζ hdiv j i)

end DkMath.Lib.NumberTheory
