/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyFiniteKernelIntegralModel
import DkMath.FLT.FreyFiniteKernelSpecialization
import DkMath.FLT.FreyRationalTorsionBounds
import DkMath.Lib.NumberTheory.EllipticFixedTorsion

#print "file: DkMath.FLT.FreyRationalTwoPTorsion"

/-!
# Cofixed 核から整数商モデル上の有理 `2p` 捩れを作る

この章では、`hno` の大域的脱出元を直接構成しない。その代わり、Cofixed な
一次元核 `L` が存在するとき、既に構成済みの同じ整数係数商モデル上に、厳密な
位数 `2 * p` の有理点を組み立てる。

源の Frey 曲線には、偶数性から有理な非零二捩れ点 `T` がある。奇素数位数の
核は `T` を含まないので、商準同型の像 `T'` も非零二捩れである。一方、
`exists_rational_torsion_on_integer_kernel` が Cofixed 性から非零有理 `p` 捩れ点
`R` を与える。従って `T' + R` は `p` が奇素数であることにより位数 `2 * p` を
持つ。

この結論は Mazur の有理捩れ分類を仮定しない。従って、ここで形式化されるのは
「Cofixed 枝から有理 `2p` 捩れが生じる」という無条件の構造的帰結であり、
`p ≥ 7` でその枝が不可能だという算術的排除は別の定理として残る。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve WeierstrassCurve.Affine

variable {p : ℕ} [Fact p.Prime] (S : Source p)

local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/--
`Even S.b` と Cofixed 一次元核から、整数係数商モデル上の有理点 `Q` を構成し、
その加法位数が厳密に `2 * p` であることを示す。

教科書の対応は次の通りである。

* `T` は源曲線上の有理二捩れ点、`T' = φ(T)` は商曲線上の非零二捩れ点。
* `R` は Cofixed 性から得た非零有理 `p` 捩れ点。
* `Q = T' + R` とおくと、`p • Q = T'`、`2 • Q ≠ 0`、`(2*p) • Q = 0`。
* `addOrderOf_eq_of_nsmul_and_div_prime_nsmul` によって `addOrderOf Q = 2*p`。

`T'` の有理性は、商写像の Galois 同変性と `exists_baseChangePoint_of_fixed` により
降下する。従って座標の有理性を追加仮定していない。
-/
theorem residual_cofixed_implies_rational_two_p_torsion (hp2 : p ≠ 2)
    (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hL.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p := by
  let E' := (S.residualIntegerKernelModel L hline hL.isStable).map (Int.castRingHom ℚ)
  let φ := S.residualIntegerKernelPointHom hp2 L hline hL.isStable
  let Taff := S.rationalTwoTorsionPoint hbe
  let Tsrc : EllipticTorsionRepresentation.Points S.rationalCurve :=
    baseChangePointHom S.rationalCurve Taff
  have hTaff_ne : Taff ≠ 0 := by
    exact WeierstrassXReflection.twoTorsionPoint_ne_zero
      S.rationalCurve_a₆ (S.a₄_twoAdic_exact hbe).1
  have hTsrc_ne : Tsrc ≠ 0 := by
    intro hz
    apply hTaff_ne
    apply baseChangePoint_injective S.rationalCurve
    change baseChangePointHom S.rationalCurve Taff = baseChangePointHom S.rationalCurve 0
    simpa [Tsrc] using hz
  have hTsrc_two : 2 • Tsrc = 0 := by
    change 2 • (baseChangePointHom S.rationalCurve Taff) = 0
    rw [← map_nsmul]
    have hTaff_two : 2 • Taff = 0 := by
      dsimp [Taff]
      exact WeierstrassXReflection.two_nsmul_twoTorsionPoint
        S.rationalCurve_a₃ S.rationalCurve_a₆ (S.a₄_twoAdic_exact hbe).1
    rw [hTaff_two]
    exact (baseChangePointHom S.rationalCurve).map_zero
  have hTsrc_neg : -Tsrc = Tsrc := by
    exact (eq_neg_of_add_eq_zero_left (by simpa [two_nsmul] using hTsrc_two)).symm
  let Timg : EllipticTorsionRepresentation.Points E' := φ Tsrc
  have hTimg_two : 2 • Timg = 0 := by
    change 2 • φ Tsrc = 0
    rw [← map_nsmul, hTsrc_two, map_zero]
  have hTimg_ne : Timg ≠ 0 := by
    intro hz
    have hm : Tsrc ∈ φ.ker := by
      change φ Tsrc = 0
      simpa [Timg] using hz
    rw [S.residual_integer_kernel_pointHom_ker hp2 L hline hL.isStable] at hm
    exact (S.residual_twoTorsion_outside hp2 L Tsrc hTsrc_ne hTsrc_neg) hm
  have hTimg_fixed : ∀ σ : Field.absoluteGaloisGroup ℚ,
      pointAction E' σ Timg = Timg := by
    intro σ
    rw [← S.residual_integer_kernel_pointHom_equivariant hp2 L hline hL.isStable σ Tsrc]
    have hTsrc_fixed : pointAction S.rationalCurve σ Tsrc = Tsrc := by
      change pointAction S.rationalCurve σ (baseChangePoint S.rationalCurve Taff) =
        baseChangePoint S.rationalCurve Taff
      exact pointAction_baseChange S.rationalCurve σ Taff
    rw [hTsrc_fixed]
  obtain ⟨T', hT'base⟩ := exists_baseChangePoint_of_fixed E' Timg hTimg_fixed
  have hT'_ne : T' ≠ 0 := by
    intro hz
    apply hTimg_ne
    rw [← hT'base, hz]
    rfl
  have hT'_two : 2 • T' = 0 := by
    apply baseChangePoint_injective E'
    change baseChangePointHom E' (2 • T') = 0
    rw [map_nsmul]
    have hT'base_hom : baseChangePointHom E' T' = Timg := hT'base
    rw [hT'base_hom, hTimg_two]
  obtain ⟨P, R, hP, hpR, hR, hRbase⟩ :=
    S.exists_rational_torsion_on_integer_kernel hp2 L hline hL
  let Q := T' + R
  have hpT' : p • T' = T' := by
    obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    rw [hk, add_nsmul, mul_nsmul, hT'_two, nsmul_zero, one_nsmul, zero_add]
  have hpQ : p • Q = T' := by
    simp only [Q, nsmul_add, hpR, add_zero, hpT']
  have hQ_ne : Q ≠ 0 := by
    intro hQ
    have : T' = 0 := by simpa [hQ] using hpQ.symm
    exact hT'_ne this
  have h2R : 2 • R ≠ 0 := by
    intro h2R
    have hRord : addOrderOf R = p := addOrderOf_eq_prime hpR hR
    have hd : p ∣ 2 := by
      rw [← hRord]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2R
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | htwo
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp2 htwo
  have h2Q : 2 • Q ≠ 0 := by
    simpa [Q, nsmul_add, hT'_two] using h2R
  have h2pQ : (2 * p) • Q = 0 := by
    calc
      (2 * p) • Q = p • (2 • Q) := by rw [mul_nsmul, smul_comm]
      _ = 2 • (p • Q) := by rw [smul_comm]
      _ = 2 • T' := by rw [hpQ]
      _ = 0 := hT'_two
  have hQ_order : addOrderOf Q = 2 * p := by
    apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul (n := 2 * p)
    · exact Nat.mul_pos (by decide) (Nat.Prime.pos (Fact.out : p.Prime))
    · exact h2pQ
    · intro q hq hqdiv
      rcases (Nat.Prime.dvd_mul hq).mp hqdiv with hq_two | hq_p
      · have hqeq : q = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp hq_two with hqone | hqtwo
          · exact (hq.ne_one hqone).elim
          · exact hqtwo
        subst q
        rw [Nat.mul_div_cancel_left p Nat.zero_lt_two]
        exact fun hz => hT'_ne (by simpa [hpQ] using hz)
      · have hqeq : q = p := by
          rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hq_p with hqone | hqprime
          · exact (hq.ne_one hqone).elim
          · exact hqprime
        subst q
        rw [Nat.mul_div_cancel 2 (Nat.Prime.pos (Fact.out : p.Prime))]
        exact h2Q
  exact ⟨Q, hQ_order⟩

/--
`a ≡ 7 mod 8` から `Even S.b` を既存の正規化補題で供給する公開ラッパー。
本体の証明を重複させず、7側の Source では偶数性を別引数として要求しない。
-/
theorem residual_cofixed_implies_rational_two_p_torsion_of_seven
    (hp2 : p ≠ 2) (ha8 : S.a % 8 = 7)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hL : IsCofixedOn S.residualRepresentation L) :
    ∃ Q : ((S.residualIntegerKernelModel L hline hL.isStable).map
      (Int.castRingHom ℚ)).toAffine.Point,
      addOrderOf Q = 2 * p :=
  S.residual_cofixed_implies_rational_two_p_torsion hp2
    (S.b_even_of_a_mod_eight_seven ha8) L hline hL

end DkMath.FLT.Frey.Source
