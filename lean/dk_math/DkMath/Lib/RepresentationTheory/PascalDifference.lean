/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap

#print "file: DkMath.Lib.RepresentationTheory.PascalDifference"

/-!
# Pascal行から残余表現の差分作用素へ

素数pのPascal行の内部係数はpで割れるので、Fₚ[X]では(X−1)^p=X^p−1となる。
この多項式等式を作用素Tへ評価すると、(T−1)^p=T^p−1を得る。
End(V)が非可換であっても一つの作用素への評価は可能であり、V=0も許す。
End(V)自身に標数pを仮定すると零空間の場合を誤って除くため、係数体で先に証明する。

従って、表現ρでρ(g^p)=1なら(ρ(g)−1)^p=0。これは一つの元のp乗作用に
前提を置く条件付きの冪零性であり、慣性群の作用が自明であることや、表現全体の
可約性・FLTの矛盾は導かない。正則／非正則の区別を使わない共通のPascal構造である。
-/
namespace DkMath.Lib.RepresentationTheory.PascalDifference
open Polynomial Module
variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- Pascalの内項が法pで消えた、多項式としての差分冪等式。 -/
theorem polynomial_difference_pow : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
  simpa only [one_pow] using (sub_pow_char (p := p) (X : (ZMod p)[X]) 1)

/-- 有限次元性や非零性なしで、同じ作用素の差分冪へ輸送する。 -/
theorem end_difference_pow (T : End (ZMod p) V) : (T - 1) ^ p = T ^ p - 1 := by
  have h := congrArg (aeval T) (polynomial_difference_pow (p := p))
  simpa only [map_pow, map_sub, aeval_X, map_one] using h

/-- 実際の残余表現にも直接適用できる差分恒等式。 -/
theorem representation_difference_pow {G : Type*} [Monoid G]
    (ρ : Representation (ZMod p) G V) (g : G) : (ρ g - 1) ^ p = ρ (g ^ p) - 1 := by
  rw [end_difference_pow, map_pow]

/-- p乗が恒等的に作用する元では、差分作用素はp段以内で零になる。 -/
theorem difference_pow_eq_zero_of_image_pow {G : Type*} [Monoid G]
    (ρ : Representation (ZMod p) G V) (g : G) (hg : ρ (g ^ p) = 1) :
    (ρ g - 1) ^ p = 0 := by rw [representation_difference_pow, hg, sub_self]

/-- 群内でg^p=1なら上の作用の前提を実際に供給できる。 -/
theorem difference_pow_eq_zero_of_pow_eq_one {G : Type*} [Monoid G]
    (ρ : Representation (ZMod p) G V) (g : G) (hg : g ^ p = 1) :
    (ρ g - 1) ^ p = 0 :=
  difference_pow_eq_zero_of_image_pow ρ g (by rw [hg, map_one])

end DkMath.Lib.RepresentationTheory.PascalDifference
