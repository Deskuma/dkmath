/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.Algebra.FiniteAdditiveTorsionCard"

/-!
# 有限加法群の素数捩れと群の位数

乗法的還元の成分群へ進む前に、幾何学から独立した群論の核を固定する。
有限加法群 `G` に非零の `q`-捩れ点があれば、素数 `q` は `Nat.card G` を割る。

この補題は成分群そのものを構成しない。したがって、Tate 曲線や Néron 模型を
先取りせず、後段で得られる「有理捩れ点から成分群への非零像」を差し込むための
最小インターフェースだけを供給する。
-/

namespace DkMath.Lib.Algebra

noncomputable section

variable {G : Type*} [AddGroup G]

/--
Any nonzero `q`-torsion element in an additive group forces `q` to divide the
natural cardinality of that group (for an infinite group this cardinality is
zero). In the finite case this is the familiar divisibility statement. The proof is the textbook two-step argument:
prime order is obtained from `q • Q = 0` and `Q ≠ 0`, then the order of an
element divides the cardinality of the finite group.
-/
theorem prime_dvd_natCard_of_nsmul_eq_zero_of_ne_zero
    {q : ℕ} [Fact q.Prime] (Q : G)
    (hQq : q • Q = 0) (hQ0 : Q ≠ 0) :
    q ∣ Nat.card G := by
  have horder : addOrderOf Q = q := addOrderOf_eq_prime hQq hQ0
  rw [← horder]
  exact addOrderOf_dvd_natCard Q

/--
If the natural cardinality of an additive group is not divisible by a prime
`q`, then its only `q`-torsion point is zero.  This is the contrapositive of
`prime_dvd_natCard_of_nsmul_eq_zero_of_ne_zero` and is the form used for a
smooth reduced point group whose cardinality has already been computed.
-/
theorem eq_zero_of_nsmul_eq_zero_of_not_dvd_natCard
    {q : ℕ} [Fact q.Prime] (hcard : ¬ q ∣ Nat.card G) (Q : G)
    (hQq : q • Q = 0) : Q = 0 := by
  by_contra hQ0
  exact hcard (prime_dvd_natCard_of_nsmul_eq_zero_of_ne_zero Q hQq hQ0)

/-
The component-group interface used later is naturally a homomorphism.  This
corollary records the exact transport step separately: the source need not be
finite, and only the image of the torsion point is required to be nonzero.
-/
/--
If a homomorphism sends a nonzero `q`-torsion point to a nonzero point, then
`q` divides the natural cardinality of the target group.  This is the textbook
component-group reduction: apply the preceding finite-group lemma to the
image, using `map_nsmul` to transport the torsion equation.
-/
theorem prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero
    {A : Type*} [AddGroup A] {q : ℕ} [Fact q.Prime]
    (φ : A →+ G) (Q : A) (hQq : q • Q = 0) (hφQ : φ Q ≠ 0) :
    q ∣ Nat.card G := by
  apply prime_dvd_natCard_of_nsmul_eq_zero_of_ne_zero (φ Q)
  · rw [← map_nsmul, hQq, map_zero]
  · exact hφQ

/--
Let `φ : A →+ G` be the prospective component map.  If its kernel has no
nonzero `q`-torsion, then every nonzero `q`-torsion point of `A` has nonzero
image.  Consequently `q` divides `Nat.card G`.

This is the precise group-theoretic form needed for multiplicative reduction:
the local geometry need only prove that a `q`-torsion point lying in the zero
component (the kernel of the component map) is zero.  It does *not* construct
a component group, prove its finiteness, or assert this kernel condition for a
particular elliptic curve.
-/
theorem prime_dvd_natCard_of_torsion_kernel_trivial
    {A : Type*} [AddGroup A] {q : ℕ} [Fact q.Prime]
    (φ : A →+ G)
    (hker : ∀ x : A, q • x = 0 → φ x = 0 → x = 0)
    (R : A) (hRq : q • R = 0) (hR0 : R ≠ 0) :
    q ∣ Nat.card G := by
  apply prime_dvd_natCard_of_addMonoidHom_map_nsmul_eq_zero_of_map_ne_zero φ R hRq
  intro hφR
  exact hR0 (hker R hRq hφR)

end
end DkMath.Lib.Algebra
