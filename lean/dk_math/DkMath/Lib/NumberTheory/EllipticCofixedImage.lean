/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.CofixedImage
import DkMath.Lib.NumberTheory.EllipticStableLine

#print "file: DkMath.Lib.NumberTheory.EllipticCofixedImage"

/-!
# NOTE-032-005C₁: 同じ核の点群写像から標的上の有理捩れ点へ

[DkMath.Lib] 実際の点群準同型φ:E(K̄)→E'(K̄)はp捩れをp捩れへ写す。
同じ核pointSubgroup E p Lとガロア同変性を明示すると、Cofixed直線Lの商の固定性は
φ(E[p])の点ごとの固定性となる。元のE[p]の次元2とLの次元1から、像は次元1で位数p。
その非零固定点を標的E'上の非零K有理p捩れ点へ降下させる。

φは実点上の加法準同型として入力する。曲線の射、Vélu公式、isogenyの次数や存在は
本章では構成しない。抽象的な商群を楕円曲線と呼ばず、標的E'の存在も入力に残す。
特に元の曲線Eの有理捩れ排除を、別の曲線E'へ無条件に移してはならない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open DkMath.Lib.RepresentationTheory
variable {K : Type*} [Field K] (E E' : WeierstrassCurve K)

/-- [DkMath.Lib] 同じ点群準同型を、同じ指数nの実際の捩れ点へ制限する。
加法性からn倍を保存し、標準ZMod線形構造を使う。 -/
noncomputable def torsionPointMap (n : ℕ) (φ : Points E →+ Points E') :
    Torsion E n →ₗ[ZMod n] Torsion E' n :=
  AddMonoidHom.toZModLinearMap n
    { toFun := fun P => ⟨φ P.val, by
          change n • φ P.val = 0
          have hk : n • P.val = 0 := P.property
          rw [← map_nsmul, hk, map_zero]⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun P Q => Subtype.ext (map_add φ P.val Q.val) }

/-- [DkMath.Lib] 捩れへの制限後も、値は元の同じ点群写像φの値である。 -/
theorem torsionPointMap_val (n : ℕ) (φ : Points E →+ Points E') (P : Torsion E n) :
    (torsionPointMap E E' n φ P).val = φ P.val := rfl

/-- [DkMath.Lib] 点群上のガロア同変性を同じ捩れ空間の同変性へ運ぶ。 -/
theorem torsionPointMap_equivariant (n : ℕ) (φ : Points E →+ Points E')
    (hφ : ∀ σ P, φ (pointAction E σ P) = pointAction E' σ (φ P))
    (σ : Field.absoluteGaloisGroup K) (P : Torsion E n) :
    torsionPointMap E E' n φ (representation E n σ P) =
      representation E' n σ (torsionPointMap E E' n φ P) :=
  Subtype.ext (hφ σ P.val)

variable (p : ℕ) [Fact p.Prime]

/-- [DkMath.Lib] 実点群での核pointSubgroupの一致を、同じE[p]上の核Lの一致へ戻す。
二つの点が同じ実点を表すことをSubtypeの単射性で確認する。 -/
theorem torsionPointMap_ker (φ : Points E →+ Points E')
    (L : Submodule (ZMod p) (Torsion E p)) (hker : φ.ker = pointSubgroup E p L) :
    LinearMap.ker (torsionPointMap E E' p φ) = L := by
  ext P
  change (torsionPointMap E E' p φ P = 0) ↔ P ∈ L
  rw [Subtype.ext_iff]
  change φ P.val = 0 ↔ P ∈ L
  change P.val ∈ φ.ker ↔ P ∈ L
  rw [hker]
  constructor
  · rintro ⟨Q, hQ, heq⟩
    have : Q = P := Subtype.ext heq
    change Q ∈ L at hQ
    rwa [this] at hQ
  · intro hP
    exact ⟨P, hP, rfl⟩

/-- [DkMath.Lib] 同じ核のガロア同変な実点写像では、Cofixed商の像の各点が固定される。
核の一致と同変性を実際のφについて保持する。 -/
theorem cofixed_pointMap_image_fixed (φ : Points E →+ Points E')
    (L : Submodule (ZMod p) (Torsion E p)) (hker : φ.ker = pointSubgroup E p L)
    (hφ : ∀ σ P, φ (pointAction E σ P) = pointAction E' σ (φ P))
    (hL : IsCofixedOn (representation E p) L)
    (P : Torsion E p) (σ : Field.absoluteGaloisGroup K) :
    pointAction E' σ (φ P.val) = φ P.val := by
  have he := CofixedImage.image_fixed (representation E p) (representation E' p)
    (torsionPointMap E E' p φ) L hL (torsionPointMap_ker E E' p φ L hker).ge
    (torsionPointMap_equivariant E E' p φ hφ) P σ
  exact congrArg Subtype.val he

variable [CharZero K] [E.IsElliptic]

/-- [DkMath.Lib] 正確に同じ一次元核を持つ点群写像のp捩れ像の次元は1。
標的が二次元であることや写像の全射性は要求しない。 -/
theorem finrank_torsionPointMap_range (φ : Points E →+ Points E')
    (L : Submodule (ZMod p) (Torsion E p)) (hline : Module.finrank (ZMod p) L = 1)
    (hker : φ.ker = pointSubgroup E p L) :
    Module.finrank (ZMod p) (LinearMap.range (torsionPointMap E E' p φ)) = 1 :=
  CofixedImage.finrank_range _ L (finrank_torsion_prime E p) hline
    (torsionPointMap_ker E E' p φ L hker)

/-- [DkMath.Lib] 同じp捩れ像の位数はp。元のE[p]全体の位数p²と区別する。 -/
theorem card_torsionPointMap_range (φ : Points E →+ Points E')
    (L : Submodule (ZMod p) (Torsion E p)) (hline : Module.finrank (ZMod p) L = 1)
    (hker : φ.ker = pointSubgroup E p L) :
    Nat.card (LinearMap.range (torsionPointMap E E' p φ)) = p := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p),
    finrank_torsionPointMap_range E E' p φ L hline hker, Nat.card_zmod, pow_one]

/-- [DkMath.Lib] Cofixed直線を正確に核とする同変な実点写像から、標的上の非零有理捩れ点を得る。
元P∉L、標的の実際のK有理点Q、同じφ(P)との基底変換等式を全て残す。
φの幾何学的構成と存在は入力であり、isogenyの存在定理ではない。 -/
theorem exists_rational_torsion_of_cofixed_pointMap [DecidableEq K]
    (φ : Points E →+ Points E') (L : Submodule (ZMod p) (Torsion E p))
    (hline : Module.finrank (ZMod p) L = 1) (hker : φ.ker = pointSubgroup E p L)
    (hφ : ∀ σ P, φ (pointAction E σ P) = pointAction E' σ (φ P))
    (hL : IsCofixedOn (representation E p) L) :
    ∃ (P : Torsion E p) (Q : E'.toAffine.Point),
      P ∉ L ∧ p • Q = 0 ∧ Q ≠ 0 ∧ baseChangePoint E' Q = φ P.val := by
  obtain ⟨P, hP, hne, hfixed⟩ := CofixedImage.exists_nonzero_fixed_image
    (representation E p) (representation E' p) (torsionPointMap E E' p φ) L
    (finrank_torsion_prime E p) hline (torsionPointMap_ker E E' p φ L hker) hL
    (torsionPointMap_equivariant E E' p φ hφ)
  obtain ⟨Q, hQ, heq⟩ := exists_rational_torsion_of_fixed E' p
    (torsionPointMap E E' p φ P) hfixed
  refine ⟨P, Q, hP, hQ, ?_, heq⟩
  intro hz
  apply hne
  apply Subtype.ext
  rw [← heq, hz]
  rfl

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
