/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
import Mathlib.Topology.Algebra.MulAction

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionContinuity"

/-!
# Krull位相から実際のtorsion点の離散連続作用へ

代数閉包の各座標はK上代数的なので、その座標を固定するガロア部分群は開く。
有限座標(x,y)の固定条件は二つの開集合の交わりとなる。
点への単射を通じて同じ結論をtorsion点へ制限すると、離散位相での連続群作用を得る。
E[p]の位数p²や次元2を先に仮定する必要はない。

ここで証明するのはガロア変数も含む実際の連続性である。各線形写像だけが連続という
条件とは区別する。一方、有限性未証明の段階では、表現全体の核が開くことや、
ある素数で慣性群が自明に作用することまでは結論しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open WeierstrassCurve
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 幾何学的な点を固定する絶対ガロア元の集合は開く。 -/
theorem pointAction_stabilizer_isOpen (P : Points E) :
    IsOpen {σ : Field.absoluteGaloisGroup K | pointAction E σ P = P} := by
  classical
  cases P with
  | zero =>
    have he : {σ : Field.absoluteGaloisGroup K | pointAction E σ .zero = .zero} = Set.univ := by
      ext σ
      constructor
      · intro _; trivial
      · intro _; rfl
    rw [he]
    exact isOpen_univ
  | some x y h =>
    have hx := stabilizer_isOpen_of_isIntegral (K := K) x
    have hy := stabilizer_isOpen_of_isIntegral (K := K) y
    have he : {σ : Field.absoluteGaloisGroup K | pointAction E σ (.some x y h) = .some x y h} =
        (MulAction.stabilizer Gal(AlgebraicClosure K/K) x : Set Gal(AlgebraicClosure K/K)) ∩
          (MulAction.stabilizer Gal(AlgebraicClosure K/K) y : Set Gal(AlgebraicClosure K/K)) := by
      ext σ
      change pointAction E σ (.some x y h) = .some x y h ↔ σ.toAlgHom x = x ∧ σ.toAlgHom y = y
      change Affine.Point.some (σ.toAlgHom x) (σ.toAlgHom y) _ = Affine.Point.some x y h ↔ _
      simp only [Affine.Point.some.injEq]
    rw [he]
    exact hx.inter hy

/-- torsion点には離散位相を入れる。ガロア群には既存のKrull位相を保つ。 -/
instance torsionTopology (n : ℕ) : TopologicalSpace (Torsion E n) := ⊥

/-- 定義した位相は離散位相である。 -/
instance torsionDiscreteTopology (n : ℕ) : DiscreteTopology (Torsion E n) := ⟨rfl⟩

/-- 同じ点への単射によって、torsion点の固定部分群も開く。 -/
theorem torsion_stabilizer_isOpen (n : ℕ) (P : Torsion E n) :
    IsOpen (MulAction.stabilizer (Field.absoluteGaloisGroup K) P : Set (Field.absoluteGaloisGroup K)) := by
  have he : (MulAction.stabilizer (Field.absoluteGaloisGroup K) P : Set (Field.absoluteGaloisGroup K)) =
      {σ : Field.absoluteGaloisGroup K | pointAction E σ P.val = P.val} := by
    ext σ
    change representation E n σ P = P ↔ pointAction E σ P.val = P.val
    exact Subtype.ext_iff
  rw [he]
  exact pointAction_stabilizer_isOpen E P.val

/-- ガロア変数とtorsion点変数についての同時連続性。 -/
instance torsionContinuousSMul (n : ℕ) : ContinuousSMul (Field.absoluteGaloisGroup K) (Torsion E n) :=
  continuousSMul_iff_stabilizer_isOpen.mpr (torsion_stabilizer_isOpen E n)

/-- 各torsion点の軌道写像は、Krull位相から離散点群への連続写像となる。 -/
theorem representation_orbit_continuous (n : ℕ) (P : Torsion E n) :
    Continuous (fun σ : Field.absoluteGaloisGroup K => representation E n σ P) := by
  change Continuous (fun σ : Field.absoluteGaloisGroup K => σ • P)
  fun_prop

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
