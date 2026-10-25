import DkMath.Lib.RepresentationTheory.CofixedDeterminant
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.StdBasis

#print "file: Note032CofixedDeterminantBoundary"

/-!
032-005Bの境界。安定性だけ、あるいは一次元性を欠く条件では行列式倍の公式は成立しない。
指標と逆指標を区別し、固定した基底の右上成分も保持する。
三次元の非可逆な自己準同型には一般核を適用し、二次元性・可逆性が不要なことを確認する。
-/
namespace CofixedDeterminantTest
open Module DkMath.Lib.RepresentationTheory

/-- 第一座標軸を第二射影の核として取る。 -/
def axis : Submodule ℚ (ℚ × ℚ) := (LinearMap.snd ℚ ℚ ℚ).ker

/-- 同じ軸の非零性・真性から次元1を確認する。 -/
theorem axis_finrank : finrank ℚ axis = 1 := by
  have hbot : axis ≠ ⊥ := by
    intro he
    have hm : ((1, 0) : ℚ × ℚ) ∈ axis := rfl
    rw [he, Submodule.mem_bot] at hm
    exact one_ne_zero (congrArg Prod.fst hm)
  have htop : axis ≠ ⊤ := by
    intro he
    have hm : ((0, 1) : ℚ × ℚ) ∈ axis := he ▸ Submodule.mem_top
    exact one_ne_zero hm
  exact (proper_nonzero_iff_finrank_one (by simp : finrank ℚ (ℚ × ℚ) = 2) axis).mp ⟨hbot, htop⟩

/-- 二つの座標へ別々のスカラーを掛ける自己準同型。 -/
noncomputable def diagonal (a b : ℚ) : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) :=
  (a • LinearMap.id : ℚ →ₗ[ℚ] ℚ).prodMap (b • LinearMap.id)

/-- 行列式は両座標の係数の積である。一般核から独立に計算する。 -/
theorem diagonal_det (a b : ℚ) : LinearMap.det (diagonal a b) = a * b := by
  simp [diagonal, LinearMap.det_prodMap]

/-- diag(2,3)は軸を保存するが商を固定しない。軸上の作用2は行列式6と異なる。 -/
theorem stable_guard_boundary :
    (∀ x ∈ axis, diagonal 2 3 x ∈ axis) ∧
      (¬ ∀ x, diagonal 2 3 x - x ∈ axis) ∧
      diagonal 2 3 (1, 0) ≠ LinearMap.det (diagonal 2 3) • ((1, 0) : ℚ × ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change 3 * x.2 = 0
    change x.2 = 0 at hx
    rw [hx, mul_zero]
  · intro h
    have he := h (0, 1)
    norm_num [axis, diagonal] at he
  · rw [diagonal_det]
    intro he
    have hf := congrArg Prod.fst he
    norm_num [diagonal] at hf

/-- 全空間なら差の所属は自動だが、次元1ではないので行列式倍の公式は成立しない。 -/
theorem dimension_guard_boundary :
    finrank ℚ (⊤ : Submodule ℚ (ℚ × ℚ)) = 2 ∧
      (∀ x, diagonal 2 3 x - x ∈ (⊤ : Submodule ℚ (ℚ × ℚ))) ∧
      diagonal 2 3 (1, 0) ≠ LinearMap.det (diagonal 2 3) • ((1, 0) : ℚ × ℚ) := by
  exact ⟨by simp, fun _ => Submodule.mem_top, stable_guard_boundary.2.2⟩

/-- 非自明な指標と非零の右上成分を持つ同じ群表現。商の第二座標は固定される。 -/
def unitShear : Representation ℚ ℚˣ (ℚ × ℚ) where
  toFun u := {
    toFun v := ((u : ℚ) * v.1 + ((u : ℚ) - 1) * v.2, v.2)
    map_add' := by
      intro v w
      apply Prod.ext
      · dsimp
        ring
      · rfl
    map_smul' := by
      intro c v
      apply Prod.ext
      · dsimp
        ring
      · rfl }
  map_one' := by ext <;> simp
  map_mul' := by
    intro u v
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · dsimp
      ring
    · rfl

/-- unitShearの商固定を実際の座標で確認する。直線上の固定とは区別する。 -/
theorem unitShear_cofixed : IsCofixedOn unitShear axis := by
  intro u x
  change x.2 - x.2 = 0
  exact sub_self _

/-- 行列式指標は単元uそのもの。逆指標ではない。 -/
theorem unitShear_det (u : ℚˣ) : LinearMap.det (unitShear u) = (u : ℚ) := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℚ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Basis.coe_finTwoProd_repr, unitShear]

/-- 指標2と逆指標1/2を区別し、同じ基底の右上成分1を保持する。
一般核の指標スカラー公式と行列の形の両方を適用する。 -/
theorem character_orientation_and_matrix :
    let u : ℚˣ := Units.mk0 2 (by norm_num)
    unitShear u (1, 0) = (u : ℚ) • ((1, 0) : ℚ × ℚ) ∧
      unitShear u (1, 0) ≠ ((u⁻¹ : ℚˣ) : ℚ) • ((1, 0) : ℚ × ℚ) ∧
      (matrixGroupHom unitShear (Basis.finTwoProd ℚ) u : Matrix (Fin 2) (Fin 2) ℚ) = !![2, 1; 0, 1] := by
  let u : ℚˣ := Units.mk0 2 (by norm_num)
  refine ⟨CofixedDeterminant.apply_eq_character_smul_of_cofixed unitShear axis axis_finrank
    unitShear_cofixed (MonoidHom.id ℚˣ) (fun v => (unitShear_det v).symm) u (by rfl), ?_, ?_⟩
  · intro he
    have hf := congrArg Prod.fst he
    norm_num [unitShear, u] at hf
  · have hspan : axis = Submodule.span ℚ ({(Basis.finTwoProd ℚ) 0} : Set (ℚ × ℚ)) := by
      apply eq_span_singleton_of_mem_of_finrank_eq_one axis_finrank ?_ ?_
      · rw [Basis.finTwoProd_zero]
        rfl
      · simp
    have hm := CofixedDeterminant.basis_line_matrix unitShear (Basis.finTwoProd ℚ)
      (hspan ▸ unitShear_cofixed) u
    rw [unitShear_det] at hm
    rw [hm]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [matrixGroupHom_val, LinearMap.toMatrix_apply,
      Basis.coe_finTwoProd_repr, unitShear, u]

/-- 三次元で第一座標だけを零へ送る非可逆な自己準同型。 -/
def projectionThree : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 3 → ℚ) where
  toFun v i := if i = 0 then 0 else v i
  map_add' := by intro v w; ext i; by_cases hi : i = 0 <;> simp [hi]
  map_smul' := by intro c v; ext i; by_cases hi : i = 0 <;> simp [hi]

/-- 周囲が三次元で作用素が非可逆でも、同じ一次元像の差から一般核を適用できる。 -/
theorem noninvertible_higher_dimension :
    finrank ℚ (Fin 3 → ℚ) = 3 ∧ LinearMap.det projectionThree = 0 ∧
      projectionThree (Pi.single 0 1) = LinearMap.det projectionThree • (Pi.single 0 1 : Fin 3 → ℚ) := by
  let v : Fin 3 → ℚ := Pi.single 0 1
  have hv : v ≠ 0 := by intro he; have := congrFun he 0; norm_num [v] at this
  have hzero : projectionThree v = 0 := by ext i; fin_cases i <;> simp [projectionThree, v]
  have hdet : LinearMap.det projectionThree = 0 := by
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
    intro he
    have hm : v ∈ LinearMap.ker projectionThree := hzero
    rw [he, Submodule.mem_bot] at hm
    exact hv hm
  refine ⟨by simp, hdet, ?_⟩
  apply CofixedDeterminant.apply_eq_det_smul_of_sub_mem projectionThree
    (Submodule.span ℚ ({v} : Set (Fin 3 → ℚ))) (finrank_span_singleton hv) ?_
    (Submodule.mem_span_singleton_self v)
  intro x
  apply Submodule.mem_span_singleton.mpr
  refine ⟨-x 0, ?_⟩
  ext i
  fin_cases i <;> simp [projectionThree, v]

end CofixedDeterminantTest
