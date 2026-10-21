/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_WeierstrassCurve_Affine_weilPairing0_galois.lean.
Upstream blob: cc05c14d0a942efea28586bee5cc9b8d1bea7c41
Modified for DkMath: construct canonical ring equivalences, use actual Point.map and
existing generic-point adapters, remove export macros and assumed extension providers.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation

#print "file: DkMath.Lib.NumberTheory.EllipticFunctionFieldGalois"

/-!
# 係数のガロア作用を座標環と関数体へ持ち上げる

曲線の係数は基礎体Fにあり、K上のF自己同型で方程式が保存される。
係数ごとの作用を座標環上に構成し、逆作用を逆写像として分数体へ延長する。
この写像はK線形ではなくσ半線形である。一般点と定数点の像を追うことで、
平行移動との交換則を証明する。Weil関数や非退化性を入力に取らない。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate nonZeroDivisors
namespace DkMath.Lib.NumberTheory.EllipticFunctionField
section GalRing

variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

/-- 基底変換された曲線の係数は基礎体にあるので、係数自己同型で方程式が保存される。 -/
theorem galRing_polynomial_map (σ : K ≃ₐ[F] K) :
    (W⁄K).polynomial.map (mapRingHom (σ : K →+* K)) = (W⁄K).polynomial := by
  have h := (baseChange_polynomial (W := W) (f := (σ : K →ₐ[F] K))).symm
  convert h using 2
  rfl
/-- 係数を写し、変数を固定する座標環準同型を方程式の根から構成する。 -/
noncomputable def galRingHom (σ : K ≃ₐ[F] K) :
    (W⁄K).CoordinateRing →+* (W⁄K).CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom (σ : K →+* K))
    (AdjoinRoot.root (W⁄K).polynomial) <| by
      rw [← eval₂_map, galRing_polynomial_map, AdjoinRoot.eval₂_root]
/-- 二変数の多項式類に対する係数ごとの作用。 -/
theorem galRingHom_mk (σ : K ≃ₐ[F] K) (p : K[X][Y]) :
    galRingHom W σ (CoordinateRing.mk (W⁄K) p) =
      CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K))) := by
  rw [galRingHom, CoordinateRing.mk, AdjoinRoot.lift_mk, ← eval₂_map]
  exact AdjoinRoot.aeval_eq <| p.map <| mapRingHom (σ : K →+* K)
/-- 係数作用の合成を座標環に持ち上げる。 -/
theorem galRingHom_comp (σ τ : K ≃ₐ[F] K) (z : (W⁄K).CoordinateRing) :
    galRingHom W σ (galRingHom W τ z) = galRingHom W (σ * τ) z := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    change galRingHom W σ (galRingHom W τ (CoordinateRing.mk (W⁄K) p)) =
      galRingHom W (σ * τ) (CoordinateRing.mk (W⁄K) p)
    rw [galRingHom_mk, galRingHom_mk, galRingHom_mk, Polynomial.map_map, Polynomial.mapRingHom_comp]
    rfl
/-- 恒等係数作用は座標環でも恒等となる。 -/
theorem galRingHom_one (z : (W⁄K).CoordinateRing) : galRingHom W 1 z = z := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    change galRingHom W 1 (CoordinateRing.mk (W⁄K) p) = CoordinateRing.mk (W⁄K) p
    have h1 : ((1 : K ≃ₐ[F] K) : K →+* K) = RingHom.id K := RingHom.ext fun _ => rfl
    rw [galRingHom_mk, h1, Polynomial.mapRingHom_id, Polynomial.map_id]
/-- 逆作用で逆写像を与える、座標環上の実際の環同型。係数体上の線形性は要求しない。 -/
noncomputable def galRingEquiv (σ : K ≃ₐ[F] K) :
    (W⁄K).CoordinateRing ≃+* (W⁄K).CoordinateRing :=
  RingEquiv.ofRingHom (galRingHom W σ) (galRingHom W σ⁻¹)
    (RingHom.ext fun z => by
      rw [RingHom.comp_apply, RingHom.id_apply, galRingHom_comp, mul_inv_cancel, galRingHom_one])
    (RingHom.ext fun z => by
      rw [RingHom.comp_apply, RingHom.id_apply, galRingHom_comp, inv_mul_cancel, galRingHom_one])
/-- 選択に頼らず構成した座標環同型の、多項式類への作用。 -/
theorem galRingEquiv_mk (σ : K ≃ₐ[F] K) (p : K[X][Y]) :
    galRingEquiv W σ (CoordinateRing.mk (W⁄K) p) =
      CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K))) := galRingHom_mk W σ p
/-- 座標差イデアルは、写した点の座標差イデアルへ移る。 -/
theorem galRing_map_XYIdeal (σ : K ≃ₐ[F] K) (φ : (W⁄K).CoordinateRing →+* (W⁄K).CoordinateRing)
    (hφ : ∀ p : K[X][Y], φ (CoordinateRing.mk (W⁄K) p) =
      CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K)))) (x y : K) :
    (CoordinateRing.XYIdeal (W⁄K) x (C y)).map φ = CoordinateRing.XYIdeal (W⁄K) (σ x) (C (σ y)) := by
  rw [CoordinateRing.XYIdeal, Ideal.map_span, Set.image_pair, CoordinateRing.XClass,
    CoordinateRing.YClass, hφ, hφ]
  simp only [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom, RingHom.coe_coe]
  rfl
/-- 座標環の実際の環同型を、その同じ分数体の環同型へ延長する。 -/
noncomputable def galFunctionFieldEquiv (σ : K ≃ₐ[F] K) :
    (W⁄K).FunctionField ≃+* (W⁄K).FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (galRingEquiv W σ)
/-- 分数体への延長は、座標環からの包含と可換である。 -/
theorem galFunctionFieldEquiv_algebraMap (σ : K ≃ₐ[F] K) (a : (W⁄K).CoordinateRing) :
    galFunctionFieldEquiv W σ (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField a) =
      algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (galRingEquiv W σ a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
/-- 関数体内の多項式類でも係数ごとのガロア作用に一致する。 -/
theorem galFunctionFieldEquiv_mk (σ : K ≃ₐ[F] K) (p : K[X][Y]) :
    galFunctionFieldEquiv W σ
      (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
        algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField
          (CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K)))) := by
  rw [galFunctionFieldEquiv_algebraMap, galRingEquiv_mk]
end GalRing
section GalA

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] (W : WeierstrassCurve F)
  (σ : K ≃ₐ[F] K)


omit [DecidableEq K] in
/-- 関数体の係数には元の自己同型が作用する。一般には係数体を固定しない。 -/
theorem gal_algebraMap (c : K) :
    (galFunctionFieldEquiv W σ).toRingHom (algebraMap K (W⁄K).FunctionField c) = algebraMap K (W⁄K).FunctionField (σ c) := by
  have h := (galFunctionFieldEquiv_mk W σ) (C (C c))
  rw [Polynomial.map_C, coe_mapRingHom, Polynomial.map_C, RingHom.coe_coe] at h
  rw [IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField c,
    IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField (σ c)]
  exact h
omit [DecidableEq K] in
/-- 基礎体の係数は固定するため、基礎体上の代数準同型として扱える。 -/
theorem gal_algebraMap_base (c : F) :
    (galFunctionFieldEquiv W σ).toRingHom (algebraMap F (W⁄K).FunctionField c) = algebraMap F (W⁄K).FunctionField c := by
  rw [IsScalarTower.algebraMap_apply F K (W⁄K).FunctionField c, gal_algebraMap W σ,
    AlgEquiv.commutes]
omit [DecidableEq K] in
/-- 変数xを固定する。 -/
theorem gal_genericX : (galFunctionFieldEquiv W σ).toRingHom (genericX W K) = genericX W K := by
  have h := (galFunctionFieldEquiv_mk W σ) (C X)
  rwa [Polynomial.map_C, coe_mapRingHom, Polynomial.map_X] at h
omit [DecidableEq K] in
/-- 変数yを固定する。 -/
theorem gal_genericY : (galFunctionFieldEquiv W σ).toRingHom (genericY W K) = genericY W K := by
  have h := (galFunctionFieldEquiv_mk W σ) Y
  rwa [Polynomial.map_X] at h
/-- 基礎体上では線形だが拡大係数体上では半線形な、実際の関数体準同型。 -/
noncomputable def galAlgHom : (W⁄K).FunctionField →ₐ[F] (W⁄K).FunctionField :=
  { (galFunctionFieldEquiv W σ).toRingHom with commutes' := gal_algebraMap_base W σ }
omit [DecidableEq K] in
/-- 基礎体上の代数準同型と環同型は、同じ元へ作用する。 -/
theorem galAlgHom_apply (h : (W⁄K).FunctionField) : galAlgHom W σ h = (galFunctionFieldEquiv W σ).toRingHom h := rfl

omit [DecidableEq K] in
/-- 一般点の座標x,yは固定され、一般点も固定される。 -/
theorem map_galAlgHom_genericPoint [W.IsElliptic] :
    Point.map (galAlgHom W σ) (genericPoint W K) = genericPoint W K := by
  rw [genericPoint, Point.map_some]
  congr 1
  · exact gal_genericX W σ
  · exact gal_genericY W σ
/-- 係数体の点への作用を、関数体の定数点への作用と同定する。 -/
theorem map_galAlgHom_baseChange (S : (W⁄K).Point) :
    Point.map (galAlgHom W σ) (Point.baseChange K (W⁄K).FunctionField S) =
      Point.baseChange K (W⁄K).FunctionField (Point.map (W' := W) σ.toAlgHom S) := by
  rcases S with _ | ⟨x, y, hxy⟩
  · rfl
  · rw [Point.map_some, Point.baseChange, Point.map_some, Point.map_some,
      Point.map_some]
    congr 1
    · exact gal_algebraMap W σ x
    · exact gal_algebraMap W σ y
/-- 係数の作用と平行移動の交換則。点は同じ係数写像で移動させる。 -/
theorem gal_transEquiv [IsAlgClosed K] [W.IsElliptic] (S : (W⁄K).Point) (f : (W⁄K).FunctionField) :
    (galFunctionFieldEquiv W σ).toRingHom (transEquiv W K S f) = transEquiv W K (Point.map (W' := W) σ.toAlgHom S) ((galFunctionFieldEquiv W σ).toRingHom f) := by
  have hQ : Point.map (galAlgHom W σ)
      (genericPoint W K + Point.baseChange K (W⁄K).FunctionField S) =
      genericPoint W K + Point.baseChange K (W⁄K).FunctionField (Point.map (W' := W) σ.toAlgHom S) := by
    rw [map_add, map_galAlgHom_genericPoint, map_galAlgHom_baseChange]
  have hx : (galFunctionFieldEquiv W σ).toRingHom (genericPoint W K + Point.baseChange K (W⁄K).FunctionField S).xc =
      (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (Point.map (W' := W) σ.toAlgHom S)).xc := by
    rw [← hQ, point_xc_map]
    rfl
  have hy : (galFunctionFieldEquiv W σ).toRingHom (genericPoint W K + Point.baseChange K (W⁄K).FunctionField S).yc =
      (genericPoint W K + Point.baseChange K (W⁄K).FunctionField (Point.map (W' := W) σ.toAlgHom S)).yc := by
    rw [← hQ, point_yc_map]
    rfl
  suffices H : (galFunctionFieldEquiv W σ).toRingHom.comp (transEquiv W K S : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField).toRingHom =
      (transEquiv W K (Point.map (W' := W) σ.toAlgHom S) : (W⁄K).FunctionField →ₐ[K] (W⁄K).FunctionField).toRingHom.comp (galFunctionFieldEquiv W σ).toRingHom from
    RingHom.congr_fun H f
  apply IsLocalization.ringHom_ext (nonZeroDivisors (W⁄K).CoordinateRing)
  refine RingHom.ext fun a => ?_
  induction a using AdjoinRoot.induction_on with
  | ih g =>
    change (galFunctionFieldEquiv W σ).toRingHom (transEquiv W K S (algebraMap _ (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) g))) =
      transEquiv W K (Point.map (W' := W) σ.toAlgHom S) ((galFunctionFieldEquiv W σ).toRingHom (algebraMap _ (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) g)))
    have hmap (p : K[X][Y]) : (galFunctionFieldEquiv W σ).toRingHom
        (algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField (CoordinateRing.mk (W⁄K) p)) =
        algebraMap (W⁄K).CoordinateRing (W⁄K).FunctionField
          (CoordinateRing.mk (W⁄K) (p.map (mapRingHom (σ : K →+* K)))) :=
      galFunctionFieldEquiv_mk W σ p
    rw [transEquiv_algebraMap, pointHom_mk, hmap, transEquiv_algebraMap, pointHom_mk,
      Polynomial.hom_eval₂, Polynomial.eval₂_map, hy]
    congr 1
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        aeval_C, gal_algebraMap W σ, coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, aeval_C]
      rfl
    · rw [RingHom.comp_apply, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
        hx, coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
end GalA
section Laws
variable {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F)

/-- 係数自己同型に関する半線形性。係数を固定するK線形写像とは区別する。 -/
theorem galFunctionFieldEquiv_const_mul (σ : K ≃ₐ[F] K) (a : K) (f : (W⁄K).FunctionField) :
    galFunctionFieldEquiv W σ (algebraMap K (W⁄K).FunctionField a * f) =
      algebraMap K (W⁄K).FunctionField (σ a) * galFunctionFieldEquiv W σ f := by
  rw [map_mul]
  exact congrArg (fun z => z * galFunctionFieldEquiv W σ f) (gal_algebraMap W σ a)

/-- 恒等ガロア元の関数体への持ち上げも恒等写像である。 -/
theorem galFunctionFieldEquiv_one (f : (W⁄K).FunctionField) : galFunctionFieldEquiv W 1 f = f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄K).CoordinateRing) f
  have ha : galRingEquiv W 1 a = a := galRingHom_one W a
  have hb' : galRingEquiv W 1 b = b := galRingHom_one W b
  rw [map_div₀, galFunctionFieldEquiv_algebraMap, galFunctionFieldEquiv_algebraMap, ha, hb']

/-- 二つの係数作用の合成は、同じ順序で関数体の作用を合成する。 -/
theorem galFunctionFieldEquiv_mul (σ τ : K ≃ₐ[F] K) (f : (W⁄K).FunctionField) :
    galFunctionFieldEquiv W (σ * τ) f = galFunctionFieldEquiv W σ (galFunctionFieldEquiv W τ f) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := (W⁄K).CoordinateRing) f
  have ha : galRingEquiv W (σ * τ) a = galRingEquiv W σ (galRingEquiv W τ a) :=
    (galRingHom_comp W σ τ a).symm
  have hb' : galRingEquiv W (σ * τ) b = galRingEquiv W σ (galRingEquiv W τ b) :=
    (galRingHom_comp W σ τ b).symm
  simp only [map_div₀, galFunctionFieldEquiv_algebraMap, ha, hb']
end Laws

end DkMath.Lib.NumberTheory.EllipticFunctionField
