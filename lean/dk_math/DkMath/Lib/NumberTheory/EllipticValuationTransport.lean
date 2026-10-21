/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
Definitions/Def_EllipticCurve_FunctionFieldPullback.lean.
Upstream blob: ce8783a9e9613db1c4c0323ce93fb0d89917ee65
Modified for DkMath: reuse proved generic points, finite places and fraction-field pullbacks.
-/

import DkMath.Lib.NumberTheory.EllipticFunctionFieldTranslation
import DkMath.Lib.NumberTheory.EllipticPointIdealValuation

#print "file: DkMath.Lib.NumberTheory.EllipticValuationTransport"

/-!
# 剰余合同から関数体の引き戻しへ

v(a−b)<1を局所的な合同とし、和・積・分母が単元の場合の商に沿って運ぶ。
座標が有限点の座標に合同なら、座標環の点イデアルをその点で消える関数へ移す。
素イデアル冪の積への帰納と、局所環の分母表示により、関数体の付値の上界を輸送する。
-/
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace Valuation

variable {L : Type*} [CommRing L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

/-- 局所合同a≡bをv(a−b)<1で定義する。付値環の極大イデアルで差が消えるという意味である。 -/
def Cong (a b : L) : Prop := v (a - b) < 1

variable {v}

/-- 局所合同の定義を付値の不等式として取り出す。 -/
theorem cong_iff {a b : L} : v.Cong a b ↔ v (a - b) < 1 := Iff.rfl

/-- 同じ元の差は0なので、局所合同は反射的。 -/
@[refl] theorem Cong.refl (a : L) : v.Cong a a := by simp [Cong]

/-- 暗黙の元について使う反射律。 -/
theorem Cong.rfl {a : L} : v.Cong a a := Cong.refl a

/-- 差の符号を変えても付値は変わらず、合同は対称的。 -/
@[symm] theorem Cong.symm {a b : L} (h : v.Cong a b) : v.Cong b a := by
  rw [Cong, ← Valuation.map_neg, neg_sub]; exact h

/-- 差を二つの差の和に分け、非Archimedes不等式から推移律を得る。 -/
theorem Cong.trans {a b c : L} (h₁ : v.Cong a b) (h₂ : v.Cong b c) : v.Cong a c := by
  have : a - c = (a - b) + (b - c) := by ring
  rw [Cong, this]
  exact (v.map_add _ _).trans_lt (max_lt h₁ h₂)

/-- 和の局所合同は二つの差の和に帰着する。 -/
theorem Cong.add {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') : v.Cong (a + b) (a' + b') := by
  have : a + b - (a' + b') = (a - a') + (b - b') := by ring
  rw [Cong, this]
  exact (v.map_add _ _).trans_lt (max_lt h₁ h₂)

/-- 符号反転は局所合同を保つ。 -/
theorem Cong.neg {a a' : L} (h : v.Cong a a') : v.Cong (-a) (-a') := by
  have : -a - -a' = -(a - a') := by ring
  rw [Cong, this, Valuation.map_neg]; exact h

/-- 加法と符号反転を合わせ、差の局所合同を得る。 -/
theorem Cong.sub {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') : v.Cong (a - b) (a' - b') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h₁.add h₂.neg

/-- 付値環内の元に合同な元も付値環に入る。 -/
theorem Cong.le_one {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) : v a ≤ 1 := by
  have : a = (a - a') + a' := by ring
  rw [this]
  exact (v.map_add _ _).trans (max_le h.le ha')

/-- 比較する元が付値環内にある場合、積も合同になる。上界の仮定を省略しない。 -/
theorem Cong.mul {a b a' b' : L} (h₁ : v.Cong a a') (h₂ : v.Cong b b') (ha' : v a' ≤ 1)
    (hb' : v b' ≤ 1) : v.Cong (a * b) (a' * b') := by
  have ha : v a ≤ 1 := h₁.le_one ha'
  have : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [Cong, this]
  refine (v.map_add _ _).trans_lt (max_lt ?_ ?_)
  · rw [Valuation.map_mul]
    calc v a * v (b - b') ≤ 1 * v (b - b') := mul_le_mul' ha le_rfl
      _ < 1 := by rw [one_mul]; exact h₂
  · rw [Valuation.map_mul]
    calc v (a - a') * v b' ≤ v (a - a') * 1 := mul_le_mul' le_rfl hb'
      _ < 1 := by rw [mul_one]; exact h₁

/-- 積の合同を帰納的に適用して自然数冪へ延長する。 -/
theorem Cong.pow {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) (n : ℕ) : v.Cong (a ^ n) (a' ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; exact Cong.rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h (by rw [Valuation.map_pow]; exact pow_le_one' ha' n) ha'

/-- 単元に合同な元の付値は1。逆数を取るための条件となる。 -/
theorem Cong.eq_of_eq_one {a a' : L} (h : v.Cong a a') (ha' : v a' = 1) : v a = 1 := by
  have : a = a' + (a - a') := by ring
  rw [this, Valuation.map_add_eq_of_lt_left]
  · exact ha'
  · rw [ha']; exact h

/-- 合同な二元は、極大イデアルへの所属条件v<1が一致する。 -/
theorem Cong.lt_one_iff {a a' : L} (h : v.Cong a a') : v a < 1 ↔ v a' < 1 := by
  constructor
  · intro ha
    have : a' = a - (a - a') := by ring
    rw [this]
    exact (v.map_sub _ _).trans_lt (max_lt ha h)
  · intro ha'
    have : a = (a - a') + a' := by ring
    rw [this]
    exact (v.map_add _ _).trans_lt (max_lt h ha')

/-- 零に合同であることは、極大イデアルに入ることそのものである。 -/
theorem cong_zero_iff {a : L} : v.Cong a 0 ↔ v a < 1 := by rw [Cong, sub_zero]

section Field

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}

/-- 単元の逆数も合同になる。分母の付値1が不可欠である。 -/
theorem Cong.inv {d d' : F} (h : w.Cong d d') (hd' : w d' = 1) : w.Cong d⁻¹ d'⁻¹ := by
  have hd : w d = 1 := h.eq_of_eq_one hd'
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hd; exact zero_ne_one hd
  have hd0' : d' ≠ 0 := fun h0 => by rw [h0, Valuation.map_zero] at hd'; exact zero_ne_one hd'
  have : d⁻¹ - d'⁻¹ = -(d - d') * (d⁻¹ * d'⁻¹) := by
    field_simp
    ring
  rw [Cong, this, Valuation.map_mul, Valuation.map_neg, Valuation.map_mul, map_inv₀, map_inv₀, hd, hd',
    inv_one, mul_one, mul_one]
  exact h

/-- 単元である分母の合同と分子の合同から商の合同を得る。 -/
theorem Cong.div {a d a' d' : F} (h₁ : w.Cong a a') (h₂ : w.Cong d d') (ha' : w a' ≤ 1)
    (hd' : w d' = 1) : w.Cong (a / d) (a' / d') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h₁.mul (h₂.inv hd') ha' (by rw [map_inv₀, hd', inv_one])

end Field

section Eval

variable {K : Type*} [CommRing K] (f : K →+* L)

/-- 定数と入力が付値環内なら、多項式評価は合同を保つ。 -/
theorem Cong.eval₂ (hf : ∀ c, v (f c) ≤ 1) {a a' : L} (h : v.Cong a a') (ha' : v a' ≤ 1) (p : K[X]) :
    v.Cong (p.eval₂ f a) (p.eval₂ f a') ∧ v (p.eval₂ f a') ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add]
    exact ⟨hp.1.add hq.1, (v.map_add _ _).trans (max_le hp.2 hq.2)⟩
  | monomial n c =>
    rw [eval₂_monomial, eval₂_monomial]
    have hpow : v (a' ^ n) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one' ha' n
    exact ⟨(Cong.refl (f c)).mul (h.pow ha' n) (hf c) hpow,
      by rw [Valuation.map_mul]; exact mul_le_one' (hf c) hpow⟩

/-- 二変数評価を一変数ずつ適用し、座標環の式の合同を運ぶ。 -/
theorem Cong.eval₂_eval₂ (hf : ∀ c, v (f c) ≤ 1) {a a' b b' : L} (ha : v.Cong a a') (ha' : v a' ≤ 1)
    (hb : v.Cong b b') (hb' : v b' ≤ 1) (p : K[X][X]) :
    v.Cong (p.eval₂ (eval₂RingHom f a) b) (p.eval₂ (eval₂RingHom f a') b') ∧
      v (p.eval₂ (eval₂RingHom f a') b') ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, eval₂_add]
    exact ⟨hp.1.add hq.1, (v.map_add _ _).trans (max_le hp.2 hq.2)⟩
  | monomial n q =>
    rw [eval₂_monomial, eval₂_monomial, coe_eval₂RingHom, coe_eval₂RingHom]
    have hq := Cong.eval₂ f hf ha ha' q
    have hpow : v (b' ^ n) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one' hb' n
    exact ⟨hq.1.mul (hb.pow hb' n) hq.2 hpow, by rw [Valuation.map_mul]; exact mul_le_one' hq.2 hpow⟩

end Eval

end Valuation

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {R' : Type*} [CommRing R'] [IsDedekindDomain R'] {K' : Type*} [Field K']
  [Algebra R' K'] [IsFractionRing R' K']

omit [IsDedekindDomain R] [IsFractionRing R K] in
/-- 素イデアルの一因子がexp(−1)以下へ写れば、m乗イデアルはexp(−m)以下へ写る。 -/
theorem valuation_map_le_exp_neg_of_mem_pow (ψ : K →+* K') (w : HeightOneSpectrum R)
    (v : HeightOneSpectrum R')
    (h0 : ∀ b : R, v.valuation K' (ψ (algebraMap R K b)) ≤ 1)
    (h1 : ∀ b : R, b ∈ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) ≤ exp (-1 : ℤ))
    (m : ℕ) : ∀ a ∈ w.asIdeal ^ m, v.valuation K' (ψ (algebraMap R K a)) ≤ exp (-(m : ℤ)) := by
  induction m with
  | zero =>
    intro a _
    rw [Nat.cast_zero, neg_zero, exp_zero]
    exact h0 a
  | succ m ih =>
    intro a ha
    rw [pow_succ'] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro c hc a' ha'
      rw [map_mul, map_mul, map_mul, Nat.cast_succ, neg_add, add_comm, exp_add]
      exact mul_le_mul' (h1 c hc) (ih a' ha')
    · intro z₁ z₂ hz₁ hz₂
      rw [map_add, map_add]
      exact (Valuation.map_add _ _ _).trans (max_le hz₁ hz₂)

/-- 局所環で分母を素イデアルの外に選ぶ表示により、座標環の評価を分数体へ延長する。 -/
theorem valuation_map_le_of_valuation_le (ψ : K →+* K') (w : HeightOneSpectrum R)
    (v : HeightOneSpectrum R')
    (h1 : ∀ b : R, b ∈ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) ≤ exp (-1 : ℤ))
    (h2 : ∀ b : R, b ∉ w.asIdeal → v.valuation K' (ψ (algebraMap R K b)) = 1)
    (x : K) (k : ℕ) (hx : w.valuation K x ≤ exp (-(k : ℤ))) :
    v.valuation K' (ψ x) ≤ exp (-(k : ℤ)) := by
  have h0 : ∀ b : R, v.valuation K' (ψ (algebraMap R K b)) ≤ 1 := by
    intro b
    by_cases hb : b ∈ w.asIdeal
    · exact (h1 b hb).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
    · exact (h2 b hb).le
  have hx1 : w.valuation K x ≤ 1 :=
    hx.trans (by rw [← exp_zero, exp_le_exp, neg_nonpos]; exact Nat.cast_nonneg k)
  obtain ⟨n, d, hnd⟩ := exists_primeCompl_mul_eq_of_integer (v := w) x hx1
  have hd : (d : R) ∉ w.asIdeal := d.2
  have hwn : w.valuation K (algebraMap R K n) ≤ exp (-(k : ℤ)) := by
    rw [← hnd, map_mul, (valuation_eq_one_iff_notMem (K := K) w).mpr hd, mul_one]
    exact hx
  rw [valuation_of_algebraMap, intValuation_le_pow_iff_mem] at hwn
  have hψn := valuation_map_le_exp_neg_of_mem_pow ψ w v h0 h1 k n hwn
  have := congrArg (fun t => v.valuation K' (ψ t)) hnd
  simp only [map_mul, h2 d hd, mul_one] at this
  rw [this]
  exact hψn

end IsDedekindDomain.HeightOneSpectrum

namespace DkMath.Lib.NumberTheory.EllipticFunctionField

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Polynomial

section Transport

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing]

/-- 整数離散値では、1未満の値はexp(−1)以下。零の値も含めて成立する。 -/
theorem _root_.WithZero.lt_one_iff_le_exp_neg_one {y : ℤᵐ⁰} : y < 1 ↔ y ≤ exp (-1 : ℤ) := by
  by_cases hy : y = 0
  · subst hy; simp
  · rw [← exp_log hy, ← exp_zero, exp_lt_exp, exp_le_exp]; omega

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 有限点の場所では、係数体の定数は付値環に入る。 -/
theorem valuation_algebraMap_le_one (P : (W⁄K).Point) (hP : P ≠ 0) (c : K) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField]
  exact valuation_le_one _ _

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 非零定数と逆数がともに付値環に入るので、定数の付値は1。 -/
theorem valuation_algebraMap_eq_one (P : (W⁄K).Point) (hP : P ≠ 0) {c : K} (hc : c ≠ 0) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (algebraMap K (W⁄K).FunctionField c) = 1 := by
  apply le_antisymm (valuation_algebraMap_le_one W K P hP c)
  have h := valuation_algebraMap_le_one W K P hP c⁻¹
  rw [map_inv₀, map_inv₀, inv_le_one₀] at h
  · exact h
  · rw [Valuation.pos_iff]
    exact (_root_.map_ne_zero _).mpr hc

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 有限点の素イデアルへの所属は、その点での評価が零となることと同値。 -/
theorem mem_placeOf_iff (P : (W⁄K).Point) (hP : P ≠ 0) (b : (W⁄K).CoordinateRing) :
    b ∈ (placeOf W K P hP).asIdeal ↔ evalAt W K (Point.nonsingular_xc_yc hP).left b = 0 := by
  constructor
  · exact evalAt_XYIdeal W K _ b
  · intro hb
    have hker : RingHom.ker (evalAt W K (Point.nonsingular_xc_yc hP).left) =
        (placeOf W K P hP).asIdeal := by
      refine ((EllipticCoordinateRing.isMaximal_XYIdeal (Point.nonsingular_xc_yc hP).left).eq_of_le
        (RingHom.ker_ne_top _) ?_).symm
      intro g hg
      exact (RingHom.mem_ker).mpr (evalAt_XYIdeal W K _ g hg)
    rw [← hker]
    exact (RingHom.mem_ker).mpr hb

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 一般点のx座標は、有限点Pのx座標に局所的に合同である。 -/
theorem cong_genericX (P : (W⁄K).Point) (hP : P ≠ 0) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (genericX W K)
      (algebraMap K (W⁄K).FunctionField P.xc) := by
  rw [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField, genericX,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [placeOf_asIdeal]
  have : CoordinateRing.mk (W⁄K) (C X) - algebraMap K (W⁄K).CoordinateRing P.xc =
      CoordinateRing.XClass (W⁄K) P.xc := by
    rw [CoordinateRing.XClass, map_sub, map_sub]; rfl
  rw [this]
  exact Ideal.subset_span (Set.mem_insert _ _)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 一般点のy座標も、有限点Pのy座標に局所的に合同である。 -/
theorem cong_genericY (P : (W⁄K).Point) (hP : P ≠ 0) :
    ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong (genericY W K)
      (algebraMap K (W⁄K).FunctionField P.yc) := by
  rw [Valuation.cong_iff, IsScalarTower.algebraMap_apply K (W⁄K).CoordinateRing (W⁄K).FunctionField, genericY,
    ← map_sub]
  apply (valuation_lt_one_iff_mem _ _).mpr
  rw [placeOf_asIdeal]
  have : CoordinateRing.mk (W⁄K) Y - algebraMap K (W⁄K).CoordinateRing P.yc =
      CoordinateRing.YClass (W⁄K) (C P.yc) := by
    rw [CoordinateRing.YClass, map_sub]; rfl
  rw [this]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 係数体からの写像と二変数多項式の評価を交換する。 -/
theorem algebraMap_evalEval (g : K[X][Y]) (a b : K) :
    algebraMap K (W⁄K).FunctionField (g.evalEval a b) =
      g.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (algebraMap K _ a)) (algebraMap K _ b) := by
  have hφ : (algebraMap K (W⁄K).FunctionField).comp (evalEvalRingHom a b) =
      eval₂RingHom (eval₂RingHom (algebraMap K (W⁄K).FunctionField) (algebraMap K _ a)) (algebraMap K _ b) := by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C, coe_eval₂RingHom,
        eval₂_C, eval₂_at_apply]
    · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_X, eval_C, coe_eval₂RingHom,
        eval₂_X]
  exact RingHom.congr_fun hφ g

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] [IsDedekindDomain (W⁄K).CoordinateRing] in
/-- 一般点での座標環の準同型を二変数評価に書き直す。 -/
theorem pointHom_mk_eq_eval₂ (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0) (g : K[X][Y]) :
    pointHom Q hQ (CoordinateRing.mk (W⁄K) g) =
      g.eval₂ (eval₂RingHom (algebraMap K (W⁄K).FunctionField) Q.xc) Q.yc := by
  rw [pointHom_mk]
  congr 1

omit [DecidableEq K] [IsAlgClosed K] [W.IsElliptic] in
/-- 引き戻し点の座標がPに合同なら、Pの零点イデアルとその冪の付値上界を輸送できる。 -/
theorem valuation_pointPull_le (Q : (W⁄(W⁄K).FunctionField).Point) (hQ : Q ≠ 0)
    (hinj : Function.Injective (pointHom Q hQ)) {P : (W⁄K).Point} (hP : P ≠ 0) {P' : (W⁄K).Point}
    (hP' : P' ≠ 0)
    (hx : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong Q.xc (algebraMap K _ P'.xc))
    (hy : ((placeOf W K P hP).valuation (W⁄K).FunctionField).Cong Q.yc (algebraMap K _ P'.yc))
    (h : (W⁄K).FunctionField) (k : ℕ)
    (hh : (placeOf W K P' hP').valuation (W⁄K).FunctionField h ≤ exp (-(k : ℤ))) :
    (placeOf W K P hP).valuation (W⁄K).FunctionField (pointPull Q hQ hinj h) ≤ exp (-(k : ℤ)) := by
  set v := (placeOf W K P hP).valuation (W⁄K).FunctionField with hv
  have hc : ∀ g : K[X][Y], v.Cong (pointHom Q hQ (CoordinateRing.mk (W⁄K) g))
      (algebraMap K _ (g.evalEval P'.xc P'.yc)) := by
    intro g
    rw [pointHom_mk_eq_eval₂, algebraMap_evalEval]
    exact (Valuation.Cong.eval₂_eval₂ (v := v) (algebraMap K _) (valuation_algebraMap_le_one W K P hP)
      hx (valuation_algebraMap_le_one W K P hP _) hy (valuation_algebraMap_le_one W K P hP _) g).1
  refine valuation_map_le_of_valuation_le (pointPull Q hQ hinj : (W⁄K).FunctionField →+* (W⁄K).FunctionField)
    (placeOf W K P' hP') (placeOf W K P hP) ?_ ?_ h k hh
  · intro b hb
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (pointPull Q hQ hinj (algebraMap _ _ (CoordinateRing.mk (W⁄K) g))) ≤ _
    rw [pointPull_algebraMap, ← lt_one_iff_le_exp_neg_one, ← Valuation.cong_zero_iff]
    have h0 : g.evalEval P'.xc P'.yc = 0 := by
      rw [← evalAt_mk W K (Point.nonsingular_xc_yc hP').left]
      exact (mem_placeOf_iff W K P' hP' _).mp hb
    simpa only [h0, map_zero] using hc g
  · intro b hb
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    change v (pointPull Q hQ hinj (algebraMap _ _ (CoordinateRing.mk (W⁄K) g))) = 1
    rw [pointPull_algebraMap]
    have h0 : g.evalEval P'.xc P'.yc ≠ 0 := by
      rw [← evalAt_mk W K (Point.nonsingular_xc_yc hP').left]
      exact fun h => hb ((mem_placeOf_iff W K P' hP' _).mpr h)
    exact (hc g).eq_of_eq_one (valuation_algebraMap_eq_one W K P hP h0)


end Transport

end DkMath.Lib.NumberTheory.EllipticFunctionField
