/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.RegularStateTransport
import DkMath.Lib.NumberTheory.PhaseObstructionTransport
import DkMath.Lib.NumberTheory.UnitObstructionPacket

#print "file: DkMath.FLT.Kummer.ObstructedState"

/-!
# IRR-005: 類障害と単元障害を保持する State 輸送

正則用 Conditions は変更しない。その隣で、元の State と全位相の非零イデアル根を保持する。
正則性を仮定しなくてもこの状態と全障害の積保存則を構成できる。
個別の類が消えた場合に限り元の根を取り出し、三項 GN 関係から重み付き後続状態を作る。
最後に選んだ係数単元比が p 乗のときだけ正規化する。未証明の消滅や降下は仮定しない。
-/
namespace DkMath.FLT.Kummer.IrregularDescent
open DkMath.Lib.NumberTheory
open DkMath.Lib.Algebra
open RegularDescent
open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {p : ℕ} [hp : Fact p.Prime] {P : RamifiedPhasePacket R p}

/-- 元の方程式・原始性・非分岐性をそのまま保持し、各剥離商のイデアル根を併記する。 -/
structure ObstructedState (P : RamifiedPhasePacket R p) (m : ℕ) where
  source : State P (m + 1)
  phases : PhaseClassPacket R p (Fin p)
  factor_eq : ∀ i, phases.factor i = P.quotient (source.center (by omega)) source.y i

/-- 正則性なしに障害付き状態を構成する。必要なのは既存のイデアル冪抽出だけ。
全位相が非零であることも、元の非零な積から検証する。 -/
noncomputable def ofState (hodd : Odd p) {m : ℕ} (E : State P (m + 1)) :
    ObstructedState P m := by
  classical
  have hz : E.z ≠ 0 := fun h => E.z_away (h ▸ dvd_zero _)
  have hprod : (∏ i : Fin p, P.quotient (E.center (by omega)) E.y i) ≠ 0 := by
    rw [E.quotient_product hodd]
    exact mul_ne_zero E.epsilon.isUnit.ne_zero
      (pow_ne_zero p (mul_ne_zero (pow_ne_zero m P.lambda_prime.ne_zero) hz))
  choose I hI using (fun i => E.quotient_ideal_power hodd i)
  have hI0 (i : Fin p) : I i ∈ (Ideal R)⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hzero
    have hq := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    apply hq
    apply Ideal.span_singleton_eq_bot.mp
    simpa [hzero, hp.out.ne_zero] using hI i
  exact ⟨E, ⟨_, fun i => ⟨⟨I i, hI0 i⟩, hI i⟩⟩, fun _ => rfl⟩

/-- 観測のために原始整数データや State の方程式を変更していない。 -/
theorem ofState_source (hodd : Odd p) {m : ℕ} (E : State P (m + 1)) :
    (ofState hodd E).source = E := rfl

/-- GN の実際の積関係から全障害の積は1になる。個々の障害は残したまま。 -/
theorem ObstructedState.product_obstruction_one {m : ℕ} (E : ObstructedState P m)
    (hodd : Odd p) : (∏ i, E.phases.obstruction i) = 1 := by
  apply E.phases.product_obstruction_eq_one hp.out.ne_zero E.source.epsilon
    (P.lambda ^ m * E.source.z)
  simp_rw [E.factor_eq]
  exact E.source.quotient_product hodd

/-- 三項関係は元の値について保持する。類群の加法関係に読み替えてはならない。 -/
theorem ObstructedState.three_term {m : ℕ} (E : ObstructedState P m) (i0 i1 i2 : Fin p) :
    (P.slope i2 - P.slope i0) * E.phases.factor i1 +
      (P.slope i0 - P.slope i1) * E.phases.factor i2 =
      (P.slope i2 - P.slope i1) * E.phases.factor i0 := by
  simp_rw [E.factor_eq]
  exact quotient_three_term _ _ _ _ _

/-- 既に得た同じ族の元の根から、分岐次数をちょうど m だけ取り出す。
この補題は類群の大域的な消滅を要求しない。 -/
theorem descent_roots_of_phase_roots (hodd : Odd p) {m : ℕ} (E : State P (m + 1))
    (u : Fin p → Rˣ) (b : Fin p → R)
    (hb : ∀ i, P.quotient (E.center (by omega)) E.y i = (u i : R) * b i ^ p) :
    ∃ (u : Fin p → Rˣ) (b : Fin p → R) (g : R),
      (∀ i, P.quotient (E.center (by omega)) E.y i = (u i : R) * b i ^ p) ∧
      P.quotient (E.center (by omega)) E.y (P.distinguished (E.center (by omega)) E.y) =
        (u (P.distinguished (E.center (by omega)) E.y) : R) * (P.lambda ^ m * g) ^ p ∧
      ¬ P.lambda ∣ g ∧
      (∀ i, i ≠ P.distinguished (E.center (by omega)) E.y → ¬ P.lambda ∣ b i) ∧
      (∀ i j, i ≠ j → IsCoprime (b i) (b j)) := by
  classical
  let i0 := P.distinguished (E.center (by omega)) E.y
  let rest := ∏ i ∈ (Finset.univ.erase i0), P.quotient (E.center (by omega)) E.y i
  have hrest : ¬ P.lambda ∣ rest := by
    intro hd
    obtain ⟨i, hi, hd⟩ := (P.lambda_prime.dvd_finsetProd_iff _).mp hd
    exact (Finset.mem_erase.mp hi).1 ((P.quotient_dvd_iff _ _ E.y_away i).mp hd)
  have hprod : P.quotient (E.center (by omega)) E.y i0 * rest =
      (E.epsilon : R) * (P.lambda ^ m * E.z) ^ p := by
    rw [← E.quotient_product hodd]
    exact Finset.mul_prod_erase _ _ (Finset.mem_univ i0)
  have hdq : P.lambda ^ (m * p) ∣ P.quotient (E.center (by omega)) E.y i0 := by
    apply P.lambda_prime.pow_dvd_of_dvd_mul_right (m * p) hrest
    rw [hprod, mul_pow, ← pow_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  rw [hb i0] at hdq
  have hdb : P.lambda ^ m ∣ b i0 := by
    have huinv : (↑((u i0)⁻¹) : R) * (u i0 : R) = 1 := (u i0).inv_val
    apply (IsIntegrallyClosed.pow_dvd_pow_iff hp.out.ne_zero).mp
    rw [← pow_mul]
    simpa only [← mul_assoc, huinv, one_mul] using
      dvd_mul_of_dvd_right hdq (↑((u i0)⁻¹) : R)
  obtain ⟨g, hg⟩ := hdb
  have hgfac : P.quotient (E.center (by omega)) E.y i0 =
      (u i0 : R) * (P.lambda ^ m * g) ^ p := by rw [hb i0, hg]
  have hcancel : (u i0 : R) * g ^ p * rest = (E.epsilon : R) * E.z ^ p := by
    apply mul_left_cancel₀ (pow_ne_zero (m * p) P.lambda_prime.ne_zero)
    calc
      _ = P.quotient (E.center (by omega)) E.y i0 * rest := by rw [hgfac]; ring
      _ = _ := by rw [hprod]; ring
  have hga : ¬ P.lambda ∣ g := by
    intro hd
    have hz := congrArg P.residue hcancel
    have hg0 := (P.residue_zero_iff _).mpr hd
    simp only [map_mul, map_pow, hg0, zero_pow hp.out.ne_zero, mul_zero, zero_mul] at hz
    have hzpow : P.residue E.z ^ p = 0 :=
      (mul_eq_zero.mp hz.symm).resolve_left (E.epsilon.isUnit.map P.residue).ne_zero
    exact E.z_away ((P.residue_zero_iff _).mp (eq_zero_of_pow_eq_zero hzpow))
  have haway : ∀ i, i ≠ i0 → ¬ P.lambda ∣ b i := by
    intro i hi hd
    have hqi : P.lambda ∣ P.quotient (E.center (by omega)) E.y i := by
      rw [hb i]
      exact dvd_mul_of_dvd_right (hd.trans (dvd_pow_self _ hp.out.ne_zero)) _
    exact hi ((P.quotient_dvd_iff _ _ E.y_away i).mp hqi)
  have hbcop : ∀ i j, i ≠ j → IsCoprime (b i) (b j) := by
    intro i j hij
    apply IsCoprime.mono _ _ (E.quotients_coprime (by omega) hij)
    · rw [hb i]; exact dvd_mul_of_dvd_right (dvd_pow_self _ hp.out.ne_zero) _
    · rw [hb j]; exact dvd_mul_of_dvd_right (dvd_pow_self _ hp.out.ne_zero) _
  exact ⟨u, b, g, hb, hgfac, hga, haway, hbcop⟩


/-- 重み付き後続状態。単元比の障害が残っていても方程式と全 guard を保持する。 -/
structure WeightedObstructedState (P : RamifiedPhasePacket R p) (m : ℕ) where
  x : R
  y : R
  z : R
  u : Rˣ
  v : Rˣ
  epsilon : Rˣ
  coprime : IsCoprime x y
  x_away : ¬ P.lambda ∣ x
  y_away : ¬ P.lambda ∣ y
  z_away : ¬ P.lambda ∣ z
  equation : (u : R) * x ^ p + (v : R) * y ^ p = epsilon * (P.lambda ^ m * z) ^ p

/-- 正規化に本当に必要な単元比だけを観測する。全単元の冪性は要求しない。 -/
def WeightedObstructedState.unitObstruction {m : ℕ} (E : WeightedObstructedState P m) :
    Rˣ ⧸ unitPowerSubgroup R p := unitPowerObstruction p (E.u / E.v)

/-- 選んだ単元比の障害が消えた場合だけ正規化し、同じ y,z と原始性を保持する。 -/
theorem WeightedObstructedState.normalize {m : ℕ} (E : WeightedObstructedState P m)
    (h : E.unitObstruction = 1) :
    ∃ F : State P m, F.y = E.y ∧ F.z = E.z := by
  obtain ⟨k, hk⟩ := (unitPowerObstruction_eq_one_iff (E.u / E.v)).mp h
  obtain ⟨F, _, hy, hz⟩ := normalize_weighted m E.x E.y E.z E.u E.v E.epsilon k
    E.coprime E.y_away E.z_away E.equation hk
  exact ⟨F, hy, hz⟩

/-- 局所的な類障害の消滅から実際の重み付き後続状態を作る。
類群全体の p-torsion-free 性と Kummer 単元 criterion は使わない。 -/
theorem ObstructedState.exists_weighted {m : ℕ} (O : ObstructedState P m)
    (hodd : Odd p) (hp3 : 3 ≤ p) (htriv : ∀ i, O.phases.obstruction i = 1) :
    Nonempty (WeightedObstructedState P m) := by
  classical
  obtain ⟨u, b, hb⟩ := O.phases.exists_roots_of_trivial htriv
  have hb' (i : Fin p) : P.quotient (O.source.center (by omega)) O.source.y i =
      (u i : R) * b i ^ p := by rw [← O.factor_eq]; exact hb i
  obtain ⟨u, b, g, hb, hgfac, hga, ha, hcop⟩ :=
    descent_roots_of_phase_roots hodd O.source u b hb'
  let E := O.source
  let i0 := P.distinguished (E.center (by omega)) E.y
  obtain ⟨i1, hi1⟩ := Finset.exists_mem_ne (s := (Finset.univ : Finset (Fin p)))
    (by simp; omega) i0
  obtain ⟨i2, hi2, hi21⟩ := Finset.exists_mem_ne
    (s := (Finset.univ.erase i0 : Finset (Fin p))) (by simp; omega) i1
  have h10 : i1 ≠ i0 := hi1.2
  have h20 : i2 ≠ i0 := (Finset.mem_erase.mp hi2).1
  have h21 : i2 ≠ i1 := hi21
  let a := (slope_sub_isUnit P h20).unit
  let b' := (slope_sub_isUnit P h10.symm).unit
  let c := (slope_sub_isUnit P h21).unit
  have ha0 : (a : R) = P.slope i2 - P.slope i0 := IsUnit.unit_spec _
  have hb0 : (b' : R) = P.slope i0 - P.slope i1 := IsUnit.unit_spec _
  have hc0 : (c : R) = P.slope i2 - P.slope i1 := IsUnit.unit_spec _
  refine ⟨⟨b i1, b i2, g, a * u i1, b' * u i2, c * u i0,
    hcop _ _ h21.symm, ha _ h10, ha _ h20, hga, ?_⟩⟩
  have hf := quotient_three_term (P := P) (E.center (by omega)) E.y i0 i1 i2
  rw [hb i1, hb i2, hgfac] at hf
  simpa only [Units.val_mul, ha0, hb0, hc0, mul_assoc] using hf

end DkMath.FLT.Kummer.IrregularDescent
