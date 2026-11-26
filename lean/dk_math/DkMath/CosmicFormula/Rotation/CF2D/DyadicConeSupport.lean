/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CosmicFormula.Rotation.CF2D.DyadicCone

#print "file: DkMath.CosmicFormula.Rotation.CF2D.DyadicConeSupport"

/-! # 保存量による二分軌道の支持不等式 -/

namespace DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel

private def detPair (p q : ℝ × ℝ) : ℝ := p.1 * q.2 - p.2 * q.1

private theorem cone_coordinates {p q : ℝ × ℝ} (hd : detPair p q ≠ 0) (x : ℝ × ℝ) :
    x = (detPair x q / detPair p q) • p + (detPair p x / detPair p q) • q := by
  apply Prod.ext
  · change x.1 = detPair x q / detPair p q * p.1 + detPair p x / detPair p q * q.1
    apply mul_right_cancel₀ hd
    rw [add_mul]
    rw [mul_right_comm (_ / _) p.1, mul_right_comm (_ / _) q.1,
      div_mul_cancel₀ _ hd, div_mul_cancel₀ _ hd]
    unfold detPair
    ring
  · change x.2 = detPair x q / detPair p q * p.2 + detPair p x / detPair p q * q.2
    apply mul_right_cancel₀ hd
    rw [add_mul]
    rw [mul_right_comm (_ / _) p.2, mul_right_comm (_ / _) q.2,
      div_mul_cancel₀ _ hd, div_mul_cancel₀ _ hd]
    unfold detPair
    ring

/-- 非退化な二方向に沿う係数がともに正なら、その点は錐の内部にある。
外積で求めた係数は連続なので、正性は開近傍で保たれる。 -/
theorem strictCone_mem_interior {p q : ℝ × ℝ}
    (hd : p.1 * q.2 - p.2 * q.1 ≠ 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a • p + b • q ∈ interior (nonnegativeCone p q) := by
  let A := fun x => detPair x q / detPair p q
  let B := fun x => detPair p x / detPair p q
  have hA : Continuous A := by unfold A detPair; fun_prop
  have hB : Continuous B := by unfold B detPair; fun_prop
  have hopen : IsOpen ({x | 0 < A x} ∩ {x | 0 < B x}) :=
    (isOpen_lt continuous_const hA).inter (isOpen_lt continuous_const hB)
  apply interior_mono (t := nonnegativeCone p q)
    (s := {x | 0 < A x} ∩ {x | 0 < B x}) ?_
  · rw [hopen.interior_eq]
    have h₁ : detPair (a • p + b • q) q = a * detPair p q := by
      change (a * p.1 + b * q.1) * q.2 - (a * p.2 + b * q.2) * q.1 = _
      unfold detPair
      ring
    have h₂ : detPair p (a • p + b • q) = b * detPair p q := by
      change p.1 * (a * p.2 + b * q.2) - p.2 * (a * p.1 + b * q.1) = _
      unfold detPair
      ring
    change 0 < detPair (a • p + b • q) q / detPair p q ∧
      0 < detPair p (a • p + b • q) / detPair p q
    change detPair p q ≠ 0 at hd
    rw [h₁, h₂, mul_div_cancel_right₀ _ hd, mul_div_cancel_right₀ _ hd]
    exact ⟨ha, hb⟩
  · intro x hx
    exact ⟨A x, B x, hx.1.le, hx.2.le, cone_coordinates hd x⟩

private theorem orbit_det (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    detPair (orbitPair n j) (orbitPair n (directVertexNext n j)) ≠ 0 := by
  change refinementCross (directVertex n j) (directVertex n (directVertexNext n j)) ≠ 0
  rw [refinement_old_cross]
  exact (beam_pos n).ne'

/-- 支持直線を越える点で保存量が 1 以下なら、対応する錐の内部にある。
二乗和を展開し、係数の和が 1 より大きいことから両係数の正性を導く。 -/
theorem outside_chord_mem_cone_interior (n : ℕ) (j : Fin (4 * 2 ^ n)) (x : Vec ℝ)
    (hx : x.q2 ≤ 1)
    (hout : (sequence (n + 1)).core ^ 2 <
      refinementDot (refinementMidpoint (directVertex n j)
        (directVertex n (directVertexNext n j))) x) :
    (x.core, x.beam) ∈ interior (DyadicCone n j) := by
  let p := directVertex n j
  let q := directVertex n (directVertexNext n j)
  let P := orbitPair n j
  let Q := orbitPair n (directVertexNext n j)
  let X : ℝ × ℝ := (x.core, x.beam)
  let a := detPair X Q / detPair P Q
  let b := detPair P X / detPair P Q
  have he : X = a • P + b • Q := cone_coordinates (orbit_det n j) X
  have h₁ : x.core = a * p.core + b * q.core := congrArg Prod.fst he
  have h₂ : x.beam = a * p.beam + b * q.beam := congrArg Prod.snd he
  let c := (sequence (n + 1)).core ^ 2
  let m := refinementMidpoint p q
  have hm₁ : refinementDot m p = c := (refinement_midpoint_dot n j).1
  have hm₂ : refinementDot m q = c := (refinement_midpoint_dot n j).2.1
  have hdot : refinementDot m x = (a + b) * c := by
    rw [← hm₁]
    have heq : refinementDot m q = refinementDot m p := hm₂.trans hm₁.symm
    unfold refinementDot at *
    rw [h₁, h₂]
    linear_combination b * heq
  change c < refinementDot m x at hout
  rw [hdot] at hout
  have hs : 1 < a + b := (mul_lt_mul_iff_right₀ (pow_pos (core_succ_pos n) 2)).mp
    (by change c * 1 < c * (a + b); nlinarith only [hout])
  have hp : p.q2 = 1 := directVertex_q2 n j
  have hq : q.q2 = 1 := directVertex_q2 n (directVertexNext n j)
  have hpq : refinementDot p q = (sequence n).core := refinement_old_dot n j
  have hmass : x.q2 = (a + b)^2 - 2 * (1 - (sequence n).core) * (a*b) := by
    unfold Vec.q2 refinementDot at *
    rw [h₁, h₂]
    linear_combination a^2 * hp + b^2 * hq + 2*a*b * hpq
  have hab : 0 < a * b := by
    by_contra! h
    rw [hmass] at hx
    have hneg := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (core_lt_one n).le) h
    nlinarith [sq_nonneg (a + b - 1)]
  have ha : 0 < a := by
    by_contra! h
    have hb : 0 < b := by linarith
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h hb.le)) hab
  have hb : 0 < b := by
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le h)) hab
  change X ∈ interior (nonnegativeCone P Q)
  rw [he]
  exact strictCone_mem_interior (orbit_det n j) ha hb

/-- 始点の単位ベクトルは、正係数を持つ点を通じて自身の錐の内部から近似できる。 -/
theorem orbit_vertex_mem_closure_cone_interior (n : ℕ) (j : Fin (4 * 2 ^ n)) :
    orbitPair n j ∈ closure (interior (DyadicCone n j)) := by
  let p := orbitPair n j
  let q := orbitPair n (directVertexNext n j)
  let F := fun t : ℝ => p + t • q
  have hF : Continuous F := by unfold F; fun_prop
  have hzero : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact Set.mem_Ici.mpr (le_refl (0 : ℝ))
  have himage : F '' Set.Ioi 0 ⊆ interior (DyadicCone n j) := by
    rintro _ ⟨t, ht, rfl⟩
    simpa only [F, p, q, DyadicCone, one_smul] using strictCone_mem_interior (orbit_det n j) one_pos ht
  have h := closure_mono himage (mem_closure_image hF.continuousAt hzero)
  simpa [F, p] using h

/-- 別の頂点が錐の内部に入ると、開近傍がその頂点自身の錐の内部にも交わってしまう。 -/
theorem orbit_vertex_not_mem_other_cone_interior (n : ℕ) {j k : Fin (4 * 2 ^ n)} (hne : j ≠ k) :
    orbitPair n k ∉ interior (DyadicCone n j) := by
  intro hk
  have hh := orbit_vertex_mem_closure_cone_interior n k
  rw [mem_closure_iff_nhds] at hh
  obtain ⟨x, hx⟩ := hh _ (isOpen_interior.mem_nhds hk)
  exact (Set.disjoint_left.mp (dyadicCones_pairwise_interior_disjoint n hne)) hx.1 hx.2

/-- 旧辺の内側半平面には全旧頂点が入る。外側の点を錐の内部に送って矛盾を導く。 -/
theorem directVertex_mem_edge_halfspace (n : ℕ) (j k : Fin (4 * 2 ^ n)) :
    refinementDot (refinementMidpoint (directVertex n j)
      (directVertex n (directVertexNext n j))) (directVertex n k) ≤
        (sequence (n + 1)).core ^ 2 := by
  by_cases h : j = k
  · subst k
    exact (refinement_midpoint_dot n j).1.le
  · by_contra! hout
    exact orbit_vertex_not_mem_other_cone_interior n h
      (outside_chord_mem_cone_interior n j _ (directVertex_q2 n k).le hout)

/-- 奇数頂点は、正規化中点公式の正係数により、対応する親錐の内部にある。 -/
theorem odd_vertex_mem_parent_cone_interior (n : ℕ) (k : Fin (4 * 2 ^ n)) :
    orbitPair (n + 1) (oddIndex n k) ∈ interior (DyadicCone n k) := by
  let c := 2 * (sequence (n + 1)).core
  have hc : 0 < c := mul_pos (by norm_num) (core_succ_pos n)
  have he : orbitPair (n + 1) (oddIndex n k) =
      c⁻¹ • orbitPair n k + c⁻¹ • orbitPair n (directVertexNext n k) := by
    rw [← smul_add]
    have h := directVertex_odd_scaled n k
    have hh : c • orbitPair (n + 1) (oddIndex n k) =
        orbitPair n k + orbitPair n (directVertexNext n k) := Prod.ext h.1 h.2
    rw [← hh, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [he]
  exact strictCone_mem_interior (orbit_det n k) (inv_pos.mpr hc) (inv_pos.mpr hc)

/-- 他の辺に追加される新頂点も、指定した旧辺の内側半平面に入る。 -/
theorem other_odd_mem_halfspace_pi_free (n : ℕ) (j k : Fin (4 * 2 ^ n)) (hne : j ≠ k) :
    refinementDot (refinementMidpoint (directVertex n j)
      (directVertex n (directVertexNext n j))) (directVertex (n + 1) (oddIndex n k)) ≤
        (sequence (n + 1)).core ^ 2 := by
  by_contra! hout
  exact (Set.disjoint_left.mp (dyadicCones_pairwise_interior_disjoint n hne))
    (outside_chord_mem_cone_interior n j _ (directVertex_q2 (n + 1) (oddIndex n k)).le hout)
    (odd_vertex_mem_parent_cone_interior n k)

end DkMath.CosmicFormula.Rotation.CF2D.QuadrantUnitKernel
