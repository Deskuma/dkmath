/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: ../NumberTheory/RegularKummer/LICENSE
Upstream notices: ../NumberTheory/RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean,
blob 25aa86a5830188d425f5ddd7b361207f10ba732a.
Modified: isolate the characteristic-independent linear algebra in DkMath.Lib.
-/

import DkMath.Lib.RepresentationTheory.InvariantLine
import DkMath.Lib.RepresentationTheory.LocalFixedCofixed

#print "file: DkMath.Lib.RepresentationTheory.ConjugateSquare"

/-!
# NOTE-031-003A: 共役二乗関係と安定直線

二次元空間の真の非零部分空間Nと商V/Nはいずれも一次元である。
T,M,M'がNを保存し、MM'=1かつMTM'=T²なら、一次元上のTのスカラーcは
c=c²を満たす。Tの単射性がc=0を除くためc=1となる。
商の単射性は、N上のTが有限次元の単射から全射にもなることを使って証明する。

結論は同じNの点ごとの固定と、全ての変化量Tx-xのNへの所属の両方である。
TそのものがV全体で恒等という結論ではない。数論のFrobenius元の存在や
野生慣性の消滅は、この線形代数の仮定を実際に供給する別の章で扱う。
-/
namespace DkMath.Lib.RepresentationTheory.ConjugateSquare

/-- 共役で二乗になる単射作用素は、保存する直線とその商の双方で恒等となる。
三作用素の安定性を全て保持し、商の可逆性を追加仮定せずに導く。 -/
theorem eq_id_on_line_of_conj_eq_sq {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (h2 : Module.finrank F V = 2)
    (N : Submodule F V) (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (T M M' : V →ₗ[F] V) (hT : Function.Injective T)
    (hMM' : ∀ x, M (M' x) = x)
    (hTN : ∀ x ∈ N, T x ∈ N) (hMN : ∀ x ∈ N, M x ∈ N) (hM'N : ∀ x ∈ N, M' x ∈ N)
    (hrel : ∀ x, M (T (M' x)) = T (T x)) :
    (∀ x ∈ N, T x = x) ∧ (∀ x, T x - x ∈ N) := by
  have hN1 : Module.finrank F N = 1 := by
    have hlt : Module.finrank F N < 2 := h2 ▸ Submodule.finrank_lt htop
    have hpos : 1 ≤ Module.finrank F N := Submodule.one_le_finrank_iff.mpr hbot
    omega
  have key : ∀ c : F, c = c * c → c = 0 ∨ c = 1 := by
    intro c hc
    have : c * (1 - c) = 0 := by rw [mul_sub, mul_one, ← hc, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h).symm
  have line_arg : ∀ {W : Type _} [AddCommGroup W] [Module F W], Module.finrank F W = 1 →
      ∀ (t m m' : W →ₗ[F] W), Function.Injective t → (∀ w, m (m' w) = w) →
        (∀ w, m (t (m' w)) = t (t w)) → ∀ w, t w = w := by
    intro W _ _ hW t m m' ht hmm' hrel'
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by
      by_contra h
      push Not at h
      have : Subsingleton W := ⟨fun a b => by rw [h a, h b]⟩
      have : Module.finrank F W = 0 := Module.finrank_zero_of_subsingleton
      omega
    have hgen : ∀ w : W, ∃ c : F, c • w₀ = w := fun w =>
      (finrank_eq_one_iff_of_nonzero' w₀ hw₀).mp hW w
    obtain ⟨c, hc⟩ := hgen (t w₀)
    obtain ⟨a, ha⟩ := hgen (m w₀)
    obtain ⟨a', ha'⟩ := hgen (m' w₀)
    have haa' : a' * a = 1 := by
      have h1 : (a' * a) • w₀ = w₀ := by
        rw [mul_smul, ha, ← map_smul, ha', hmm']
      by_contra hne
      apply hw₀
      have : (a' * a - 1) • w₀ = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact h
    have hcc : c • w₀ = (c * c) • w₀ := by
      have lhs : m (t (m' w₀)) = (a' * c * a) • w₀ := by
        rw [← ha', map_smul, ← hc, map_smul, map_smul, ← ha, smul_smul, smul_smul]
      have rhs : t (t w₀) = (c * c) • w₀ := by
        rw [← hc, map_smul, ← hc, smul_smul]
      have := hrel' w₀
      rw [lhs, rhs] at this
      rwa [show a' * c * a = c by rw [mul_right_comm, haa', one_mul]] at this
    have hc' : c = c * c := by
      have : (c - c * c) • w₀ = 0 := by rw [sub_smul, hcc, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hw₀
    have hc1 : c = 1 := by
      rcases key c hc' with h | h
      · exfalso
        apply hw₀
        apply ht
        rw [← hc, h, zero_smul, LinearMap.map_zero]
      · exact h
    intro w
    obtain ⟨d, rfl⟩ := hgen w
    rw [map_smul, ← hc, hc1, one_smul]
  constructor
  · let t : N →ₗ[F] N := T.restrict (p := N) (q := N) hTN
    let m : N →ₗ[F] N := M.restrict (p := N) (q := N) hMN
    let m' : N →ₗ[F] N := M'.restrict (p := N) (q := N) hM'N
    have ht : Function.Injective t := fun a b hab => by
      apply Subtype.ext
      apply hT
      simpa [t] using congrArg Subtype.val hab
    have hmm' : ∀ w, m (m' w) = w := fun w => Subtype.ext (by simp [m, m', hMM'])
    have hrel' : ∀ w, m (t (m' w)) = t (t w) := fun w => Subtype.ext (by simp [m, m', t, hrel])
    intro x hx
    have := line_arg hN1 t m m' ht hmm' hrel' ⟨x, hx⟩
    simpa [t] using congrArg Subtype.val this
  · have hQ1 : Module.finrank F (V ⧸ N) = 1 := by
      have := Submodule.finrank_quotient_add_finrank N
      omega
    have hTN' : N ≤ N.comap T := fun x hx => hTN x hx
    have hMN' : N ≤ N.comap M := fun x hx => hMN x hx
    have hM'N' : N ≤ N.comap M' := fun x hx => hM'N x hx
    let t : V ⧸ N →ₗ[F] V ⧸ N := N.mapQ N T hTN'
    let m : V ⧸ N →ₗ[F] V ⧸ N := N.mapQ N M hMN'
    let m' : V ⧸ N →ₗ[F] V ⧸ N := N.mapQ N M' hM'N'
    have hTonto : ∀ y ∈ N, ∃ x ∈ N, T x = y := by
      let t₀ : N →ₗ[F] N := T.restrict (p := N) (q := N) hTN
      have ht₀ : Function.Injective t₀ := fun a b hab => by
        apply Subtype.ext
        apply hT
        simpa [t₀] using congrArg Subtype.val hab
      have hsurj : Function.Surjective t₀ := LinearMap.surjective_of_injective ht₀
      intro y hy
      obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy⟩
      exact ⟨x, hx, by simpa [t₀] using congrArg Subtype.val hxy⟩
    have ht : Function.Injective t := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      induction z using Submodule.Quotient.induction_on with
      | H x =>
        have hx : T x ∈ N := by
          simpa [t, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] using hz
        obtain ⟨x', hx'N, hx'⟩ := hTonto (T x) hx
        have : x = x' := hT hx'.symm
        rw [Submodule.Quotient.mk_eq_zero, this]
        exact hx'N
    have hmm' : ∀ w, m (m' w) = w := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H x => simp [m, m', Submodule.mapQ_apply, hMM']
    have hrel' : ∀ w, m (t (m' w)) = t (t w) := by
      intro w
      induction w using Submodule.Quotient.induction_on with
      | H x => simp [m, m', t, Submodule.mapQ_apply, hrel]
    intro x
    have := line_arg hQ1 t m m' ht hmm' hrel' (Submodule.Quotient.mk x)
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, sub_eq_zero]
    simpa [t, Submodule.mapQ_apply] using this

end DkMath.Lib.RepresentationTheory.ConjugateSquare
