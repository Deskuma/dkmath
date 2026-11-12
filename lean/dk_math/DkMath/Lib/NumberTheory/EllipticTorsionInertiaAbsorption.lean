/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticInertiaTransport
import DkMath.Lib.NumberTheory.EllipticGoodReductionInertia

#print "file: DkMath.Lib.NumberTheory.EllipticTorsionInertiaAbsorption"

/-!
# 有限捩れ上の局所慣性の吸収を大域 Galois 作用へ運ぶ

`K` は同じ幾何学的点群の任意の部分群とする。全有限素点で
`τ • y - y ∈ K` が成立すれば、全 Galois 元について同じ所属が成り立つ。

証明は既存の三つの実定理を合成する。

* 非零 `n` の `E[n]` は有限。
* 座標作用の連続性から、その表現の核は Krull 位相で開く。
* 全有限素点の絶対慣性を含む開部分群は絶対 Galois 群全体。

最後の算術は `AbsoluteInertiaRepresentation` から供給する。生成性や開核を
provider として追加仮定せず、`K` の安定性・有限性も要求しない。
良還元かつ `q ∤ n` の住所では既存の慣性固定性を使い、利用側に残す局所条件を
`q ∣ n` または `q ∣ Δ` の住所だけへ絞る。
-/

namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

open WeierstrassCurve IsLocalRing ValuationInertia
open DkMath.Lib.RepresentationTheory

noncomputable section

/-- 点群の部分群を、同じ `E[n]` の部分加群へ引き戻す。点の値を変更しない。 -/
def torsionSubmoduleOfPointSubgroup (E : WeierstrassCurve ℚ) (n : ℕ)
    (K : AddSubgroup (Points E)) : Submodule (ZMod n) (Torsion E n) :=
  AddSubgroup.toZModSubmodule n (K.comap (torsionGroup E n).subtype)

/-- 引き戻した部分加群への所属は、元の点の `K` 所属そのものである。 -/
theorem mem_torsionSubmoduleOfPointSubgroup_iff (E : WeierstrassCurve ℚ) (n : ℕ)
    (K : AddSubgroup (Points E)) (P : Torsion E n) :
    P ∈ torsionSubmoduleOfPointSubgroup E n K ↔ P.val ∈ K := Iff.rfl

/-- 実際の有限 `E[n]` 上で、全局所慣性による差の吸収から全 Galois 元による吸収を得る。
任意の `K` に適用でき、`K` 自体の安定性を先に仮定する必要はない。 -/
theorem pointAction_sub_mem_of_inertia_absorbs
    (E : WeierstrassCurve ℚ) {n : ℕ} (hn : n ≠ 0) (K : AddSubgroup (Points E))
    (hlocal : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      LiesOverPrime A q → ∀ τ ∈ inertiaSubgroupIn A ℚ,
        ∀ y : Points E, n • y = 0 → pointAction E τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) {y : Points E} (hy : n • y = 0) :
    pointAction E σ y - y ∈ K := by
  have hcof := isCofixedOn_of_inertia E n hn
    (torsionSubmoduleOfPointSubgroup E n K) (by
      intro q hq A hA τ hτ P
      exact hlocal q hq A hA τ hτ P.val P.property)
  exact hcof σ (⟨y, hy⟩ : Torsion E n)

/-- 良還元と `q ∤ n` は、同じ整数モデルから `E[n]` 上の慣性固定性を供給する。
有限剰余体を仮定せず、任意の延長付値環の剰余標数と整数の単元性を使う。 -/
theorem pointAction_eq_of_inertia_of_integer_good
    (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E)
    {q n : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ n) (hgood : ¬ (q : ℤ) ∣ W.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points E} (hy : n • y = 0) : pointAction E τ y = y := by
  classical
  let M := W.map (Int.castRingHom A)
  have hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ) := by
    rw [← hW]
    ext <;> simp [M, WeierstrassCurve.baseChange]
  let : CharP (ResidueField A) q := ValuationPrimeSupport.charP_residueField A hq hA
  have hΔ : (M.map (residue A)).Δ ≠ 0 := by
    change ((W.map (Int.castRingHom A)).map (residue A)).Δ ≠ 0
    simpa only [WeierstrassCurve.map_Δ, Int.coe_castRingHom, map_intCast,
      ne_eq, CharP.intCast_eq_zero_iff (ResidueField A) q] using hgood
  have hn : A.valuation (n : AlgebraicClosure ℚ) = 1 := by
    have hnd : ¬ (q : ℤ) ∣ (n : ℤ) := by exact_mod_cast hqn
    simpa only [Int.cast_natCast] using
      ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
        ((ValuationSubring.mem_nonunits_iff A).mp hA) hnd
  exact congrArg Subtype.val (EllipticGoodReductionInertia.fixed_of_inertia_of_good_model
    E n A M hmodel hΔ hn τ hτ (⟨y, hy⟩ : Torsion E n))

/-- 全良還元素数を内部で処理し、吸収の仮定を捩れ指数または判別式を割る住所へ限定する。
この定理は局所条件の大域化を完了するが、残る悪い住所の吸収自体は仮定である。 -/
theorem pointAction_sub_mem_of_inertia_absorbs_bad_support
    (E : WeierstrassCurve ℚ) (W : WeierstrassCurve ℤ)
    (hW : W.map (Int.castRingHom ℚ) = E)
    {n : ℕ} (hn : n ≠ 0) (K : AddSubgroup (Points E))
    (hbad : ∀ q : ℕ, q.Prime → (q ∣ n ∨ (q : ℤ) ∣ W.Δ) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points E,
          n • y = 0 → pointAction E τ y - y ∈ K)
    (σ : Field.absoluteGaloisGroup ℚ) {y : Points E} (hy : n • y = 0) :
    pointAction E σ y - y ∈ K := by
  apply pointAction_sub_mem_of_inertia_absorbs E hn K ?_ σ hy
  intro q hq A hA τ hτ z hz
  by_cases hqn : q ∣ n
  · exact hbad q hq (Or.inl hqn) A hA τ hτ z hz
  · by_cases hΔ : (q : ℤ) ∣ W.Δ
    · exact hbad q hq (Or.inr hΔ) A hA τ hτ z hz
    · rw [pointAction_eq_of_inertia_of_integer_good E W hW hq hqn hΔ A hA τ hτ hz,
        sub_self]
      exact K.zero_mem

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
