/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia
import DkMath.Lib.RepresentationTheory.FixedLineExtension

#print "file: DkMath.FLT.FreyCyclotomicExtensionCharacter"

/-!
# 同じ逆像商の円分指標核上の有限加法指標

全巡回段で固定直線値の指標を実際に構成する。その値域は `p` 個であり、
共役では逆円分指標で変換される。`p` 上の局所分裂から指標核と分解群の
交わりでの消滅を得る。`p` 外は前章の非共鳴吸収と、明示して残した共鳴入力を使う。
この指標の大域消滅は証明せず、大域補直線・塔の次段と正確に接続する。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule ValuationInertia
open DkMath.Lib.RepresentationTheory
open FixedLineExtension

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticCyclotomicExtensionCharacter : S.rationalCurve.IsElliptic :=
  S.rationalCurve_isElliptic

variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)

include hline hcofixed hstable hm hcard hbase

/-- 同じ商の円分スカラー公式を通常の `ZMod p` スカラーで公開する。 -/
theorem residual_cyclic_extension_quotient_character
    (σ : Field.absoluteGaloisGroup ℚ) (v : TorsionPreimageQuotient.Quotient p K) :
    preimageRepresentation S.rationalCurve p K hstable σ v -
      (cyclotomicCharacter p σ : ZMod p) • v ∈ TorsionPreimageQuotient.torsionImage p K := by
  rw [← ZMod.natCast_zmod_val (cyclotomicCharacter p σ : ZMod p), Nat.cast_smul_eq_nsmul]
  exact S.residual_cofixed_cyclic_extension_quotient_cyclotomic L hline hcofixed K hstable hm hcard hbase σ v

/-- 大域安定な同じ巡回段の商から、指標核上の固定直線値の実際の準同型を作る。 -/
def residualCyclicExtensionCharacter (v : TorsionPreimageQuotient.Quotient p K) :
    (cyclotomicCharacter (K := ℚ) p).ker →*
      Multiplicative (TorsionPreimageQuotient.torsionImage p K) :=
  deviationAt (preimageRepresentation S.rationalCurve p K hstable)
    (TorsionPreimageQuotient.torsionImage p K) (cyclotomicCharacter p)
    (S.residual_cofixed_cyclic_extension_profile L hcofixed K hstable hm hcard hbase).2.2.2.1
    (S.residual_cyclic_extension_quotient_character L hline hcofixed K hstable hm hcard hbase) v

/-- この指標の値は、指定された同じ商ベクトルの作用差そのもの。 -/
theorem residualCyclicExtensionCharacter_apply (v : TorsionPreimageQuotient.Quotient p K)
    (g : (cyclotomicCharacter (K := ℚ) p).ker) :
    (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g).toAdd.val =
      preimageRepresentation S.rationalCurve p K hstable g.val v - v := rfl

omit hline hcofixed hstable hbase in
/-- 値域は固定直線の実際の `p` 個の元。 -/
theorem residual_cyclic_extension_character_value_card :
    Nat.card (TorsionPreimageQuotient.torsionImage p K) = p :=
  card_torsionImage_of_cyclic S.rationalCurve K hm hcard

/-- 共役の向きは逆円分指標。Kummer 双対化前の重みを取り違えない。 -/
theorem residual_cyclic_extension_character_conjugate
    (v : TorsionPreimageQuotient.Quotient p K) (σ : Field.absoluteGaloisGroup ℚ)
    (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : cyclotomicCharacter p (σ * g.val * σ⁻¹) = 1) :
    (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
      ⟨σ * g.val * σ⁻¹, hg⟩).toAdd =
      (cyclotomicCharacter p σ⁻¹ : ZMod p) •
        (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g).toAdd :=
  deviationAt_conjugate _ _ _ _ _ v σ g hg

/-- `p` 上では円分指標核と分解群の交わり全体で消える。慣性より強い局所結論。 -/
theorem residual_cyclic_extension_character_at_p (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (v : TorsionPreimageQuotient.Quotient p K) (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : g.val ∈ A.decompositionSubgroup ℚ) :
    S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g = 1 := by
  obtain ⟨D, hCD, hD, _⟩ := S.residual_cofixed_cyclic_extension_locally_split_at_p
    hp5 L hline hcofixed K hstable hm hcard hbase A hA
  apply (deviationAt_eq_one_iff _ _ _ _ _ v g).mpr
  have he := eq_one_of_complement (preimageRepresentation S.rationalCurve p K hstable)
    _ (cyclotomicCharacter p)
    (S.residual_cofixed_cyclic_extension_profile L hcofixed K hstable hm hcard hbase).2.2.2.1
    (S.residual_cyclic_extension_quotient_character L hline hcofixed K hstable hm hcard hbase)
    D hCD (hD g.val hg) g.property
  rw [he]; rfl

/-- 指標核上の固定性と、実際の大域補直線の存在との同値。非自明な円分値も内部供給する。 -/
theorem residual_cyclic_extension_splits_iff_character_trivial (hp5 : 5 ≤ p) :
    (∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) ↔
      ∀ v, ∀ g : (cyclotomicCharacter (K := ℚ) p).ker,
        S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g = 1 := by
  obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) (Fact.out : p.Prime)
  obtain ⟨t, _, ht⟩ := CyclotomicInertia.exists_inertia_cyclotomic_eq A hA (-1)
  have htne : (cyclotomicCharacter p t : ZMod p) ≠ 1 := by
    rw [ht]
    change (-1 : ZMod p) ≠ 1
    intro he
    have h2 : (2 : ZMod p) = 0 := by linear_combination -he
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  let hf := (S.residual_cofixed_cyclic_extension_profile L hcofixed K hstable hm hcard hbase).2.2.2.1
  let hq := S.residual_cyclic_extension_quotient_character L hline hcofixed K hstable hm hcard hbase
  exact (stable_complement_iff_kernel_trivial _ _ _ hf hq htne).trans
    (kernel_trivial_iff_deviationAt_trivial _ _ _ hf hq)

/-- 指標は実際に開核を持つ。元の高次捩れ表現の開核から内部供給する。 -/
theorem residual_cyclic_extension_character_kernel_isOpen
    (v : TorsionPreimageQuotient.Quotient p K) :
    IsOpen ((S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v).ker :
      Set (cyclotomicCharacter (K := ℚ) p).ker) := by
  let ρ := preimageRepresentation S.rationalCurve p K hstable
  let H : Subgroup (cyclotomicCharacter (K := ℚ) p).ker :=
    ρ.ker.comap (cyclotomicCharacter (K := ℚ) p).ker.subtype
  have hH : IsOpen (H : Set (cyclotomicCharacter (K := ℚ) p).ker) :=
    (S.residual_cofixed_cyclic_extension_profile L hcofixed K hstable hm hcard hbase).2.2.2.2.preimage
      continuous_subtype_val
  apply Subgroup.isOpen_mono (H₁ := H) ?_ hH
  intro g hg
  change S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g = 1
  apply (deviationAt_eq_one_iff _ _ _ _ _ v g).mpr
  change ρ g.val = 1 at hg
  change ρ g.val v = v
  rw [hg]; rfl

/-- 指標の像の濃度も `p` 以下。無限群上での抽象的な連続性だけに留めない。 -/
theorem residual_cyclic_extension_character_range_card_le
    (v : TorsionPreimageQuotient.Quotient p K) :
    Nat.card (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v).range ≤ p := by
  have hc := card_torsionImage_of_cyclic S.rationalCurve K hm hcard
  let : Finite (TorsionPreimageQuotient.torsionImage p K) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : p.Prime).ne_zero)
  calc
    Nat.card (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v).range ≤
        Nat.card (Multiplicative (TorsionPreimageQuotient.torsionImage p K)) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = p := hc

/-- `p` 外の指標の局所消滅。未実装の入力は共鳴する悪い住所に限る。 -/
theorem residual_cyclic_extension_character_inertia_away (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q →
        ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (v : TorsionPreimageQuotient.Quotient p K) (g : (cyclotomicCharacter (K := ℚ) p).ker)
    (hg : g.val ∈ inertiaSubgroupIn A ℚ) :
    S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g = 1 := by
  apply (deviationAt_eq_one_iff _ _ _ _ _ v g).mpr
  exact S.residual_preimage_unramified_away_of_resonant_inertia hp5 L hline hcofixed K hstable
    hm hcard hbase hbad q hq hqp A hA g.val hg v

/-- 大域分裂しないなら、この同じ指標族の一つは位数 `p` の値域全体へ全射。
これが次の類群・単数の算術で排除すべき実際の有限商である。 -/
theorem residual_cyclic_extension_nonsplit_has_surjective_character (hp5 : 5 ≤ p)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) :
    ∃ v, Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) := by
  classical
  have hn := (S.residual_cyclic_extension_splits_iff_character_trivial
    L hline hcofixed K hstable hm hcard hbase hp5).not.mp hns
  push Not at hn
  obtain ⟨v, g, hg⟩ := hn
  refine ⟨v, ?_⟩
  let f := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  have hc : Nat.card (Multiplicative (TorsionPreimageQuotient.torsionImage p K)) = p :=
    card_torsionImage_of_cyclic S.rationalCurve K hm hcard
  let : Finite (Multiplicative (TorsionPreimageQuotient.torsionImage p K)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : p.Prime).ne_zero)
  have hd : Nat.card f.range ∣ p := by
    simpa only [hc] using Subgroup.card_subgroup_dvd_card f.range
  have hr : Nat.card f.range = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with h | h
    · have : Subsingleton f.range := (Nat.card_eq_one_iff_unique.mp h).1
      exact (hg (congrArg Subtype.val
        (Subsingleton.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1))).elim
    · exact h
  have hs : Function.Surjective (Subtype.val : f.range →
      Multiplicative (TorsionPreimageQuotient.torsionImage p K)) :=
    (Subtype.val_injective.bijective_of_nat_card_le (by rw [hc, hr])).2
  intro z
  obtain ⟨⟨_, ⟨u, rfl⟩⟩, hu⟩ := hs z
  exact ⟨u, hu⟩

/-- この具体的な指標族の消滅から、同じ点群で巡回塔の次段を構成する。
消滅は算術入力として明示し、未証明の大域 extension 消滅を宣言しない。 -/
theorem residual_cyclic_tower_step_of_character_trivial (hp5 : 5 ≤ p)
    (hzero : ∀ v, ∀ g : (cyclotomicCharacter (K := ℚ) p).ker,
      S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v g = 1) :
    ∃ K' : AddSubgroup (Points S.rationalCurve), K ≤ K' ∧ Nat.card K' = p ^ (m + 1) ∧ IsAddCyclic K' ∧
      (∀ x ∈ K', p ^ (m + 1) • x = 0) ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K', pointAction S.rationalCurve σ x ∈ K') ∧
      (∀ x ∈ K', p • x = 0 → x ∈ K) := by
  obtain ⟨D, hCD, hD⟩ :=
    (S.residual_cyclic_extension_splits_iff_character_trivial L hline hcofixed K hstable hm hcard hbase hp5).mpr hzero
  apply exists_tower_step_of_stable_complement S.rationalCurve K hstable hm hcard ?_ D hCD hD
  intro x hx
  exact congrArg (fun z : K => z.val) (hcard ▸ card_nsmul_eq_zero' (x := (⟨x, hx⟩ : K)))

end
end DkMath.FLT.Frey.Source
