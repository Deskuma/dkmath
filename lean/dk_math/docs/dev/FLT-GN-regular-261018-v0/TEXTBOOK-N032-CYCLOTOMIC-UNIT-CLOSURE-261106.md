# NOTE-032 教科書：固定無限素点・射影子トレースと単元側算術の完成

日付：2026-11-06。前段：`TEXTBOOK-N032-NUMBER-FIELD-UNIT-TRACE-261105.md`。
今回の2ステップは、①同じ円分 Galois 指標による固定無限素点の分類、
②同じ ω² 射影子の重み付きトレース計算である。
最後に既存の次元・対数検出経路と合成し、Frey 分裂入口から単元側の算術入力を除去する。

3つの Lean ブロックは production ファイルの著作権・通知を含む全文である。
個別のコピー後コンパイルも検証する。順にモジュールとして配置して利用する。
正確なファイル同定のため、import 直後の `#print "file: …"` は省略しない。

## 今回の到達点と残る境界

| 内容 | 状態 |
| --- | --- |
| σd が無限素点を固定する ⇔ d=±1 | 同じ根・同じ指標で証明済み |
| 固定点数が (p−1)/2 または0 | 証明済み |
| 同じ unitAction の具体的なトレース | 証明済み |
| 同じ omegaSquareProjector の trace=1 | 証明済み |
| 同じ ω² 単元空間の次元1 | provider なしで証明済み |
| 同じ primary 単元空間が零 | provider なしで証明済み |
| 同じ条件の整数環単元の大域 p 乗根 | 存在を証明済み |
| Frey 分裂の hrank/htrace/hunit/hdetect 入力 | 新しい入口から除去済み |
| hbad・hclass・巡回塔・一般 hno | 引き続き未完成 |

ここで「provider なし」は、素数 p≥5 と指定した原始根のもとで、
以前の次元・トレース・単元消滅を入力しないという意味である。
一般 hno 全体の完成を意味しない。

## ステップ1：同じ σd による固定無限素点

F=rootField ζ、σd=(characterEquiv hζ).symm d を取る。
既存の指標同型も、指定された原始根 ζ も、体も選び直さない。
無限素点 w の複素埋め込みを ι とすると、Mathlib の作用は ι∘σd⁻¹ により定まる。
従って、同じ根に対して実際に必要な冪則は

    σd⁻¹(ζ)=ζ^(d⁻¹).val

である。`symm_symm_apply_zeta` がこの逆元を明示する。

`InfinitePlace.mk_eq_iff` により、固定される条件を

1. ι∘σd⁻¹=ι、
2. 複素共役を取れば ι∘σd⁻¹ と ι が一致する、

に分ける。前者では埋め込みの単射性から σd=1、よって d=1。
後者では埋め込まれた原始根 z が単位円上にあることを使い、conj(z)=z⁻¹ とする。
同じ根の原始性から d⁻¹=−1、従って d=−1 を得る。
逆に d=−1 の場合は、同じ原始根から作った power basis の生成性を使い、
埋め込み全体が複素共役に一致することを証明する。

従って、p>2 の任意の無限素点 w に対して

    σd • w=w ↔ d=1 ∨ d=−1

となる。d=±1 ならすべての素点が固定され、それ以外では固定点の型が空になる。
同じ円分体の実素点数0・複素素点数 φ(p)/2 を用いて

    #Fix(d)=(p−1)/2 if d=±1, and 0 otherwise

を証明する。固定点数の provider を追加しない。

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Unit action and trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: retain DkMath SAME rootField, specified primitive root and characterEquiv;
handle inverse Galois action explicitly, without replacing the cyclotomic field.
-/

import DkMath.Lib.NumberTheory.NumberFieldUnitLogTrace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

#print "file: DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed"

/-!
# 同じ円分指標による無限素点の固定点分類

指定された原始根と同じ rootField の既存 characterEquiv を保持する。
埋め込みの一致／複素共役の一致を分け、逆自己同型の指数 d⁻¹ を明示する。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed

open NumberField NumberField.InfinitePlace
open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
noncomputable section

variable {p : ℕ} [Fact p.Prime]
local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

lemma neg_one_inv' : (-1 : (ZMod p)ˣ)⁻¹ = -1 :=
  inv_eq_of_mul_eq_one_right (by simp)

lemma pow_natCast_neg_one {z : ℂ} (hz : IsPrimitiveRoot z p)
    {n : ℕ} (hn : (n : ZMod p) = -1) : z ^ n = z⁻¹ := by
  have hd : p ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hn]
    ring
  obtain ⟨k, hk⟩ := hd
  have h1 : z ^ (n + 1) = 1 := by rw [hk, pow_mul, hz.pow_eq_one, one_pow]
  rw [pow_succ] at h1
  exact eq_inv_of_mul_eq_one_left h1

lemma natCast_eq_neg_one_of_pow {z : ℂ} (hz : IsPrimitiveRoot z p) (hz0 : z ≠ 0)
    {n : ℕ} (hpow : z ^ n = z⁻¹) : (n : ZMod p) = -1 := by
  have h1 : z ^ (n + 1) = 1 := by rw [pow_succ, hpow, inv_mul_cancel₀ hz0]
  have h2 := (hz.pow_eq_one_iff_dvd _).mp h1
  have h0 : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 素点の作用は自己同型の逆元を使う。同じ根の指数も d⁻¹。 -/
theorem symm_symm_apply_zeta (d : (ZMod p)ˣ) :
    ((characterEquiv hζ).symm d).symm (baseRoot ζ) =
      baseRoot ζ ^ ((d⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
  have he : ((characterEquiv hζ).symm d).symm = (characterEquiv hζ).symm d⁻¹ := by
    rw [← AlgEquiv.aut_inv, ← map_inv]
  rw [he]
  exact characterEquiv_symm_root hζ d⁻¹

/-- 同じ σd が一つの無限素点を固定することは d=±1 と同値。 -/
theorem smul_infinitePlace_eq_self_iff (_hp : 2 < p) (d : (ZMod p)ˣ) (w : InfinitePlace (rootField ζ)) :
    (characterEquiv hζ).symm d • w = w ↔ (d = 1 ∨ d = -1) := by
  let := rootField_isCyclotomic hζ
  have hroot := baseRoot_primitive hζ
  have hzprim : IsPrimitiveRoot (w.embedding (baseRoot ζ)) p :=
    hroot.map_of_injective w.embedding.injective
  have hz0 : w.embedding (baseRoot ζ) ≠ 0 := by
    intro h0
    have := hzprim.pow_eq_one
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at this
    exact zero_ne_one this
  have hznorm : ‖w.embedding (baseRoot ζ)‖ = 1 := by
    refine Complex.norm_eq_one_of_pow_eq_one ?_ (Fact.out : p.Prime).ne_zero
    rw [← map_pow, hroot.pow_eq_one, map_one]
  have hconj : (starRingEnd ℂ) (w.embedding (baseRoot ζ)) =
      (w.embedding (baseRoot ζ))⁻¹ :=
    (Complex.inv_eq_conj hznorm).symm
  constructor
  · intro hw
    rw [← mk_embedding w, smul_mk] at hw
    rcases mk_eq_iff.mp hw with h | h
    · left
      have hσ1 : (characterEquiv hζ).symm d = 1 := by
        have hsymm : ((characterEquiv hζ).symm d).symm = 1 := by
          apply AlgEquiv.ext
          intro x
          exact w.embedding.injective (RingHom.congr_fun h x)
        calc (characterEquiv hζ).symm d
            = ((characterEquiv hζ).symm d).symm.symm := (AlgEquiv.symm_symm _).symm
          _ = (1 : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)).symm := by rw [hsymm]
          _ = 1 := rfl
      have hd1 : d = characterEquiv hζ ((characterEquiv hζ).symm d) :=
        (MulEquiv.apply_symm_apply _ d).symm
      rw [hσ1, map_one] at hd1
      exact hd1
    · right
      have heval : w.embedding (((characterEquiv hζ).symm d).symm
          (baseRoot ζ)) =
          (w.embedding (baseRoot ζ))⁻¹ := by
        have h2 := congrArg (starRingEnd ℂ)
          (RingHom.congr_fun h (baseRoot ζ))
        rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj] at h2
        rw [RingHom.coe_comp, Function.comp_apply] at h2
        exact h2.trans hconj
      rw [symm_symm_apply_zeta, map_pow] at heval
      have hcast : (((((d⁻¹ : (ZMod p)ˣ) : ZMod p)).val : ZMod p)) = -1 :=
        natCast_eq_neg_one_of_pow (p := p) hzprim hz0 heval
      rw [ZMod.natCast_val, ZMod.cast_id] at hcast
      have hinv : d⁻¹ = (-1 : (ZMod p)ˣ) := by
        apply Units.ext
        rw [hcast]
        simp
      rw [← inv_inv d, hinv, neg_one_inv']
  · intro hd
    rcases hd with rfl | rfl
    · rw [map_one]
      exact one_smul _ w
    · rw [← mk_embedding w, smul_mk, mk_eq_iff]
      right
      have hgen : w.embedding (((characterEquiv hζ).symm (-1)).symm
          (baseRoot ζ)) =
          ComplexEmbedding.conjugate w.embedding (baseRoot ζ) := by
        rw [symm_symm_apply_zeta, map_pow, ComplexEmbedding.conjugate_coe_eq, hconj]
        refine pow_natCast_neg_one (p := p) hzprim ?_
        rw [ZMod.natCast_val, ZMod.cast_id, neg_one_inv']
        simp
      have h1 : RingHom.toRatAlgHom
          (w.embedding.comp ↑(((characterEquiv hζ).symm (-1)).symm)) =
          RingHom.toRatAlgHom (ComplexEmbedding.conjugate w.embedding) := by
        apply PowerBasis.algHom_ext (hroot.powerBasis ℚ)
        rw [IsPrimitiveRoot.powerBasis_gen]
        exact hgen
      have h2 : w.embedding.comp ↑(((characterEquiv hζ).symm (-1)).symm) =
          ComplexEmbedding.conjugate w.embedding := congrArg AlgHom.toRingHom h1
      rw [h2]
      exact star_star w.embedding

/-- 同じ素点作用の実際の固定点数。まず一般の totient 表示で得る。 -/
theorem card_fixedPlaces (hp : 2 < p) (d : (ZMod p)ˣ) :
    Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} =
      if d = 1 ∨ d = -1 then p.totient / 2 else 0 := by
  let := rootField_isCyclotomic hζ
  split_ifs with hd
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun w => (smul_infinitePlace_eq_self_iff hζ hp d w).mpr hd))]
    rw [Nat.card_eq_fintype_card]
    have h1 := card_eq_nrRealPlaces_add_nrComplexPlaces (rootField ζ)
    have h2 : nrRealPlaces (rootField ζ) = 0 := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (rootField ζ) hp
    have h3 : nrComplexPlaces (rootField ζ) = p.totient / 2 := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two p (rootField ζ)
    omega
  · have he : IsEmpty {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} := by
      refine ⟨fun x => hd ?_⟩
      exact (smul_infinitePlace_eq_self_iff hζ hp d x.1).mp x.2
    have := he
    exact Nat.card_of_isEmpty


/-- 素数次数での固定点数。新しい濃度・作用 provider を要求しない。 -/
theorem card_fixedPlaces_prime (hp : 2 < p) (d : (ZMod p)ˣ) :
    Nat.card {w : InfinitePlace (rootField ζ) // (characterEquiv hζ).symm d • w = w} =
      if d = 1 ∨ d = -1 then (p - 1) / 2 else 0 := by
  rw [card_fixedPlaces hζ hp, Nat.totient_prime (Fact.out : p.Prime)]


end
end DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed
```

## ステップ2：同じ射影子の trace=1

前段で証明した実際のトレース

    trace(ρd)=d+#Fix(d)−1

に同じ固定点数を代入する。

    trace(ρd)=(d−1)+if d=±1 then (p−1)/2 else 0

が同じ既存の unitAction について成立する。
以前の `omegaSquareProjector_apply_units` から線形写像の等式を導き、
同じ射影子を別名で定義し直すことなく、トレースの線形性を適用する。

    trace(e₂)=|𝔽pˣ|⁻¹ Σd d⁻² trace(ρd)

p≥5 なら p−1 は1も2も割らないので、有限体の非自明な冪和により

    Σd d⁻¹=0,    Σd d⁻²=0

が成立する。指示関数の項については、d=1 と d=−1 が異なることを証明して

    Σd d⁻²(if d=±1 then m else 0)=2m

を得る。p の奇数性により 2((p−1)/2)=p−1 となるので、

    trace(e₂)=−1 * (−1)=1

となる。計算のすべての項は ZMod p で扱い、自然数の割り算の等式を明示的に係数へ写す。

## 次元1と同じ単元の大域 p 乗根まで

前段の有限次元性、同じ射影子の range、自然数次元<p の証明はすでに存在する。
今回の trace=1 を `weightSquareSpace_finrank_eq_one_of_trace` へ渡せば、
同じ `weightSquareSpace hζ` の自然数次元が1になる。
さらに同じ円分単元の射影 g=e₂[1+ζ] の非零検出を使い、
同じ局所 p 乗条件付き空間 `primaryWeightSquareSpace hζ` が零になる。
これらの公開定理は hrank/htrace/hdetect/hunit を要求しない。

`exists_global_unit_pow_of_primary` は、同じ整数環単元 u の実際の
固有・局所条件から、実際の大域整数環単元 a の存在 a^p=u を返す。
単に空間を零と仮定したり、別の単元に代表元を取り替えたりしていない。

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Unit action and trace arguments adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean.
Upstream blob: 6801f82a5eec740ce4d5d658b7a1dc35040f2aba
Modified: use DkMath SAME unitAction and omegaSquareProjector. Derive all-prime
unit-rank and primary-unit vanishing from actual fixed-place and finite-sum proofs.
-/

import DkMath.Lib.NumberTheory.CyclotomicInfinitePlaceFixed
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareUnitRank

#print "file: DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace"

/-!
# 同じ ω² 射影子の trace=1 と、単元側の無条件消滅

指定された根と同じ無限素点の固定点数を代入し、有限体の重み付き和を計算する。
既存の同じ射影子の trace を1と証明して、従来の hrank/hunit を内部供給する。
類群・共鳴素点・巡回塔は本章では証明しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace

open CyclotomicKernelField CyclotomicKummerWeight CyclotomicOmegaSquareProjector
open CyclotomicInfinitePlaceFixed NumberFieldUnitLogTrace CyclotomicOmegaSquareUnitRank
open CyclotomicPrimaryUnitSpace KummerSelmerExact
open scoped NumberField
noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-- 有限体の単元上の非自明な冪和は零。 -/
theorem sum_units_pow_eq_zero (i : ℕ) (hi : ¬ (p - 1) ∣ i) :
    ∑ d : (ZMod p)ˣ, (d : ZMod p) ^ i = 0 := by
  have h := FiniteField.sum_pow_units (ZMod p) i
  rw [ZMod.card p, ite_eq_right hi] at h
  simpa [Units.val_pow_eq_pow_val] using h

/-- 逆元による並べ替えを使った、逆冪の和の零化。 -/
theorem sum_units_inv_pow_eq_zero (i : ℕ) (hi : ¬ (p - 1) ∣ i) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ i)⁻¹ = 0 := by
  rw [← sum_units_pow_eq_zero (p := p) i hi]
  refine Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ fun d => ?_
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_pow]

/-- 射影子の trace の非指示関数項は相殺する。 -/
theorem sum_inv_sq_mul_sub_one (hp5 : 5 ≤ p) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * ((d : ZMod p) - 1) = 0 := by
  have h1 : ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 1)⁻¹ = 0 :=
    sum_units_inv_pow_eq_zero (p := p) 1 (by intro h; have := Nat.le_of_dvd one_pos h; omega)
  have h2 : ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ = 0 :=
    sum_units_inv_pow_eq_zero (p := p) 2 (by intro h; have := Nat.le_of_dvd two_pos h; omega)
  have : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * ((d : ZMod p) - 1) =
      ((d : ZMod p) ^ 1)⁻¹ - ((d : ZMod p) ^ 2)⁻¹ := by
    intro d
    have hd : (d : ZMod p) ≠ 0 := Units.ne_zero d
    field_simp
  simp only [this, Finset.sum_sub_distrib, h1, h2, sub_zero]

/-- d=±1 の2つの指示関数項は正確に2mを与える。 -/
theorem sum_inv_sq_mul_indicator (hp5 : 5 ≤ p) (m : ZMod p) :
    ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * (if d = 1 ∨ d = -1 then m else 0) = 2 * m := by
  have : Fact (2 < p) := ⟨by omega⟩
  have hne : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    simp only [Units.val_neg, Units.val_one] at this
    exact ZMod.neg_one_ne_one this
  have hsplit : ∀ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ * (if d = 1 ∨ d = -1 then m else 0) =
      (if d = 1 then m else 0) + (if d = -1 then m else 0) := by
    intro d
    by_cases h1 : d = 1
    · subst h1; simp [hne.symm]
    · by_cases h2 : d = -1
      · subst h2; simp [hne]
      · simp [h1, h2]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 同じ既存 unitAction の具体的なトレース。 -/
theorem trace_unitAction (hp5 : 5 ≤ p) (d : (ZMod p)ˣ) :
    LinearMap.trace (ZMod p) _ (unitAction (p := p) ((characterEquiv hζ).symm d)) =
      ((d : ZMod p) - 1) +
        (if d = 1 ∨ d = -1 then (((p - 1) / 2 : ℕ) : ZMod p) else 0) := by
  rw [trace_unitAction_eq_character_add_fixedPlaces, card_fixedPlaces_prime hζ (by omega)]
  split_ifs <;> push_cast <;> ring

/-- 以前の同じ射影子の、同じ指標同型による有限和表示。新しく定義し直さない。 -/
theorem omegaSquareProjector_eq_units_sum :
    omegaSquareProjector hζ = (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ •
      ∑ d : (ZMod p)ˣ, ((d : ZMod p) ^ 2)⁻¹ • unitAction (p := p) ((characterEquiv hζ).symm d) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.smul_apply, LinearMap.sum_apply, unitAction,
    MonoidHom.coe_mk, OneHom.coe_mk] using omegaSquareProjector_apply_units hζ x

/-- 実際の無限素点分類と有限体の和から、同じ射影子の trace=1 を証明する。 -/
theorem trace_omegaSquareProjector (hp5 : 5 ≤ p) :
    LinearMap.trace (ZMod p) _ (omegaSquareProjector hζ) = 1 := by
  have hm : (2 : ZMod p) * (((p - 1) / 2 : ℕ) : ZMod p) = -1 := by
    have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left (by omega)
    have h : 2 * ((p - 1) / 2) = p - 1 := by omega
    have hc := congrArg (Nat.cast : ℕ → ZMod p) h
    push_cast at hc
    rw [hc, Nat.cast_sub hp.out.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [omegaSquareProjector_eq_units_sum, map_smul, map_sum]
  simp only [map_smul, trace_unitAction hζ hp5, smul_eq_mul, mul_add,
    Finset.sum_add_distrib, sum_inv_sq_mul_sub_one hp5, sum_inv_sq_mul_indicator hp5,
    zero_add, hm, CyclotomicPrimaryLogNonzero.card_units_inv]
  ring

/-- 同じ実際の単元 ω² 固有空間の次元1。hrank/trace provider を要求しない。 -/
theorem weightSquareSpace_finrank_eq_one (hp5 : 5 ≤ p) :
    Module.finrank (ZMod p) (weightSquareSpace hζ) = 1 :=
  weightSquareSpace_finrank_eq_one_of_trace hζ hp5 (trace_omegaSquareProjector hζ hp5)

/-- 同じ局所冪条件付き ω² 単元空間の無条件消滅。単元側の算術入力を解消する。 -/
theorem primaryWeightSquareSpace_eq_bot (hp5 : 5 ≤ p) : primaryWeightSquareSpace hζ = ⊥ :=
  primaryWeightSquareSpace_eq_bot_of_trace hζ hp5 (trace_omegaSquareProjector hζ hp5)

/-- 同じ固有・局所冪条件を持つ実際の単元には、大域の整数環単元の p 乗根が存在する。 -/
theorem exists_global_unit_pow_of_primary (hp5 : 5 ≤ p) (u : (𝓞 (rootField ζ))ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ) :
    ∃ a : (𝓞 (rootField ζ))ˣ, a ^ p = u :=
  (primaryWeightSquareSpace_eq_bot_iff_global_power hζ).mp
    (primaryWeightSquareSpace_eq_bot hζ hp5) u hu

end
end DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace
```

## 同じ Frey 分裂入口から単元側の入力を除去

新しい入口は

    residual_cyclic_extension_has_stable_complement_of_class_vanishing

である。今回の無条件の単元消滅を内部で構成し、以前の同じ Frey 分裂定理へ渡す。
元の S、L、K、巡回段の全安定性・位数・底の包含条件は保持する。
結論は元の torsionImage の、元の preimageRepresentation における大域安定な補空間である。

公開入力に hrank、htrace、hunit、hdetect、g、v、P、hsurj、hns を残さない。
**実際の hbad と hclass は必要なままであり、この定理はそれらに条件付きである。**
定理名の class_vanishing は、hbad を省略する意味ではない。
次は同じ実際の円分類群商の消滅 hclass と、共鳴素点での hbad を証明する必要がある。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalSplit
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareTrace

#print "file: DkMath.FLT.FreyCyclotomicUnitSplit"

/-!
# 単元算術を内部供給した、類群・共鳴素点条件付きの同じ Frey 分裂

同じ ω² 射影子の実際の trace=1 と、同じ単元の非零検出から単元消滅を内部供給する。
公開入口には hrank/htrace/hunit/hdetect を要求しない。
hbad・hclass・同じ巡回段の全条件は保持する。一般 hno や巡回塔はまだ未完成。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation CyclotomicRootModule CyclotomicKernelField
open CyclotomicCharacterField CyclicKummer CyclotomicKummerWeight
open KummerLocalPower NumberFieldCompletionComparison KummerSelmer KummerSelmerExact
open CyclotomicPrimaryUnitSpace CyclotomicPrimaryCongruence
open DkMath.Lib.RepresentationTheory
open scoped NumberField Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance instIsEllipticUnitSplit : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldUnitSplit : NumberField (rootField ζ) := rootField_numberField ζ

include hline hcofixed hstable hm hcard hbase

/-- 単元側の算術入力を除去した同じ安定補空間。hbad と実際の hclass は保持する。 -/
theorem residual_cyclic_extension_has_stable_complement_of_class_vanishing
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D := by
  exact S.residual_cyclic_extension_has_stable_complement
    L hline hcofixed K hstable hm hcard hbase hζ hp5 hbad hclass
    (CyclotomicOmegaSquareTrace.primaryWeightSquareSpace_eq_bot hζ hp5)

end
end DkMath.FLT.Frey.Source
```

## 回帰例と監査

`DkMathTest.FLT.CyclotomicUnitClosure` は実際の原始5乗根と7乗根を固定する。
5次では、d=2 の自己同型の逆が同じ根に3乗で作用することを確認する。
d=1,−1 の固定素点数は2、d=2 の固定点数は0で、どの素点も固定されない。
同じ unitAction の d=−1 の trace は0、d=2 の trace は1である。
複素素点をすべて固定することと、単元商の作用が恒等写像であることを区別する。
同じ射影子の trace=1、同じ空間の次元1、primary 空間の零化を無条件で確認する。
同じ固有・局所条件の単元 u に大域の p 乗根が存在することも確認する。
7次でも d=−1 の固定点数3、射影子の trace=1、同じ空間の次元1と零化を確認する。

主要12宣言の公理報告と、型・構成子・不透明な証明本体の再帰依存監査を行う。
公開入力監査は、固定点数・trace・rank・unit 消滅の provider が不要になったことと、
Frey 側に hbad・hclass・同じ巡回段の全条件が残ることを確認する。
コード全文一致、モジュール表示、Lib/FLT/root/test の到達性は別に検証する。
検証記録：`evidence/validation-note032-cyclotomic-unit-closure.txt`。

## 数学的境界と出典

**p≥5 の同じ円分単元 ω² 空間について、単元側の hrank/hunit の実装は完成した。**
一般 hno には hclass・hbad と巡回塔の反復・最終接続が残るため、一般 hno は未完成である。
この区別を保ったまま次の算術層へ進む。

固定素点の判定・固定点数と有限体上の重み付き trace の議論は、ローカルの
`anthropics/fermats-last-theorem` の
`P2M/Sol/S_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two.lean`
（blob `6801f82a5eec740ce4d5d658b7a1dc35040f2aba`）を参考に適応した。
該当2 production と本稿のコードに Apache 著作権・License・NOTICE・blob を保持する。
外部の galEquivZMod、ModP、unitsGalAction、omegaIdempotent、最終次元1定理を import せず、
DkMath の同じ指定根・characterEquiv・UnitClass・unitAction・omegaSquareProjector で証明した。
外部 checkout をビルドしたり、公理監査したりしたという主張はしない。
