# NOTE-032 教科書 — 実際の馴分岐商と同じ障害値の共鳴二分岐

日付: 2026-11-08。最新レビューの共鳴二分岐の提案とローカル模範解答を参考に、4ステップを実装した。
4つの Lean ブロックは、4つの production ソースの全文である。
import 群直後の正確な `#print "file: モジュール名"` を保持する。
既存 DkMath の Lake 環境で各ブロックを別ファイルへコピペし、個別に検査できる。

## 同じ野生部分群から実際の商へ

前回と同じ付値環 A、慣性群 I_A を使う。
W_A は全非零元に対する野生合同 σ(z)/z−1∈A.nonunits で定義した同じ部分群である。
分解群の元 g は A の非単元性を保存するので、

    σ が野生合同を満たす ⇒ gσg⁻¹ も同じ野生合同を満たす

が成り立つ。実際、z の代わりに g⁻¹z を使い、比の合同を g で写せばよい。
この証明は代数性・離散性・完備性・pro-q 性を要求しない。
慣性元は同じ分解群に属するので W_A は I_A 内で正規となり、実際の群商

    J_A = I_A / W_A

を構成できる。今回の `tameInertiaQuotient A` はこの明示的な商である。
別の ramification filtration や標準 pro-q 群の API との同値は主張しない。

前回の同じ差分準同型 c_x:I_A→Multiplicative Q は W_A を核に含む。
ここで Q=E[p^(n+2)]/T は元の同じ巡回段による有限捩れ商である。
したがって標準の群商の普遍性から

    c̄_x : J_A → Multiplicative Q
    c̄_x([σ]) = c_x(σ)

を定義できる。元の慣性群の Krull 部分群位相と標準商位相を使い、降下した準同型も連続と証明した。
また、像は集合として元の c_x の像と等しい。
前回の有限 p 冪像を保つが、J_A 全体が有限であるとは主張しない。
今回、W_A の閉性、商の Hausdorff 性や巡回性は証明していない。

## Frobenius 関係を商元自体へ

同じ実際の φ と証明 `IsFrobeniusAt A φ q` を使う。
前回の共役冪誤差 ε=φτφ⁻¹(τ^q)⁻¹ は、同じ I_A に属し野生合同を満たすので、

    [φτφ⁻¹] = [τ]^q   in J_A

が成り立つ。今回は特定の指標値での一致に加え、この **元の群商の元そのものの等式** を証明した。
この等式に c̄_x を適用して、その同じ値についての q 冪公式を得る。
商加群の線形作用 ρ(φ)c_x(τ)=q•c_x(τ) とは異なる。
今回、共役を商の自己同型としてまとめる API は追加していない。

## 厳密位数 p と共鳴条件を結ぶ

群の同じ元 z の位数が正確に p なら、

    z^q = z  ↔  q = 1 in ZMod p

が成り立つ。有限位数の冪の一致と、指数の mod p の一致を使う。
また q=-1 in ZMod p なら z^q=z⁻¹。
p>2 のとき z⁻¹=z は z²=1 と p∣2 を意味するので不可能である。
従って負の共鳴では z^q≠z。
この一般群論は `PrimeOrderResonance` に分離し、Frey 固有の仮定に依存させない。

同じ障害証明書の点 y と元 τ を使い、t=[τ]∈J_A、z=c̄_y(t) とする。
前回の非自明・厳密位数 p の値は、降下後も同じ値である。
同じ実際の Frobenius の共役先を t'=[φτφ⁻¹] とすると、

| 元の証明書の共鳴分岐 | 同じ馴分岐指標の値 |
| --- | --- |
| q=1 in ZMod p | c̄_y(t')=z |
| q=-1 in ZMod p | c̄_y(t')=z⁻¹、かつ c̄_y(t')≠z |

を証明した。`h.resonance` を実際に使って、この二分岐を結論に出力する。
さらに `c̄_y(t')=z ↔ (q:ZMod p)=1` も公開したので、もし共役不変性を別途得られれば
正の剰余条件が必要になる。しかし、その不変性を今回の Frey の算術から供給したわけではない。
負の分岐で値が変化すること自体は矛盾ではなく、正の分岐にも矛盾は生じない。
t 自身の厳密位数が p とも主張しない。厳密位数 p なのは、その同じ指標値 z である。

## hno に向けた正確な終点

`residual_exists_resonant_tame_character` は従来の正確な rootField ζ の ClassModP の
ω² 固有空間消滅 `hclass` と、同じ Cofixed 候補から元の n,T,q,A,τ,y と障害証明書を得る。
その **同じ対象** について、連続な馴分岐商値準同型、非自明・厳密位数 p の値、
実際の Frobenius の証明、商元の q 冪関係、正負の共鳴分岐を一緒に出力する。
新しい正規性・連続性・商群・指標・Frobenius・共役不変性を算術 provider として追加しない。
局所の正規性・商降下・群論は hclass/Cofixed から独立し、最終の存在定理のみが従来の入力を保持する。

今回の結果は馴分岐側の障害を正確に記述するもの。
元の差分は依然として元の商加群における作用差という coboundary の形であり、非零 H¹ 類は主張しない。
商の線形 Frobenius 作用との比較、両共鳴分岐の算術的排除、hclass の算術的供給は残る。
**無条件の一般 hno は引き続き未完成。**

## 模範解答との照合

ローカル模範解答の `S_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.lean` の
共役による慣性保存・Frobenius の野生誤差の計算を照合した。
`S_ValuationSubring_IsFrobeniusAt_conj_mul_pow_inv_mem_inertiaSubgroupIn_and_wild.lean` の公開解答と、
`S_Subgroup_exists_wild_tame_cyclic_unramified_chain_of_le.lean` の定理入力・最初の商共役計算も確認した。
後者には有限指数や生成条件などが明示的に残る。それらを今回の実際の慣性商の巡回性・有限性へ勝手に移さない。
DkMath では既存の同じ野生誤差と核包含を使用して実際の商を構成する。
外部 theorem/provider や P2M/P2MW を import しない。
参照 HEAD と SHA-256 は `evidence/note032-frey-tame-resonance-reference-audit.json` に保存した。

## 1. 分解群による野生合同の保存と慣性内の正規性

作用比を同じ分解群元で写し、非単元性の保存から共役安定性を得る。

ソース: `DkMath/Lib/NumberTheory/ValuationWildNormality.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationWildRigidity
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.ValuationWildNormality"

/-!
# 同じ付値環の分解群による野生合同の保存

全非零元の合同を、分解群が非単元を保存することから共役で輸送する。
別の ramification filtration との同値や pro-q 性は仮定しない。
-/
namespace DkMath.Lib.NumberTheory.ValuationWildRigidity
open ValuationTameCharacter.TameCharacter
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- 同じ付値環の分解群による共役は、全非零元の野生合同を保存する。 -/
theorem IsWildAt.conjugate {σ g : L ≃ₐ[K] L} (hσ : IsWildAt A σ)
    (hg : g ∈ A.decompositionSubgroup K) : IsWildAt A (g * σ * g⁻¹) := by
  apply (isWildAt_iff A).mpr
  intro z hz
  have hz' : g⁻¹ z ≠ 0 := (map_ne_zero g⁻¹).mpr hz
  have h := (isWildAt_iff A).mp hσ (g⁻¹ z) hz'
  have hgg : g (g⁻¹ z) = z := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have he : (g * σ * g⁻¹) z * z⁻¹ - 1 = g (σ (g⁻¹ z) * (g⁻¹ z)⁻¹ - 1) := by
    rw [map_sub, map_mul, map_inv₀, map_one, hgg, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
  rw [he, apply_mem_nonunits_iff hg]
  exact h

/-- 野生合同部分群は、元の慣性群へ引き戻すと正規部分群になる。 -/
instance inertiaWild_normal :
    ((wildSubgroup (K := K) A).comap (ValuationInertia.inertiaSubgroupIn A K).subtype).Normal where
  conj_mem σ hσ g := by
    change IsWildAt A (g.val * σ.val * g.val⁻¹)
    exact IsWildAt.conjugate A hσ (mem_inertiaSubgroupIn_iff.mp g.property).1

end DkMath.Lib.NumberTheory.ValuationWildRigidity
```

## 2. 実際の馴分岐商と連続な差分準同型

群商の lift を使って同じ指標を降ろし、値・像・連続性を保持する。Frobenius の関係も商元自体へ降ろす。

ソース: `DkMath/FLT/FreyTameInertiaQuotient.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyWildInertia
import DkMath.Lib.NumberTheory.ValuationWildNormality

#print "file: DkMath.FLT.FreyTameInertiaQuotient"

/-!
# 同じ野生合同部分群による実際の馴分岐商と連続差分準同型

元の慣性群を正規な野生合同部分群で割る。商の有限性は主張しない。
元の有限像と厳密位数を持つ値を保ち、Frobenius 共役冪関係を商元自体で証明する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation ValuationInertia ValuationWildRigidity
noncomputable section

/-- 同じ全非零元の野生合同部分群は、元の慣性群の中で正規。 -/
instance wildInertiaSubgroup_normal (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (wildInertiaSubgroup A).Normal := inertiaWild_normal A

/-- 今回の明示的な野生合同部分群による、元の慣性群の実際の商。 -/
abbrev tameInertiaQuotient (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  (inertiaSubgroupIn A ℚ) ⧸ wildInertiaSubgroup A

variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 元の同じ差分準同型を、実際の馴分岐商へ降ろす。 -/
def ResidualCyclicStage.tameDifferenceCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    tameInertiaQuotient A →* Multiplicative T.upperQuotient :=
  QuotientGroup.lift (wildInertiaSubgroup A)
    (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x)
    (T.wildInertia_le_character_kernel hp5 hq hqp haddr A hA x)

/-- 同じ慣性元の像での値は、元の同じ商値と等しい。 -/
theorem ResidualCyclicStage.tameDifferenceCharacter_mk
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    T.tameDifferenceCharacter hp5 hq hqp haddr A hA x (QuotientGroup.mk σ) =
      T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ := rfl

/-- 元の Krull 部分群位相・標準商位相で、降下した同じ準同型は連続。 -/
theorem ResidualCyclicStage.tameDifferenceCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.tameDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  apply continuous_quot_lift
  exact T.inertiaQuotientDifferenceCharacter_continuous hp5 hq hqp haddr A hA x

/-- 降下は同じ準同型の像を保つ。商群全体が有限であるとは結論しない。 -/
theorem ResidualCyclicStage.tameDifferenceCharacter_range
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (T.tameDifferenceCharacter hp5 hq hqp haddr A hA x).range =
      (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x).range := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨σ, hw⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨QuotientGroup.mk σ, hσ⟩

end

/-- 実際の Frobenius 共役は、同じ馴分岐商の元自体で q 乗となる。 -/
theorem tameInertia_frobenius_power {q : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ q) (τ : inertiaSubgroupIn A ℚ) :
    ∃ hconj : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
      (QuotientGroup.mk ⟨φ * τ.val * φ⁻¹, hconj⟩ : tameInertiaQuotient A) =
        (QuotientGroup.mk τ) ^ q := by
  obtain ⟨he, hw⟩ := frobenius_conjugate_error_wild A hφ τ.property
  have hc : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ := by
    have hh := (inertiaSubgroupIn A ℚ).mul_mem he ((inertiaSubgroupIn A ℚ).pow_mem τ.property q)
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨hc, ?_⟩
  let e : inertiaSubgroupIn A ℚ := ⟨φ * τ.val * φ⁻¹ * (τ.val ^ q)⁻¹, he⟩
  have hew : e ∈ wildInertiaSubgroup A := (isWildAt_iff A).mpr hw
  have hk : (QuotientGroup.mk e : tameInertiaQuotient A) = 1 := (QuotientGroup.eq_one_iff e).mpr hew
  have heq : e = (⟨φ * τ.val * φ⁻¹, hc⟩ : inertiaSubgroupIn A ℚ) * (τ ^ q)⁻¹ := rfl
  change (QuotientGroup.mk' (wildInertiaSubgroup A)) e = 1 at hk
  rw [heq, map_mul, map_inv, map_pow] at hk
  exact eq_of_mul_inv_eq_one hk

end DkMath.FLT.Frey.Source
```

## 3. 厳密位数と正負の共鳴

冪が元を固定するための正確な剰余条件、負の剰余での逆元化と非固定性を証明する。

ソース: `DkMath/Lib/Algebra/PrimeOrderResonance.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic

#print "file: DkMath.Lib.Algebra.PrimeOrderResonance"

/-!
# 厳密位数と共鳴する冪の固定・反転

元の同じ群の元の厳密位数を使う。共役不変性を仮定せずに結論しない。
-/
namespace DkMath.Lib.Algebra.PrimeOrderResonance
variable {G : Type*} [Group G] {p q : ℕ} {z : G}

/-- 位数が正確に p の元は、q 乗で固定されることと q=1 mod p が同値。 -/
theorem pow_eq_self_iff (hz : orderOf z = p) : z ^ q = z ↔ (q : ZMod p) = 1 := by
  conv_lhs => rhs; rw [← pow_one z]
  rw [pow_inj_mod, hz]
  simpa only [Nat.ModEq, Nat.cast_one] using (ZMod.natCast_eq_natCast_iff q 1 p).symm

/-- q=-1 mod p なら、同じ位数 p の元の q 乗は逆元。 -/
theorem pow_eq_inv (hz : orderOf z = p) (hq : (q : ZMod p) = -1) : z ^ q = z⁻¹ := by
  have hm : ((q + 1 : ℕ) : ZMod p) = 0 := by simp only [Nat.cast_add, Nat.cast_one, hq, neg_add_cancel]
  have hd : p ∣ q + 1 := (ZMod.natCast_eq_zero_iff (q + 1) p).mp hm
  have he : z ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (hz ▸ hd)
  exact eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_succ] using he)

/-- p>2 の厳密位数 p の元は、その逆元と異なる。 -/
theorem inv_ne_self (hp : 2 < p) (hz : orderOf z = p) : z⁻¹ ≠ z := by
  intro he
  have h2 : z ^ 2 = 1 := by
    rw [pow_two]
    calc z * z = z⁻¹ * z := congrArg (fun w => w * z) he.symm
         _ = 1 := inv_mul_cancel z
  have hd : p ∣ 2 := hz ▸ orderOf_dvd_of_pow_eq_one h2
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 負の共鳴分岐では、q 乗によって同じ値が実際に変化する。 -/
theorem pow_ne_self_of_negative (hp : 2 < p) (hz : orderOf z = p)
    (hq : (q : ZMod p) = -1) : z ^ q ≠ z := by
  rw [pow_eq_inv hz hq]
  exact inv_ne_self hp hz

end DkMath.Lib.Algebra.PrimeOrderResonance
```

## 4. 同じ障害証明書の馴分岐指標と共鳴二分岐

同じ点・同じ指標値・同じ Frobenius を保ち、元の h.resonance を使って実際の分岐を出力する。

ソース: `DkMath/FLT/FreyTameResonance.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTameInertiaQuotient
import DkMath.Lib.Algebra.PrimeOrderResonance

#print "file: DkMath.FLT.FreyTameResonance"

/-!
# 同じ馴分岐商の非自明な値と共鳴二分岐

位数が正確に p の同じ値について、Frobenius 共役先の値が元と等しいことは
q=1 mod p と同値。q=-1 mod p では逆元へ動くが、それ自体を矛盾とはしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.Algebra.PrimeOrderResonance
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {y : Points S.rationalCurve}

/-- 同じ障害点の値は、実際の馴分岐商へ降ろしても非自明・厳密位数 p。 -/
theorem NarrowAbsorptionObstruction.tame_character_nontrivial
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
    c t ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c t)) = p :=
  h.inertia_character_nontrivial hp5

/-- 同じ実際の Frobenius と同じ商元で、固定・反転・非不変性を正確に分類する。 -/
theorem NarrowAbsorptionObstruction.tame_resonant_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
    Continuous c ∧ c t ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c t)) = p ∧
    ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ValuationFrobenius.IsFrobeniusAt A φ q ∧
      ∃ hconj : φ * τ * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
      let t' : tameInertiaQuotient A := QuotientGroup.mk ⟨φ * τ * φ⁻¹, hconj⟩
      t' = t ^ q ∧ (c t' = c t ↔ (q : ZMod p) = 1) ∧
        ((q : ZMod p) = -1 → c t' = (c t)⁻¹ ∧ c t' ≠ c t) ∧
        (((q : ZMod p) = 1 ∧ c t' = c t) ∨
          ((q : ZMod p) = -1 ∧ c t' = (c t)⁻¹ ∧ c t' ≠ c t)) := by
  let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
  let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
  let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
  obtain ⟨hn, ho⟩ := h.tame_character_nontrivial hp5
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime h.prime A h.lies_over
  obtain ⟨hc, ht⟩ := tameInertia_frobenius_power A hφ ⟨τ, h.inertia⟩
  let t' : tameInertiaQuotient A := QuotientGroup.mk ⟨φ * τ * φ⁻¹, hc⟩
  have hct : c t' = (c t) ^ q := by
    change c (QuotientGroup.mk ⟨φ * τ * φ⁻¹, hc⟩) = _
    rw [ht, map_pow]
  have hfix : c t' = c t ↔ (q : ZMod p) = 1 := by
    rw [hct]
    exact pow_eq_self_iff ho
  have hinv : (q : ZMod p) = -1 → c t' = (c t)⁻¹ ∧ c t' ≠ c t := by
    intro hneg
    rw [hct]
    exact ⟨pow_eq_inv ho hneg, pow_ne_self_of_negative (by omega) ho hneg⟩
  refine ⟨T.tameDifferenceCharacter_continuous hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over x, hn, ho, φ, hφ, hc, ht, hfix, hinv, ?_⟩
  rcases h.resonance with hpos | hneg
  · exact Or.inl ⟨hpos, hfix.mpr hpos⟩
  · exact Or.inr ⟨hneg, hinv hneg⟩

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 同じ hclass と Cofixed 候補から、同じ馴分岐商上の連続指標と共鳴分岐の証明書を得る。 -/
theorem residual_exists_resonant_tame_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.tameDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      let t : tameInertiaQuotient A := QuotientGroup.mk ⟨τ, h.inertia⟩
      Continuous c ∧ c t ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c t)) = p ∧
      ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ValuationFrobenius.IsFrobeniusAt A φ q ∧
        ∃ hconj : φ * τ * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
        let t' : tameInertiaQuotient A := QuotientGroup.mk ⟨φ * τ * φ⁻¹, hconj⟩
        t' = t ^ q ∧ (c t' = c t ↔ (q : ZMod p) = 1) ∧
          ((q : ZMod p) = -1 → c t' = (c t)⁻¹ ∧ c t' ≠ c t) ∧
        (((q : ZMod p) = 1 ∧ c t' = c t) ∨
          ((q : ZMod p) = -1 ∧ c t' = (c t)⁻¹ ∧ c t' ≠ c t)) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.tame_resonant_profile hp5⟩

end
end DkMath.FLT.Frey.Source
```

## 検証

新規16宣言の checked type・constructor・opaque proof value を再帰走査する依存監査と、
15件の公開入力監査を通常テスト入口へ追加した。
ZMod5 の位数5の値の指数11での固定・19での反転、指数2での非固定を検査する。
ZMod2 では逆元が元に等しい例で p>2 の必要性を確認する。
ZMod25→ZMod5 の同じ核による商への lift で、元1と元6から同じ非自明な位数5の値が得られることも検査する。
結果は `evidence/validation-note032-frey-tame-resonance.txt` を参照。
