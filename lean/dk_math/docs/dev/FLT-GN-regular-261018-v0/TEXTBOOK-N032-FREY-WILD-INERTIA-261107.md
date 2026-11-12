# NOTE-032 教科書 — 野生慣性消滅と同じ差分の Frobenius 共役冪公式

日付: 2026-11-07。最新レビューの野生慣性への提案とローカル模範解答を照合し、4ステップを実装した。
この文書の4つの Lean ブロックは、4つの production ファイルの全文である。
各 import 群の直後に正確な `#print "file: モジュール名"` を保持する。
同じ DkMath の Lake 環境で、別々のファイルへコピペして検査できる。

## 今回閉じた局所部分

同じ Frey 曲線 E、q≠p の同じ悪い住所、付値環 A、その実際の慣性群 I_A を保つ。
全非零元 z に対する野生合同を

    σ(z)/z − 1 ∈ A.nonunits

と定義する。この条件と v(σz−z)<v(z) の同値を証明し、
自己同型群の部分群 `wildSubgroup A` を構成する。
`wildInertiaSubgroup A` はそれを同じ慣性部分群へ引き戻したものである。
ここでの野生群はこの明示的な全非零元条件による定義。
別の ramification filtration や pro-q API との同値は今回証明していない。

模範解答の作用差の軌道和の証明を移植・整理すると、

    σ が野生合同を満たす、v(m)=1、σ^m(y)=y  ⇒  σ(y)=y

を得る。q 上の住所と gcd(m,q)=1 から v(m)=1 は既存の Bezout 補題で内部供給する。
q 進付値を数値へ正規化したり、離散性・完備性を仮定したりしない。

一方、前回までの実際の節点慣性積零性から、同じ有限捩れ点 x に対して

    ρ(σ^m)x − x = m • (ρ(σ)x − x)

が成り立つ。N=p^(n+1) で消える点 x は σ^N に固定される。
その **同じ幾何点の座標** は周期 N を持ち、gcd(N,q)=1 なので野生剛性を適用できる。
したがって

    σ ∈ wildInertiaSubgroup A ⇒ ρ_N(σ)x=x  （全ての x∈E[N]）

を得る。有限像の pro-q 理論を provider として追加することなく、
今回の実際の有限 p 冪捩れ表現で野生慣性消滅を証明した。

同じ上位商 Q=E[p^(n+2)]/T、同じ基点 x の差分準同型 c_x:I_A→Multiplicative Q について、

    wildInertiaSubgroup A ≤ ker c_x

となる。これは前回未証明だった局所消滅を実際に供給する結果である。
ただし、慣性群全体の作用消滅や c_x=0 を結論しない。

## 同じ Frobenius の証明を保持する

既存の付値環の Frobenius 存在定理から、実際の φ と `IsFrobeniusAt A φ q` を得る。
以前の穏分岐指標の計算を φ を固定した補題へ切り出し、

    e = φ τ φ⁻¹ (τ^q)⁻¹ ∈ I_A
    e(z)/z−1 ∈ A.nonunits  （全ての非零 z）

を示す。今回は e が同じ差分準同型の核に入ることを上記の局所消滅で証明できる。
通常の群準同型の積・逆元・冪保存から

    1 = c_x(e) = c_x(φτφ⁻¹) c_x(τ)^(-q)
    c_x(φτφ⁻¹) = c_x(τ)^q

が従う。加法記法では右辺は q•c_x(τ)。`Multiplicative` は元の加法群の型タグである。

これは **同じ基点で定義した通常の慣性準同型を共役先で評価する公式** であり、
商加群への φ の作用についての `ρ(φ)c_x(τ)=q•c_x(τ)` を証明したものではない。
以前の基点を動かす共役輸送公式とも区別する。
今回の存在定理は φ の単なる存在だけでなく `IsFrobeniusAt` の証明を結論に保持する。

## hno に向けた正確な終点

従来の正確な rootField ζ の ClassModP の ω² 固有空間消滅 `hclass` と、
同じ Cofixed 候補から得た同じ障害点 y・慣性元 τ に接続した。
`residual_exists_tame_inertia_character` は同じ非自明な位数 p の値とともに、
野生部分群の核への包含と実際の Frobenius による共役冪公式を出力する。
新たな hbad、配置、野生消滅、Frobenius、周期の算術 provider は要求しない。
前回の連続性・有限像・開閉核の定理も、同じ対象へそのまま適用できる。

野生部分群が核に入っても馴分岐側の p 成分は残り得る。
今回、野生群の正規性・標準 tame quotient への降下や、分解群全体の作用の算術解析は実装していない。
同じ差分は依然として商加群の作用差という coboundary の形であり、非零 H¹ 類は主張しない。
この馴分岐障害の排除と `hclass` の算術的供給が残る。
**無条件の一般 hno は引き続き未完成。**

## 模範解答と出典

ローカル模範解答の `S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.lean` を読み、
野生合同・冪・望遠和の証明を DkMath の単元周期 API へ整理した。
元の Bezout 証明を重複させず、既存の `ValuationPrimeSupport` を使う。
有限正規中間体上での q 冪固定を与える二つの関連解答も照合した。
今回の Frey 適用では、既存の節点積零性から p 冪周期を内部供給するので、
有限正規中間体や pro-q 理論の構成を要しない。

Frobenius 誤差の計算は既存の `ValuationTameCharacter` から、同じ φ の証明を保持する形で切り出した。
移植箇所の Apache-2.0 と upstream notices はソース冒頭に保持する。
P2M/P2MW の theorem/provider を import しない。
参照 HEAD・ソース SHA-256 は `evidence/note032-frey-wild-inertia-reference-audit.json` に保存した。

## 1. 全非零元の野生合同と単元周期の剛性

主項 m•w と厳密に小さい誤差和を分け、相殺不可能性から固定性を得る。

ソース: `DkMath/Lib/NumberTheory/ValuationWildRigidity.lean`

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.lean.
Modified: unit-period API, existing DkMath prime-support bridge, no P2M imports.
-/

import DkMath.Lib.NumberTheory.ValuationPrimeSupport
import Mathlib.Algebra.Field.GeomSum

#print "file: DkMath.Lib.NumberTheory.ValuationWildRigidity"

/-!
# 野生合同と単元周期の剛性

野生合同から厳密な付値不等式を得て、作用差の軌道和を telescoping する。
単元周期の主項と、それより小さい誤差和は相殺しない。
-/
namespace DkMath.Lib.NumberTheory.ValuationWildRigidity
open ValuationInertia ValuationPrimeSupport
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- 非零の分母に対する厳密な付値不等式を、比の非単元性へ翻訳する。 -/
theorem valuation_lt_iff_div_mem_nonunits (x y : L) (hy : y ≠ 0) :
    A.valuation x < A.valuation y ↔ x / y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff, map_div₀, div_lt_one₀]
  exact (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hy))

/-- 全非零元の作用差が元より小さい、という野生合同の付値表示。 -/
def IsWildAt (σ : L ≃ₐ[K] L) : Prop := ∀ z : L, z ≠ 0 → A.valuation (σ z - z) < A.valuation z

/-- 模範解答と既存の Frobenius 誤差が持つ比の合同から、同じ付値条件を得る。 -/
theorem isWildAt_of_forall_mem_nonunits {σ : L ≃ₐ[K] L} (h : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) :
    IsWildAt A σ := by
  intro z hz
  rw [valuation_lt_iff_div_mem_nonunits A _ _ hz, sub_div, div_self hz, div_eq_mul_inv]
  exact h z hz

/-- 野生自己同型は付値を保つ。誤差が元より厳密に小さいことを使う。 -/
theorem IsWildAt.valuation_apply {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) (w : L) : A.valuation (σ w) = A.valuation w := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  have h := Valuation.map_add_eq_of_lt_right A.valuation (hw w hw0)
  rwa [sub_add_cancel] at h

/-- 野生合同は合成で保たれる。 -/
theorem IsWildAt.mul {σ τ : L ≃ₐ[K] L} (hσ : IsWildAt A σ) (hτ : IsWildAt A τ) :
    IsWildAt A (σ * τ) := by
  intro z hz
  have he : (σ * τ) z - z = σ (τ z - z) + (σ z - z) := by
    rw [AlgEquiv.mul_apply, map_sub]; ring
  rw [he]
  apply Valuation.map_add_lt _ _ (hσ z hz)
  rw [hσ.valuation_apply A]
  exact hτ z hz

/-- 野生合同は逆元で保たれる。 -/
theorem IsWildAt.inv {σ : L ≃ₐ[K] L} (hσ : IsWildAt A σ) : IsWildAt A σ⁻¹ := by
  intro z hz
  have hz' : σ⁻¹ z ≠ 0 := (map_ne_zero σ⁻¹).mpr hz
  have h := hσ (σ⁻¹ z) hz'
  have hv := hσ.valuation_apply A (σ⁻¹ z)
  have hcan : σ (σ⁻¹ z) = z := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  rw [hcan] at h hv
  have he : σ⁻¹ z - z = -(z - σ⁻¹ z) := by ring
  rw [he, Valuation.map_neg]
  exact h.trans_eq hv.symm

/-- 剛性の付値条件と、全非零元の作用比による野生合同は同値。 -/
theorem isWildAt_iff {σ : L ≃ₐ[K] L} : IsWildAt A σ ↔
    ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits := by
  constructor
  · intro h z hz
    have h' := (valuation_lt_iff_div_mem_nonunits A _ _ hz).mp (h z hz)
    have he : (σ z - z) / z = σ z * z⁻¹ - 1 := by field_simp
    rw [← he]
    exact h'
  · exact isWildAt_of_forall_mem_nonunits A

/-- 全非零元の野生合同で定義する実際の自己同型部分群。 -/
def wildSubgroup : Subgroup (L ≃ₐ[K] L) where
  carrier := IsWildAt A
  one_mem' := by intro z hz; simpa using (zero_lt_iff.mpr ((map_ne_zero A.valuation).mpr hz))
  mul_mem' hσ hτ := IsWildAt.mul A hσ hτ
  inv_mem' hσ := IsWildAt.inv A hσ

/-- 任意の自然数冪も、同じ全非零元の野生条件を満たす。 -/
theorem IsWildAt.pow {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) (n : ℕ) : IsWildAt A (σ ^ n) := by
  induction n with
  | zero => intro z hz; simp [(map_ne_zero A.valuation).mpr hz, zero_lt_iff]
  | succ n ih =>
    intro z hz
    have hsplit : (σ ^ (n + 1)) z - z = σ ((σ ^ n) z - z) + (σ z - z) := by
      rw [pow_succ', AlgEquiv.mul_apply, map_sub]; ring
    rw [hsplit]
    refine Valuation.map_add_lt _ ?_ (hw z hz)
    rw [IsWildAt.valuation_apply A hw]
    exact ih z hz

/-- 周期 m が付値環の単元なら、その周期を持つ同じ元は既に固定される。 -/
theorem IsWildAt.fixed_of_unit_period {σ : L ≃ₐ[K] L} (hw : IsWildAt A σ) {m : ℕ} (hm : A.valuation (m : L) = 1) (y : L) (hy : (σ ^ m) y = y) : σ y = y := by
  by_contra hne
  set w := σ y - y with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  -- 周期の望遠和は零。
  have htel : (Finset.range m).sum (fun i => (σ ^ i) w) = 0 := by
    have h := Finset.sum_range_sub (fun i => (σ ^ i) y) m
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [hy, sub_self] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hwdef, map_sub, ← AlgEquiv.mul_apply, ← pow_succ]
  -- 各項を主項 w と小さい誤差に分ける。
  have hdec : (Finset.range m).sum (fun i => (σ ^ i) w)
      = (m : L) * w + (Finset.range m).sum (fun i => (σ ^ i) w - w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hS : A.valuation ((Finset.range m).sum (fun i => (σ ^ i) w - w)) < A.valuation ((m : L) * w) := by
    rw [map_mul, hm, one_mul]
    exact Valuation.map_sum_lt _ ((map_ne_zero _).mpr hw0) (fun i _ => (IsWildAt.pow A hw i) w hw0)
  have hval : A.valuation ((Finset.range m).sum (fun i => (σ ^ i) w)) = A.valuation ((m : L) * w) := by
    rw [hdec, add_comm]
    exact Valuation.map_add_eq_of_lt_right _ hS
  rw [htel, map_zero, map_mul, hm, one_mul, eq_comm, map_eq_zero] at hval
  exact hw0 hval

/-- q 上の野生合同を満たす自己同型は、q と互いに素な周期を持つ同じ元を固定する。 -/
theorem fixed_of_coprime_period {q m : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q)
    {σ : L ≃ₐ[K] L}
    (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits)
    (hm : m.Coprime q) {y : L} (hy : (σ ^ m) y = y) : σ y = y := by
  have hnot : ¬ (q : ℤ) ∣ (m : ℤ) := by
    exact_mod_cast ((Nat.Prime.coprime_iff_not_dvd hq).mp hm.symm)
  have hu : A.valuation (m : L) = 1 := by
    simpa only [Int.cast_natCast] using valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff A).mp hA) hnot
  exact IsWildAt.fixed_of_unit_period A (isWildAt_of_forall_mem_nonunits A hwild) hu y hy

end DkMath.Lib.NumberTheory.ValuationWildRigidity
```

## 2. 同じ積零作用の冪公式

既存の通常の差分準同型の冪保存を使い、同じ点の周期を明示的に供給する。

ソース: `DkMath/Lib/RepresentationTheory/UnipotentDifferencePower.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter

#print "file: DkMath.Lib.RepresentationTheory.UnipotentDifferencePower"

/-!
# 積零の作用差分の冪公式と同じ点の周期

通常の差分準同型の冪保存から線形な冪公式を得る。
有限捩れへの適用で周期を内部供給し、野生剛性へ渡す。
-/
namespace DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
variable {R Γ V : Type*} [Ring R] [Group Γ] [AddCommGroup V] [Module R V]
    (ρ : Representation R Γ V) (hprod : ∀ σ τ, (ρ σ - 1) * (ρ τ - 1) = 0)

include hprod

/-- 同じ基点の m 乗の作用差は、元の作用差の m 倍。 -/
theorem difference_pow (σ : Γ) (x : V) (m : ℕ) :
    ρ (σ ^ m) x - x = m • (ρ σ x - x) :=
  congrArg Multiplicative.toAdd (map_pow (character ρ hprod x) σ m)

/-- m で消える同じ点は、同じ作用元の m 乗に固定される。 -/
theorem fixed_by_pow_of_killed (σ : Γ) (x : V) {m : ℕ} (hx : m • x = 0) :
    ρ (σ ^ m) x = x := by
  apply sub_eq_zero.mp
  rw [difference_pow ρ hprod σ x m, nsmul_sub, ← map_nsmul, hx, map_zero, sub_self]

end DkMath.Lib.RepresentationTheory.UnipotentDifferenceCharacter
```

## 3. 同じ楕円曲線の点から座標へ

周期点の同じ x,y 座標に野生剛性を適用し、同じ実際の捩れ表現へ戻す。

ソース: `DkMath/Lib/NumberTheory/EllipticWildRigidity.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationWildRigidity
import DkMath.Lib.NumberTheory.EllipticTorsionRepresentation

#print "file: DkMath.Lib.NumberTheory.EllipticWildRigidity"

/-!
# 同じ幾何点の周期を座標の野生剛性へ渡す

曲線の点の固定性を同じ座標に戻す。有限性や pro-q 性の provider は要求しない。
周期が q と互いに素であることは利用側で証明する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open ValuationInertia ValuationWildRigidity
open scoped WeierstrassCurve.Affine
variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- 同じ野生自己同型の q と互いに素な周期を持つ幾何点は、その自己同型に固定される。 -/
theorem pointAction_fixed_of_wild_coprime_period
    (A : ValuationSubring (AlgebraicClosure K)) {q m : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup K)
    (hwild : ∀ z : AlgebraicClosure K, z ≠ 0 → σ.toAlgHom z * z⁻¹ - 1 ∈ A.nonunits)
    (hm : m.Coprime q) (P : Points E) (hP : pointAction E (σ ^ m) P = P) :
    pointAction E σ P = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    change WeierstrassCurve.Affine.Point.some ((σ ^ m).toAlgHom x) ((σ ^ m).toAlgHom y) _ =
      WeierstrassCurve.Affine.Point.some x y h at hP
    have hxy : (σ ^ m).toAlgHom x = x ∧ (σ ^ m).toAlgHom y = y := by
      simpa only [WeierstrassCurve.Affine.Point.some.injEq] using hP
    obtain ⟨hx, hy⟩ := hxy
    change WeierstrassCurve.Affine.Point.some (σ.toAlgHom x) (σ.toAlgHom y) _ =
      WeierstrassCurve.Affine.Point.some x y h
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨fixed_of_coprime_period A hq hA hwild hm hx,
      fixed_of_coprime_period A hq hA hwild hm hy⟩

/-- 上の座標の固定性を、同じ実際の捩れ表現へ戻す。 -/
theorem representation_fixed_of_wild_coprime_period
    (A : ValuationSubring (AlgebraicClosure K)) {q m N : ℕ} (hq : q.Prime) (hA : LiesOverPrime A q)
    (σ : Field.absoluteGaloisGroup K)
    (hwild : ∀ z : AlgebraicClosure K, z ≠ 0 → σ.toAlgHom z * z⁻¹ - 1 ∈ A.nonunits)
    (hm : m.Coprime q) (x : Torsion E N) (hx : representation E N (σ ^ m) x = x) :
    representation E N σ x = x := by
  apply Subtype.ext
  exact pointAction_fixed_of_wild_coprime_period E A hq hA σ hwild hm x.val
    (congrArg Subtype.val hx)

end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
```

## 4. Frey 野生慣性消滅と Frobenius 共役冪公式

局所積零性と q≠p を内部使用する。実際の Frobenius の証明と元の障害点を保持する。

ソース: `DkMath/FLT/FreyWildInertia.lean`

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Frobenius error calculation adapted through DkMath ValuationTameCharacter from
S_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.lean.
Modified: retain IsFrobeniusAt, actual Frey wild-kernel elimination, SAME character.
-/

import DkMath.FLT.FreyInertiaCharacterFiniteImage
import DkMath.Lib.NumberTheory.EllipticWildRigidity
import DkMath.Lib.NumberTheory.ValuationTameCharacter
import DkMath.Lib.RepresentationTheory.UnipotentDifferencePower

#print "file: DkMath.FLT.FreyWildInertia"

/-!
# Frey の実際の野生慣性消滅と差分値の Frobenius 共役公式

q≠p の同じ悪い住所で、野生合同と既存の節点積零性を結ぶ。
野生元の作用は有限 p 冪捩れ全体で自明。Frobenius 共役の野生誤差を実際に消す。
共役先は通常の慣性差分準同型で評価する。Galois 加群値の輸送や基点不変性とは区別する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia ValuationWildRigidity
open ValuationTameCharacter.TameCharacter
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じ全自己同型群の野生合同部分群を、元の慣性部分群へ引き戻す。 -/
def wildInertiaSubgroup (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Subgroup (inertiaSubgroupIn A ℚ) :=
  (wildSubgroup (K := ℚ) A).comap (inertiaSubgroupIn A ℚ).subtype

section Local
variable (n : ℕ) (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 同じ野生慣性元は、実際の有限 p 冪捩れ群の全点を固定する。 -/
theorem prime_power_wild_inertia_fixed (σ : inertiaSubgroupIn A ℚ)
    (hwild : σ ∈ wildInertiaSubgroup A)
    (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    representation S.rationalCurve (p ^ (n + 1)) σ.val x = x := by
  let ρ := (representation S.rationalCurve (p ^ (n + 1))).comp (inertiaSubgroupIn A ℚ).subtype
  have hx : p ^ (n + 1) • x = 0 := by
    apply Subtype.ext
    exact x.property
  have hperiod := UnipotentDifferenceCharacter.fixed_by_pow_of_killed ρ
    (S.prime_power_inertia_difference_product_zero n hp5 hq hqp haddr A hA) σ x hx
  exact representation_fixed_of_wild_coprime_period S.rationalCurve A hq hA σ.val
    ((isWildAt_iff A).mp hwild)
    (((Nat.coprime_primes (Fact.out : p.Prime) hq).mpr hqp.symm).pow_left (n + 1)) x hperiod

end Local

/-- 同じ実際の Frobenius の共役冪誤差は、慣性に属し野生合同を満たす。 -/
theorem frobenius_conjugate_error_wild {q : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {φ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hφ : ValuationFrobenius.IsFrobeniusAt A φ q) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ inertiaSubgroupIn A ℚ ∧
      ∀ z : AlgebraicClosure ℚ, z ≠ 0 →
        (φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹ - 1 ∈ A.nonunits := by
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) := inferInstance
    exact h
  have hφD : φ ∈ A.decompositionSubgroup ℚ := hφ.mem_decompositionSubgroup
  have hτD : τ ∈ A.decompositionSubgroup ℚ := (mem_inertiaSubgroupIn_iff.mp hτ).1
  have hconj : φ * τ * φ⁻¹ ∈ inertiaSubgroupIn A ℚ := conj_mem_inertiaSubgroupIn hτ hφD
  have hpow : τ ^ q ∈ inertiaSubgroupIn A ℚ := Subgroup.pow_mem _ hτ q
  have hω : φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ inertiaSubgroupIn A ℚ :=
    Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hpow)
  refine ⟨hω, fun z hz => ?_⟩
  have hτqD : τ ^ q ∈ A.decompositionSubgroup ℚ := Subgroup.pow_mem _ hτD q
  have hτqiD : (τ ^ q)⁻¹ ∈ A.decompositionSubgroup ℚ := (A.decompositionSubgroup ℚ).inv_mem hτqD
  have hωD : φ * τ * φ⁻¹ * (τ ^ q)⁻¹ ∈ A.decompositionSubgroup ℚ :=
    (mem_inertiaSubgroupIn_iff.mp hω).1
  have h1 := theta_mul hconj hτqiD hz
  have h2 := theta_mul_theta_inv hpow hz
  rw [theta_pow hτ hz q] at h2
  have h3 := theta_frob_conj hφ hτ hz
  have hθω : rq A ((φ * τ * φ⁻¹ * (τ ^ q)⁻¹) z * z⁻¹) = 1 := by
    rw [h1, h3, h2]
  rw [← rq_one (A := A), rq_eq_rq_iff (apply_mul_inv_mem hωD hz).1 A.one_mem] at hθω
  exact hθω

section Stage
variable {S} {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ実際の差分準同型の核は、同じ野生慣性部分群を含む。 -/
theorem ResidualCyclicStage.wildInertia_le_character_kernel
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    wildInertiaSubgroup A ≤ (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x).ker := by
  intro σ hσ
  change Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) = 0
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 hq hqp haddr A hA x σ,
    S.prime_power_wild_inertia_fixed (n + 1) hp5 hq hqp haddr A hA σ hσ x, sub_self, map_zero]

/-- 構成した同じ Frobenius 共役を、同じ固定基点の通常の慣性準同型で評価する。
野生誤差が核に入るため q 倍公式を得る。商作用による輸送公式は主張しない。 -/
theorem ResidualCyclicStage.exists_frobenius_character_power
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ValuationFrobenius.IsFrobeniusAt A φ q ∧ ∀ τ : inertiaSubgroupIn A ℚ,
      ∃ hconj : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
        T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x
          ⟨φ * τ.val * φ⁻¹, hconj⟩ =
        (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x τ) ^ q := by
  obtain ⟨φ, hφ⟩ := ValuationFrobenius.exists_isFrobeniusAt_of_liesOverPrime hq A hA
  refine ⟨φ, hφ, fun τ => ?_⟩
  obtain ⟨he, hw⟩ := frobenius_conjugate_error_wild A hφ τ.property
  have hc : φ * τ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ := by
    have hh := (inertiaSubgroupIn A ℚ).mul_mem he ((inertiaSubgroupIn A ℚ).pow_mem τ.property q)
    simpa only [inv_mul_cancel_right] using hh
  refine ⟨hc, ?_⟩
  let c := T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x
  let e : inertiaSubgroupIn A ℚ := ⟨φ * τ.val * φ⁻¹ * (τ.val ^ q)⁻¹, he⟩
  have hew : e ∈ wildInertiaSubgroup A := (isWildAt_iff A).mpr hw
  have hk : c e = 1 := T.wildInertia_le_character_kernel hp5 hq hqp haddr A hA x hew
  have heq : e = (⟨φ * τ.val * φ⁻¹, hc⟩ : inertiaSubgroupIn A ℚ) * (τ ^ q)⁻¹ := rfl
  rw [heq, map_mul, map_inv, map_pow] at hk
  exact eq_of_mul_inv_eq_one hk

end Stage
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
/-- 同じ hclass と Cofixed 候補から、野生慣性を消す非自明な同じ差分準同型と共役冪公式を得る。 -/
theorem residual_exists_tame_inertia_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p ∧
      wildInertiaSubgroup A ≤ c.ker ∧
      ∃ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ValuationFrobenius.IsFrobeniusAt A φ q ∧ ∀ γ : inertiaSubgroupIn A ℚ,
        ∃ hconj : φ * γ.val * φ⁻¹ ∈ inertiaSubgroupIn A ℚ,
          c ⟨φ * γ.val * φ⁻¹, hconj⟩ = (c γ) ^ q := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  refine ⟨n, T, q, A, τ, y, h, (h.inertia_character_nontrivial hp5).1,
    (h.inertia_character_nontrivial hp5).2, ?_, ?_⟩
  · exact T.wildInertia_le_character_kernel hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  · exact T.exists_frobenius_character_power hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩

end
end DkMath.FLT.Frey.Source
```

## 検証

21宣言の checked type・constructor・opaque proof value の再帰依存監査と、
13件の公開入力監査を通常のテスト入口へ追加した。
有限例では (ZMod25)^2 の剪断表現の実際の周期25・周期5・零乗公式を確認し、
積零性だけでは作用自体は消えない例も検査する。
検証記録は `evidence/validation-note032-frey-wild-inertia.txt` を参照。
