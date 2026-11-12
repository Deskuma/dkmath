# NOTE-032 教科書：ω² 射影子と大域円分単元の非零検出

日付：2026-11-04。前段：`TEXTBOOK-N032-CYCLOTOMIC-PRIMARY-LOG-261104.md`。
今回の2ステップは、①同じ単元商上の ω² 射影子、②同じ大域円分単元の射影に対する非零評価である。
最後に、既存の Frey の分裂経路へ接続する。

3つの Lean コードブロックは production ファイルの著作権表示を含む全文である。
順番にモジュールとして配置して使用する。個別のコピペ後コンパイルも検証する。
ファイルを特定するための import 直後の `#print "file: …"` を省略しない。

## 今回の到達点

| 内容 | 状態 |
| --- | --- |
| 実際の Galois 作用に対する線形射影 e₂ | 証明済み |
| 射影の像 = 既存の同じ weightSquareSpace | 証明済み |
| 同じ円分単元 c=1+ζ のクラスの射影 g | 構成済み |
| 同じ Λ に対する Λ(g)=−h³λ²≠0 | 証明済み |
| 同じ ω² 単元空間が零でないこと | 証明済み |
| 同じ空間の次元1から hunit | 非零評価を内部供給して証明済み |
| 次元1そのもの | 未証明 |
| hbad・hclass・巡回塔の反復・一般 hno | 引き続き未完成 |

## ステップ1：同じ ω² 固有空間への実際の射影

p を素数とし、同じ代数閉包内の原始 p 乗根 ζ を指定する。
F=rootField ζ、Δ=Gal(F/ℚ)、U=Additive(𝓞 Fˣ/(𝓞 Fˣ)^p) と置く。
実際の作用 ρ(γ) は既存の `unitClassLinearMap p (integerAut γ)` である。
作用の乗法則は整数環への同じ制限の合成から証明する。

    e₂ = |Δ|⁻¹ Σγ ω(γ)⁻² ρ(γ)

を `Module.End (ZMod p) U` として定義する。
ここで ω は、同じ `baseRoot_primitive hζ` の `autToPow` から作った `baseCharacter` である。
|Δ|=p−1 とその mod p での可逆性は既存の証明から内部供給する。
群の位数や分母の可逆性を新たな仮定にしない。

左乗法による Δ の添字変更により、ρ(δ)e₂x=ω(δ)²e₂x を証明する。
固有空間の元 x については各項 ω(γ)⁻²ρ(γ)x が x となるので e₂x=x。
従って e₂²=e₂、range(e₂)=weightSquareSpace hζ が成立する。
この時点では像の次元も非零性も主張していない。

計算用に、同じ指標 ω:Δ→𝔽pˣ 自身を同型 `characterEquiv` にする。
単射性は指定された原始根、全射性は両側の位数 p−1 から得る。
標準 zeta の円分体や外部実装の作用に取り替えず、同じ作用の和を d∈𝔽pˣ に添字変更する。
逆同型で選んだ γd は、実際に同じ根を ζ^d.val へ送る。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace
import DkMath.Lib.NumberTheory.CyclotomicClassVanishing

#print "file: DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector"

/-!
# 同じ単元商・同じ Galois 作用の ω² 射影子

実際の群の位数 p−1 の可逆性を内部供給する。
像が既存 weightSquareSpace と一致する射影を構成する。
固有空間の次元・非零性はここでは主張しない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector

open CyclotomicKernelField CyclotomicKummerWeight CyclotomicKummerEquivariance
open KummerSelmerExact KummerSelmerUnitEquivariance CyclotomicPrimaryUnitSpace
open CyclotomicClassVanishing
open scoped NumberField
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 元の整数環作用を、同じ単元冪商上の実際の線形表現にまとめる。 -/
def unitAction : ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) →*
    Module.End (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) where
  toFun γ := unitClassLinearMap p (integerAut γ)
  map_one' := by
    ext x
    change Additive.ofMul (unitClassMap p (integerAut 1) x.toMul) = x
    rw [integerAut_one, unitClassMap_refl]
    rfl
  map_mul' γ δ := by
    ext x
    change Additive.ofMul (unitClassMap p (integerAut (γ * δ)) x.toMul) =
      Additive.ofMul (unitClassMap p (integerAut γ) (unitClassMap p (integerAut δ) x.toMul))
    rw [integerAut_mul, unitClassMap_trans]

/-- 同じ baseCharacter の二乗に対する平均射影。 -/
def omegaSquareProjector : Module.End (ZMod p)
    (Additive (UnitClass (𝓞 (rootField ζ)) p)) :=
  (Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) : ZMod p)⁻¹ •
    ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitAction (p := p) γ

/-- 射影の実際の有限和表示。 -/
theorem omegaSquareProjector_apply (x : Additive (UnitClass (𝓞 (rootField ζ)) p)) :
    omegaSquareProjector hζ x =
      (Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) : ZMod p)⁻¹ •
        ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut γ) x := by
  simp only [omegaSquareProjector, LinearMap.smul_apply, LinearMap.sum_apply, unitAction,
    MonoidHom.coe_mk, OneHom.coe_mk]

/-- 平均の像は同じ ω² 固有条件を満たす。 -/
theorem omegaSquareProjector_mem (x : Additive (UnitClass (𝓞 (rootField ζ)) p)) :
    omegaSquareProjector hζ x ∈ weightSquareSpace hζ := by
  intro δ
  rw [omegaSquareProjector_apply, map_smul, map_sum]
  have he : ∀ γ, unitClassLinearMap p (integerAut δ)
      (((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut γ) x) =
      ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut (δ * γ)) x := by
    intro γ
    rw [map_smul]
    exact congrArg (fun y => ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • y)
      (LinearMap.congr_fun (map_mul (unitAction (p := p)) δ γ) x).symm
  rw [Finset.sum_congr rfl (fun γ _ => he γ)]
  have hs : ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ •
      unitClassLinearMap p (integerAut (δ * γ)) x =
      (baseCharacter hζ δ : ZMod p) ^ 2 •
        ∑ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut γ) x := by
    rw [Finset.smul_sum]
    refine Fintype.sum_bijective (δ * ·) (Group.mulLeft_bijective δ) _ _ (fun γ => ?_)
    rw [smul_smul, map_mul, Units.val_mul, mul_pow, mul_inv_rev]
    congr 1
    have hn : (baseCharacter hζ δ : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 (baseCharacter hζ δ).ne_zero
    field_simp
  rw [hs, smul_comm]

/-- 固有空間上で射影は恒等写像。群位数の可逆性は算術から供給する。 -/
theorem omegaSquareProjector_eq_self (x : Additive (UnitClass (𝓞 (rootField ζ)) p))
    (hx : x ∈ weightSquareSpace hζ) : omegaSquareProjector hζ x = x := by
  rw [omegaSquareProjector_apply]
  have he : ∀ γ, ((baseCharacter hζ γ : ZMod p) ^ 2)⁻¹ •
      unitClassLinearMap p (integerAut γ) x = x := by
    intro γ
    rw [hx γ, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 (baseCharacter hζ γ).ne_zero), one_smul]
  rw [Finset.sum_congr rfl (fun γ _ => he γ), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul (R := ZMod p), smul_smul,
    inv_mul_cancel₀ (root_galois_card_isUnit hζ).ne_zero, one_smul]

/-- 射影を二度適用しても変わらない。 -/
theorem omegaSquareProjector_idempotent :
    omegaSquareProjector hζ * omegaSquareProjector hζ = omegaSquareProjector hζ := by
  ext x
  exact omegaSquareProjector_eq_self hζ _ (omegaSquareProjector_mem hζ x)

/-- 射影の像は新しい代用品でなく、既存の同じ固有空間である。 -/
theorem omegaSquareProjector_range :
    LinearMap.range (omegaSquareProjector hζ) = weightSquareSpace hζ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact omegaSquareProjector_mem hζ y
  · intro hx
    exact ⟨x, omegaSquareProjector_eq_self hζ x hx⟩

/-- 指定した根の指標自体を同型にする。標準 zeta への取り替えを使わない。 -/
def characterEquiv : ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) ≃* (ZMod p)ˣ :=
  letI := rootField_isCyclotomic hζ
  MulEquiv.ofBijective (baseCharacter hζ) (by
    apply (Fintype.bijective_iff_injective_and_card (baseCharacter hζ)).mpr
    refine ⟨(baseRoot_primitive hζ).autToPow_injective ℚ, ?_⟩
    rw [← Nat.card_eq_fintype_card, root_galois_card hζ, ZMod.card_units p])

/-- 逆同型で選んだ自己同型は、同じ指定根を d 乗へ送る。 -/
theorem characterEquiv_symm_root (d : (ZMod p)ˣ) :
    (characterEquiv hζ).symm d (baseRoot ζ) = baseRoot ζ ^ (d : ZMod p).val := by
  have h := (baseRoot_primitive hζ).autToPow_spec ℚ ((characterEquiv hζ).symm d)
  have hd : baseCharacter hζ ((characterEquiv hζ).symm d) = d :=
    (characterEquiv hζ).apply_symm_apply d
  rw [show (baseRoot_primitive hζ).autToPow ℚ ((characterEquiv hζ).symm d) = d from hd] at h
  exact h.symm

/-- 非零評価に使う、同じ指標同型による有限和の添字変更。 -/
theorem omegaSquareProjector_apply_units (x : Additive (UnitClass (𝓞 (rootField ζ)) p)) :
    omegaSquareProjector hζ x =
      (Nat.card (ZMod p)ˣ : ZMod p)⁻¹ • ∑ d : (ZMod p)ˣ,
        ((d : ZMod p) ^ 2)⁻¹ • unitClassLinearMap p (integerAut ((characterEquiv hζ).symm d)) x := by
  rw [omegaSquareProjector_apply]
  have hc : Fintype.card ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) = Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (characterEquiv hζ).toEquiv
  rw [hc]
  congr 1
  exact Fintype.sum_equiv (characterEquiv hζ).toEquiv _ _ (fun γ => by
    change _ = ((characterEquiv hζ γ : ZMod p) ^ 2)⁻¹ •
      unitClassLinearMap p (integerAut ((characterEquiv hζ).symm (characterEquiv hζ γ))) x
    rw [MulEquiv.symm_apply_apply]
    rfl)

end
end DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector
```

## ステップ2：実際の大域単元の非零検出

p≥5 とする。原始根の幾何級数の単元定理から

    c=1+ζ ∈ 𝓞 Fˣ,    g=e₂[c] ∈ weightSquareSpace hζ

を構成する。g は新しい任意の検出ベクトルではなく、この具体的な単元クラスの射影である。

同じ3次商 Q=𝓞 F/(λ³)、λ=ζ−1 を使用する。
前段で構成した h=ι(2⁻¹)、2h=1、λ³=0、λ²≠0、char Q=p を再利用する。

### 共役単元の計算

t³=0 の可換環では、任意の自然数 a に対して

    (1+t)^a = 1+a t+choose(a,2)t²

が正確に成立する。三次以上の項を近似として無視しているわけではない。
2 choose(a,2)+a=a² を使い、標数 p の冪と切断対数を計算すると

    Λ([γd(c)]) = −h a λ + (h² a−h³ a²)λ²,    a=d.val

を得る。`integerAut_root` が指定根の冪則と整数環作用をつなぎ、
`unitLog_conjugate` がその同じ実際の単元に対する等式を証明する。

### 有限和と正規化

d∈𝔽pˣ 上で Σd⁻¹=0、Σ1=p−1=−1 となる。
これは有限体の実際の冪和と、逆元による全単元の並べ替えから証明する。
Λ の加法性と実際の ι に関するスカラー則を使い、上の評価に d⁻² を掛けて和を取る。
線形項と二次の h² の項が消え、群位数の逆数 −1 を掛けることで

    Λ(g) = −h³λ²

となる。これは **DkMath の同じ射影子・同じ単元商・同じ primaryLog** についての定理である。
外部実装と正規化が一致することを、この実際の計算で確認している。

Q は体でも整域でもない。非零性には零積則を使わず、
仮に h³λ²=0 なら 2³ を掛けて λ²=0 とする。2h=1 と λ²≠0 に矛盾する。
従って Λ(g)≠0、g≠0、weightSquareSpace hζ≠⊥ を得る。
ここで有限次元性を新たに仮定していないため、finrank の正値までは主張しない。

前段の条件付き消滅定理にこの具体的な g と非零評価を渡せる。
新しい `primaryWeightSquareSpace_eq_bot_of_rank_one` の公開入力には
`hrank` が残る一方、任意の `g`・`hdetect`・`hunit` は要求しない。

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: retain the specified root and DkMath unit quotient and projector;
transport conjugates using the SAME baseCharacter equivalence, prove the actual
nonzero log evaluation, and supply hdetect internally without external imports.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero"

/-!
# 同じ円分単元の ω² 射影に対する実際の非零評価

同じ rootField、同じ射影子、同じ primaryLog に対して Λ(e₂[1+ζ])=−h³λ²。
非零性を証明し、前段の hdetect を内部供給する。次元1は依然として入力である。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero

open CyclotomicTruncatedLog CyclotomicPrimaryLog CyclotomicPrimaryCongruence
open CyclotomicOmegaSquareProjector CyclotomicPrimaryUnitSpace CyclotomicKernelField
open CyclotomicKummerWeight CyclotomicKummerEquivariance KummerSelmerExact
open KummerSelmerUnitEquivariance CyclotomicPrimaryLogCriterion
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- 二項係数の整数恒等式。後の 1/2 の扱いに除算を導入しない。 -/
theorem two_mul_choose_two_add (a : ℕ) : 2 * a.choose 2 + a = a ^ 2 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    zify at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

section QRing

variable {Q : Type*} [CommRing Q]

/-- t³=0 の環での有限二項展開。 -/
theorem one_add_pow_trunc {t : Q} (ht : t ^ 3 = 0) (a : ℕ) :
    (1 + t) ^ a = 1 + (a : Q) * t + (a.choose 2 : Q) * t ^ 2 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination (n.choose 2 : Q) * ht

/-- 二項係数の整数恒等式を任意の可換環へ写す。 -/
theorem cast_choose_two (a : ℕ) : (2 : Q) * (a.choose 2 : Q) = (a : Q) ^ 2 - a := by
  have h := congrArg (Nat.cast : ℕ → Q) (two_mul_choose_two_add a)
  push_cast at h
  linear_combination h

/-- 標数 p と冪零性から、(2+s)^(p−1) を2次まで正確に計算する。 -/
theorem two_add_pow_sub_one [CharP Q p] (hp3 : 3 ≤ p) {h s : Q} (h2 : 2 * h = 1)
    (hs : s ^ 3 = 0) : (2 + s) ^ (p - 1) = 1 - h * s + h ^ 2 * s ^ 2 := by
  have hsp : s ^ p = 0 := pow_eq_zero_of_le hp3 hs
  have h2p : (2 : Q) ^ p = 2 := by
    have e : (ZMod.castHom (dvd_refl p) Q) 2 = (2 : Q) := map_ofNat _ 2
    rw [← e, ← map_pow, ZMod.pow_card]
  have hp1 : (2 + s) ^ p = 2 := by rw [add_pow_char, hsp, h2p, add_zero]
  have hA : (1 - h * s + h ^ 2 * s ^ 2) * (2 + s) = 2 := by
    linear_combination (-s + h * s ^ 2) * h2 + h ^ 2 * hs
  have hsucc : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  calc (2 + s) ^ (p - 1)
      = (2 + s) ^ (p - 1) * (h * ((1 - h * s + h ^ 2 * s ^ 2) * (2 + s))) := by
          rw [hA, mul_comm h 2, h2, mul_one]
    _ = h * (1 - h * s + h ^ 2 * s ^ 2) * ((2 + s) ^ (p - 1) * (2 + s)) := by ring
    _ = h * (1 - h * s + h ^ 2 * s ^ 2) * 2 := by rw [← pow_succ, hsucc, hp1]
    _ = 1 - h * s + h ^ 2 * s ^ 2 := by linear_combination (1 - h * s + h ^ 2 * s ^ 2) * h2

/-- 上の正確な冪計算に切断対数を適用する。 -/
theorem tlog_two_add_pow_sub_one [CharP Q p] (hp3 : 3 ≤ p) {h s : Q} (h2 : 2 * h = 1)
    (hs : s ^ 3 = 0) : tlog h ((2 + s) ^ (p - 1)) = -(h * s) + (h ^ 2 - h ^ 3) * s ^ 2 := by
  rw [two_add_pow_sub_one (p := p) hp3 h2 hs, tlog]
  linear_combination (2 * h ^ 4 - h ^ 5 * s) * hs

/-- 共役された同じ円分単元 1+ζ^a の評価に使う環の式。 -/
theorem tlog_conj_eval [CharP Q p] (hp3 : 3 ≤ p) {h t : Q} (h2 : 2 * h = 1)
    (ht : t ^ 3 = 0) (a : ℕ) :
    tlog h ((1 + (1 + t) ^ a) ^ (p - 1)) =
      -(h * a) * t + (h ^ 2 * a - h ^ 3 * (a : Q) ^ 2) * t ^ 2 := by
  set T : Q := (a.choose 2 : Q) with hTdef
  have hT : 2 * T = (a : Q) ^ 2 - a := cast_choose_two a
  have hs : (1 + t) ^ a = 1 + (a : Q) * t + T * t ^ 2 := one_add_pow_trunc ht a
  have hs3 : ((a : Q) * t + T * t ^ 2) ^ 3 = 0 := by
    have : ((a : Q) * t + T * t ^ 2) ^ 3 = t ^ 3 * ((a : Q) + T * t) ^ 3 := by ring
    rw [this, ht, zero_mul]
  have : (1 + (1 + t) ^ a) = 2 + ((a : Q) * t + T * t ^ 2) := by rw [hs]; ring
  rw [this, tlog_two_add_pow_sub_one (p := p) hp3 h2 hs3]
  linear_combination (h * T * t ^ 2) * h2 + (-(h ^ 2 * t ^ 2)) * hT +
    ((h ^ 2 - h ^ 3) * (2 * (a : Q) * T + T ^ 2 * t)) * ht

end QRing

section GenericField

variable {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)

private theorem two_coprime (hp5 : 5 ≤ p) : Nat.Coprime 2 p := by
  apply Nat.Coprime.symm
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 実際の整数環単元 1+ζ。 -/
def cyclotomicUnit (hp5 : 5 ≤ p) : (𝓞 F)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (Fact.out : p.Prime).two_le
    (two_coprime hp5)).unit

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
/-- 選んだ単元の値は同じ指定根の 1+ζ。 -/
theorem cyclotomicUnit_val (hp5 : 5 ≤ p) : (cyclotomicUnit hζ hp5 : 𝓞 F) = 1 + hζ.toInteger := by
  simpa only [cyclotomicUnit, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one] using
    (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (Fact.out : p.Prime).two_le
      (two_coprime hp5)).unit_spec

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
/-- 同じ指定根を3次商へ写すと 1+λ になる。 -/
theorem mk_integerRoot : Ideal.Quotient.mk (ramifiedIdeal hζ ^ 3) hζ.toInteger =
    1 + parameter hζ := by
  rw [parameter, ← map_one (Ideal.Quotient.mk _), ← map_add, add_sub_cancel]

/-- 整数環上の実際の自己同型による共役単元の評価。 -/
theorem unitLog_conjugate (hp5 : 5 ≤ p) (σ : 𝓞 F ≃+* 𝓞 F) (a : ℕ)
    (hσ : σ hζ.toInteger = hζ.toInteger ^ a) :
    unitLog hζ hp5 (Additive.ofMul (Units.map σ.toMonoidHom (cyclotomicUnit hζ hp5))) =
      -(half hζ hp5 * a) * parameter hζ +
        (half hζ hp5 ^ 2 * a - half hζ hp5 ^ 3 * (a : ResidueCube hζ) ^ 2) * parameter hζ ^ 2 := by
  let := residueCharP hζ hp5
  rw [unitLog_apply]
  have hcoe : ((Units.map σ.toMonoidHom (cyclotomicUnit hζ hp5) : (𝓞 F)ˣ) : 𝓞 F) =
      σ (1 + hζ.toInteger) := by
    change σ (cyclotomicUnit hζ hp5 : 𝓞 F) = _
    rw [cyclotomicUnit_val]
  rw [hcoe, map_add, map_one, hσ, map_add, map_one, map_pow, mk_integerRoot]
  exact tlog_conj_eval (p := p) (by omega) (two_mul_half hζ hp5) (parameter_cube hζ) a

/-- 非自明な1次指標の有限体単元上の和は零。 -/
theorem sum_units_val (hp5 : 5 ≤ p) : ∑ d : (ZMod p)ˣ, (d : ZMod p) = 0 := by
  have h := FiniteField.sum_pow_units (K := ZMod p) 1
  simp only [pow_one, ZMod.card] at h
  rw [h, ite_eq_right]
  intro hdvd
  have := Nat.le_of_dvd Nat.one_pos hdvd
  omega

/-- 逆元による全単元の並べ替えから、逆数の和も零。 -/
theorem sum_units_inv (hp5 : 5 ≤ p) : ∑ d : (ZMod p)ˣ, (d : ZMod p)⁻¹ = 0 := by
  calc ∑ d : (ZMod p)ˣ, (d : ZMod p)⁻¹ = ∑ d : (ZMod p)ˣ, ((d⁻¹ : (ZMod p)ˣ) : ZMod p) :=
        Finset.sum_congr rfl fun d _ => (Units.val_inv_eq_inv_val d).symm
    _ = ∑ d : (ZMod p)ˣ, (d : ZMod p) :=
        Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ (fun _ => rfl)
    _ = 0 := sum_units_val (p := p) hp5

/-- 単元の個数 p−1 は標数 p で −1。 -/
theorem sum_units_one : ∑ _d : (ZMod p)ˣ, (1 : ZMod p) = -1 := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units p, nsmul_eq_mul, mul_one,
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one, ZMod.natCast_self, zero_sub]

/-- 平均を取る際の実際の正規化係数は −1。 -/
theorem card_units_inv : ((Nat.card (ZMod p)ˣ : ZMod p))⁻¹ = -1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units p, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one,
    ZMod.natCast_self, zero_sub, inv_neg, inv_one]

/-- 同じスカラー写像による重み付き和を計算し、線形項を消去する。 -/
theorem e2_sum (hp5 : 5 ≤ p) :
    scalarMap hζ hp5 ((Nat.card (ZMod p)ˣ : ZMod p))⁻¹ *
      ∑ d : (ZMod p)ˣ, scalarMap hζ hp5 (((d : ZMod p) ^ 2)⁻¹) *
        (-(half hζ hp5 * ((d : ZMod p).val : ResidueCube hζ)) * parameter hζ +
          (half hζ hp5 ^ 2 * ((d : ZMod p).val : ResidueCube hζ) -
            half hζ hp5 ^ 3 * ((d : ZMod p).val : ResidueCube hζ) ^ 2) * parameter hζ ^ 2) =
      -(half hζ hp5 ^ 3 * parameter hζ ^ 2) := by
  simp only [half]
  set ι := scalarMap hζ hp5 with hι
  set t := parameter hζ
  have hval : ∀ d : (ZMod p)ˣ, ((d : ZMod p).val : ResidueCube hζ) = ι d := fun d =>
    (scalarMap_apply hζ hp5 d).symm
  have hsummand : ∀ d : (ZMod p)ˣ,
      ι (((d : ZMod p) ^ 2)⁻¹) *
        (-(ι 2⁻¹ * ((d : ZMod p).val : ResidueCube hζ)) * t +
          ((ι 2⁻¹) ^ 2 * ((d : ZMod p).val : ResidueCube hζ) -
            (ι 2⁻¹) ^ 3 * ((d : ZMod p).val : ResidueCube hζ) ^ 2) * t ^ 2) =
      ι (-(2⁻¹ * (d : ZMod p)⁻¹)) * t + ι ((2⁻¹) ^ 2 * (d : ZMod p)⁻¹ - (2⁻¹) ^ 3) * t ^ 2 := by
    intro d
    have hd : (d : ZMod p) ≠ 0 := d.ne_zero
    have e1 : ((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) = (d : ZMod p)⁻¹ := by
      field_simp
    have e2 : ((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hd)
    rw [hval d]
    have : ι (-(2⁻¹ * (d : ZMod p)⁻¹)) = -(ι (((d : ZMod p) ^ 2)⁻¹) * (ι 2⁻¹ * ι d)) := by
      rw [← e1]; simp only [map_neg, map_mul]; ring
    rw [this]
    have : ι ((2⁻¹) ^ 2 * (d : ZMod p)⁻¹ - (2⁻¹) ^ 3) =
        ι (((d : ZMod p) ^ 2)⁻¹) * ((ι 2⁻¹) ^ 2 * ι d - (ι 2⁻¹) ^ 3 * (ι d) ^ 2) := by
      rw [← e1]
      conv_lhs => rw [show ((2 : ZMod p)⁻¹) ^ 3 = (2⁻¹) ^ 3 * (((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) ^ 2)
        by rw [e2, mul_one]]
      simp only [map_sub, map_mul, map_pow]; ring
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun d _ => hsummand d), Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, ← map_sum, ← map_sum]
  have s1 : ∑ d : (ZMod p)ˣ, -(2⁻¹ * (d : ZMod p)⁻¹) = 0 := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_units_inv (p := p) hp5, mul_zero, neg_zero]
  have s2 : ∑ d : (ZMod p)ˣ, ((2 : ZMod p)⁻¹ ^ 2 * (d : ZMod p)⁻¹ - 2⁻¹ ^ 3) = 2⁻¹ ^ 3 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_units_inv (p := p) hp5, mul_zero, Finset.sum_const,
      Finset.card_univ, ZMod.card_units p, nsmul_eq_mul, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one,
      ZMod.natCast_self]
    ring
  rw [s1, s2, card_units_inv (p := p), map_zero, zero_mul, zero_add, map_neg, map_one, map_pow]
  ring

end GenericField

section RootField

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 円分単元類の同じ ω² 射影。 -/
def projectedCyclotomicUnit (hp5 : 5 ≤ p) : weightSquareSpace hζ :=
  letI := rootField_isCyclotomic hζ
  ⟨omegaSquareProjector hζ (Additive.ofMul
      (cyclotomicUnit (baseRoot_primitive hζ) hp5 : UnitClass (𝓞 (rootField ζ)) p)),
    omegaSquareProjector_mem hζ _⟩

/-- 指定根の Galois 指標と整数環作用が実際に同じ冪を与える。 -/
theorem integerAut_root (d : (ZMod p)ˣ) :
    (integerAut ((characterEquiv hζ).symm d)).integers (baseRoot_primitive hζ).toInteger =
      (baseRoot_primitive hζ).toInteger ^ (d : ZMod p).val := by
  apply NumberField.RingOfIntegers.coe_injective
  exact characterEquiv_symm_root hζ d

/-- 同じ大域単元の射影に対する具体的な評価。 -/
theorem primaryLog_projectedCyclotomicUnit (hp5 : 5 ≤ p) :
    letI := rootField_isCyclotomic hζ
    primaryLog (baseRoot_primitive hζ) hp5 (projectedCyclotomicUnit hζ hp5) =
      -(half (baseRoot_primitive hζ) hp5 ^ 3 * parameter (baseRoot_primitive hζ) ^ 2) := by
  let := rootField_isCyclotomic hζ
  change primaryLog (baseRoot_primitive hζ) hp5
    (omegaSquareProjector hζ (Additive.ofMul
      (cyclotomicUnit (baseRoot_primitive hζ) hp5 : UnitClass (𝓞 (rootField ζ)) p))) = _
  rw [omegaSquareProjector_apply_units, primaryLog_smul, map_sum]
  simp only [primaryLog_smul]
  have he : ∀ d : (ZMod p)ˣ,
      primaryLog (baseRoot_primitive hζ) hp5
        (unitClassLinearMap p (integerAut ((characterEquiv hζ).symm d))
          (Additive.ofMul (cyclotomicUnit (baseRoot_primitive hζ) hp5 :
            UnitClass (𝓞 (rootField ζ)) p))) =
      -(half (baseRoot_primitive hζ) hp5 * (d : ZMod p).val) * parameter (baseRoot_primitive hζ) +
        (half (baseRoot_primitive hζ) hp5 ^ 2 * (d : ZMod p).val -
          half (baseRoot_primitive hζ) hp5 ^ 3 * ((d : ZMod p).val :
            ResidueCube (baseRoot_primitive hζ)) ^ 2) * parameter (baseRoot_primitive hζ) ^ 2 := by
    intro d
    change unitLog (baseRoot_primitive hζ) hp5 (Additive.ofMul
      (Units.map (integerAut ((characterEquiv hζ).symm d)).integers.toMonoidHom
        (cyclotomicUnit (baseRoot_primitive hζ) hp5))) = _
    exact unitLog_conjugate (baseRoot_primitive hζ) hp5 _ _ (integerAut_root hζ d)
  simp only [he]
  exact e2_sum (baseRoot_primitive hζ) hp5

/-- h は実際に可逆なスカラー。Q が整域であるとは仮定しない。 -/
theorem half_cube_parameter_sq_ne_zero (hp5 : 5 ≤ p) :
    letI := rootField_isCyclotomic hζ
    half (baseRoot_primitive hζ) hp5 ^ 3 * parameter (baseRoot_primitive hζ) ^ 2 ≠ 0 := by
  let := rootField_isCyclotomic hζ
  intro hzero
  apply parameter_sq_ne_zero (baseRoot_primitive hζ)
  have h := congrArg (fun z : ResidueCube (baseRoot_primitive hζ) => 2 ^ 3 * z) hzero
  have he : (2 : ResidueCube (baseRoot_primitive hζ)) ^ 3 *
      (half (baseRoot_primitive hζ) hp5 ^ 3 * parameter (baseRoot_primitive hζ) ^ 2) =
        parameter (baseRoot_primitive hζ) ^ 2 := by
    rw [← mul_assoc, ← mul_pow, two_mul_half, one_pow, one_mul]
  rwa [he, mul_zero] at h

/-- 実際の大域単元の ω² 射影が、同じ Λ により検出される。 -/
theorem primaryLog_projectedCyclotomicUnit_ne_zero (hp5 : 5 ≤ p) :
    letI := rootField_isCyclotomic hζ
    primaryLog (baseRoot_primitive hζ) hp5 (projectedCyclotomicUnit hζ hp5) ≠ 0 := by
  let := rootField_isCyclotomic hζ
  rw [primaryLog_projectedCyclotomicUnit, neg_ne_zero]
  exact half_cube_parameter_sq_ne_zero hζ hp5

/-- 同じ実際の ω² 単元空間に非零元が存在する。 -/
theorem projectedCyclotomicUnit_ne_zero (hp5 : 5 ≤ p) :
    projectedCyclotomicUnit hζ hp5 ≠ 0 := by
  let := rootField_isCyclotomic hζ
  intro h
  apply primaryLog_projectedCyclotomicUnit_ne_zero hζ hp5
  simp [h]

/-- 同じ固有空間そのものが零でない。有限次元性を追加仮定しない。 -/
theorem weightSquareSpace_ne_bot (hp5 : 5 ≤ p) : weightSquareSpace hζ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨projectedCyclotomicUnit hζ hp5, (projectedCyclotomicUnit hζ hp5).property, ?_⟩
  intro hz
  exact projectedCyclotomicUnit_ne_zero hζ hp5 (Subtype.ext hz)

/-- 非零評価 hdetect を内部供給し、残条件を実際の同じ空間の次元1へ減らす。 -/
theorem primaryWeightSquareSpace_eq_bot_of_rank_one (hp5 : 5 ≤ p)
    (hrank : Module.finrank (ZMod p) (weightSquareSpace hζ) = 1) :
    primaryWeightSquareSpace hζ = ⊥ :=
  primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection hζ hp5 hrank
    (projectedCyclotomicUnit hζ hp5) (primaryLog_projectedCyclotomicUnit_ne_zero hζ hp5)

end RootField
end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero
```

## Frey の同じ大域分裂経路への接続

新しい公開入口は

    residual_cyclic_extension_has_stable_complement_of_unit_rank_one

である。元の S、L、K、同じ巡回段の安定性・位数・底の包含条件を保つ。
結論は同じ torsionImage の、同じ preimageRepresentation における大域安定な補空間である。
同じ `weightSquareSpace hζ` の次元1 `hrank` から内部で hunit を証明し、既存の分裂定理へ渡す。
公開入力に `g`、`hdetect`、`hunit`、`v`、`P`、`hsurj`、`hns` を追加していない。

**hrank・hbad・hclass は依然として入力である。**
非零評価が閉じたことで単元側の具体的な残条件は次元計算になったが、
この定理は一般 hno の無条件な証明ではない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicConditionalSplit
import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero

#print "file: DkMath.FLT.FreyCyclotomicPrimaryLogSplit"

/-!
# 同じ円分単元の非零検出を内部供給した、次元1条件付き大域分裂

hunit や hdetect を入力しない。実際の単元空間の次元1を入力し、
証明済みの実際の Λ の非零評価から hunit を構成して既存の分裂定理に渡す。
hbad・hclass・同じ巡回段の全条件は保持する。次元1・一般 hno は未証明。
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
local instance instIsEllipticPrimaryLogSplit : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldPrimaryLogSplit : NumberField (rootField ζ) := rootField_numberField ζ

include hline hcofixed hstable hm hcard hbase

/-- hdetect と hunit を内部供給する。残る単元算術入力は同じ固有空間の次元1。 -/
theorem residual_cyclic_extension_has_stable_complement_of_unit_rank_one
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hrank : Module.finrank (ZMod p) (weightSquareSpace hζ) = 1) :
    ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D := by
  exact S.residual_cyclic_extension_has_stable_complement
    L hline hcofixed K hstable hm hcard hbase hζ hp5 hbad hclass
    (CyclotomicPrimaryLogNonzero.primaryWeightSquareSpace_eq_bot_of_rank_one hζ hp5 hrank)

end
end DkMath.FLT.Frey.Source
```

## 回帰・依存監査

`DkMathTest.FLT.CyclotomicPrimaryLogNonzero` は代数閉包内の実際の原始5乗根と
原始7乗根を選び、それぞれの同じ rootField を使用する。
5次の場合は群位数4、同じ指標逆同型の根への作用、射影の所属と恒等性を確認する。
特に −1/8=3 in 𝔽5 を用いた Λ(g)=3λ² を検証し、符号・正規化を確認する。
実際に Λ(g)≠0 と g≠0 を証明し、元の円分単元が整数環単元の5乗でないことも導く。
7次でも実際の射影の対数が非零であることを確認する。
これらは以前の「商環中の 1+λ²」のテストより強く、大域単元クラスに対する検証である。

主要14宣言について公理報告と再帰的な型・構成子・不透明証明本体の依存監査を行う。
入力監査では非零評価に hrank/hdetect/hunit が不要であることと、
最後の分裂定理に hrank・hbad・hclass と巡回段の全条件が残ることを確認する。
構文的 import 閉包、正確なモジュール表示、教科書全文一致も別に検証する。
検証結果：`evidence/validation-note032-cyclotomic-omega-square-detection.txt`。

## 次に残る数学

1. 同じ固有空間 `weightSquareSpace hζ` の次元が1であること。
   非零元の構成は完成したが、有限次元性と次元の上界は別途必要である。
2. 同じ円分類群商の ω² 成分消滅 hclass。
3. 共鳴素点での hbad の算術・幾何学。
4. 同じ巡回塔の反復と最終 hno への接続。

今回の2ステップと分裂定理への接続は完成している。一般 hno は未完成である。

## 出典

切断された二項展開・共役円分単元の対数計算・有限体上の重み付き和は、
ローカルの `anthropics/fermats-last-theorem` の
`P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean`
（blob `89f85644f3cc853c293396363bd290c9ff81a237`）を参考に適応した。
該当 production ファイルに Apache 著作権・License・NOTICE・blob を保持する。
外部の ModP、unitsGalAction、最終消滅定理を import せず、
DkMath の同じ UnitClass・integerAut・baseCharacter・primaryLog で再証明した。
射影子は DkMath の既存の重み付き和の議論と実際の群位数の定理を使って構成する。
外部 checkout のビルドや公理監査を行ったという主張はしない。
