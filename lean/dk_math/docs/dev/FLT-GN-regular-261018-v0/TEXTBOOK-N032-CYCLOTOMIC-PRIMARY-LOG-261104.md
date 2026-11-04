# NOTE-032 教科書：同じ単元商上の切断対数 Λ

日付：2026-11-04。前段：`TEXTBOOK-N032-CYCLOTOMIC-CONDITIONAL-SPLIT-261104.md`。
レビューを参考に、切断対数と単元商への降下を実装した。
本稿の3つの Lean ブロックは、各 production ファイルの著作権表示を含む全文である。
個別にコピーしてコンパイルできる。import 直後の `#print "file: …"` は省略しない。
ブロック1をモジュールとして配置してから2、2を配置してから3を利用する。

## 今回閉じた矢印

指定した素数 p≥5、数体 F、同じ原始根 ζ に対し、

- λ=ζ−1、𝔭=(λ)、Q=𝓞 F/𝔭³ を固定する。
- p∈𝔭³ を既存の分岐公式から導き、Q の標数 p を証明する。
- λ³=0、λ²≠0 を同じ Q で証明する。
- h=ι(2⁻¹) と置く。ι:𝔽p→Q は実際の環準同型で、2h=1 を満たす。
- ℓ(z)=(z−1)−h(z−1)² は 1+(λ) の乗法を加法へ送る。
- Λ₀(u)=ℓ(u^(p−1)) は整数環単元群から Q への加法準同型になる。
- Λ₀(u^p)=pΛ₀(u)=0 を証明し、実際の UnitClass=𝓞 Fˣ/(𝓞 Fˣ)^p へ降ろす。

従って、前段の実際の3次合同から

    u^(p−1)−1∈𝔭³  ⇒  Λ([u])=0

が成立する。さらに代表元を選ばず、`localPowerSpace F p` のすべての元を Λ が零に送る。
合同式を新たな入力に加える必要はなく、同じ局所 p 乗条件から導出する。

## 切断対数の加法性

z=1+a、w=1+b と書くと、ℓ(zw)−ℓ(z)−ℓ(w) は

    (1−2h)ab − h(2a²b + 2ab² + a²b²)

となる。2h=1 と三つのイデアル元の積が零という条件で全項が消える。
無限級数や解析的対数を導入しない、可換環の有限恒等式である。
単元の p−1 乗が 1+(λ) に入ることは、前段の剰余体濃度 p の定理で供給する。

## 1. 汎用の環恒等式

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Truncated-logarithm identities adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: expose reusable public ring identities and a group-to-additive map;
remove all external namespaces, export machinery and number-field specialization.
-/

import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.Ring

#print "file: DkMath.Lib.NumberTheory.CyclotomicTruncatedLog"

/-!
# 3次で消えるイデアル上の切断対数

tlog h z = (z−1) − h(z−1)², 2h=1 とする。
J の三つの元の積が零なら、1+J 上の乗法を加法へ送る。
数体・固有空間・単元消滅を仮定しない、環の恒等式である。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicTruncatedLog

variable {Q : Type*} [CommRing Q]

/-- 3次項以降を捨てた対数。h=1/2 に相当する値を明示する。 -/
def tlog (h : Q) (z : Q) : Q := (z - 1) - h * (z - 1) ^ 2

theorem tlog_one (h : Q) : tlog h 1 = 0 := by simp [tlog]

/-- 3次の積が零のとき、1+J 上で乗法を加法に送る。 -/
theorem tlog_mul {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) {z w : Q} (hz : z - 1 ∈ J) (hw : w - 1 ∈ J) :
    tlog h (z * w) = tlog h z + tlog h w := by
  obtain ⟨a, rfl⟩ : ∃ a, z = 1 + a := ⟨z - 1, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, w = 1 + b := ⟨w - 1, by ring⟩
  simp only [add_sub_cancel_left] at hz hw
  have h1 : a * a * b = 0 := hJ a hz a hz b hw
  have h3 : a * b * b = 0 := hJ a hz b hw b hw
  have key : tlog h ((1 + a) * (1 + b)) - (tlog h (1 + a) + tlog h (1 + b)) =
      (1 - 2 * h) * (a * b) - h * (2 * (a * a * b) + 2 * (a * b * b) + (a * a * b) * b) := by
    unfold tlog; ring
  rw [h1, h3, h2] at key
  rw [← sub_eq_zero, key]
  ring

/-- 環準同型は切断対数の明示式と可換する。 -/
theorem map_tlog {Q' : Type*} [CommRing Q'] (f : Q →+* Q') (h : Q) (z : Q) :
    f (tlog h z) = tlog (f h) (f z) := by
  simp [tlog, map_sub, map_mul, map_pow]

/-- 対数の値は元と同じ冪零イデアルに属する。 -/
theorem tlog_mem {J : Ideal Q} (h : Q) {z : Q} (hz : z - 1 ∈ J) : tlog h z ∈ J := by
  unfold tlog
  exact J.sub_mem hz (J.mul_mem_left _ (by rw [pow_two]; exact J.mul_mem_left _ hz))

section Hom

variable {G : Type*} [Group G]

/-- 像が 1+J に入る群準同型に対する、実際の加法準同型。 -/
def tlogHom {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) (f : G →* Q) (hf : ∀ g, f g - 1 ∈ J) : Additive G →+ Q where
  toFun x := tlog h (f x.toMul)
  map_zero' := by simp [tlog_one]
  map_add' x y := by
    simp only [toMul_add, map_mul]
    exact tlog_mul hJ h2 (hf _) (hf _)

theorem tlogHom_apply {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) (f : G →* Q) (hf : ∀ g, f g - 1 ∈ J) (g : G) :
    tlogHom hJ h2 f hf (Additive.ofMul g) = tlog h (f g) := rfl

end Hom

end DkMath.Lib.NumberTheory.CyclotomicTruncatedLog
```

## 2. 実際の単元商への降下

`unitLog_pow` が降下条件そのものである。
`primaryLog` は `QuotientGroup.lift` を用い、その条件を証明して商の準同型を構成する。
単に代表元を選んで関数を定義しているわけではない。
`primaryLog_smul` は任意の a∈𝔽p に対して

    Λ(a • x)=ι(a)Λ(x)

を証明する。Q は一般には体ではないため、Q 内で零積から任意の因子を消去してはならない。
後段では非零の **𝔽p スカラー** の逆元を環準同型 ι で写し、実際に可逆な因子だけを消去する。

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
Modified: retain the specified root and field; descend to DkMath UnitClass,
and derive zero on the actual localPowerSpace without external theorem imports.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence
import DkMath.Lib.NumberTheory.CyclotomicTruncatedLog

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryLog"

/-!
# 同じ単元商上の primary logarithm

Q=𝓞 F/(ζ−1)³ 上で Λ([u])=tlog(1/2, u^(p−1)) を構成する。
p≥5 から char Q=p を導き、p 乗を零へ送ることを証明してから商へ降ろす。
局所 p 乗類は実際に ker Λ に入る。Λ の固有空間上の単射性は未証明。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryLog

open CyclotomicPrimaryCongruence CyclotomicPrimaryUnitSpace CyclotomicTruncatedLog
open KummerSelmerExact DkMath.Lib.Algebra
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- 指定した根の同じ分岐イデアルによる3次商。 -/
abbrev ResidueCube := 𝓞 F ⧸ ramifiedIdeal hζ ^ 3

/-- 商における同じ局所パラメータ λ。 -/
def parameter : ResidueCube hζ := Ideal.Quotient.mk _ (hζ.toInteger - 1)

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
theorem parameter_cube : parameter hζ ^ 3 = 0 := by
  rw [parameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ramifiedIdeal,
    Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-- λ² は3次商で消えない。後続の非零評価に必要な算術的事実。 -/
theorem parameter_sq_ne_zero : parameter hζ ^ 2 ≠ 0 := by
  rw [parameter, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, ramifiedIdeal,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hζ.zeta_sub_one_prime'.ne_zero hζ.zeta_sub_one_prime'.not_isUnit]
  omega

theorem natCast_eq_zero (hp5 : 5 ≤ p) : (p : ResidueCube hζ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact natCast_mem_ramifiedIdeal_pow hζ 3 (by omega)

/-- 3次商は零環でない。同じ分岐素点が真の素イデアルであることを使う。 -/
instance residueCubeNontrivial : Nontrivial (ResidueCube hζ) :=
  Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have hle := Ideal.pow_le_self (I := ramifiedIdeal hζ) (n := 3) (by norm_num)
    rw [h, top_le_iff] at hle
    exact (ramifiedPlace hζ).isPrime.ne_top hle)

/-- 分岐公式から導いた標数。新しい標数仮定を要求しない。 -/
abbrev residueCharP (hp5 : 5 ≤ p) : CharP (ResidueCube hζ) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (natCast_eq_zero hζ hp5)

/-- Fp のスカラーを3次商へ送る実際の環準同型。 -/
def scalarMap (hp5 : 5 ≤ p) : ZMod p →+* ResidueCube hζ :=
  letI := residueCharP hζ hp5
  ZMod.castHom (dvd_refl p) _

theorem scalarMap_apply (hp5 : 5 ≤ p) (a : ZMod p) :
    scalarMap hζ hp5 a = (a.val : ResidueCube hζ) := by
  let := residueCharP hζ hp5
  rw [scalarMap, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- 商の中の 1/2。 -/
def half (hp5 : 5 ≤ p) : ResidueCube hζ := scalarMap hζ hp5 (2⁻¹)

theorem two_mul_half (hp5 : 5 ≤ p) : 2 * half hζ hp5 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  rw [half, ← map_ofNat (scalarMap hζ hp5) 2, ← map_mul, mul_inv_cancel₀ h2, map_one]

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
theorem parameterIdeal_cube (a : ResidueCube hζ) (ha : a ∈ Ideal.span {parameter hζ})
    (b : ResidueCube hζ) (hb : b ∈ Ideal.span {parameter hζ})
    (c : ResidueCube hζ) (hc : c ∈ Ideal.span {parameter hζ}) : a * b * c = 0 := by
  rw [Ideal.mem_span_singleton] at ha hb hc
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨c', rfl⟩ := hc
  calc
    _ = parameter hζ ^ 3 * (a' * b' * c') := by ring
    _ = 0 := by rw [parameter_cube, zero_mul]

/-- 単元を p−1 乗してから、同じ3次商へ写す。 -/
def residuePower : (𝓞 F)ˣ →* ResidueCube hζ :=
  (powMonoidHom (p - 1)).comp
    ((Ideal.Quotient.mk _).toMonoidHom.comp (Units.coeHom _))

theorem residuePower_sub_one_mem (u : (𝓞 F)ˣ) :
    residuePower hζ u - 1 ∈ Ideal.span {parameter hζ} := by
  have hx := unit_pow_sub_one_mem_ramifiedIdeal hζ u
  rw [ramifiedIdeal, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  change (Ideal.Quotient.mk _ (u : 𝓞 F)) ^ (p - 1) - 1 ∈ _
  rw [← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub, hy, map_mul,
    Ideal.mem_span_singleton]
  exact ⟨_, rfl⟩

/-- 単元群からの加法準同型。 -/
def unitLog (hp5 : 5 ≤ p) : Additive (𝓞 F)ˣ →+ ResidueCube hζ :=
  tlogHom (parameterIdeal_cube hζ) (two_mul_half hζ hp5)
    (residuePower hζ) (residuePower_sub_one_mem hζ)

theorem unitLog_apply (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ) :
    unitLog hζ hp5 (Additive.ofMul u) =
      tlog (half hζ hp5) ((Ideal.Quotient.mk _ (u : 𝓞 F)) ^ (p - 1)) := rfl

/-- 商への降下条件は標数 p と加法性から証明する。 -/
theorem unitLog_pow (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ) :
    unitLog hζ hp5 (Additive.ofMul (u ^ p)) = 0 := by
  change unitLog hζ hp5 (p • Additive.ofMul u) = 0
  rw [map_nsmul, nsmul_eq_mul, natCast_eq_zero hζ hp5, zero_mul]

/-- 実際の p 乗部分群を核に含むことを用いて UnitClass へ降ろす。 -/
def primaryLog (hp5 : 5 ≤ p) : Additive (UnitClass (𝓞 F) p) →+ ResidueCube hζ :=
  (QuotientGroup.lift (powerSubgroup (𝓞 F)ˣ p)
    (unitLog hζ hp5).toMultiplicativeRight (by
      rintro _ ⟨u, rfl⟩
      change unitLog hζ hp5 (Additive.ofMul (u ^ p)) = 0
      exact unitLog_pow hζ hp5 u)).toAdditive

theorem primaryLog_mk (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ) :
    primaryLog hζ hp5 (Additive.ofMul (u : UnitClass (𝓞 F) p)) =
      unitLog hζ hp5 (Additive.ofMul u) := rfl

/-- 同じ単元の3次合同から Λ の零化へ。 -/
theorem primaryLog_mk_eq_zero_of_congruence (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ)
    (hu : (u : 𝓞 F) ^ (p - 1) - 1 ∈ ramifiedIdeal hζ ^ 3) :
    primaryLog hζ hp5 (Additive.ofMul (u : UnitClass (𝓞 F) p)) = 0 := by
  rw [primaryLog_mk, unitLog_apply]
  have h : (Ideal.Quotient.mk (ramifiedIdeal hζ ^ 3) (u : 𝓞 F)) ^ (p - 1) = 1 := by
    rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  rw [h, tlog_one]

/-- 実際の局所冪条件から、合同式を新規入力にせず Λ([u])=0 を得る。 -/
theorem primaryLog_mk_eq_zero_of_local_power (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 F) p) ∈ localPowerSpace F p) :
    primaryLog hζ hp5 (Additive.ofMul (u : UnitClass (𝓞 F) p)) = 0 :=
  primaryLog_mk_eq_zero_of_congruence hζ hp5 u
    (pow_sub_one_mem_ramifiedIdeal_cube_of_local_power hζ hp5 u hu)

/-- 代表元を選ばない、局所冪空間全体についての零化。 -/
theorem primaryLog_eq_zero_of_mem_localPowerSpace (hp5 : 5 ≤ p)
    (x : Additive (UnitClass (𝓞 F) p)) (hx : x ∈ localPowerSpace F p) :
    primaryLog hζ hp5 x = 0 := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (powerSubgroup (𝓞 F)ˣ p) x.toMul
  have he : Additive.ofMul (u : UnitClass (𝓞 F) p) = x := congrArg Additive.ofMul hu
  rw [← he] at hx ⊢
  exact primaryLog_mk_eq_zero_of_local_power hζ hp5 u hx

/-- Fp スカラーに関する実際の線形性（商側への環写像を明示）。 -/
theorem primaryLog_smul (hp5 : 5 ≤ p) (a : ZMod p)
    (x : Additive (UnitClass (𝓞 F) p)) :
    primaryLog hζ hp5 (a • x) = scalarMap hζ hp5 a * primaryLog hζ hp5 x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, scalarMap_apply]

end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryLog
```

## 3. 次元1・非零評価との合成

DkMath の `weightSquareSpace hζ` は同じ根で生成した `rootField ζ` と
実際の `integerAut`・`baseCharacter` による ω² 固有空間である。
ここで比較対象を別の円分体や別の作用に取り替えない。
`baseRoot_primitive hζ` による同じ Λ を使い、次の二条件を明示する。

1. `hrank`: その実際の固有空間の finrank が1。
2. `g`: その空間の元で、`hdetect`: Λ(g)≠0。

一次元性から x=a•g と書ける。局所冪条件から Λ(x)=0 なので、ι(a)Λ(g)=0。
a≠0 なら ι(a⁻¹) を掛けて Λ(g)=0 となり矛盾する。従って a=0、x=0。
これにより `primaryWeightSquareSpace hζ = ⊥`、つまり前段の hunit を得る。
この合成定理には **hrank と hdetect が依然として入力される**。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryLog
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion"

/-!
# Λ による primary 単元消滅の明示的な二つの残条件

同じ ω² 単元空間の次元1と、その空間内の元 g の Λ(g)≠0 が与えられた場合、
局所冪空間の消滅を証明する。次元計算・円分単元の射影・非零評価は証明しない。
Λ を任意の写像に取り替えず、指定された原始根の実際の3次商と単元商を使う。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion

open CyclotomicPrimaryLog CyclotomicPrimaryUnitSpace CyclotomicKernelField
open CyclotomicKummerWeight KummerSelmerExact
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- 実際の Λ は、一次元の部分空間上で一つの非零評価があれば単射になる。 -/
theorem eq_zero_of_rank_one_of_log_eq_zero (hp5 : 5 ≤ p)
    (W : Submodule (ZMod p) (Additive (UnitClass (𝓞 F) p)))
    (hrank : Module.finrank (ZMod p) W = 1)
    (g : W) (hdetect : primaryLog hζ hp5 g ≠ 0)
    (x : W) (hx : primaryLog hζ hp5 x = 0) : x = 0 := by
  have hg : g ≠ 0 := by
    intro h
    apply hdetect
    simp [h]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hrank hg x
  have he : scalarMap hζ hp5 a * primaryLog hζ hp5 g = 0 := by
    rw [← primaryLog_smul]
    exact (congrArg (fun y : W => primaryLog hζ hp5 y) ha).trans hx
  have ha0 : a = 0 := by
    by_contra hn
    have hm := congrArg (fun z => scalarMap hζ hp5 a⁻¹ * z) he
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul, mul_zero] at hm
    exact hdetect hm
  simpa only [ha0, zero_smul] using ha.symm

end

section RootField

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 局所冪空間の元は、選び直していない同じ根の Λ の核に入る。 -/
theorem primaryWeightSquareSpace_log_eq_zero (hp5 : 5 ≤ p)
    (x : Additive (UnitClass (𝓞 (rootField ζ)) p))
    (hx : x ∈ primaryWeightSquareSpace hζ) :
    let := rootField_isCyclotomic hζ
    primaryLog (baseRoot_primitive hζ) hp5 x = 0 := by
  let := rootField_isCyclotomic hζ
  exact primaryLog_eq_zero_of_mem_localPowerSpace (baseRoot_primitive hζ) hp5 x hx.2

/-- 次元1・実際の Λ の非零評価から hunit を構成する。
この二つの算術入力は残条件であり、この定理自身の無条件の結論ではない。 -/
theorem primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection (hp5 : 5 ≤ p)
    (hrank : Module.finrank (ZMod p) (weightSquareSpace hζ) = 1)
    (g : weightSquareSpace hζ)
    (hdetect : letI := rootField_isCyclotomic hζ
      primaryLog (baseRoot_primitive hζ) hp5 g ≠ 0) :
    primaryWeightSquareSpace hζ = ⊥ := by
  let := rootField_isCyclotomic hζ
  apply (Submodule.eq_bot_iff (primaryWeightSquareSpace hζ)).mpr
  intro x hx
  have he := eq_zero_of_rank_one_of_log_eq_zero (baseRoot_primitive hζ) hp5
    (weightSquareSpace hζ) hrank g hdetect ⟨x, hx.1⟩
    (primaryWeightSquareSpace_log_eq_zero hζ hp5 x hx)
  exact congrArg Subtype.val he

end RootField
end DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion
```

## 条件付き分裂への接続と残る算術

`primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection` の結論は、既存の
`residual_cyclic_extension_has_stable_complement` の hunit 入力にそのまま渡せる。
この段階では、既存 Frey 定理から hunit 仮定を無条件に除去したとは主張しない。
既存の hbad・hclass、実際の巡回段の安定性・位数・底の包含条件も保持する。

次は hrank の単元群の階数・指標計算と、g=e₂[1+ζ] の構成・Λ(g)≠0 の評価が必要である。
本稿は g を円分単元の射影として構成しておらず、一般の非零評価も証明していない。
この2つを閉じて初めて hunit の算術的消滅が完成する。
その後にも共鳴素点の hbad、円分類群商の hclass、巡回塔の反復が残る。一般 hno は未完成。

## 回帰例と監査の意味

`DkMathTest.FLT.CyclotomicPrimaryLog` は実際の5次円分体で標数5と 2h=1、
λ²≠0、未補正の z−1 の非加法性、補正後の加法性、ℓ(1+λ²)=λ² を確認する。
最後の評価は Q 上の環のテストであり、ω² 成分の大域単元 g の検出を証明するものではない。
実際の円分単元 c=1+ζ の5乗について、局所冪条件から Λ([c^5])=0 となることも確認する。
代表元への5乗の掛け算による Λ₀ の不変性を確認する。この例の商類は零である。

主要10宣言の公理報告と、再帰的な型・構成子・不透明な証明本体の依存監査を行う。
公開入力監査では、Λ 自体が hunit・hrank・hdetect を要求せず構成されること、
合成定理には hrank・g・hdetect が残ることを確認する。
構文的な import 閉包検査と、公理・証明依存監査は別の検証である。
検証結果は `evidence/validation-note032-cyclotomic-primary-log.txt` に記録する。

## 出典と適応範囲

汎用の切断対数および円分体の3次商・単元対数の構成は、ローカルにある
`anthropics/fermats-last-theorem` の
`P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean`
（blob `89f85644f3cc853c293396363bd290c9ff81a237`）を参考に適応した。
Apache の著作権・通知を production の2ファイルと本稿のコードに保持する。
DkMath では指定した原始根を保持し、自身の powerSubgroup による UnitClass に降ろす。
外部の最終消滅定理・ModP・GalAction の型を同一視したり、その定理を import したりしない。
次元1の合成は Mathlib の一次元線形代数 API と DkMath の実際の Λ を使用する。
