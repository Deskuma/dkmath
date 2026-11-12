# NOTE-032 教科書 — 実際の互換根の塔・全段の Kummer 慣性生成元・可視な補正

日付: 2026-11-08。今回は生成元を仮定した補題を増やす段階から進み、
既存 DkMath の Kummer 分岐計算を使って、根の塔の全正段で原始的に作用する
**実際の同じ慣性元の存在**を構成した。

後半の5つの Lean ブロックは対応する production ソースの全文。
各 import 群直後の正確な `#print "file: モジュール名"` を省略しない。
既存 DkMath の Lake 環境でそれぞれ別ファイルへコピペして検査できる。
最初の4モジュールは Frey に依存しない DkMath.Lib、最後だけが DkMath.FLT の適用層である。

## 対象と到達点を区別する

相異なる素数 p,q、q の上の同じ付値環 A、実際の慣性群 I を使う。
代数閉包内で q の根の塔 α_n と、その作用比の単元値指標 χ_n を構成する。

    α_0=q,  α_(n+1)^p=α_n,
    χ_n(σ)=σ(α_n)/α_n ∈ (AlgebraicClosure ℚ)ˣ,
    C_n=I/ker χ_n.

今回の C_n は「この根の段に作用する慣性核商」である。
前回までの Frey 共通商 H=J/ker Ψ と同一視しない。
正段について C_n の巡回性・濃度・生成元を実際に構成するが、
**ker χ_n⊆ker(I→H) という比較は、今回まだ証明していない。**

## 1. 互換な根の塔を実際に構成する

`PrimeRadicalTower` は任意の代数閉体 L、正の自然数 p、基点 a∈L に対し、
代数閉性から次の p 乗根を逐次選んで同じ塔を構成する。
根の存在を新しい provider にしない。

    α_(n+d)^(p^d)=α_n,  α_n^(p^n)=a

を帰納法で証明し、a≠0 なら全段が非零であることを得る。
以後は L=AlgebraicClosure ℚ、a=q に特殊化し、同じ実際の塔を一貫して使う。

## 2. 同じ根に作用する単元値慣性指標

任意の Galois 元 σ の作用比 σ(α_n)/α_n は p^n 乗根の1である。
元の q 上の付値環で p は単元なので、既存の `ValuationInertiaPower` により、
実際の慣性は全ての p 冪根の1を固定する。
従って交差準同型の係数作用が消え、

    χ_n(στ)=χ_n(σ)χ_n(τ)

という通常の準同型になる。値は非零なので実際の単元群に保持する。
q≠p、q 上の住所、元の慣性元という条件を捨てない。

同じ塔の互換性から

    χ_(n+d)(σ)^(p^d)=χ_n(σ)

も証明する。これが一つの慣性元を全段へ上げる鍵となる。

## 3. 全ての正段で原始的に作用する同じ慣性元が存在する

第1段は α_1^p=q。既存の

    KummerInertia.exists_inertia_ne_of_pow_eq

を m=1 に適用する。p は1を割らないので、同じ A の慣性群に

    γ(α_1)≠α_1

となる実際の γ が存在する。この既存定理は有限分解体での分岐指数と整数の
素因数重複度を使い、指定された同じ A へ有限慣性元を持ち上げる算術定理である。
生成元を仮定する入力ではない。

χ_1(γ) は p 乗で1、しかも1ではないので厳密位数 p。
段間互換性 χ_(n+2)(γ)^p=χ_(n+1)(γ) と、各段の p 冪零化から、
同じ γ について帰納的に

    IsPrimitiveRoot (χ_(n+1)(γ)) (p^(n+1))

を証明する。全正段で同じ γ を使い、段ごとに選び直していない。
証明済みの存在定理から選ぶ名前付き `generator` と、その `generator_primitive` を公開した。
**hgen、hcyclic、htail、hclass、Cofixed、Frey Source はこの存在定理の入力にない。**

## 4. 実際の有限根核商と有界な補正分解

原始的な χ_(n+1)(γ) は全ての p^(n+1) 乗根の1をその冪で表す。
従って任意の同じ τ∈I に対し

    ∃ j<p^(n+1),  χ_(n+1)(τ)=χ_(n+1)(γ)^j

を得る。ε=(γ^j)^(-1)τ と置けば

    τ=γ^j ε,
    ε∈ker χ_(n+1),
    ε(α_(n+1))=α_(n+1).

ここで ε は同じ実際の慣性群の元である。
比が1であることと、元の根を固定することの同値を明示的に証明した。

さらに、実際の指標像は χ_(n+1)(γ) が生成する巡回部分群そのもの。
第一同型定理と位数から

    |C_(n+1)|=p^(n+1),  IsCyclic C_(n+1)

となる。全正段の原始性・濃度・巡回性・有界な補正分解を、一つの実際の γ の存在としてまとめた。
`of_primitive` の局所的な代数補題は原始性の証明を入力に取るが、
最終存在定理では第3段階の算術的存在からその証明を内部供給する。

## 5. Frey の同じ障害元へ接続し、補正項を消さずに保持する

元の Frey Source、巡回段 T、共通商への全射 π:I→H と、障害慣性元 τ を保つ。
以前の消費側が使う段に合わせて根の段 n+3 を取る。
同じ実際の γ と、内部構成した j,ε に対して

    0≤j<p^(n+3),  τ=γ^j ε,
    π(τ)=π(γ)^j π(ε)

を証明する。ε は α_(n+3) を固定する。
ただし **π(ε)=1 は結論していない。**

元の同じ核元 k と位数 p の固定差分 d について、

    d=j•ev_γ(k)+ev_ε(k)

を証明した。右辺の補正評価 ev_ε(k) は実際の値として残す。
根を固定することを、Frey の全指標で零になることへ勝手に置き換えない。

最終定理 `residual_exists_radical_generator_error` は元の hclass と Cofixed から、
同じ n,T,q,A,τ,y,h と、内部構成した同じ γ、実際に巡回な C_(n+3)、その正確な濃度、
同じ障害点の補正分解と評価式を出力する。生成元や補正消滅の新しい provider は要求しない。

## 模範解答との比較と、次に必要な算術

ローカル模範解答の互換な根の塔、Kummer 比の原始性の帰納法、有界な冪による根への作用一致を参考にした。
参照 HEAD は 115356cbc627159d0d16add0da6e9a2bb3655ed8。
DkMath では既存の Kummer 分岐定理で第1段の非固定性を直接供給できるため、
最初に動く段を Nat.find で探す部分を使わず、第1段から同じ γ の全段原始性を証明した。
適応した4 Lib モジュールには Apache-2.0、元ソース、コミット、変更点、既存 NOTICE の参照を保持する。
P2M/P2MW や既存 FLT 終点は import しない。

模範のより強い分解は τ=γ^j x^(p^m)w^(p^m) であり、今回の τ=γ^j ε とは異なる。
今回証明した ε は一つの指定した根の段を固定するが、
慣性群内で p^m 乗根を持つこと、全段を固定すること、野生合同部分群に入ることは証明していない。

共通 Frey 商 H の生成性へ進むには、例えば

    ker χ_(n+3) ⊆ ker π

という実際の核の比較を証明すればよい。その場合 ε の像が消え、同じ π(γ) が H を生成する。
今回この包含を仮定した追加の条件付き API は作らず、未解決の算術的比較として明記する。
以前の有限段分解消費側の hgen を供給したという主張もしていない。

**根の塔の実際の生成元存在と各有限根核商の巡回性は今回完成。Frey 共通商の生成性は未完成。**
連続 H¹ の比較、大域算術・共鳴障害の排除、hclass の供給も残る。
**無条件の一般 hno は引き続き未完成である。**

## 検証の範囲

ZMod5² の二つの座標写像で、根核商の生成元が別の商を生成するとは限らないことを検査する。
根側で固定される補正が、他方の写像で非零になる例と、核包含が成立しないことを形式的に示す。
また有界な冪と可視な補正の分解、ZMod25 での厳密位数25と5倍非零性を検査する。
新規31宣言の再帰依存監査、31件の公開入力監査、公理出力、Lib/FLT/root と通常入口の公開を確認する。
検証結果は `evidence/validation-note032-frey-radical-generator.txt`。
参照 SHA-256 は `evidence/note032-frey-radical-generator-reference-audit.json`。

## コピペ用 Lean 全文

### 1. DkMath.Lib.NumberTheory.PrimeRadicalTower

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: named compatible radical tower, arbitrary algebraically closed fields.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic

#print "file: DkMath.Lib.NumberTheory.PrimeRadicalTower"

/-!
# 実際に構成した互換な p 冪根の塔

根の存在を provider にせず、代数閉性から各次段を選ぶ。同じ塔の全段を保つ。
-/
namespace DkMath.Lib.NumberTheory.PrimeRadicalTower
noncomputable section
variable {L : Type*} [Field L] [IsAlgClosed L] (p : ℕ) (hp : 0 < p) (a : L)

/-- 代数閉性から逐次選ぶ、同じ基点 a の p 冪根の塔。 -/
def tower : ℕ → L := Nat.rec a (fun _ b => Classical.choose (IsAlgClosed.exists_pow_nat_eq b hp))

/-- 第0段は元の同じ基点。 -/
theorem tower_zero : tower p hp a 0 = a := rfl

/-- 各次段の p 乗は前段そのもの。 -/
theorem tower_succ_pow (n : ℕ) : tower p hp a (n + 1) ^ p = tower p hp a n :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (tower p hp a n) hp)

/-- 任意の二段の互換性。 -/
theorem tower_compat (n d : ℕ) : tower p hp a (n + d) ^ (p ^ d) = tower p hp a n := by
  induction d with
  | zero => rw [pow_zero, pow_one, Nat.add_zero]
  | succ d ih =>
    rw [pow_succ', pow_mul]
    change (tower p hp a (n + d + 1) ^ p) ^ (p ^ d) = _
    rw [tower_succ_pow, ih]

/-- 各段は元の同じ基点の p^n 乗根。 -/
theorem tower_pow (n : ℕ) : tower p hp a n ^ (p ^ n) = a := by
  simpa only [Nat.zero_add, tower_zero] using tower_compat p hp a 0 n

/-- 基点が非零なら、実際の塔の全段も非零。 -/
theorem tower_ne_zero (ha : a ≠ 0) (n : ℕ) : tower p hp a n ≠ 0 := by
  intro hz
  apply ha
  rw [← tower_pow p hp a n, hz, zero_pow (pow_ne_zero n hp.ne')]

end
end DkMath.Lib.NumberTheory.PrimeRadicalTower
```

### 2. DkMath.Lib.NumberTheory.InertiaRadicalCharacter

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual DkMath inertia/unit-power rigidity and named unit-valued characters.
-/

import DkMath.Lib.NumberTheory.PrimeRadicalTower
import DkMath.Lib.NumberTheory.ValuationInertiaPower

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalCharacter"

/-!
# 同じ q の根の塔に作用する実際の慣性 Kummer 指標

q 上の慣性は全ての p 冪根の1を固定する。従って根の作用比は交差準同型でなく
通常の単元値準同型となる。p≠q と元の付値環を保持する。
-/
namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia PrimeRadicalTower
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ有理素数 q を基点とする、実際の互換な根。 -/
abbrev radical (p q : ℕ) (hp : p.Prime) : ℕ → AlgebraicClosure ℚ := tower p hp.pos (q : AlgebraicClosure ℚ)

/-- 同じ根に対する作用比。 -/
def ratio (base : ℕ) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) : AlgebraicClosure ℚ :=
  σ (radical p base hp n) / radical p base hp n

include hq in
/-- 根の非零性は q の素数性から供給する。 -/
theorem radical_ne_zero (n : ℕ) : radical p q hp n ≠ 0 :=
  tower_ne_zero p hp.pos (q : AlgebraicClosure ℚ) (Nat.cast_ne_zero.mpr hq.ne_zero) n

include hq in
/-- 任意の Galois 元の作用比は p^n 乗根の1。 -/
theorem ratio_pow (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) : ratio hp q σ n ^ (p ^ n) = 1 := by
  rw [ratio, div_pow, ← map_pow, tower_pow, map_natCast, div_self (Nat.cast_ne_zero.mpr hq.ne_zero)]

/-- 同じ作用比の段間互換性。 -/
theorem ratio_compat (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n d : ℕ) :
    ratio hp q σ (n + d) ^ (p ^ d) = ratio hp q σ n := by
  rw [ratio, div_pow, ← map_pow, tower_compat]
  rfl

include hq in
/-- 比が1であることと、元の同じ根を固定することは同値。 -/
theorem ratio_eq_one_iff (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) :
    ratio hp q σ n = 1 ↔ σ (radical p q hp n) = radical p q hp n :=
  div_eq_one_iff_eq (radical_ne_zero hp hq n)

include hp hq hpq hA in
/-- 実際の q 上の付値環で p は単元。 -/
theorem valuation_prime_eq_one : A.valuation (p : AlgebraicClosure ℚ) = 1 := by
  apply ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
    ((ValuationSubring.mem_nonunits_iff A).mp hA) (z := (p : ℤ))
  intro hd
  rcases (Nat.dvd_prime hp).mp (Int.natCast_dvd_natCast.mp hd) with he | he
  · exact hq.ne_one he
  · exact hpq he.symm

include hp hq hpq hA in
/-- 全 p 冪根の1は、同じ実際の慣性群に固定される。 -/
theorem inertia_fixes_primePower_root (σ : inertiaSubgroupIn A ℚ) (n : ℕ)
    (z : AlgebraicClosure ℚ) (hz : z ^ (p ^ n) = 1) : σ.val z = z := by
  apply ValuationInertiaPower.inertia_fixed_of_pow_eq_one A ℚ (pow_ne_zero n hp.ne_zero)
    (n := p ^ n) ?_ σ.val σ.property hz
  rw [Nat.cast_pow, map_pow, valuation_prime_eq_one hp hq hpq A hA, one_pow]

/-- 根の作用比を値とする、実際の単元値慣性準同型。 -/
def character (n : ℕ) : inertiaSubgroupIn A ℚ →* (AlgebraicClosure ℚ)ˣ where
  toFun σ := Units.mk0 (ratio hp q σ.val n)
    (div_ne_zero (by
      intro hz
      apply radical_ne_zero hp hq n
      exact σ.val.injective (hz.trans (map_zero σ.val).symm)) (radical_ne_zero hp hq n))
  map_one' := by
    apply Units.ext
    change radical p q hp n / radical p q hp n = 1
    exact div_self (radical_ne_zero hp hq n)
  map_mul' σ τ := by
    apply Units.ext
    change σ.val (τ.val (radical p q hp n)) / radical p q hp n = ratio hp q σ.val n * ratio hp q τ.val n
    have hf := inertia_fixes_primePower_root hp hq hpq A hA σ n _ (ratio_pow hp hq τ.val n)
    have he : τ.val (radical p q hp n) = ratio hp q τ.val n * radical p q hp n :=
      (div_mul_cancel₀ _ (radical_ne_zero hp hq n)).symm
    rw [he, map_mul, hf, mul_div_assoc, mul_comm]
    rfl

/-- 単元として保持しても、元の同じ作用比を回収する。 -/
theorem character_val (n : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    (character hp hq hpq A hA n σ : AlgebraicClosure ℚ) = ratio hp q σ.val n := rfl

/-- 同じ慣性指標の全ての値は、元の p^n 乗で1になる。 -/
theorem character_pow (n : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    (character hp hq hpq A hA n σ : AlgebraicClosure ℚ) ^ (p ^ n) = 1 := ratio_pow hp hq σ.val n

/-- 同じ慣性指標の段間互換性を単元の中で保持する。 -/
theorem character_compat (n d : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    character hp hq hpq A hA (n + d) σ ^ (p ^ d) = character hp hq hpq A hA n σ := by
  apply Units.ext
  exact ratio_compat hp σ.val n d

end
end DkMath.Lib.NumberTheory.InertiaRadical
```

### 3. DkMath.Lib.NumberTheory.InertiaRadicalGenerator

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual DkMath Kummer inertia supplies first-stage movement; no tail-root hypothesis.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalCharacter
import DkMath.Lib.NumberTheory.KummerInertia
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalGenerator"

/-!
# 全ての正の根の段で原始的に作用する、実際の同じ慣性元

第1段の根を動かす元を既存の有限分岐計算から構成する。その同じ元は塔の互換性により
全段で原始的な Kummer 比を持つ。共通 Frey 商の生成性や tail の冪根存在はまだ主張しない。
-/
namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia PrimeRadicalTower
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 追加の生成元入力なしで、同じ慣性元が全ての正の根の段に原始的に作用する。 -/
theorem exists_primitive_generator :
    ∃ γ : inertiaSubgroupIn A ℚ, ∀ n : ℕ,
      IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hs : radical p q hp 1 ^ p = (q : AlgebraicClosure ℚ) ^ 1 := by
    simpa only [tower_zero, pow_one] using tower_succ_pow p hp.pos (q : AlgebraicClosure ℚ) 0
  have hm : ¬ p ∣ 1 := fun hd => hp.ne_one (Nat.dvd_one.mp hd)
  obtain ⟨τ, hτ, hmove⟩ := KummerInertia.exists_inertia_ne_of_pow_eq A hA hq hp hpq hm hs
  let γ : inertiaSubgroupIn A ℚ := ⟨τ, hτ⟩
  refine ⟨γ, ?_⟩
  intro n
  induction n with
  | zero =>
    have hne : (character hp hq hpq A hA 1 γ : AlgebraicClosure ℚ) ≠ 1 := by
      intro he
      exact hmove ((ratio_eq_one_iff hp hq τ 1).mp he)
    have hpow : (character hp hq hpq A hA 1 γ : AlgebraicClosure ℚ) ^ p = 1 := by
      simpa only [pow_one] using character_pow hp hq hpq A hA 1 γ
    have ho := orderOf_eq_prime hpow hne
    have hz := IsPrimitiveRoot.orderOf (character hp hq hpq A hA 1 γ : AlgebraicClosure ℚ)
    rw [ho] at hz
    simpa only [Nat.zero_add, pow_one] using hz
  | succ n ih =>
    have hc := ratio_compat hp (q := q) τ (n + 1) 1
    rw [pow_one] at hc
    change (character hp hq hpq A hA (n + 1 + 1) γ : AlgebraicClosure ℚ) ^ p =
      (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) at hc
    have hfin := character_pow hp hq hpq A hA (n + 1 + 1) γ
    have hnot : ¬ (character hp hq hpq A hA (n + 1 + 1) γ : AlgebraicClosure ℚ) ^ (p ^ (n + 1)) = 1 := by
      intro he
      rw [pow_succ' p n, pow_mul, hc] at he
      have hd := (ih.pow_eq_one_iff_dvd (p ^ n)).mp he
      have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
      omega
    have ho := orderOf_eq_prime_pow hnot hfin
    have hz := IsPrimitiveRoot.orderOf (character hp hq hpq A hA (n + 1 + 1) γ : AlgebraicClosure ℚ)
    rwa [ho] at hz

/-- 証明済みの存在定理から選ぶ、全段で同じ実際の慣性元。 -/
def generator : inertiaSubgroupIn A ℚ := Classical.choose (exists_primitive_generator hp hq hpq A hA)

/-- 選んだ同じ元は全ての正の根の段で原始的に作用する。 -/
theorem generator_primitive (n : ℕ) :
    IsPrimitiveRoot (character hp hq hpq A hA (n + 1) (generator hp hq hpq A hA) : AlgebraicClosure ℚ)
      (p ^ (n + 1)) := Classical.choose_spec (exists_primitive_generator hp hq hpq A hA) n

end
end DkMath.Lib.NumberTheory.InertiaRadical
```

### 4. DkMath.Lib.NumberTheory.InertiaRadicalCorrection

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual finite radical quotients, bounded powers and visible fixed-root correction.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalGenerator

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalCorrection"

/-!
# 実際の有限根拡大を生成する慣性元と、同じ根を固定する補正元

生成元の存在を内部構成する。補正元が固定するのは指定した根の段であり、
野生合同部分群への所属や慣性内での p 冪根の存在は結論しない。
-/
namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 指標の核は、元の同じ根を固定する実際の慣性元からなる。 -/
theorem character_eq_one_iff_root_fixed (n : ℕ) (σ : inertiaSubgroupIn A ℚ) :
    character hp hq hpq A hA n σ = 1 ↔ σ.val (radical p q hp n) = radical p q hp n := by
  constructor
  · intro he
    exact (ratio_eq_one_iff hp hq σ.val n).mp (congrArg Units.val he)
  · intro he
    apply Units.ext
    exact (ratio_eq_one_iff hp hq σ.val n).mpr he

/-- 原始的な同じ指標値の有界な冪で、任意の同じ慣性値を表す。 -/
theorem image_eq_pow_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)))
    (τ : inertiaSubgroupIn A ℚ) :
    ∃ j < p ^ (n + 1), character hp hq hpq A hA (n + 1) τ = character hp hq hpq A hA (n + 1) γ ^ j := by
  let : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨j, hj, he⟩ := hprimitive.eq_pow_of_pow_eq_one (character_pow hp hq hpq A hA (n + 1) τ)
  exact ⟨j, hj, Units.ext he.symm⟩

/-- 同じ γ の冪からの補正は、同じ実際の慣性群に属し、指定した根を固定する。 -/
theorem correction_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)))
    (τ : inertiaSubgroupIn A ℚ) :
    ∃ j < p ^ (n + 1), ∃ ε : inertiaSubgroupIn A ℚ, τ = γ ^ j * ε ∧
      ε ∈ (character hp hq hpq A hA (n + 1)).ker ∧
      ε.val (radical p q hp (n + 1)) = radical p q hp (n + 1) := by
  obtain ⟨j, hj, he⟩ := image_eq_pow_of_primitive hp hq hpq A hA n γ hprimitive τ
  let ε := (γ ^ j)⁻¹ * τ
  have hε : character hp hq hpq A hA (n + 1) ε = 1 := by
    change character hp hq hpq A hA (n + 1) ((γ ^ j)⁻¹ * τ) = 1
    rw [map_mul, map_inv, map_pow, he, inv_mul_cancel]
  exact ⟨j, hj, ε, by simp [ε], hε, (character_eq_one_iff_root_fixed hp hq hpq A hA (n + 1) ε).mp hε⟩

/-- 実際の指標像は、同じ原始的な指標値が生成する巡回部分群。 -/
theorem range_eq_zpowers_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1))) :
    (character hp hq hpq A hA (n + 1)).range = Subgroup.zpowers (character hp hq hpq A hA (n + 1) γ) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨τ, rfl⟩ := hz
    obtain ⟨j, _, he⟩ := image_eq_pow_of_primitive hp hq hpq A hA n γ hprimitive τ
    exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), (zpow_natCast _ j).trans he.symm⟩
  · exact Subgroup.zpowers_le.mpr ⟨γ, rfl⟩

/-- 同じ有限根拡大の慣性核商の濃度は、正確に p^(n+1)。 -/
theorem quotient_card_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1))) :
    Nat.card ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) = p ^ (n + 1) := by
  have hc := Nat.card_congr (QuotientGroup.quotientKerEquivRange (character hp hq hpq A hA (n + 1))).toEquiv
  rw [range_eq_zpowers_of_primitive hp hq hpq A hA n γ hprimitive, Nat.card_zpowers] at hc
  exact hc.trans (orderOf_units.symm.trans hprimitive.eq_orderOf.symm)

/-- 同じ実際の根の段の慣性核商は巡回。 -/
theorem quotient_isCyclic_of_primitive (n : ℕ) (γ : inertiaSubgroupIn A ℚ)
    (hprimitive : IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1))) :
    IsCyclic ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) := by
  have hc : IsCyclic (character hp hq hpq A hA (n + 1)).range := by
    rw [range_eq_zpowers_of_primitive hp hq hpq A hA n γ hprimitive]
    infer_instance
  let := hc
  exact (QuotientGroup.quotientKerEquivRange (character hp hq hpq A hA (n + 1))).isCyclic.mpr inferInstance

/-- 一つの実際の γ が全正段の根拡大を生成し、全ての慣性元に有界な補正分解を与える。 -/
theorem exists_generator_corrections :
    ∃ γ : inertiaSubgroupIn A ℚ, ∀ n : ℕ,
      IsPrimitiveRoot (character hp hq hpq A hA (n + 1) γ : AlgebraicClosure ℚ) (p ^ (n + 1)) ∧
      Nat.card ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) = p ^ (n + 1) ∧
      IsCyclic ((inertiaSubgroupIn A ℚ) ⧸ (character hp hq hpq A hA (n + 1)).ker) ∧
      ∀ τ : inertiaSubgroupIn A ℚ, ∃ j < p ^ (n + 1), ∃ ε : inertiaSubgroupIn A ℚ, τ = γ ^ j * ε ∧
        ε ∈ (character hp hq hpq A hA (n + 1)).ker ∧
        ε.val (radical p q hp (n + 1)) = radical p q hp (n + 1) := by
  let γ := generator hp hq hpq A hA
  have hg := generator_primitive hp hq hpq A hA
  exact ⟨γ, fun n => ⟨hg n, quotient_card_of_primitive hp hq hpq A hA n γ (hg n),
    quotient_isCyclic_of_primitive hp hq hpq A hA n γ (hg n),
    correction_of_primitive hp hq hpq A hA n γ (hg n)⟩⟩

end
end DkMath.Lib.NumberTheory.InertiaRadical
```

### 5. DkMath.FLT.FreyRadicalGeneratorCertificate

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameStructureCertificate
import DkMath.Lib.NumberTheory.InertiaRadicalCorrection

#print "file: DkMath.FLT.FreyRadicalGeneratorCertificate"

/-!
# 実際の根の塔の生成元と、同じ Frey 慣性元の可視な補正

根拡大の有限核商 C は実際に巡回となる。以前の Frey 共通商 H とは区別する。
補正 ε は指定した根を固定するが、同じ H で消えることは今回まだ証明していない。
評価式の ε 項を残し、未証明の野生性・冪分解・巡回性を入力にしない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 実際に構成した同じ根の生成元と補正を、元の同じ共通商へ射影する。 -/
theorem ResidualCyclicStage.radical_generator_stage_correction (τ : inertiaSubgroupIn A ℚ) :
    let hp : p.Prime := Fact.out
    let γ := InertiaRadical.generator hp hq hqp.symm A hA
    ∃ j < p ^ (n + 3), ∃ ε : inertiaSubgroupIn A ℚ, τ = γ ^ j * ε ∧
      ε ∈ (InertiaRadical.character hp hq hqp.symm A hA (n + 3)).ker ∧
      ε.val (InertiaRadical.radical p q hp (n + 3)) = InertiaRadical.radical p q hp (n + 3) ∧
      T.fixedKernelCommonProjection A hp5 hq hqp haddr hA τ =
        T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ ^ j *
          T.fixedKernelCommonProjection A hp5 hq hqp haddr hA ε := by
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp hq hqp.symm A hA
  have hg := InertiaRadical.generator_primitive hp hq hqp.symm A hA (n + 2)
  obtain ⟨j, hj, ε, he, hker, hfix⟩ := InertiaRadical.correction_of_primitive hp hq hqp.symm A hA (n + 2) γ hg τ
  exact ⟨j, hj, ε, he, hker, hfix, by rw [he, map_mul, map_pow]⟩

end

noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害元の評価を、実際の根の生成元の寄与と、消していない補正の寄与へ分ける。 -/
theorem NarrowAbsorptionObstruction.radical_generator_error
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let hp : p.Prime := Fact.out
    let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
    let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
    ∃ j < p ^ (n + 3), ∃ ε : inertiaSubgroupIn A ℚ, ⟨τ, h.inertia⟩ = γ ^ j * ε ∧
      ε ∈ (InertiaRadical.character hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 3)).ker ∧
      ε.val (InertiaRadical.radical p q hp (n + 3)) = InertiaRadical.radical p q hp (n + 3) ∧
      T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩ =
        T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over γ ^ j *
          T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ε ∧
      h.fixedDifference hp5 = j • T.fixedKernelEvaluation A γ k + T.fixedKernelEvaluation A ε k := by
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
  let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  obtain ⟨j, hj, ε, he, hker, hfix, hproj⟩ := T.radical_generator_stage_correction A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩
  refine ⟨j, hj, ε, he, hker, hfix, hproj, ?_⟩
  calc
    h.fixedDifference hp5 = T.fixedKernelEvaluation A ⟨τ, h.inertia⟩ k :=
      (h.fixedKernelEvaluation_obstruction hp5).symm
    _ = Multiplicative.toAdd (T.fixedKernelCharacter A k (γ ^ j * ε)) := by rw [he]; rfl
    _ = j • T.fixedKernelEvaluation A γ k + T.fixedKernelEvaluation A ε k := by rw [map_mul, map_pow]; rfl

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
attribute [local instance 2000] Submodule.module
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
/-- 元の同じ算術証明書へ、実際の根の生成元・巡回核商・消していない補正評価を接続する。 -/
theorem residual_exists_radical_generator_error
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let hp : p.Prime := Fact.out
      let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
      let χ := InertiaRadical.character hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 3)
      let C := (inertiaSubgroupIn A ℚ) ⧸ χ.ker
      let k := T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
      IsPrimitiveRoot (χ γ : AlgebraicClosure ℚ) (p ^ (n + 3)) ∧ Nat.card C = p ^ (n + 3) ∧ IsCyclic C ∧
      ∃ j < p ^ (n + 3), ∃ ε : inertiaSubgroupIn A ℚ, ⟨τ, h.inertia⟩ = γ ^ j * ε ∧
        ε ∈ χ.ker ∧ ε.val (InertiaRadical.radical p q hp (n + 3)) = InertiaRadical.radical p q hp (n + 3) ∧
        T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩ =
          T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over γ ^ j *
            T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ε ∧
        h.fixedDifference hp5 = j • T.fixedKernelEvaluation A γ k + T.fixedKernelEvaluation A ε k := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp h.prime h.ne_torsion_prime.symm A h.lies_over
  have hg := InertiaRadical.generator_primitive hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 2)
  exact ⟨n, T, q, A, τ, y, h, hg,
    InertiaRadical.quotient_card_of_primitive hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 2) γ hg,
    InertiaRadical.quotient_isCyclic_of_primitive hp h.prime h.ne_torsion_prime.symm A h.lies_over (n + 2) γ hg,
    h.radical_generator_error hp5⟩

end
end DkMath.FLT.Frey.Source
```

