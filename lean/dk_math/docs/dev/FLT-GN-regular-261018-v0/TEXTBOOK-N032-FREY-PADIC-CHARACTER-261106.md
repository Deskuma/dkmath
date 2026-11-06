# NOTE-032 教科書：同じ巡回塔の連続 p 進指標と良還元での非自明性

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-TOWER-CHARACTER-261106.md`。

今回の2ステップは、①両立する有限単元値指標の実際の ℤₚˣ 値極限、
②同じ Frey 塔への適用と良還元 Frobenius の定量的な非自明性である。
以下の2ブロックは新規 production ファイルの全文であり、順にモジュールへ配置できる。
コードだけをコピーしても同定できるよう、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：有限指標から実際の p 進単元値指標を構成する

Γ を群、p を素数とし、実際の有限指標

    cₙ : Γ →* (ZMod (p^(n+1)))ˣ

と、標準剰余写像での隣接両立性を与える。
これは汎用構成の入力である。後半の Frey 適用では、前回構成した同じ塔の指標と
証明済みの両立性を代入し、新たな指標・両立性 provider は要求しない。

### 整数代表の極限

同じ g∈Γ について、法1の成分を0で補い、

    a₀=0, aₙ₊₁=(cₙ(g)).val

という整数列を取る。隣接両立性から pⁱ∣aᵢ₊₁−aᵢ が従う。
Mathlib の `PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub` によって Cauchy 列となり、
`PadicInt.ofIntSeq` で実際の ℤₚ の元 `value g` を構成する。
`PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub` を使い、

    value(g) mod p^(n+1) = cₙ(g)

を証明する。極限の存在やその剰余公式を新しい仮定として追加しない。

全ての正冪剰余で等しい p 進整数は等しい。法1の成分は自明なので、
`PadicInt.ext_of_toZModPow` から正冪のみの外延性を得る。
それを使って value(1)=1、value(gh)=value(g)value(h) を証明する。
Γ の逆元を写して可逆性を得て、`character : Γ →* ℤ_[p]ˣ` を構成する。
同じ有限剰余を持つ単元値準同型の一意性も証明する。

### 連続性と固定性

各有限段の核が開なら、極限指標は連続である。
任意の ε>0 に対し p^(−(k+1))<ε となる k を選ぶ。
第 k 段の開核内では極限指標の剰余が1なので、その値と1の差は p^(k+1) の倍数となる。
従って p 進ノルムは p^(−(k+1)) 以下であり、単位元での連続性が得られる。
準同型の単位元での連続性から全域での連続性を導く。

これは **無限段の核が開** という主張ではない。
極限指標値1と「全ての有限指標値が1」の同値は、正確な剰余公式と外延性から導く。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Group.Neighborhood
import Mathlib.Topology.Algebra.Group.Units

#print "file: DkMath.Lib.Algebra.PadicCharacterLimit"

/-!
# 両立する有限単元値指標の実際の p 進極限

第 n 段の法は p^(n+1)。法1の第0成分を補って整数代表の Cauchy 列を作る。
極限の各剰余が元の指標であることから乗法性・一意性を証明する。
有限段の開核から極限の連続性を導く。無限段の核が開とは主張しない。
-/

namespace DkMath.Lib.Algebra.PadicCharacterLimit

noncomputable section
variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ]
    (c : ∀ n : ℕ, Γ →* (ZMod (p ^ (n + 1)))ˣ)
    (hc : ∀ n g, Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1)))).toMonoidHom (c (n + 1) g) = c n g)

/-- 法1の成分を0とした、同じ有限指標の非負整数代表。 -/
def representatives (g : Γ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => (c n g : ZMod (p ^ (n + 1))).val

include hc in
/-- 隣接両立性が、整数代表の差の p 冪可除性を与える。 -/
theorem representatives_dvd (g : Γ) (i : ℕ) :
    (p : ℤ) ^ i ∣ representatives c g (i + 1) - representatives c g i := by
  cases i with
  | zero => simp
  | succ i =>
    rw [← Int.natCast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub]
    have h := congrArg Units.val (hc i g)
    change ZMod.castHom _ _ (c (i + 1) g : ZMod (p ^ (i + 1 + 1))) = _ at h
    rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
    simpa only [representatives, Int.cast_natCast, ZMod.natCast_zmod_val, sub_eq_zero] using h

/-- 実際の整数 Cauchy 列の p 進極限。 -/
def value (g : Γ) : ℤ_[p] :=
  PadicInt.ofIntSeq (representatives c g)
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (representatives_dvd c hc g))

/-- 各有限剰余は、元の同じ指標そのものである。 -/
theorem value_mod (n : ℕ) (g : Γ) :
    PadicInt.toZModPow (n + 1) (value c hc g) = (c n g : ZMod (p ^ (n + 1))) := by
  have h := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (representatives_dvd c hc g) (n + 1)
  simpa only [value, representatives, Int.cast_natCast, ZMod.natCast_zmod_val] using h

/-- 全ての正冪剰余が同じなら p 進整数は同じ。法1の成分は自明。 -/
theorem ext_positive {x y : ℤ_[p]}
    (h : ∀ n, PadicInt.toZModPow (n + 1) x = PadicInt.toZModPow (n + 1) y) : x = y := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  cases n with
  | zero =>
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n => exact h n

/-- 剰余ごとの乗法性から作った実際の p 進準同型。 -/
def valueHom : Γ →* ℤ_[p] where
  toFun := value c hc
  map_one' := by
    apply ext_positive
    intro n
    rw [value_mod, map_one, map_one, Units.val_one]
  map_mul' g h := by
    apply ext_positive
    intro n
    rw [value_mod, map_mul, map_mul, value_mod, value_mod, Units.val_mul]

/-- 群の逆元を使って単元へ持ち上げた実際の極限指標。 -/
def character : Γ →* ℤ_[p]ˣ := (valueHom c hc).toHomUnits

/-- 極限指標の有限段への単元値剰余公式。 -/
theorem character_mod (n : ℕ) (g : Γ) :
    Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (character c hc g) = c n g := by
  apply Units.ext
  exact value_mod c hc n g

/-- 同じ有限指標を持つ p 進単元値指標は一意。 -/
theorem character_unique (d : Γ →* ℤ_[p]ˣ)
    (hd : ∀ n g, Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (d g) = c n g) :
    character c hc = d := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply ext_positive
  intro n
  exact (value_mod c hc n g).trans (congrArg Units.val (hd n g)).symm

/-- 極限指標値1は、すべての有限段の指標値1と同値。 -/
theorem character_eq_one_iff (g : Γ) : character c hc g = 1 ↔ ∀ n, c n g = 1 := by
  constructor
  · intro h n
    rw [← character_mod c hc n g, h, map_one]
  · intro h
    apply Units.ext
    apply ext_positive
    intro n
    change PadicInt.toZModPow (n + 1) (value c hc g) = PadicInt.toZModPow (n + 1) 1
    rw [value_mod, h n, map_one, Units.val_one]

/-- 各有限段の開核から極限指標の連続性を証明する。無限段の開核は結論しない。 -/
theorem character_continuous [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hopen : ∀ n, IsOpen ((c n).ker : Set Γ)) : Continuous (character c hc) := by
  apply Continuous.of_coeHom_comp
  apply continuous_of_continuousAt_one
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  have hsmall : (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) < ε := by
    refine lt_of_le_of_lt ?_ hk
    gcongr
    · exact_mod_cast (Fact.out : p.Prime).one_le
    · omega
  filter_upwards [(hopen k).mem_nhds ((c k).ker.one_mem)] with g hg
  apply lt_of_le_of_lt _ hsmall
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero]
  change PadicInt.toZModPow (k + 1) (value c hc g) =
    PadicInt.toZModPow (k + 1) (value c hc 1)
  rw [value_mod, value_mod, map_one, Units.val_one]
  exact congrArg Units.val hg

end
end DkMath.Lib.Algebra.PadicCharacterLimit
```

## ステップ2：同じ Frey 塔へ適用し、Frobenius の非自明性を導く

以前の条件付き塔を構成した Source、残余直線 L、rootField、hclass、全段 hbad を保持する。
新しい別の塔や独立な指標を選ばず、同じ `residualCyclicTowerCharacter` を汎用構成へ渡す。
隣接両立性は以前の `residualCyclicTowerCharacter_compatible` から、
有限段の開核は同じ実際の全捩れ表現の開核から内部供給する。

得られる `residualPadicTowerCharacter` は実際の連続準同型 Gℚ→ℤₚˣ であり、
各 n で標準の `toZModPow (n+1)` を適用すると元の有限指標を回収する。
mod p 成分は、法 p¹ から法 p への標準写像も明示して、元の同じ円分指標と一致する。
高位成分まで p 進円分指標と一致するとは証明していない。

また、同じ点群内の実際の塔の合併について、

    χ∞(σ)=1 ↔ 合併内の全ての点 x に対して σ(x)=x

が成立する。合併所属を実際の有限段所属に戻し、前段の有限固定性判定を使う。

### 良還元点数による定量的な非自明性

同じ良還元素点 ℓ≠p、同じ付値環 A と実際の Frobenius 元 σ を取る。
N=#E(𝔽ℓ) とすると、前回の定理は

    χₙ(σ)=1 → p^(n+1)≤N

だった。従って p^(n+1)>N なら χₙ(σ)≠1 である。
素数 p≥2 では n<p^(n+1) なので、特に n≥N の全段で非自明となる。
この有限段の定理は、既存段 T さえあれば hclass/hbad/hchar を追加要求しない。

同じ条件付き無限塔なら段 N を使用できる。
χ∞(σ)=1 ならその有限剰余 χ_N(σ)=1 となり、上の非自明性に反する。
従って同じ良還元 Frobenius について χ∞(σ)≠1 と証明できる。

**非自明性は矛盾ではない。**
これは χ∞(σ)=1 を算術的に証明したことではなく、そのような全点固定を仮定する
論証が必ず追加の算術を必要とすることを示す結果である。
良還元素点やその Frobenius の存在をここで新たに証明しているわけでもない。
全て同じ実際の素点・付値・Frobenius の入力を保持する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclicTowerCharacter
import DkMath.Lib.Algebra.PadicCharacterLimit

#print "file: DkMath.FLT.FreyPadicTowerCharacter"

/-!
# 同じ巡回塔の連続 p 進単元値指標と良還元での非自明性

有限指標の両立性から実際の ℤₚˣ 値指標を構成する。
hclass と全段 hbad は従来のまま保持する。良還元では大きい有限段の
Frobenius 指標が非自明となる。非自明性自体は矛盾ではない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation DkMath.Lib.RepresentationTheory
noncomputable section

variable {p : ℕ} [Fact p.Prime] {S : Source p}
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 良還元の有限点数より大きい同じ段は Frobenius に全点固定されない。 -/
theorem ResidualCyclicStage.character_ne_one_of_good_bound (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)
    (hlarge : S.goodReductionPointCount ell < p ^ (n + 1)) : T.character σ ≠ 1 := by
  intro h
  exact (not_le_of_gt hlarge) (T.card_le_good_points_of_character_one hell hellp hgood A hA σ hσ h)

/-- 点数 N 以下でない段 n≥N なら、素数 p の増大から非自明性が従う。 -/
theorem ResidualCyclicStage.character_ne_one_of_good_count (T : S.ResidualCyclicStage L n)
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell)
    (hn : S.goodReductionPointCount ell ≤ n) : T.character σ ≠ 1 := by
  apply T.character_ne_one_of_good_bound hell hellp hgood A hA σ hσ
  exact lt_of_le_of_lt hn (lt_trans (Nat.lt_succ_self n) (Nat.lt_pow_self (Fact.out : p.Prime).one_lt))

end

section Tower
noncomputable section
open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "chars" => S.residualCyclicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "compat" => S.residualCyclicTowerCharacter_compatible L hline hcofixed hζ hp5 hclass hbad
local notation "towerUnion" => S.residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad

/-- 同じ条件付き塔の有限指標から構成した実際の p 進単元値指標。 -/
def residualPadicTowerCharacter : Field.absoluteGaloisGroup ℚ →* ℤ_[p]ˣ :=
  PadicCharacterLimit.character chars compat

local notation "padicChar" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 元の有限指標を、標準剰余写像で正確に回収する。 -/
theorem residualPadicTowerCharacter_mod (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (padicChar σ) = chars n σ :=
  PadicCharacterLimit.character_mod chars compat n σ

/-- 有限段の実際の開核から、構成した極限指標は連続となる。 -/
theorem residualPadicTowerCharacter_continuous : Continuous padicChar :=
  PadicCharacterLimit.character_continuous chars compat (fun n => (tower n).character_kernel_isOpen)

/-- 正確な mod p 成分は同じ元の円分指標。高位成分が円分指標とは主張しない。 -/
theorem residualPadicTowerCharacter_mod_prime (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map ((ZMod.castHom (dvd_pow_self p (by omega : 0 + 1 ≠ 0)) (ZMod p)).comp
      (PadicInt.toZModPow 1)).toMonoidHom (padicChar σ) =
      CyclotomicRootModule.cyclotomicCharacter p σ := by
  change Units.map (ZMod.castHom (dvd_pow_self p (by omega : 0 + 1 ≠ 0)) (ZMod p)).toMonoidHom
    (Units.map (PadicInt.toZModPow (0 + 1)).toMonoidHom (padicChar σ)) = _
  rw [S.residualPadicTowerCharacter_mod L hline hcofixed hζ hp5 hclass hbad]
  exact (tower 0).character_mod_prime hline hcofixed σ

/-- 極限指標値1は、同じ実際の合併の全点固定と正確に同値。 -/
theorem residualPadicTowerCharacter_eq_one_iff (σ : Field.absoluteGaloisGroup ℚ) :
    padicChar σ = 1 ↔ ∀ x ∈ towerUnion, pointAction S.rationalCurve σ x = x := by
  change PadicCharacterLimit.character chars compat σ = 1 ↔ _
  rw [PadicCharacterLimit.character_eq_one_iff]
  constructor
  · intro h x hx
    obtain ⟨n, hn⟩ := (S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mp hx
    exact ((tower n).character_eq_one_iff σ).mp (h n) x hn
  · intro h n
    apply ((tower n).character_eq_one_iff σ).mpr
    intro x hx
    exact h x ((S.mem_residualCyclicTowerUnion L hline hcofixed hζ hp5 hclass hbad x).mpr ⟨n, hx⟩)

/-- 同じ良還元 Frobenius の極限指標は非自明。これは矛盾を与える定理ではない。 -/
theorem residualPadicTowerCharacter_frobenius_ne_one
    {ell : ℕ} (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : ValuationInertia.LiesOverPrime A ell)
    (σ : Field.absoluteGaloisGroup ℚ) (hσ : ValuationFrobenius.IsFrobeniusAt A σ ell) :
    padicChar σ ≠ 1 := by
  intro h
  have hn := (tower (S.goodReductionPointCount ell)).character_ne_one_of_good_count
    hell hellp hgood A hA σ hσ le_rfl
  apply hn
  have hm := S.residualPadicTowerCharacter_mod L hline hcofixed hζ hp5 hclass hbad
    (S.goodReductionPointCount ell) σ
  rw [h, map_one] at hm
  exact hm.symm

end
end Tower
end DkMath.FLT.Frey.Source
```

## 回帰例と検証

`DkMathTest.FLT.FreyPadicTowerCharacter` は、具体的な5進単元群 Γ=ℤ₅ˣ とその標準有限剰余を使う。
有限段の両立性を標準剰余写像の合成公式から証明し、構成した極限が恒等準同型となることを確認する。
特定の点だけでなく、元の任意の5進単元が全ての有限剰余から復元される。
第4冪での回収も確認する。

さらに、(ZMod 25)ˣ の実際の単元6（逆元21）について、mod 5 で1だが mod 25 では1でないことを確認する。
これにより「mod p で円分指標と一致する」ことを高位成分の固定性へ取り違えない。
同じ抽象 Source の既存段では、段番号 n≥N からの非自明性と、実際に動く点の存在を確認する。

主要13宣言の公理報告、型・構成子・不透明証明本体を含む再帰依存監査、10件の公開入力監査を追加する。
汎用構成の両立性 hc/開核 hopen は明示し、実際の Frey 適用では前段から供給する。
Frey の極限・連続性・非自明性に hlimit/hcont/hchar/hfixed を新たに要求しない。
同じ実際の hclass と全段 hbad は要求する。

検証記録：`evidence/validation-note032-frey-padic-character.txt`。
ルート公開、通常のテスト入口、root smoke、教科書2ブロックの全文一致と個別コンパイルも確認する。

## 残る境界

- 同じ円分類群商の特定 ω² 成分の消滅 hclass は未証明。
- 全ての適格な段での共鳴素点条件 hbad、または反復に十分な保存性は未証明。
- 最終矛盾に必要な Galois 作用の局所・大域算術は未完成。
- 連続 ℤₚˣ 値指標は今回実際に構成したが、Tate 加群の階数1部分加群やイソジェニーの構成はしていない。
- Frobenius の特性多項式を実際の高位捩れ作用へ接続する定理も今回追加していない。

**今回の2ステップは完成。一般 hno は引き続き未完成である。**
使用する極限・p 進ノルム・剰余外延性はローカル Mathlib の API、
有限段の作用・開核・円分一致・還元上界は既存の DkMath の証明を使う。
外部の類群消滅定理や有理巡回イソジェニー分類は移植・import していない。
