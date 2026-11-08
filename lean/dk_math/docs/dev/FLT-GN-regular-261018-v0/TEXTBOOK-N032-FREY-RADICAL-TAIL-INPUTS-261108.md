# NOTE-032 教科書 — 核比較の同値条件と tail 体の実際の剰余冪根入力

日付: 2026-11-08。今回は求める核包含の同値条件を固定し、模範解答の tail 算術が消費する
剰余冪根・有限位数・固定体内の根の1の持ち上げ・単元冪根近似を5ステップ実装した。
**核包含そのもの、正確な体内 p 乗根、tail の p 可除性は今回も未証明である。**

後半の5つの Lean ブロックは対応する production ソースの全文。
各 import 群直後の正確な `#print "file: モジュール名"` を省略しない。
既存 DkMath の Lake 環境でそれぞれ別ファイルへコピペして検査できる。
第1段階は Frey 固有の同値条件で DkMath.FLT、残る4段階は Source に依存しない DkMath.Lib。

## 1. 二つの実際の核の比較を、同じ評価値で特定する

元の慣性群 I、根の段の指標 χ_(n+3)、Frey 共通商への射影 π:I→H、
元の係数核 K と評価 ev_σ:K→F をそのまま使う。
忠実な H の値写像から

    σ∈ker π ↔ ∀k∈K, ev_σ(k)=0

を証明する。さらに任意の k が元の有限捩れ点の連結像で表せることから

    σ∈ker π ↔ ∀x∈E[p^(n+2)], c_x(σ)=1

も得る。c_x は元の同じ固定部分群値の差分指標である。
根指標の核が同じ根を固定する慣性元であることと合わせると、目標の

    ker χ_(n+3)≤ker π

は「同じ根を固定する全ての慣性元について、全 K の評価が零」、
または「全ての元の有限捩れ点の固定差分が1」という命題と同値になる。
核包含を新しい入力にはしていない。ここで証明したのは同値条件であり、包含の算術的証明ではない。

## 2. 実際の剰余冪根と、非零剰余の有限位数

代数閉体 L の付値環 A と正の n について、任意の剰余 c の持ち上げ x を取り、
代数閉性で β^n=x を選ぶ。x が整なら β も同じ A に入ることを付値で証明し、
β の剰余が c の n 乗根となることを示した。

    ∀c∈κ(A), ∃y∈κ(A), y^n=c

これは全正冪写像の全射性であり、剰余体が代数閉という型クラス全体を構成したという主張ではない。

L が ℚ 上代数的で A が q 上にある場合には、非零 c の有限位数も内部証明する。
x を消す整数多項式の原始部分を取ると、その q 還元は非零のまま c を消す。
c は有限体 ZMod q 上代数的となり、c を生成する部分代数は有限。
その中で冪が重複するため、c≠0 を使って

    ∃N>0, c^N=1

が従う。剰余標数 q は同じ住所と q の素数性から供給する。
剰余体全体の有限性は結論していない。実際の代数閉包での適用に外部の torsion provider は要らない。

## 3. 剰余の p 冪根の1を、同じ慣性固定体へ持ち上げる

K₀=ℚ̄^I を実際の中間体として定義する。
単元指数 m の根の1は、同じ剰余を持てば一致する。
証明では差の因数分解と局所環の単元性を使い、指数の単元ガードを保持する。

一つの原始 m 乗根の冪は m 個あり、その還元は全て異なる。
剰余体上の m 乗根の1の個数は高々 m なので、全ての剰余根の1が持ち上がる。

p≠q と同じ q 上の住所から m=p^i が単元であることを証明し、
代数閉性から原始根を内部選択する。慣性は p 冪根の1を固定するため、持ち上げ ζ は同じ K₀ に属する。

    y^(p^i)=1 → ∃ζ∈K₀, ζ^(p^i)=1, ζ∈A, residue(ζ)=y

根の1の持ち上げと慣性固定性を、新しい算術入力にしない。

## 4. K₀ を含む中間体の単元 p 乗根近似

実際の中間体 E⊆ℚ̄ が K₀ を含むとする。
A を E に引き戻した付値環 B と、その単元 u を取る。
第2段階で residue(u) の p 乗根 y と有限位数 N を供給し、N=p^a m、p∤m と分解する。
互いに素な部分は residue(u) の冪として表し、残る p-primary な根の1を第3段階で K₀ 内へ持ち上げる。
これらを掛け合わせた同じ E の元 z は

    z^p-u∈maximalIdeal B

を満たす。u の単元性から z^p も単元となり、z 自身も単元と証明した。

公開入力は E と実際の包含 K₀≤E、u とその単元性、元の素数と住所だけ。
剰余冪根、剰余の有限位数、根の1の持ち上げは全て証明済みの定理から内部供給する。
ここで得たのは **剰余合同を満たす単元近似根**。
**z^p=u という正確な体内冪根を証明したものではない。**

## 5. 元の全 q 根を含む実際の tail 体への供給

模範解答に対応する中間体を、同じ対象から実際に構成する。

    E∞=ℚ(K₀ ∪ {α | ∃n, α^(p^n)=q}) ⊆ ℚ̄

K₀≤E∞、全ての同じ q の p 冪根の所属を証明し、前回構成した互換根の塔を
同じ E∞ の元として保持する。

    ∃α:ℕ→E∞, α₀=q, α_(n+d)^(p^d)=α_n, α_n^(p^n)=q

剰余の p 冪根の1も同じ E∞ 内へ持ち上がる。
さらに第4段階の構造的包含を、ここでは定義から証明して供給するので、
E∞ の全単元に対する単元 p 乗根近似を内部構成できる。
E∞ を含む任意の同じ中間体についてもこの近似入力を供給する。
有限次拡大という仮定は近似には不要である。

これで模範の tail 体における剰余側の入力は実際の定理になった。
ただし体内の全非零元が p 乗根を持つという結論ではない。
非単元の値群の処理、正確な根の持ち上げ、慣性群内の冪根の存在への輸送は別途必要。

## 模範解答との照合と次の証明境界

ローカル模範解答の `exists_pow_eq_residue`、`exists_pow_eq_one_residue`、
`exists_mem_fixedField_residue_eq`、`exists_pow_sub_mem_of_lifts` と、
それらを消費する `hdiv_Kinf` を読んで分解した。
参照 HEAD は 115356cbc627159d0d16add0da6e9a2bb3655ed8。
4つの Lib 適応には Apache-2.0、元ソース、コミット、変更点、既存 LICENSE/NOTICE を保持する。
P2M/P2MW と FLT 終点は import しない。

今回 hdiv_Kinf 自体や、その先の慣性 tail の p 可除性は移植していない。
剰余近似から正確な冪根へ進むには、単根持ち上げに必要な付値環の安定性・henselian 性を実証明で供給する必要がある。
一般の非零元には値群の p 可除性の処理も必要となる。
さらに有限 Galois 商の指数の p 非可除性と、位相的極限を使う群内冪根の構成が残る。
これらの仮定を provider として足して今回の成果にはしていない。

**核比較の同値条件と、実際の tail 体の剰余冪根入力は完成。核比較と正確な tail 冪根は未完成。**
Frey 共通商の巡回性、同じ γ の単一評価、大域的算術排除、hclass の供給も未完成。
**無条件の一般 hno は引き続き未完成である。**

## 検証の範囲

ZMod9 の単元 u=4 と近似根 z=1 で、3 を法とする合同と正確な冪根方程式を区別する。
指数2では根の1の還元が単射となる有限例、指数3では異なる根が同じ剰余を持つ反例を検査し、
単元指数・p≠q のガードを省略しない。
二座標写像で、根側の核包含が他方の核へ自動的には成立しないことも保持する。

新規25宣言の再帰依存監査、25件の公開入力監査、公理出力と各 facade/root/通常入口を確認する。
検証結果は `evidence/validation-note032-frey-radical-tail-inputs.txt`。
参照 SHA-256 は `evidence/note032-frey-radical-tail-inputs-reference-audit.json`。

## コピペ用 Lean 全文

### 1. DkMath.FLT.FreyRadicalKernelComparison

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalGeneratorCertificate

#print "file: DkMath.FLT.FreyRadicalKernelComparison"

/-!
# 根核と Frey 共通商核の比較の、同じ値による同値条件

核包含を仮定も結論もしない。実際に必要な算術命題を、全核元の評価、
または元の有限捩れ点の固定差分という同値な形で特定する。
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

/-- 元の共通射影の核への所属は、同じ全核元の評価の零性と同値。 -/
theorem ResidualCyclicStage.mem_commonProjection_kernel_iff_evaluations (σ : inertiaSubgroupIn A ℚ) :
    σ ∈ (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ k : T.fixedH1CoefficientKernel A, T.fixedKernelEvaluation A σ k = 0 := by
  change T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ = 1 ↔ _
  constructor
  · intro he k
    have hv := congrArg (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA) he
    rw [map_one] at hv
    exact congrArg Multiplicative.toAdd (congrFun hv k)
  · intro he
    apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
    rw [map_one]
    apply funext
    intro k
    exact congrArg Multiplicative.ofAdd (he k)

/-- 同じ共通核への所属は、元の全有限捩れ点の固定差分が1になることと同値。 -/
theorem ResidualCyclicStage.mem_commonProjection_kernel_iff_fixed_differences (σ : inertiaSubgroupIn A ℚ) :
    σ ∈ (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
        T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ = 1 := by
  rw [T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ]
  constructor
  · intro he x
    have hv := he (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x)
    rw [T.fixedKernelEvaluation_coset A hp5 hq hqp haddr hA x σ] at hv
    exact congrArg Multiplicative.ofAdd hv
  · intro he k
    obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
    rw [T.fixedKernelEvaluation_coset A hp5 hq hqp haddr hA x σ]
    exact congrArg Multiplicative.toAdd (he x)

/-- 求める核包含は「同じ根を固定する元の全評価が零」という算術命題と同値。 -/
theorem ResidualCyclicStage.radical_kernel_comparison_iff_evaluations :
    (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ σ : inertiaSubgroupIn A ℚ,
        σ.val (InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3)) =
          InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3) →
        ∀ k : T.fixedH1CoefficientKernel A, T.fixedKernelEvaluation A σ k = 0 := by
  constructor
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ).mp
    exact he ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mpr hs)
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ).mpr
    exact he σ ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mp hs)

/-- 同じ核包含の、元の有限捩れ点の差分だけを使う同値な形。 -/
theorem ResidualCyclicStage.radical_kernel_comparison_iff_fixed_differences :
    (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker ↔
      ∀ σ : inertiaSubgroupIn A ℚ,
        σ.val (InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3)) =
          InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3) →
        ∀ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
          T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ = 1 := by
  constructor
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_fixed_differences A hp5 hq hqp haddr hA σ).mp
    exact he ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mpr hs)
  · intro he σ hs
    apply (T.mem_commonProjection_kernel_iff_fixed_differences A hp5 hq hqp haddr hA σ).mpr
    exact he σ ((InertiaRadical.character_eq_one_iff_root_fixed (Fact.out : p.Prime) hq hqp.symm A hA (n + 3) σ).mp hs)

end
end DkMath.FLT.Frey.Source
```

### 2. DkMath.Lib.NumberTheory.AlgebraicResiduePowers

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual q-address and algebraicity class supply residue characteristic and torsion.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalGenerator
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Algebra.ZMod

#print "file: DkMath.Lib.NumberTheory.AlgebraicResiduePowers"

/-!
# tail の根構成に使う、実際の剰余冪根と有限位数

剰余の冪根の存在、非零剰余の有限位数を外部 provider にしない。
後者は整数の原始多項式を q で還元し、実際の有限部分代数を構成して証明する。
-/
namespace DkMath.Lib.NumberTheory.AlgebraicResidue
open Polynomial
noncomputable section
variable {L : Type} [Field L]

/-- 代数閉体の付値剰余体では、全ての正の冪写像が全射。 -/
theorem power_surjective [IsAlgClosed L] (P : ValuationSubring L) (n : ℕ) (hn : n ≠ 0)
    (c : IsLocalRing.ResidueField P) : ∃ y : IsLocalRing.ResidueField P, y ^ n = c := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) (Nat.pos_of_ne_zero hn)
  have hβP : β ∈ P := by
    by_contra h
    have h1 : 1 < P.valuation β := by rwa [← not_le, P.valuation_le_one_iff]
    have h2 : P.valuation β ^ n ≤ 1 := by rw [← map_pow, hβ]; exact P.valuation_le_one x
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have h3 : P.valuation β ≤ P.valuation β ^ (k + 1) := by
      rw [pow_succ]
      calc P.valuation β = 1 * P.valuation β := (one_mul _).symm
        _ ≤ P.valuation β ^ k * P.valuation β := mul_le_mul' (one_le_pow_of_one_le' h1.le k) le_rfl
    exact absurd (lt_of_lt_of_le h1 (h3.trans h2)) (lt_irrefl 1)
  refine ⟨IsLocalRing.residue P ⟨β, hβP⟩, ?_⟩
  rw [← map_pow]
  congr 1
  exact Subtype.ext hβ

/-- ℚ 上代数的な体の q 上の剰余体では、非零元の乗法位数は有限。 -/
theorem nonzero_finite_order [CharZero L] [Algebra.IsAlgebraic ℚ L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hA : ValuationInertia.LiesOverPrime P q)
    (c : IsLocalRing.ResidueField P) (hc : c ≠ 0) : ∃ N : ℕ, 0 < N ∧ c ^ N = 1 := by
  classical
  have hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    exact hA
  have hqκ : (q : IsLocalRing.ResidueField P) = 0 := by
    have : IsLocalRing.residue P (q : P) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hq
    simpa using this
  have : Fact q.Prime := ⟨hqp⟩
  have : CharP (IsLocalRing.ResidueField P) q := (CharP.charP_iff_prime_eq_zero hqp).mpr hqκ
  let : Algebra (ZMod q) (IsLocalRing.ResidueField P) := ZMod.algebra _ q
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective c
  have halgZ : IsAlgebraic ℤ (x : L) := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨g, hg0, hgx⟩ := halgZ
  set pp : ℤ[X] := g.primPart with hppdef
  have hppL : aeval (x : L) pp = 0 := by
    have h := hgx
    rw [g.eq_C_content_mul_primPart, map_mul, aeval_C] at h
    refine (mul_eq_zero.mp h).resolve_left ?_
    have : g.content ≠ 0 := mt Polynomial.content_eq_zero_iff.mp hg0
    exact (map_ne_zero_iff (algebraMap ℤ L) (algebraMap ℤ L).injective_int).mpr this
  have hppP : aeval x pp = 0 := by
    have h := Polynomial.aeval_algHom_apply (P.subtype.toIntAlgHom) x pp
    apply P.subtype_injective
    rw [map_zero]
    change P.subtype.toIntAlgHom (aeval x pp) = 0
    rw [← h]
    exact hppL
  have hppκ : aeval (IsLocalRing.residue P x) pp = 0 := by
    have h := Polynomial.aeval_algHom_apply ((IsLocalRing.residue P).toIntAlgHom) x pp
    refine h.trans ?_
    rw [hppP, map_zero]
  set h : (ZMod q)[X] := pp.map (Int.castRingHom (ZMod q)) with hhdef
  have hh0 : h ≠ 0 := by
    intro h0
    have hdvd : C (q : ℤ) ∣ pp := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have : (Int.castRingHom (ZMod q)) (pp.coeff i) = 0 := by
        rw [← coeff_map, ← hhdef, h0, coeff_zero]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    have hu : IsUnit (q : ℤ) := (isPrimitive_iff_isUnit_of_C_dvd.mp g.isPrimitive_primPart) _ hdvd
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact hqp.one_lt.ne' (by exact_mod_cast h1)
    · have : (0 : ℤ) ≤ q := Int.natCast_nonneg q
      omega
  have hhc : aeval (IsLocalRing.residue P x) h = 0 := by
    rw [hhdef, aeval_def, eval₂_map]
    have : (algebraMap (ZMod q) (IsLocalRing.ResidueField P)).comp (Int.castRingHom (ZMod q)) =
        algebraMap ℤ (IsLocalRing.ResidueField P) := RingHom.ext_int _ _
    rw [this, ← aeval_def, hppκ]
  have halgc : IsAlgebraic (ZMod q) (IsLocalRing.residue P x) := ⟨h, hh0, hhc⟩
  have hint : IsIntegral (ZMod q) (IsLocalRing.residue P x) :=
    IsAlgebraic.isIntegral (K := ZMod q) (A := IsLocalRing.ResidueField P) halgc
  set S := (Algebra.adjoin (ZMod q) {IsLocalRing.residue P x}).toSubmodule with hS
  have : Module.Finite (ZMod q) S := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : Finite S := Module.finite_of_finite (ZMod q)
  have hmem : ∀ i : ℕ, IsLocalRing.residue P x ^ i ∈ S := fun i =>
    show IsLocalRing.residue P x ^ i ∈ Algebra.adjoin (ZMod q) {IsLocalRing.residue P x} from
      Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ _) i
  obtain ⟨i, j, hij, hpow⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => (⟨_, hmem i⟩ : S))
  have hpow' : IsLocalRing.residue P x ^ i = IsLocalRing.residue P x ^ j := congrArg Subtype.val hpow
  have key : ∀ i j : ℕ, i < j → IsLocalRing.residue P x ^ i = IsLocalRing.residue P x ^ j →
      ∃ N : ℕ, 0 < N ∧ IsLocalRing.residue P x ^ N = 1 := by
    intro i j hlt heq
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have hsplit : IsLocalRing.residue P x ^ j = IsLocalRing.residue P x ^ i * IsLocalRing.residue P x ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hsplit] at heq
    have hi0 : IsLocalRing.residue P x ^ i ≠ 0 := pow_ne_zero _ hc
    exact (mul_right_injective₀ hi0 (heq.symm.trans (mul_one _).symm))
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt hpow'
  · exact key j i hlt hpow'.symm

end
end DkMath.Lib.NumberTheory.AlgebraicResidue
```

### 3. DkMath.Lib.NumberTheory.InertiaResidueRootLifts

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual DkMath inertia fixed field and internally supplied prime-power root lifts.
-/

import DkMath.Lib.NumberTheory.AlgebraicResiduePowers
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

#print "file: DkMath.Lib.NumberTheory.InertiaResidueRootLifts"

/-!
# 元の慣性固定体にある根の1で、実際の剰余の p 冪根の1を持ち上げる

還元の単射性と根数上界を使う。持ち上げや慣性固定性を provider にしない。
-/
namespace DkMath.Lib.NumberTheory.InertiaResidue
open ValuationInertia IsLocalRing Finset
noncomputable section
/-- 単元指数の根の1は、同じ剰余を持てば一致する。 -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : R)) (x y : R) (hx : x ^ m = 1) (hy : y ^ m = 1)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  have htel : (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) * (x - y) = 0 := by
    rw [geom_sum₂_mul, hx, hy, sub_self]
  have hres : IsLocalRing.residue R x = IsLocalRing.residue R y := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hxy
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy hm
  have hS : IsUnit (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff]
    have hr : IsLocalRing.residue R (∑ i ∈ range m, x ^ i * y ^ (m - 1 - i)) =
        (m : IsLocalRing.ResidueField R) * IsLocalRing.residue R y ^ (m - 1) := by
      rw [map_sum]; simp only [map_mul, map_pow, hres]; exact geom_sum₂_self _ _
    rw [hr]
    have h1 : IsUnit (m : IsLocalRing.ResidueField R) := by
      simpa using hmu.map (IsLocalRing.residue R)
    exact (h1.mul ((hyu.map (IsLocalRing.residue R)).pow (m - 1))).ne_zero
  exact sub_eq_zero.mp ((hS.mul_right_eq_zero).mp htel)

variable {L : Type*} [Field L]

/-- 非零指数の根の1は、同じ付値環に属する。 -/
theorem root_mem (A : ValuationSubring L) {μ : L} {m : ℕ} (hm : m ≠ 0) (hμ : μ ^ m = 1) : μ ∈ A := by
  have hv : A.valuation μ = 1 := by
    apply pow_left_injective (M := A.ValueGroup) hm
    change A.valuation μ ^ m = 1 ^ m
    rw [← map_pow, hμ, map_one, one_pow]
  exact (A.valuation_le_one_iff μ).mp hv.le

/-- 根の1を実際の付値剰余体へ写す。 -/
def residueRoot (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (ζ : L) (hζ : ζ ^ m = 1) : IsLocalRing.ResidueField A :=
  IsLocalRing.residue A ⟨ζ, root_mem A hm hζ⟩

/-- 同じ剰余の値も同じ冪で1となる。 -/
theorem residueRoot_pow (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (ζ : L) (hζ : ζ ^ m = 1) : (residueRoot A hm ζ hζ) ^ m = 1 := by
  rw [residueRoot, ← map_pow, ← map_one (IsLocalRing.residue A)]
  congr 1
  exact Subtype.ext (by simpa using hζ)

/-- 単元指数の根の還元は単射。 -/
theorem residueRoot_injective (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : A)) (ζ ξ : L) (hζ : ζ ^ m = 1) (hξ : ξ ^ m = 1)
    (hres : residueRoot A hm ζ hζ = residueRoot A hm ξ hξ) : ζ = ξ := by
  set x : A := ⟨ζ, root_mem A hm hζ⟩
  set y : A := ⟨ξ, root_mem A hm hξ⟩
  have hx : x ^ m = 1 := Subtype.ext (by simpa using hζ)
  have hy : y ^ m = 1 := Subtype.ext (by simpa using hξ)
  have hxy : x - y ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]; exact hres
  exact congrArg Subtype.val (eq_of_pow_eq_one_of_sub_mem hm hmu x y hx hy hxy)

/-- 原始根の還元の単射性と根数上界から、剰余の根の1を持ち上げる。 -/
theorem exists_root_lift (A : ValuationSubring L) {m : ℕ} (hm : m ≠ 0)
    (hmu : IsUnit ((m : ℕ) : A)) (ζ₀ : L) (hζ₀ : IsPrimitiveRoot ζ₀ m)
    (η : IsLocalRing.ResidueField A) (hη : η ^ m = 1) :
    ∃ (ζ : L) (hζ : ζ ^ m = 1), residueRoot A hm ζ hζ = η := by
  classical
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  set f : Fin m → IsLocalRing.ResidueField A := fun i =>
    residueRoot A hm (ζ₀ ^ (i : ℕ)) (by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one,
      one_pow])
  have hfmem : ∀ i : Fin m, f i ∈ Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) := by
    intro i
    rw [Polynomial.mem_nthRootsFinset hm']
    exact residueRoot_pow A hm _ _
  have hfinj : Function.Injective f := by
    intro i j hij
    have hpow : ζ₀ ^ (i : ℕ) = ζ₀ ^ (j : ℕ) :=
      residueRoot_injective A hm hmu _ _ _ _ hij
    exact Fin.ext (hζ₀.pow_inj i.2 j.2 hpow)
  have hcard : (Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A)).card ≤ m := by
    classical
    rw [Polynomial.nthRootsFinset_def]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)
  have himage : (Finset.univ.image f) = Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hfmem i
    · rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
      exact hcard
  have hηmem : η ∈ Polynomial.nthRootsFinset m (1 : IsLocalRing.ResidueField A) :=
    (Polynomial.mem_nthRootsFinset hm' 1).mpr hη
  rw [← himage] at hηmem
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hηmem
  exact ⟨ζ₀ ^ (i : ℕ), _, rfl⟩


/-- 元の同じ絶対慣性群の固定体。 -/
def fixedField (A : ValuationSubring (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (inertiaSubgroupIn A ℚ)

/-- 全ての剰余 p 冪根の1は、同じ慣性固定体内の実際の根の1へ持ち上がる。 -/
theorem primePower_root_lift {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (i : ℕ) (y : IsLocalRing.ResidueField A) (hy : y ^ (p ^ i) = 1) :
    ∃ ζ : AlgebraicClosure ℚ, ζ ∈ fixedField A ∧ ζ ^ (p ^ i) = 1 ∧
      ∃ hζA : ζ ∈ A, IsLocalRing.residue A ⟨ζ, hζA⟩ = y := by
  have hm : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
  have hunitp : IsUnit (p : A) := (A.valuation_eq_one_iff (p : A)).mpr
    (InertiaRadical.valuation_prime_eq_one hp hq hpq A hA)
  have hunitm : IsUnit ((p ^ i : ℕ) : A) := by simpa only [Nat.cast_pow] using hunitp.pow i
  let : NeZero ((p ^ i : ℕ) : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hm⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ i)
  obtain ⟨ζ, hζ, hres⟩ := exists_root_lift A hm hunitm ζ₀ hζ₀ y hy
  refine ⟨ζ, ?_, hζ, root_mem A hm hζ, hres⟩
  rw [fixedField, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  exact InertiaRadical.inertia_fixes_primePower_root hp hq hpq A hA ⟨τ, hτ⟩ i ζ hζ

end
end DkMath.Lib.NumberTheory.InertiaResidue
```

### 4. DkMath.Lib.NumberTheory.InertiaResidueUnitRoots

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual residue roots/torsion/fixed lifts supplied internally for original overfield.
-/

import DkMath.Lib.NumberTheory.InertiaResidueRootLifts
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.Lib.NumberTheory.InertiaResidueUnitRoots"

/-!
# 慣性固定体を含む実際の中間体での単元 p 冪根近似

剰余冪根・有限位数・根の1の固定体内持ち上げを、全て証明済みの定理から供給する。
得られるのは極大イデアルを法とする近似であり、体内の正確な p 乗根ではない。
-/
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open ValuationInertia

/-- 同じ固定体を含む中間体の単元は、同じ付値環で p 乗根近似を持つ。 -/
theorem approximate_unit_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime P q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : fixedField P ≤ E)
    (u : P.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : P.comap (algebraMap E (AlgebraicClosure ℚ)),
      z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
  have hroots (c : IsLocalRing.ResidueField P) : ∃ y, y ^ p = c :=
    AlgebraicResidue.power_surjective P p hp.ne_zero c
  have htor (c : IsLocalRing.ResidueField P) (hc : c ≠ 0) : ∃ N : ℕ, 0 < N ∧ c ^ N = 1 :=
    AlgebraicResidue.nonzero_finite_order P q hq hA c hc
  have hμ (i : ℕ) (y : IsLocalRing.ResidueField P) (hy : y ^ (p ^ i) = 1) :
      ∃ k : E, ∃ hk : algebraMap E (AlgebraicClosure ℚ) k ∈ P,
        IsLocalRing.residue P ⟨algebraMap E (AlgebraicClosure ℚ) k, hk⟩ = y := by
    obtain ⟨ζ, hζE, _, hζA, hres⟩ := primePower_root_lift hp hq hpq P hA i y hy
    exact ⟨⟨ζ, hE hζE⟩, hζA, hres⟩
  classical
  let ψ : P.comap (algebraMap E (AlgebraicClosure ℚ)) →+* P :=
    { toFun := fun k => ⟨algebraMap E (AlgebraicClosure ℚ) k, k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let r : P.comap (algebraMap E (AlgebraicClosure ℚ)) →+* IsLocalRing.ResidueField P := (IsLocalRing.residue P).comp ψ
  have hr : ∀ (k : E) (hk : algebraMap E (AlgebraicClosure ℚ) k ∈ P),
      r ⟨k, hk⟩ = IsLocalRing.residue P ⟨algebraMap E (AlgebraicClosure ℚ) k, hk⟩ := fun _ _ => rfl
  have hrefl : ∀ t, r t = 0 → t ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
    intro t ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro htu
    have h1 : IsUnit (ψ t) := htu.map ψ
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at h1
    exact h1 ht
  have hū : r u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hu.map ψ)
  obtain ⟨y, hy⟩ := hroots (r u)
  obtain ⟨N, hN, hN1⟩ := htor (r u) hū
  obtain ⟨a, m, hnd, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.one_lt.ne'
  have hyM : y ^ (p ^ (a + 1) * m) = 1 := by
    rw [pow_succ', mul_assoc, pow_mul, hy, ← hNam, hN1]
  have tail : ∀ (e : ℕ) (w : IsLocalRing.ResidueField P), w ^ (p ^ (a + 1)) = 1 → y = r u ^ e * w →
      ∃ z : P.comap (algebraMap E (AlgebraicClosure ℚ)), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
    intro e w hw hyw
    obtain ⟨k, hk, hkw⟩ := hμ (a + 1) w hw
    refine ⟨⟨k, hk⟩ * u ^ e, hrefl _ ?_⟩
    rw [map_sub, map_pow, map_mul, map_pow, sub_eq_zero, hr k hk, hkw, mul_comm, ← hyw, hy]
  by_cases hm1 : m = 1
  · refine tail 0 y ?_ (by rw [pow_zero, one_mul])
    rw [← hyM, hm1, mul_one]
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hNam
      exact hN.ne' hNam
    have hm : 1 < m := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hm0) (Ne.symm hm1)
    have hcop : Nat.Coprime (p ^ (a + 1)) m :=
      (Nat.coprime_pow_left_iff (Nat.succ_pos a) _ _).mpr (hp.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨A, -, hA⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm
    set j := p ^ (a + 1) * A / m with hj
    have hMA : p ^ (a + 1) * A = m * j + 1 := by
      have := Nat.div_add_mod (p ^ (a + 1) * A) m
      rw [hA] at this
      exact this.symm
    have hyjM : (y ^ (m * j)) ^ (p ^ (a + 1)) = 1 := by
      rw [← pow_mul, show m * j * p ^ (a + 1) = (p ^ (a + 1) * m) * j by ring, pow_mul, hyM, one_pow]
    refine tail (p ^ a * A) ((y ^ (m * j)) ^ (p ^ (a + 1) - 1)) ?_ ?_
    · rw [← pow_mul, mul_comm (p ^ (a + 1) - 1) (p ^ (a + 1)), pow_mul, hyjM, one_pow]
    · symm
      calc r u ^ (p ^ a * A) * (y ^ (m * j)) ^ (p ^ (a + 1) - 1)
          = y ^ (m * j) * y * (y ^ (m * j)) ^ (p ^ (a + 1) - 1) := by
            rw [← hy, ← pow_mul, show p * (p ^ a * A) = p ^ (a + 1) * A by ring, hMA, pow_succ]
        _ = y * ((y ^ (m * j)) ^ (p ^ (a + 1) - 1) * y ^ (m * j)) := by ring
        _ = y * (y ^ (m * j)) ^ (p ^ (a + 1)) := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
        _ = y := by rw [hyjM, mul_one]

/-- 同じ近似根は単元でもある。後の単根持ち上げに使うガードを保持する。 -/
theorem approximate_unit_pRoot_isUnit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime P q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : fixedField P ≤ E)
    (u : P.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : P.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit z ∧
      z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
  obtain ⟨z, hz⟩ := approximate_unit_pRoot hp hq hpq P hA E hE u hu
  have hzn : IsUnit (z ^ p) := by
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hum := Ideal.sub_mem _ hm hz
    rw [sub_sub_cancel] at hum
    exact (IsLocalRing.mem_maximalIdeal _).mp hum hu
  exact ⟨z, (isUnit_pow_iff hp.ne_zero).mp hzn, hz⟩

end
end DkMath.Lib.NumberTheory.InertiaResidue
```

### 5. DkMath.Lib.NumberTheory.InertiaRadicalTailField

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual named radical overfield and internally constructed unit-root approximation inputs.
-/

import DkMath.Lib.NumberTheory.InertiaResidueUnitRoots

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalTailField"

/-!
# 同じ慣性固定体と全 q 根を含む実際の tail 体

同じ互換根の塔と、単元の p 乗根近似を内部構成する。近似を正確な体内冪根へ変える
単根持ち上げや、慣性の tail の p 可除性そのものは、まだ結論しない。
-/
namespace DkMath.Lib.NumberTheory.InertiaResidue
open ValuationInertia
noncomputable section

/-- 同じ有理数 q の全 p 冪根の集合。 -/
def radicals (p q : ℕ) : Set (AlgebraicClosure ℚ) := {z | ∃ n : ℕ, z ^ (p ^ n) = (q : AlgebraicClosure ℚ)}

/-- 元の慣性固定体と全 p 冪根を添加した、実際の中間体。 -/
def tailField (A : ValuationSubring (AlgebraicClosure ℚ)) (p q : ℕ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ ((fixedField A : Set (AlgebraicClosure ℚ)) ∪ radicals p q)

/-- 元の同じ慣性固定体は、同じ tail 体に含まれる。 -/
theorem fixedField_le_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) (p q : ℕ) :
    fixedField A ≤ tailField A p q := fun _ hz => IntermediateField.subset_adjoin ℚ _ (Or.inl hz)

/-- q の任意の同じ p 冪根は、構成した tail 体に入る。 -/
theorem radical_mem_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) {p q n : ℕ}
    {z : AlgebraicClosure ℚ} (hz : z ^ (p ^ n) = (q : AlgebraicClosure ℚ)) : z ∈ tailField A p q :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨n, hz⟩)

/-- 以前の同じ互換根の塔を、同じ tail 体内へ戻す。 -/
theorem tower_mem_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) {p q : ℕ}
    (hp : p.Prime) (n : ℕ) : InertiaRadical.radical p q hp n ∈ tailField A p q :=
  radical_mem_tailField A (PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) n)

/-- tail 体内に、元の同じ互換根の全段を持つ実際の塔が存在する。 -/
theorem compatible_roots_in_tailField (A : ValuationSubring (AlgebraicClosure ℚ)) {p q : ℕ} (hp : p.Prime) :
    ∃ α : ℕ → tailField A p q, α 0 = (q : tailField A p q) ∧
      (∀ n d, α (n + d) ^ (p ^ d) = α n) ∧ ∀ n, α n ^ (p ^ n) = (q : tailField A p q) := by
  let α : ℕ → tailField A p q := fun n => ⟨InertiaRadical.radical p q hp n, tower_mem_tailField A hp n⟩
  exact ⟨α, rfl, fun n d => Subtype.ext (PrimeRadicalTower.tower_compat p hp.pos (q : AlgebraicClosure ℚ) n d),
    fun n => Subtype.ext (PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) n)⟩

/-- 剰余の p 冪根の1は、同じ tail 体内の実際の根の1へ持ち上がる。 -/
theorem tailField_primePower_root_lifts {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (i : ℕ) (y : IsLocalRing.ResidueField A) (hy : y ^ (p ^ i) = 1) :
    ∃ ζ : tailField A p q, ζ ^ (p ^ i) = 1 ∧
      ∃ hζA : (ζ : AlgebraicClosure ℚ) ∈ A, IsLocalRing.residue A ⟨(ζ : AlgebraicClosure ℚ), hζA⟩ = y := by
  obtain ⟨ζ, hζK, hζ, hζA, hres⟩ := primePower_root_lift hp hq hpq A hA i y hy
  exact ⟨⟨ζ, fixedField_le_tailField A p q hζK⟩, Subtype.ext hζ, hζA, hres⟩

/-- 同じ tail 体の単元に、実際の単元 p 乗根近似を供給する。 -/
theorem tailField_unit_roots {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (u : A.comap (algebraMap (tailField A p q) (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : A.comap (algebraMap (tailField A p q) (AlgebraicClosure ℚ)), IsUnit z ∧
      z ^ p - u ∈ IsLocalRing.maximalIdeal (A.comap (algebraMap (tailField A p q) (AlgebraicClosure ℚ))) :=
  approximate_unit_pRoot_isUnit hp hq hpq A hA (tailField A p q) (fixedField_le_tailField A p q) u hu

/-- 同じ tail 体を含む任意の実際の中間体でも、同じ単元近似入力を内部供給する。 -/
theorem tailOverfield_unit_roots {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (u : A.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : A.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit z ∧
      z ^ p - u ∈ IsLocalRing.maximalIdeal (A.comap (algebraMap E (AlgebraicClosure ℚ))) :=
  approximate_unit_pRoot_isUnit hp hq hpq A hA E ((fixedField_le_tailField A p q).trans hE) u hu

end
end DkMath.Lib.NumberTheory.InertiaResidue
```

