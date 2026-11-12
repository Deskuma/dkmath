# NOTE-032 教科書: 局所条件付き単元空間と条件付き非分裂排除

日付: 2026-11-04。同じ `S,L,K,m,v,ψ,P,F,M,α,b` と、単元還元が返す同じ u を追う。

今回の到達点は二つある。

1. 実際の完備体の局所 p 乗根から、同じ原始根の素点で **u^(p−1)−1∈(ζ−1)^3** を証明した。
2. 局所条件付き ω² 単元空間の消滅を明示入力とすると、**元の非分裂を排除し、同じ商表現の安定補空間を得る**。

算術的な単元空間消滅そのものは、依然として未証明である。一般 hno の完成を主張しない。
最終定理に残る主要な入力は、元の共鳴住所の `hbad`、実際の類群商の `hclass`、
今回型を定めた実際の単元空間の `hunit` である。

## 1. 外部証明を確認して選んだ接続

ローカルの外部実装
`ExtCitation.Cyclotomic.unitsOmegaEigenvector_two_eq_zero_of_local_pow`
の公開声明、局所合同の証明本体、最終の証明接続を照合した。
参照コミット・blob・SHA-256・確認範囲は
[evidence/note032-primary-unit-external-proof-path.json](evidence/note032-primary-unit-external-proof-path.json)
に保存した。この記録の範囲はソース比較である。

外部の最終証明は、ω² 単元空間の次元1、対数型写像 Λ、その写像の円分単元での非零値を使う。
局所 p 乗性は、まず u^(p−1)−1∈(ζ−1)^3 を導き、Λ の値が零になることへつながる。
今回、この最初の具体的な合同を独立の DkMath 定理として移した。
適応したソースには Apache の著作権・通知・blob 出典を保持する。
[ライセンス](../../../DkMath/Lib/NumberTheory/RegularKummer/LICENSE)と
[上流通知](../../../DkMath/Lib/NumberTheory/RegularKummer/ANTHROPIC-NOTICE)も参照できる。

次元1と Λ の非零評価を DkMath の型へ接続する仕事は残る。
`rootField ζ` と外部の `CyclotomicField p ℚ`、単元商、指標と作用の比較を済ませたことにはしない。
新しい生産コードは外部の P2M/P2MW/ExtCitation 定理を import せず、DkMath の依存監査を通す。

## 2. 同じ素点の局所根から3次合同へ

実装: [KummerLocalPrimaryUnit.lean](../../../DkMath/Lib/NumberTheory/KummerLocalPrimaryUnit.lean)。

一般の Dedekind 環 R と分数体 K、同じ非零素点 v、同じ単元 u∈R^× を固定する。
仮定は次の三つである。

\[
u^{p-1}-1\in v,\qquad p\in v^2,\qquad
\exists t\in K_v^\times,\quad t^p=u.
\]

p は素数で p≥5 とする。u は整数環単元なので付値が1であり、
整数値付値群の非零部分はねじれを持たないため、同じ局所根 t の付値も1である。
y=t^(p−1)、h=y−1 と置くと、素数次数の二項展開は

\[
u^{p-1}-1=h^p+p\,h\,S,\qquad |S|_v\le1
\]

となる。中間二項係数の p 可除性は Mathlib の `add_pow_prime_eq` を使う。

最初は |h|≤1 が分かる。もし |h|=1 なら右辺の h^p の付値は1、
一方 p h S の付値は1未満なので、右辺全体の付値が1になる。
これは最初の合同 u^(p−1)−1∈v と矛盾する。
従って |h|<1、離散性により |h|≤exp(-1) である。

\[
|h^p|\le\exp(-p)\le\exp(-3),\qquad
|p\,h\,S|\le\exp(-2)\exp(-1)=\exp(-3).
\]

完備体と元の R の付値の一致を使い、同じ素点に戻して

\[
\boxed{u^{p-1}-1\in v^3}
\]

を得る。根の存在や最初の合同を消した一般定理ではない。
以下は著作権表示を含むソース全文であり、単独コピーでコンパイルできる。

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
Modified: standalone Dedekind-domain theorem, actual field-valued local root,
DkMath namespace and textbook boundary. No upstream theorem is imported.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.CharP.Lemmas

#print "file: DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit"

/-!
# 同じ単元の局所 p 乗性から、同じ素点での3次の合同へ

u^(p-1)-1∈v と p∈v² の住所を保ち、実際の完備体の p 乗根を使って
u^(p-1)-1∈v³ を証明する。p 乗根の付値が1であることから出発し、
二項展開の中間項の p 可除性と正規化整数付値の離散性を使う。
これは単元類の消滅ではなく、その算術的検出に必要な具体的な合同である。
-/

namespace DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Finset
noncomputable section

private lemma zm0_eq_one_of_pow_eq_one {x : ℤᵐ⁰} (hx : x ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n = 1) : x = 1 := by
  rw [← exp_log hx, ← exp_nsmul, ← exp_zero, exp_inj] at h
  rw [← exp_log hx, ← exp_zero, exp_inj]
  have h' : (n : ℤ) * x.log = 0 := by rw [← nsmul_eq_mul]; exact h
  exact (mul_eq_zero.mp h').resolve_left (Int.natCast_ne_zero.mpr hn)

private lemma zm0_le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← exp_log hx, ← exp_zero, exp_lt_exp] at h
    rw [← exp_log hx, exp_le_exp]
    omega

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- 同じ素点における局所 p 乗根から、単元の p−1 乗の3次合同を得る。 -/
theorem pow_sub_one_mem_cube_of_local_pow
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (𝔭 : HeightOneSpectrum R) (u : Rˣ)
    (hz1 : (u : R) ^ (p - 1) - 1 ∈ 𝔭.asIdeal)
    (hp2 : (p : R) ∈ 𝔭.asIdeal ^ 2)
    (hloc : ∃ v : (𝔭.adicCompletion K)ˣ,
      (v : 𝔭.adicCompletion K) ^ p = algebraMap R (𝔭.adicCompletion K) (u : R)) :
    (u : R) ^ (p - 1) - 1 ∈ 𝔭.asIdeal ^ 3 := by
  obtain ⟨v, hv⟩ := hloc
  -- 整数環の埋め込みと付値の正規化を一致させる。
  have hwR : ∀ r : R, Valued.v ((algebraMap R (𝔭.adicCompletion K)) r)
      = 𝔭.intValuation r := by
    intro r
    have h1 : (algebraMap R (𝔭.adicCompletion K)) r = ((algebraMap R K r : K) :
        𝔭.adicCompletion K) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  -- 整数環単元と局所根の付値は1になる。
  have hu1 : 𝔭.intValuation (u : R) = 1 := by
    refine le_antisymm (intValuation_le_one 𝔭 _) ?_
    have humul : 𝔭.intValuation (u : R) * 𝔭.intValuation ((u⁻¹ : Rˣ) : R) = 1 := by
      rw [← Valuation.map_mul, Units.mul_inv, Valuation.map_one]
    calc (1 : ℤᵐ⁰) = 𝔭.intValuation (u : R) * 𝔭.intValuation ((u⁻¹ : Rˣ) : R) :=
          humul.symm
    _ ≤ 𝔭.intValuation (u : R) * 1 :=
          mul_le_mul' le_rfl (intValuation_le_one 𝔭 _)
    _ = 𝔭.intValuation (u : R) := mul_one _
  have hwu : Valued.v ((algebraMap R (𝔭.adicCompletion K)) (u : R)) = 1 := by
    rw [hwR]; exact hu1
  -- 同じ局所根の冪等式を体の元の等式として使う。
  have hv' : (v : 𝔭.adicCompletion K) ^ p
      = (algebraMap R (𝔭.adicCompletion K)) (u : R) := hv
  have hwv : Valued.v (v : 𝔭.adicCompletion K) = 1 := by
    have hpow : (Valued.v (v : 𝔭.adicCompletion K)) ^ p = 1 := by
      rw [← map_pow, hv', hwu]
    have hne : Valued.v (v : 𝔭.adicCompletion K) ≠ 0 := by
      simp
    exact zm0_eq_one_of_pow_eq_one hne hp.ne_zero hpow
  -- p−1乗を取り、1からの誤差を調べる。
  set y : 𝔭.adicCompletion K := (v : 𝔭.adicCompletion K) ^ (p - 1) with hy_def
  set h : 𝔭.adicCompletion K := y - 1 with hh_def
  have hwy : Valued.v y = 1 := by rw [hy_def, map_pow, hwv, one_pow]
  have hwh_le : Valued.v h ≤ 1 := by
    calc Valued.v h ≤ max (Valued.v y) (Valued.v (1 : 𝔭.adicCompletion K)) :=
          Valuation.map_sub _ _ _
    _ ≤ 1 := by rw [hwy, map_one]; exact max_le le_rfl le_rfl
  -- 二項展開の中間項を p でまとめる。
  have hyp_eq : y ^ p = (algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1)) := by
    rw [hy_def, ← pow_mul, mul_comm, pow_mul, hv', ← map_pow]
  set S : 𝔭.adicCompletion K :=
    ∑ k ∈ Ioo 0 p, (1 : 𝔭.adicCompletion K) ^ (k - 1) * h ^ (p - k - 1)
      * ((p.choose k / p : ℕ) : 𝔭.adicCompletion K) with hS_def
  have hident : y ^ p = 1 + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by
    have hyh : (1 : 𝔭.adicCompletion K) + h = y := by rw [hh_def]; ring
    calc y ^ p = ((1 : 𝔭.adicCompletion K) + h) ^ p := by rw [hyh]
    _ = 1 ^ p + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by
          rw [add_pow_prime_eq hp]
    _ = 1 + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by rw [one_pow]
  have hzL : (algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)
      = h ^ p + (p : 𝔭.adicCompletion K) * h * S := by
    rw [map_sub, map_one, ← hyp_eq, hident]; ring
  -- 係数和の各整数係数の付値を抑える。
  have hwnat : ∀ n : ℕ, Valued.v ((n : 𝔭.adicCompletion K)) ≤ 1 := by
    intro n
    have hcast : ((n : 𝔭.adicCompletion K)) = (algebraMap R (𝔭.adicCompletion K)) (n : R) := by
      rw [map_natCast]
    rw [hcast, hwR]; exact intValuation_le_one 𝔭 _
  have hwS : Valued.v S ≤ 1 := by
    rw [hS_def]
    refine Valuation.map_sum_le _ ?_
    intro k _
    calc Valued.v ((1 : 𝔭.adicCompletion K) ^ (k - 1) * h ^ (p - k - 1)
          * ((p.choose k / p : ℕ) : 𝔭.adicCompletion K))
        = (Valued.v (1 : 𝔭.adicCompletion K)) ^ (k - 1) * (Valued.v h) ^ (p - k - 1)
          * Valued.v (((p.choose k / p : ℕ) : 𝔭.adicCompletion K)) := by
          rw [map_mul, map_mul, map_pow, map_pow]
    _ ≤ 1 := by
          rw [map_one, one_pow, one_mul]
          exact mul_le_one' (pow_le_one' hwh_le _) (hwnat _)
  have hwp2 : Valued.v ((p : 𝔭.adicCompletion K)) ≤ exp (-2 : ℤ) := by
    have hcast : ((p : 𝔭.adicCompletion K)) = (algebraMap R (𝔭.adicCompletion K)) ((p : ℕ) : R) := by
      rw [map_natCast]
    rw [hcast, hwR]
    have h2 := (intValuation_le_pow_iff_mem 𝔭 ((p : ℕ) : R) 2).mpr hp2
    simpa using h2
  have hwz_lt : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)) < 1 := by
    rw [hwR]; exact (intValuation_lt_one_iff_mem 𝔭 _).mpr hz1
  have hwp_lt : Valued.v ((p : 𝔭.adicCompletion K)) < 1 :=
    lt_of_le_of_lt hwp2 (by rw [← exp_zero, exp_lt_exp]; omega)
  -- 離散付値により誤差は一様化元一個分以上小さい。
  have hwh_lt : Valued.v h < 1 := by
    rcases lt_or_eq_of_le hwh_le with hlt | heq
    · exact hlt
    · exfalso
      have h1 : Valued.v (h ^ p) = 1 := by rw [map_pow, heq, one_pow]
      have h2 : Valued.v ((p : 𝔭.adicCompletion K) * h * S) < 1 := by
        calc Valued.v ((p : 𝔭.adicCompletion K) * h * S)
            = Valued.v ((p : 𝔭.adicCompletion K)) * Valued.v h * Valued.v S := by
              rw [map_mul, map_mul]
        _ ≤ Valued.v ((p : 𝔭.adicCompletion K)) * 1 * 1 :=
              mul_le_mul' (mul_le_mul' le_rfl heq.le) hwS
        _ = Valued.v ((p : 𝔭.adicCompletion K)) := by rw [mul_one, mul_one]
        _ < 1 := hwp_lt
      have h3 : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)) = 1 := by
        rw [hzL, Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h2), h1]
      exact absurd h3 (ne_of_lt hwz_lt)
  have hwh_le' : Valued.v h ≤ exp (-1 : ℤ) := zm0_le_exp_neg_one_of_lt_one hwh_lt
  -- 各項の付値を3次の閾値以下にする。
  have hfinal : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1))
      ≤ exp (-3 : ℤ) := by
    rw [hzL]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [map_pow]
      have hb1 : (Valued.v h) ^ p ≤ (exp (-1 : ℤ)) ^ p := pow_le_pow_left' hwh_le' p
      have hb2 : (exp (-1 : ℤ)) ^ p = exp (-(p : ℤ)) := by
        rw [← exp_nsmul]
        congr 1
        rw [nsmul_eq_mul]
        ring
      rw [hb2] at hb1
      exact le_trans hb1 (by rw [exp_le_exp]; omega)
    · calc Valued.v ((p : 𝔭.adicCompletion K) * h * S)
          = Valued.v ((p : 𝔭.adicCompletion K)) * Valued.v h * Valued.v S := by
            rw [map_mul, map_mul]
      _ ≤ exp (-2 : ℤ) * exp (-1 : ℤ) * 1 :=
            mul_le_mul' (mul_le_mul' hwp2 hwh_le') hwS
      _ = exp (-3 : ℤ) := by rw [mul_one, ← exp_add]; norm_num
  -- 最後に完備体の不等式を元の同じイデアルの所属へ戻す。
  have hle : 𝔭.intValuation ((u : R) ^ (p - 1) - 1) ≤ exp (-(3 : ℕ) : ℤ) := by
    rw [← hwR]
    simpa using hfinal
  exact (intValuation_le_pow_iff_mem 𝔭 _ 3).mp hle

end
end DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit
```

## 3. 円分体では必要な住所と合同を内部供給する

実装: [CyclotomicPrimaryCongruence.lean](../../../DkMath/Lib/NumberTheory/CyclotomicPrimaryCongruence.lean)。

指定した同じ数体 F と同じ原始根 ζ に対し、λ=ζ−1、P=(λ) を取る。
原始根は `zeta` へ選び直さず、定理の引数に指定したものを保つ。
Mathlib の円分体の分岐イデアル等式と剰余体の濃度公式により、

\[
p\in P^{p-1},\qquad \#(\mathcal O_F/P)=p
\]

を得る。従って p≥5 なら p∈P² であり、同じ剰余体の単元の p−1 乗は1となる。
これが一般補題の二つのイデアル条件を内部で供給する。
Frey では `baseRoot_primitive hζ` に適用するので、元の rootField 内の同じ根である。

この具体的な3次合同は、今後 Λ によって ω² 単元類を検出する際の入力となる。
3次合同だけから大域 p 乗を結論する定理は今回証明していない。

## 4. 局所条件を、実際の単元商の部分空間として定義する

実装: [CyclotomicPrimaryUnitSpace.lean](../../../DkMath/Lib/NumberTheory/CyclotomicPrimaryUnitSpace.lean)。

U=O_F^×、UnitClass=U/U^p とする。各 v について、自然な埋め込みから

\[
\ell_v:U/U^p\longrightarrow F_v^\times/F_v^{\times p}
\]

を実際の商群の写像として構成した。核に入ることは、同じ代表元 u に対して
実際の局所根 t が存在することと同値である。
局所根の選び方はこの商写像の定義に入らない。

\[
U_{\mathrm{loc},p}=\bigcap_{v\mid p}\ker\ell_v,
\qquad
W_2=\{a\mid\forall\gamma,\ \gamma a=\omega(\gamma)^2a\},
\qquad
U_{\mathrm{primary}}^{(2)}=W_2\cap U_{\mathrm{loc},p}.
\]

W₂ は、既存の同じ `integerAut γ`、`unitClassLinearMap`、`baseCharacter hζ` で定義する。
新しい別の作用を仮定していない。

未解決の `hunit` は、正確には

```text
primaryWeightSquareSpace hζ = ⊥
```

である。これは、同じ条件を満たす各整数環単元 u について、
**大域の整数環単元 a が存在して a^p=u となる**、という命題と同値であることも証明した。
この同値は単元商の定義と代表元の全射性によるもの。
その大域根の存在そのものを今回証明したわけではない。

以下も著作権表示を含むソース全文である。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.KummerSelmerUnitEquivariance
import DkMath.Lib.NumberTheory.CyclotomicKummerEquivariance
import DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace"

/-!
# 実際の局所冪の核と、同じ円分単元商の ω² 部分空間

整数環単元の p 乗商から、指定した同じ素点の完備体の Kummer 商への写像を作る。
局所 p 乗条件をその核の共通部分として定義するため、代表元に依存しない。
同じ整数環 Galois 作用の ω² 固有空間と交差を取り、未解決の消滅条件を正確に述べる。
この空間が零であること自体は仮定に残す。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace

open DkMath.Lib.Algebra KummerSelmerExact KummerSelmerUnitEquivariance
open CyclotomicKummerWeight CyclotomicKernelField CyclotomicKummerEquivariance
open IsDedekindDomain
open scoped NumberField
noncomputable section

variable {R E : Type*} [CommRing R] [Field E]

/-- 指定した環準同型を、単元冪商から実際の Kummer 商への写像に下ろす。 -/
def classMapAlong (p : ℕ) (φ : R →+* E) :
    UnitClass R p →* KummerClass E p :=
  QuotientGroup.map _ _ (Units.map φ.toMonoidHom) (by
    rintro _ ⟨a, rfl⟩
    exact ⟨Units.map φ.toMonoidHom a,
      (map_pow _ _ _).symm⟩)

/-- 核への所属は、同じ単元の実際の局所 p 乗根の存在と同値。 -/
theorem classMapAlong_mk_eq_one_iff (p : ℕ) (φ : R →+* E) (u : Rˣ) :
    classMapAlong p φ (u : UnitClass R p) = 1 ↔
      ∃ t : Eˣ,
        (t : E) ^ p = φ (u : R) := by
  change ((Units.map φ.toMonoidHom u :
    Eˣ) : KummerClass E p) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change (∃ t : Eˣ,
    t ^ p = Units.map φ.toMonoidHom u) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h := congrArg Units.val ht
    rw [Units.val_pow_eq_pow_val] at h
    exact h
  · rintro ⟨t, ht⟩
    refine ⟨t, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val]
    exact ht

variable {F : Type*} [Field F] [NumberField F]

/-- 同じ整数環の単元商から指定した完備体へ、実際の自然な写像を適用する。 -/
def localClassMap (p : ℕ) (vF : HeightOneSpectrum (𝓞 F)) :
    UnitClass (𝓞 F) p →* KummerClass (vF.adicCompletion F) p :=
  classMapAlong p (algebraMap (𝓞 F) (vF.adicCompletion F))

/-- 同じ素点への写像の核を、実際の局所根の等式として読む。 -/
theorem localClassMap_mk_eq_one_iff (p : ℕ) (vF : HeightOneSpectrum (𝓞 F)) (u : (𝓞 F)ˣ) :
    localClassMap p vF (u : UnitClass (𝓞 F) p) = 1 ↔
      ∃ t : (vF.adicCompletion F)ˣ,
        (t : vF.adicCompletion F) ^ p = algebraMap (𝓞 F) (vF.adicCompletion F) (u : 𝓞 F) :=
  classMapAlong_mk_eq_one_iff p _ u

/-- 同じ局所化写像を、既存の同じ ZMod p 加群構造で読む。 -/
def localClassLinearMap (p : ℕ) (vF : HeightOneSpectrum (𝓞 F)) :
    Additive (UnitClass (𝓞 F) p) →ₗ[ZMod p] Additive (KummerClass (vF.adicCompletion F) p) :=
  (localClassMap p vF).toAdditive.toZModLinearMap p

/-- p 上の全素点における局所 p 乗条件を満たす、実際の単元商の部分空間。 -/
def localPowerSpace (F : Type*) [Field F] [NumberField F] (p : ℕ) :
    Submodule (ZMod p) (Additive (UnitClass (𝓞 F) p)) :=
  ⨅ vF : HeightOneSpectrum (𝓞 F), ⨅ (_hpv : (p : 𝓞 F) ∈ vF.asIdeal),
    (localClassLinearMap p vF).ker

/-- 任意の代表元で、同じ局所根の条件を読む。 -/
theorem mk_mem_localPowerSpace_iff (p : ℕ) (u : (𝓞 F)ˣ) :
    Additive.ofMul (u : UnitClass (𝓞 F) p) ∈ localPowerSpace F p ↔
      ∀ vF : HeightOneSpectrum (𝓞 F), (p : 𝓞 F) ∈ vF.asIdeal →
        ∃ t : (vF.adicCompletion F)ˣ,
          (t : vF.adicCompletion F) ^ p = algebraMap (𝓞 F) (vF.adicCompletion F) (u : 𝓞 F) := by
  simp only [localPowerSpace, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h vF hpv
    apply (localClassMap_mk_eq_one_iff p vF u).mp
    have ht := h vF hpv
    change localClassMap p vF (u : UnitClass (𝓞 F) p) = 1 at ht
    exact ht
  · intro h vF hpv
    change localClassMap p vF (u : UnitClass (𝓞 F) p) = 1
    exact (localClassMap_mk_eq_one_iff p vF u).mpr (h vF hpv)

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance instRootNumberField : NumberField (rootField ζ) := rootField_numberField ζ

/-- 同じ整数環作用と同じ円分指標に対する ω² 単元固有空間。 -/
def weightSquareSpace : Submodule (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) where
  carrier := {a | ∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
    unitClassLinearMap p (integerAut γ) a = (baseCharacter hζ γ : ZMod p) ^ 2 • a}
  zero_mem' γ := by simp
  add_mem' hx hy γ := by rw [map_add, hx γ, hy γ, smul_add]
  smul_mem' c a ha γ := by rw [map_smul, ha γ, smul_comm]

/-- 今回の Frey の出力を受ける、同じ単元商上の正確な部分空間。 -/
def primaryWeightSquareSpace :
    Submodule (ZMod p) (Additive (UnitClass (𝓞 (rootField ζ)) p)) :=
  weightSquareSpace hζ ⊓ localPowerSpace (rootField ζ) p

/-- 同じ整数環単元について、固有条件と底体の各完備体での根を同時に読む。 -/
theorem mk_mem_primaryWeightSquareSpace_iff (u : (𝓞 (rootField ζ))ˣ) :
    Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ ↔
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        unitClassLinearMap p (integerAut γ) (Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p)) =
          (baseCharacter hζ γ : ZMod p) ^ 2 • Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p)) ∧
      ∀ vF : HeightOneSpectrum (𝓞 (rootField ζ)), (p : 𝓞 (rootField ζ)) ∈ vF.asIdeal →
        ∃ t : (vF.adicCompletion (rootField ζ))ˣ,
          (t : vF.adicCompletion (rootField ζ)) ^ p =
            algebraMap (rootField ζ) (vF.adicCompletion (rootField ζ))
              (algebraMap (𝓞 (rootField ζ)) (rootField ζ) u) := by
  rw [primaryWeightSquareSpace, Submodule.mem_inf, mk_mem_localPowerSpace_iff]
  rfl

/-- 部分空間の消滅が供給されたとき、同じ単元類が1になる。算術的消滅自体は入力。 -/
theorem unitClass_eq_one_of_space_eq_bot
    (hunit : primaryWeightSquareSpace hζ = ⊥) (u : (𝓞 (rootField ζ))ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ) :
    (u : UnitClass (𝓞 (rootField ζ)) p) = 1 := by
  rw [hunit, Submodule.mem_bot] at hu
  exact Additive.ofMul.injective hu

/-- 未解決の空間消滅は、同じ固有・局所条件の単元が大域の単元 p 乗になるという命題と同値。
局所根から大域根への移行を定義だけで済ませず、算術的に証明すべき条件として露出させる。 -/
theorem primaryWeightSquareSpace_eq_bot_iff_global_power :
    primaryWeightSquareSpace hζ = ⊥ ↔
      ∀ u : (𝓞 (rootField ζ))ˣ,
        Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ →
        ∃ a : (𝓞 (rootField ζ))ˣ, a ^ p = u := by
  constructor
  · intro hunit u hu
    have h := unitClass_eq_one_of_space_eq_bot hζ hunit u hu
    exact (QuotientGroup.eq_one_iff u).mp h
  · intro hpower
    apply (Submodule.eq_bot_iff (primaryWeightSquareSpace hζ)).mpr
    intro x hx
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
      (powerSubgroup (𝓞 (rootField ζ))ˣ p) x.toMul
    have hxu : Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) = x :=
      congrArg Additive.ofMul hu
    obtain ⟨a, ha⟩ := hpower u (hxu.symm ▸ hx)
    have hclass : (u : UnitClass (𝓞 (rootField ζ)) p) = 1 :=
      (QuotientGroup.eq_one_iff u).mpr ⟨a, ha⟩
    exact hxu.symm.trans (congrArg Additive.ofMul hclass)

end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryUnitSpace
```

## 5. 同じ非零単元からの条件付き矛盾と安定補空間

実装: [FreyCyclotomicConditionalSplit.lean](../../../DkMath/FLT/FreyCyclotomicConditionalSplit.lean)。

前章の同じ単元 u,c を受け取り、次を同時に返す。

\[
b=u c^p,\quad [b]=[u],\quad [u]\ne0,\quad
[u]\in U_{\mathrm{primary}}^{(2)},\quad
u^{p-1}-1\in(\zeta-1)^3.
\]

ここまでに `hunit` は不要である。
ここへ未解決の算術条件 `hunit` を渡すと、**同じ** [u] が零となり、非零性に矛盾する。

さらに元の商表現が非分裂であると仮定すると、既存の
`residual_nonsplit_has_kummer_presentation` から、同じ巡回段の v、全射指標、P を内部で得る。
従って最終の非分裂排除・補空間の公開定理では、これらを新しい入力に要求しない。

| 入力 | 最終の安定補空間定理での状態 |
| --- | --- |
| 元の Source、直線、Cofixed、K、巡回性、安定性、hm、hcard、hbase | 保持 |
| 原始根 hζ と hp5 | 保持 |
| 共鳴住所の hbad | 未解決の入力として保持 |
| 実際の類群商の hclass | 未解決の入力として保持 |
| 実際の局所条件付き単元空間の hunit | 未解決の入力として保持 |
| v、P、hsurj | 非分裂から内部取得 |
| hval、hzero | 既存経路で内部導出 |
| hns | 補空間存在定理の入力には置かない |

得られる D は、同じ商表現の全絶対 Galois 群に対して安定な、実際の補部分加群である。
塔の全段を反復して構成したという結論は含めない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCyclotomicKummerLocalPower
import DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence

#print "file: DkMath.FLT.FreyCyclotomicConditionalSplit"

/-!
# 同じ Frey 単元の3次合同と、算術仮定を明示した非分裂排除

同じ非零 ω² 単元類を、実際の局所冪核の部分空間へ入れる。
同じ原始根の素点で u^(p−1)−1∈(ζ−1)^3 も証明する。
局所条件付き単元空間の消滅を明示入力とすると、その同じ非零類から矛盾する。
非分裂から v と P を内部構成し、同じ元の extension の安定補空間を得る。
hbad、実際の類群商の消滅、局所条件付き単元空間の消滅は未解決の入力である。
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
local instance instIsEllipticCyclotomicConditionalSplit : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (K : AddSubgroup (Points S.rationalCurve)) [Finite K] [IsAddCyclic K]
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K, pointAction S.rationalCurve σ x ∈ K)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Nat.card K = p ^ m)
    (hbase : pointSubgroup S.rationalCurve p L ≤ K)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance instRootFieldNumberFieldConditionalSplit : NumberField (rootField ζ) := rootField_numberField ζ

section Presentation

variable (v : TorsionPreimageQuotient.Quotient p K)
    (P : (letI := extensionAlgebra (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v) hζ;
      Presentation p (rootField ζ) (S.residualCharacterField L hline hcofixed K hstable hm hcard hbase v)))

include hline hcofixed hstable hm hcard hbase P

/-- 同じ単元類が局所冪核と ω² 固有空間の交差に属し、同じ根の素点で3次合同を満たす。 -/
theorem residual_kummer_primary_unit_witness
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0) :
    let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
    letI := extensionAlgebra ψ hζ
    ∃ (u : (𝓞 (rootField ζ))ˣ) (c : (rootField ζ)ˣ),
      P.constant = algebraMap (𝓞 (rootField ζ)) (rootField ζ) u * (c : rootField ζ) ^ p ∧
      constantVector ψ hζ P = Additive.ofMul
        ((Units.map (algebraMap (𝓞 (rootField ζ)) (rootField ζ)).toMonoidHom u :
          (rootField ζ)ˣ) : KummerClass (rootField ζ) p) ∧
      (u : UnitClass (𝓞 (rootField ζ)) p) ≠ 1 ∧
      Additive.ofMul (u : UnitClass (𝓞 (rootField ζ)) p) ∈ primaryWeightSquareSpace hζ ∧
      (u : 𝓞 (rootField ζ)) ^ (p - 1) - 1 ∈ ramifiedIdeal (baseRoot_primitive hζ) ^ 3 := by
  obtain ⟨u, c, hdec, hvec, hnz, heig, hloc⟩ :=
    S.residual_kummer_unit_weight_square_and_local_power
      L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hclass
  have hmem := (mk_mem_primaryWeightSquareSpace_iff hζ u).mpr ⟨heig, hloc⟩
  refine ⟨u, c, hdec, hvec, hnz, hmem, ?_⟩
  let : IsCyclotomicExtension {p} ℚ (rootField ζ) := rootField_isCyclotomic hζ
  exact pow_sub_one_mem_ramifiedIdeal_cube_of_local_power (baseRoot_primitive hζ) hp5 u hmem.2

/-- 同じ非零単元類を使う条件付き矛盾。単元空間消滅自体は hunit に明示する。 -/
theorem residual_kummer_impossible_of_primary_unit_vanishing
    (hp5 : 5 ≤ p)
    (hbad : ∀ q : ℕ, q.Prime → q ≠ p → 5 ≤ q → (q : ℤ) ∣ S.a * S.b * S.c →
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q →
        ∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
          p • y ∈ K → pointAction S.rationalCurve τ y - y ∈ K)
    (hsurj : Function.Surjective
      (S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v))
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hunit : primaryWeightSquareSpace hζ = ⊥) : False := by
  obtain ⟨u, _, _, _, hnz, hmem, _⟩ := S.residual_kummer_primary_unit_witness
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hclass
  exact hnz (unitClass_eq_one_of_space_eq_bot hζ hunit u hmem)

end Presentation

include hline hcofixed hstable hm hcard hbase

/-- 元の extension の非分裂から同じ v と P を内部で供給し、条件付きで排除する。 -/
theorem residual_cyclic_extension_nonsplit_impossible
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
    (hunit : primaryWeightSquareSpace hζ = ⊥)
    (hns : ¬ ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D) : False := by
  obtain ⟨v, hsurj, hP⟩ := S.residual_nonsplit_has_kummer_presentation
    L hline hcofixed K hstable hm hcard hbase hp5 hζ hns
  let ψ := S.residualCyclicExtensionCharacter L hline hcofixed K hstable hm hcard hbase v
  let := extensionAlgebra ψ hζ
  obtain ⟨P⟩ := hP
  exact S.residual_kummer_impossible_of_primary_unit_vanishing
    L hline hcofixed K hstable hm hcard hbase hζ v P hp5 hbad hsurj hclass hunit

/-- 算術仮定を保ったまま、同じ巡回段の商表現に実際の大域安定な補空間を得る。 -/
theorem residual_cyclic_extension_has_stable_complement
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
    (hunit : primaryWeightSquareSpace hζ = ⊥) :
    ∃ D : Submodule (ZMod p) (TorsionPreimageQuotient.Quotient p K),
      IsCompl (TorsionPreimageQuotient.torsionImage p K) D ∧
        IsStable (preimageRepresentation S.rationalCurve p K hstable) D := by
  classical
  by_contra hns
  exact S.residual_cyclic_extension_nonsplit_impossible
    L hline hcofixed K hstable hm hcard hbase hζ hp5 hbad hclass hunit hns

end
end DkMath.FLT.Frey.Source
```

## 6. 検証と未解決の境界

有限体 F₇ では、単元2が立方根を持たず、その立方商の像が非零であることを確認する。
一方、単元6は値として1と異なり、立方根3によって立方商では1になる。
単元そのものの等式と、単元商の零条件の区別を検査している。

実際の5次円分体では、同じ λ=ζ−1 について剰余体の濃度5、5∈(λ)^4、
λ²∉(λ)^3 を確認する。最後の例は3次の商が実際に情報を持つことを示す。
円分単元 c=1+ζ を実際に構成し、その同じ5乗 u=c^5 が局所冪核に属することと、
u^4−1∈(λ)^3 を今回の定理で証明する。
この回帰例の単元類は大域5乗なので零である。Frey が返す非零単元類の消滅を確認した例ではない。

13宣言の公理報告、型・コンストラクタ・不透明な証明本体の再帰監査と公開入力監査を追加する。
新規7 Lean ファイルと上の3ブロックは、import 直後の正確な `#print "file: …"` を保持する。
実行結果は
[evidence/validation-note032-cyclotomic-conditional-split.txt](evidence/validation-note032-cyclotomic-conditional-split.txt)
に記録する。

残る主要な数学は次の通り。

- 同じ実際の ω² 単元空間の次元と Λ の構成・非零評価から、hunit を算術的に証明する。
- 実際の類群商の hclass を算術的に証明する。
- 共鳴住所の hbad を幾何学的に解決する。
- この条件付き分裂を巡回塔の反復へ接続し、一般 hno へ進む。

**今回閉じたのは、具体的な3次合同と、明示した算術仮定から元の非分裂排除までの接続である。
一般 hno は未完成である。**
