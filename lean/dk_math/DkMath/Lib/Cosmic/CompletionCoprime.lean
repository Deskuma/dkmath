/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTail
import DkMath.Lib.NumberTheory.PadicValNat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.Lib.Cosmic.CompletionCoprime"

/-!
# GN完成の三者gcdと素数支持

自然数の座標 `g,u` と次数 `d` について、この教科書では
`Big = (g+u)^d`、`Body = g * GTail d 1 g u`、`Gap = u^d` と読む。
上位のBigN/BodyNというcarrierを導入せず、既存の有限和を直接使う。

`Body + Gap = Big` により、三つのgcdは同じ値になる。
冪のgcdを底のgcdへ戻すと、その値は `gcd(g,u)^d` である。
原始性はこの一般等式の仮定には要らず、互いに素性を得る段階で使う。
次数0も `Big=Gap=1, Body=0` として含まれる。

正次数では完成根 `g+u` の素数支持とBigの素数支持が一致する。
原始対なら、その素数はBodyにもGapにも現れない。
Bigの付値のd倍則は既存のLibの冪付値定理を特殊化する。
完成根の素数性やFLT状態の排除は、これらの結論に含まれない。
-/

namespace DkMath.Lib.Cosmic

open DkMath.CosmicFormula

/--
[DkMath.Lib] GN-LIB-002の完成語彙への橋。
既存の `add_pow_eq_mul_GTail_one_add_gap` を逆向きに読む。
Bodyを自然数差で定義しないため、全次数・零座標で同じ式を使える。
-/
theorem completion_body_add_gap (d g u : ℕ) :
    g * GTail d 1 g u + u ^ d = (g + u) ^ d :=
  (add_pow_eq_mul_GTail_one_add_gap d g u).symm

/--
[DkMath.Lib] GN-LIB-002で新規固定した一般gcdの橋。
同じ次数の冪のgcdを底へ戻し、`gcd(g+u,u)=gcd(g,u)` を使う。
原始性・正性・正次数を仮定せず、非原始対の共通因子もd乗のまま保持する。
-/
theorem completion_gcd_big_gap (d g u : ℕ) :
    Nat.gcd ((g + u) ^ d) (u ^ d) = Nat.gcd g u ^ d := by
  rw [Nat.pow_gcd_pow, Nat.gcd_add_self_left]

/--
[DkMath.Lib] GN-LIB-002で新規固定したBody/Gapのgcd。
Gapを足してもgcdは変わらないので、完成等式からBig/Gapのgcdへ運ぶ。
共通因子を消去せず、非原始対も含む正確な値を返す。
-/
theorem completion_gcd_body_gap (d g u : ℕ) :
    Nat.gcd (g * GTail d 1 g u) (u ^ d) = Nat.gcd g u ^ d := by
  calc
    Nat.gcd (g * GTail d 1 g u) (u ^ d) =
        Nat.gcd (g * GTail d 1 g u + u ^ d) (u ^ d) :=
      (Nat.gcd_add_self_left _ _).symm
    _ = Nat.gcd ((g + u) ^ d) (u ^ d) := by rw [completion_body_add_gap]
    _ = Nat.gcd g u ^ d := completion_gcd_big_gap d g u

/--
[DkMath.Lib] GN-LIB-002で新規固定したBody/Bigのgcd。
BigをBody+Gapに戻すと、同じBody/Gapのgcdになる。
これはBody内部のgとGNが互いに素であるという主張ではない。
-/
theorem completion_gcd_body_big (d g u : ℕ) :
    Nat.gcd (g * GTail d 1 g u) ((g + u) ^ d) = Nat.gcd g u ^ d := by
  calc
    Nat.gcd (g * GTail d 1 g u) ((g + u) ^ d) =
        Nat.gcd (g * GTail d 1 g u) (g * GTail d 1 g u + u ^ d) := by
      rw [completion_body_add_gap]
    _ = Nat.gcd (g * GTail d 1 g u) (u ^ d) := Nat.gcd_self_add_right _ _
    _ = Nat.gcd g u ^ d := completion_gcd_body_gap d g u

/--
[DkMath.Lib] 原始対のBigとGapは全次数で互いに素である。
原始性はgcdを1へ特殊化するこの段階で使い、次数0を除外しない。
-/
theorem completion_coprime_big_gap (d g u : ℕ) (h : g.Coprime u) :
    ((g + u) ^ d).Coprime (u ^ d) := by
  change Nat.gcd ((g + u) ^ d) (u ^ d) = 1
  rw [completion_gcd_big_gap, h.gcd_eq_one, one_pow]

/--
[DkMath.Lib] 原始対のBodyとGapは互いに素である。
Bodyを構成するgとGNの内部gcdを別途仮定しない。
-/
theorem completion_coprime_body_gap (d g u : ℕ) (h : g.Coprime u) :
    (g * GTail d 1 g u).Coprime (u ^ d) := by
  change Nat.gcd (g * GTail d 1 g u) (u ^ d) = 1
  rw [completion_gcd_body_gap, h.gcd_eq_one, one_pow]

/--
[DkMath.Lib] 原始対のBodyとBigは互いに素である。
完成等式によるgcd保存から従うため、Bodyの正性は必要ない。
-/
theorem completion_coprime_body_big (d g u : ℕ) (h : g.Coprime u) :
    (g * GTail d 1 g u).Coprime ((g + u) ^ d) := by
  change Nat.gcd (g * GTail d 1 g u) ((g + u) ^ d) = 1
  rw [completion_gcd_body_big, h.gcd_eq_one, one_pow]

/--
[DkMath.Lib] 原始完成の三者がpairwise coprimeであることを三つ組で公開する。
順序はBody/Gap、Body/Big、Big/Gap。Big=Gap=1となる次数0も許す。
-/
theorem completion_pairwise_coprime (d g u : ℕ) (h : g.Coprime u) :
    (g * GTail d 1 g u).Coprime (u ^ d) ∧
      (g * GTail d 1 g u).Coprime ((g + u) ^ d) ∧
      ((g + u) ^ d).Coprime (u ^ d) :=
  ⟨completion_coprime_body_gap d g u h, completion_coprime_body_big d g u h,
    completion_coprime_big_gap d g u h⟩

/--
[DkMath.Lib] 原始完成のBigを割る素数はBodyにもGapにも現れない。
次数0はBig=1なので入力が成立せず、ここでは正次数を仮定する必要がない。
-/
theorem completion_prime_not_dvd_body_gap_of_dvd_big
    (d g u : ℕ) (h : g.Coprime u) {q : ℕ} (hq : q.Prime)
    (hbig : q ∣ (g + u) ^ d) :
    ¬q ∣ g * GTail d 1 g u ∧ ¬q ∣ u ^ d := by
  constructor
  · exact hq.coprime_iff_not_dvd.mp
      ((completion_coprime_body_big d g u h).coprime_dvd_right hbig).symm
  · exact hq.coprime_iff_not_dvd.mp
      ((completion_coprime_big_gap d g u h).coprime_dvd_left hbig)

/--
[DkMath.Lib] 正次数のBigと完成根は同じ素数支持を持つ。
原始性は不要だが、次数0のBig=1へ逆向きを拡張しない。
完成根が0でも、正次数なら両辺の可除性は同じ意味を持つ。
-/
theorem completion_prime_dvd_big_iff_dvd_sum
    (d g u : ℕ) (hd : 0 < d) {q : ℕ} (hq : q.Prime) :
    q ∣ (g + u) ^ d ↔ q ∣ g + u := by
  constructor
  · exact hq.dvd_of_dvd_pow
  · intro hsum
    exact hsum.trans (dvd_pow_self (g + u) (Nat.ne_of_gt hd))

/--
[DkMath.Lib] 完成根の素数からBody/Gapの排除へ進む原始・正次数版。
Bigを割る場合との違いは、完成根からBigへ進むための正次数条件にある。
-/
theorem completion_prime_not_dvd_body_gap_of_dvd_sum
    (d g u : ℕ) (hd : 0 < d) (h : g.Coprime u) {q : ℕ} (hq : q.Prime)
    (hsum : q ∣ g + u) :
    ¬q ∣ g * GTail d 1 g u ∧ ¬q ∣ u ^ d :=
  completion_prime_not_dvd_body_gap_of_dvd_big d g u h hq
    ((completion_prime_dvd_big_iff_dvd_sum d g u hd hq).mpr hsum)

/--
[DkMath.Lib] 完成によるBigの付値は、完成根の付値のd倍である。
既存の `DkMath.Lib.NumberTheory.padicValNat_pow` への薄い橋。
零の付値規約を隠さないよう完成根の非零性を公開型に残す。原始性は不要。
-/
theorem completion_padicValNat_big
    (d g u : ℕ) {q : ℕ} (hq : q.Prime) (hsum : g + u ≠ 0) :
    padicValNat q ((g + u) ^ d) = d * padicValNat q (g + u) :=
  DkMath.Lib.NumberTheory.padicValNat_pow hq d hsum

/--
[DkMath.Lib] 次数はBigの素数付値を割る。
同じ非零条件を保った付値倍化の帰結であり、次数0なら0が0を割る場合になる。
-/
theorem completion_degree_dvd_padicValNat_big
    (d g u : ℕ) {q : ℕ} (hq : q.Prime) (hsum : g + u ≠ 0) :
    d ∣ padicValNat q ((g + u) ^ d) := by
  rw [completion_padicValNat_big d g u hq hsum]
  exact dvd_mul_right d _

end DkMath.Lib.Cosmic
