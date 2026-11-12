/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.FreyC4CentralSeat

#print "file: DkMath.NumberTheory.Legendre.FreyJCentralSeat"

/-!
# NOTE-007: 中央席と良還元時の j=0

j=c₄³/Δ は非特異な曲線の不変量である。零 Gap n=0 を除いた実際の有理曲線に
Mathlib の j を適用し、中央席 Qₙ の式を得る。Qₙ の素因子 q での還元は既に
非特異なので、同じ定義で j=0 を得る。これは剰余体上の結論であり、元の有理曲線の
複素乗法や、新しい素因子の存在を結論しない。旧支持 q≤n も保持する。
-/

namespace DkMath.NumberTheory.Legendre.FreyC4CentralSeat

/-- n>0 の正規化モデルの真の j-不変量。非特異性の証明を定義に保持する。 -/
noncomputable def rationalJ (n : ℕ) (hn : 0 < n) : ℚ :=
  let := rationalCurve_isElliptic hn
  (rationalCurve n).j

/-- 中央席表示 j=256 Qₙ³/(n²(n+1)²)。正規化で現れる256をそのまま追跡する。 -/
theorem rationalJ_eq (n : ℕ) (hn : 0 < n) :
    rationalJ n hn = 256 * (centralSeat n : ℚ) ^ 3 /
      ((n : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2) := by
  unfold rationalJ
  rw [WeierstrassCurve.j_eq, rationalCurve_c4, rationalCurve_discriminant]
  rw [mul_pow, inv_div]
  ring

/-- 中央席の既存素因子での実際の還元曲線の j。良還元の証明を先に供給する。 -/
noncomputable def reductionJ (n q : ℕ) (hq : q.Prime) (hd : q ∣ centralSeat n) : ZMod q :=
  let : Fact q.Prime := ⟨hq⟩
  let := reduction_isElliptic hq hd
  ((curve n).map (Int.castRingHom (ZMod q))).j

/-- c₄=0 かつ Δ≠0 の剰余曲線では、定義通り j=0 となる。 -/
theorem reductionJ_eq_zero {q n : ℕ} (hq : q.Prime) (hd : q ∣ centralSeat n) :
    reductionJ n q hq hd = 0 := by
  let : Fact q.Prime := ⟨hq⟩
  let := reduction_isElliptic hq hd
  exact WeierstrassCurve.j_eq_zero _ (reduction_c4_eq_zero hd)

/-- 旧支持の上界、良還元時の j=0、三次位相の合同類を同時に保持する。
この定理の入力は既に存在する素因子であり、素因子を新たに構成しない。 -/
theorem j_bridge_of_mem_support {q n : ℕ}
    (hs : q ∈ squareOffsetPrimeSupport n (n + 1)) :
    ∃ (hq : q.Prime) (hd : q ∣ centralSeat n),
      q ≤ n ∧ reductionJ n q hq hd = 0 ∧ (q = 3 ∨ q % 3 = 1) := by
  obtain ⟨hq, hqn, hd⟩ := mem_primeSupport_iff.mp hs
  exact ⟨hq, hd, hqn, reductionJ_eq_zero hq hd, prime_three_or_mod_three hq hd⟩

end DkMath.NumberTheory.Legendre.FreyC4CentralSeat
