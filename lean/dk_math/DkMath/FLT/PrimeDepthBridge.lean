/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyPrimeProfile
import DkMath.NumberTheory.Legendre.FreyJDepth

#print "file: DkMath.FLT.PrimeDepthBridge"

/-!
# 同じ素数で読む二つの曲線の深度

中央席 Qₙ の素因子qは2でない。この同じqで、Legendre曲線の j 深度は3倍、
冪和 Source の Frey 曲線の最小判別式深度は2p倍となる。
二つの曲線の一致やガロア表現の一致を主張せず、独立の入力を同じ素数で比較する。
旧支持から入る場合には q≤n を残す。素数の存在は結論に足さない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.NumberTheory.Legendre FreyC4CentralSeat

/-- 同じ中央席素因子における二つの実際の有理不変量の付値。 -/
theorem centralSeat_depth_pair {p n q : ℕ} (S : Source p) (hp : 0 < p)
    (hn : 0 < n) (hq : q.Prime) (hd : q ∣ centralSeat n) :
    padicValRat q (rationalJ n hn) = 3 * (padicValNat q (centralSeat n) : ℤ) ∧
      padicValRat q S.rationalCurve.Δ = (2 * p : ℕ) * (padicValInt q (S.a * S.b * S.c) : ℤ) := by
  let : Fact q.Prime := ⟨hq⟩
  exact ⟨rationalJ_valuation hn hq hd, (S.minimal_discriminant_valuation hp (divisor_ne_two hd)).2⟩

/-- 支持制約を保つ入口。上限q≤nを比較の際に忘れない。 -/
theorem oldSupport_depth_pair {p n q : ℕ} (S : Source p) (hp : 0 < p) (hn : 0 < n)
    (hs : q ∈ squareOffsetPrimeSupport n (n + 1)) :
    q ≤ n ∧
      padicValRat q (rationalJ n hn) = 3 * (padicValNat q (centralSeat n) : ℤ) ∧
      padicValRat q S.rationalCurve.Δ = (2 * p : ℕ) * (padicValInt q (S.a * S.b * S.c) : ℤ) := by
  obtain ⟨hq, hqn, hd⟩ := mem_primeSupport_iff.mp hs
  exact ⟨hqn, S.centralSeat_depth_pair hp hn hq hd⟩

end DkMath.FLT.Frey.Source
