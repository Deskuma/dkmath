/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationInertia
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Valuation.LocalSubring

#print "file: DkMath.Lib.NumberTheory.ValuationPrimeExistence"

/-!
# NOTE-032-004: 標数0の体で有限素点の住所を供給する

[DkMath.Lib] 標数0の体Lと素数qに対し、qが非単元となる付値環A⊆Lが存在する。
ℤの極大イデアル(q)をℤのL内での整数閉包へ持ち上げ、
その極大イデアルを非単元へ送る付値環を取る。
体Lの代数性・代数閉性・完備性は要求しない。値群の正規化も選ばない。

単なる「何らかの付値環の存在」ではなく、指定した同じ素数qが非単元であることを保持する。
局所慣性やFrobeniusの定理には、その追加の幾何・ガロア条件を利用側で供給する。
-/
namespace DkMath.Lib.NumberTheory.ValuationPrimeExistence
open ValuationInertia

/-- [DkMath.Lib] 任意の標数0の体に、指定した素数q上の付値環が存在する。
標数0から整数の埋込みは単射、整数閉包はℤ上整なのでlying-overを適用できる。
極大イデアル中の同じqを、付値環の非単元へ写す。 -/
theorem exists_liesOverPrime {L : Type*} [Field L] [CharZero L] {q : ℕ} (hq : q.Prime) :
    ∃ A : ValuationSubring L, LiesOverPrime A q := by
  let O := integralClosure ℤ L
  let P : Ideal ℤ := Ideal.span {(q : ℤ)}
  have : P.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := O) P
  have := hQ
  have := hQP
  have hqQ : (q : O) ∈ Q := by
    simpa using (Ideal.mem_of_liesOver Q P (q : ℤ)).mp (Ideal.mem_span_singleton_self _)
  obtain ⟨A, -, hQA⟩ := Ideal.image_subset_nonunits_valuationSubring
    (A := (integralClosure ℤ L).toSubring) Q hQ.ne_top
  exact ⟨A, hQA ⟨(q : O), hqQ, by simp [O]⟩⟩

end DkMath.Lib.NumberTheory.ValuationPrimeExistence
