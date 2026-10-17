/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedUnitResidue
import DkMath.Lib.NumberTheory.CosmicRamifiedQuadratic

#print "file: DkMath.FLT.Kummer.GNRamifiedQuadratic"

/-!
# FLT 座標の正規化単元を mod λ² まで読む

前章の一次正規化 γᵢ≡1 mod λ により γᵢ^p≡1 mod λ² となる。
剥離商の幾何和の次の係数 choose i 2 が、そのまま単元の二次合同に現れる。
x=a+b,u=−b では `εᵢ ≡ i*b + choose i 2 * λ*b mod λ²`。
必要な λ³∣(a+b) は既存パケットの付値保存から導き、追加仮定にはしない。
-/

namespace DkMath.FLT.Kummer

open scoped BigOperators NumberField
open DkMath.Lib.NumberTheory

/-- 分岐側の正規化単元の二次合同条件。
一次正規化と同じ基底データを使い、全非自明添字について
`γᵢ≡1 mod λ`、`εᵢ≡i*b mod λ`、`εᵢ≡i*b+choose i 2*λ*b mod λ²` を返す。
p=3 も含む。単元の p 乗性や FLT の最終矛盾は結論しない。 -/
theorem exists_GN_ramified_quadratic_normalized_packet
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ Q : RamifiedPrincipalPowerPacket hζ (a + b) (-b) c,
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q.unitFactor i) = (i : ZMod p) * (b : ZMod p) ∧
        (hζ.toInteger - 1) ^ 2 ∣ Q.unitFactor i - (i : 𝓞 K) * (b : 𝓞 K) -
          (Nat.choose i 2 : 𝓞 K) * (hζ.toInteger - 1) * (b : 𝓞 K) := by
  obtain ⟨P⟩ := nonempty_GN_ramified_packet_of_flt_equation hζ hodd hp3 hc0 heq hprim hcase
  obtain ⟨Q, _⟩ := P.exists_principal_extension hreg
  obtain ⟨Q', _, hquad⟩ := Q.exists_quadratic_normalization hodd
  refine ⟨Q', fun i hi => ⟨(hquad i hi).1, ?_, ?_⟩⟩
  · simpa only [Int.cast_neg, neg_mul_neg] using (hquad i hi).2.1
  · simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using (hquad i hi).2.2

end DkMath.FLT.Kummer
