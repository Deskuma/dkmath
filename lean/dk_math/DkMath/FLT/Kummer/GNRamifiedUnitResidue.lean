/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNRamifiedArithmetic
import DkMath.Lib.NumberTheory.CosmicRamifiedUnitNormalization

#print "file: DkMath.FLT.Kummer.GNRamifiedUnitResidue"

/-!
# FLT 座標での単元の一次剰余

整数ノルムの根 t≡1 mod p の次に、円分整数環の生成元と単元へ戻る。
x=a+b, u=−b なので、剥離商の先頭項 −i*u は i*b になる。
生成元を γᵢ≡1 mod λ に選べば、残る単元の剰余は εᵢ≡i*b である。
この正規化は同じ剥離商・イデアル根を保持し、λ² 以上の単元解析や降下は行わない。
-/

namespace DkMath.FLT.Kummer

open scoped BigOperators NumberField
open DkMath.Lib.NumberTheory

/-- 分岐側の教科書的な一次単元正規化。
原始的 FLT 方程式と類数条件から全非自明因子のパケットを実際に構成し、
同じイデアル根の生成元を `γᵢ≡1` に選ぶ。そのとき `εᵢ≡i*b mod λ`。
各因子の厳密な等式 `a+ζ^i b=λ(εᵢ γᵢ^p)` はパケット内に保持される。 -/
theorem exists_GN_ramified_residue_normalized_packet
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p) (hp3 : 3 ≤ p)
    {a b c : ℤ} (hc0 : c ≠ 0) (heq : a ^ p + b ^ p = c ^ p)
    (hprim : IsCoprime a b) (hcase : (p : ℤ) ∣ c)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ Q : RamifiedPrincipalPowerPacket hζ (a + b) (-b) c,
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q.unitFactor i) = (i : ZMod p) * (b : ZMod p) := by
  obtain ⟨P⟩ := nonempty_GN_ramified_packet_of_flt_equation hζ hodd hp3 hc0 heq hprim hcase
  obtain ⟨Q, _, hred⟩ := P.exists_residue_normalized_principal_extension hodd hreg
  exact ⟨Q, by simpa only [Int.cast_neg, neg_mul_neg] using hred⟩

end DkMath.FLT.Kummer
