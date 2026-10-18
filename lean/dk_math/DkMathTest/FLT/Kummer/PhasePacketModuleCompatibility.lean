/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

module

public import DkMath.FLT.Kummer.CaseIConjugationPacket

#print "file: DkMathTest.FLT.Kummer.PhasePacketModuleCompatibility"

/-! Preserve the existing provider import from Lean's module system as well as ordinary imports. -/

@[expose] public section

open scoped NumberField
open DkMath.FLT.Kummer.CaseIConjugation

example {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (hp5 : 5 ≤ p) {ζ : 𝓞 K}
    (hζ : IsPrimitiveRoot ζ p) {a b : ℤ} {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (hfactor : (u : 𝓞 K) * α ^ p = a + ζ * b) :
    Nonempty (Packet (p := p) ζ a b) := packet_of_factor hp5 hζ hfactor
