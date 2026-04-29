# CF-Pythagoras Chapter 2 Route Map

cid: 69e72cfc-9944-83e8-8786-53c02b36fb89

この文書は、ピタゴラス宇宙式から FLT 型の高次差冪へ進めた
Chapter 2 の接続図を固定するための route map である。

## Scope

Chapter 2 で閉じた範囲は、d=3 の ordinary primitive branch である。

具体的には、次の bundled context を標準入口とする。

```lean
CubicPrimitiveFLTContext
```

この context は次の仮定を束ねる。

```text
PrimitivePrimeFactorOfDiffPow q a b 3
b < a
Int.gcd (a : ℤ) (b : ℤ) = 1
(b : ℤ)^3 + y^3 = (a : ℤ)^3
y.natAbs ≠ 0
q ≠ 3
```

ここに GN 側の fuel として次のどちらかを渡すと、`False` へ到達する。

```lean
padicValNat C.q
  (DkMath.CosmicFormulaBinom.GN 3 ((C.a : ℤ) - (C.b : ℤ)) (C.b : ℤ)).natAbs ≤ 1

Squarefree
  (DkMath.CosmicFormulaBinom.GN 3 ((C.a : ℤ) - (C.b : ℤ)) (C.b : ℤ)).natAbs
```

したがって、現時点での正確な到達点は次の通り。

```text
d=3 ordinary primitive branch (`q ≠ 3`) の抽象反駁エンジンは no-sorry で接続済み。
```

ただし、FLT d=3 全体を閉じたとはまだ言わない。

## Route

通常枝の主要経路は次の通り。

```text
PrimitiveBeam
  -> GN
  -> PowerBeam
  -> gcd / p-adic valuation
  -> contradiction
```

Lean 上の接続は、おおむね次の層に分かれる。

| Layer | File | Main API |
| --- | --- | --- |
| PowerGap / PowerBeam algebra | `DkMath/CosmicFormula/PowerGapBeam.lean` | `powerGap_eq_sub`, `powerBeam_eq_diffPowSum`, `powerBeam_three`, `flt_eq_forces_powerGapBeam` |
| GN bridge | `DkMath/CosmicFormula/PowerGapBeamGN.lean` | `powerBeam_three_eq_GN_of_gap`, `powerBeam_three_padicValNat_eq_GN_gap`, `powerBeam_three_squarefree_of_GN_squarefree` |
| gcd / valuation contradiction | `DkMath/CosmicFormula/PowerGapBeamGcd.lean` | `flt_beam_prime_val_le_one_contradiction`, `flt_beam_squarefree_prime_contradiction` |
| primitive-prime bridge | `DkMath/CosmicFormula/PowerGapBeamPrimitive.lean` | `primitive_prime_dvd_powerBeam_three_natAbs`, `flt_three_primitive_GN_val_le_one_contradiction_of_lt_ne_three`, `flt_three_primitive_GN_squarefree_contradiction_of_lt_ne_three` |
| bundled ordinary cubic context | `DkMath/CosmicFormula/PowerGapBeamPrimitive.lean` | `CubicPrimitiveFLTContext`, `CubicPrimitiveFLTContext.val_le_one_contradiction`, `CubicPrimitiveFLTContext.squarefree_contradiction` |

## Ordinary Cubic Context API

For an ordinary cubic context `C : CubicPrimitiveFLTContext`, use these as the
standard surface.

```lean
C.prime
C.q_not_dvd_three
C.beam_dvd
C.beam_ne
C.val_le_one_contradiction
C.squarefree_contradiction
```

The first four expose derived facts from the bundled hypotheses:

```text
C.prime            : Nat.Prime C.q
C.q_not_dvd_three  : ¬ C.q ∣ 3
C.beam_dvd         : C.q ∣ (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs
C.beam_ne          : (powerBeam 3 (C.b : ℤ) (C.a : ℤ)).natAbs ≠ 0
```

The last two are the standard contradiction endpoints:

```text
C.val_le_one_contradiction
  : v_q(GN(3, a-b, b)) ≤ 1 -> False

C.squarefree_contradiction
  : Squarefree(|GN(3, a-b, b)|) -> False
```

## What Is Closed

Chapter 2 closes the ordinary cubic primitive route as an abstract engine.

In words:

```text
If a primitive prime witness q for a^3 - b^3 exists with b < a,
the FLT-shaped equation b^3 + y^3 = a^3 is primitive,
y is nonzero, and q ≠ 3,
then either a valuation upper bound v_q(GN) ≤ 1 or squarefreeness of GN
contradicts the FLT-shaped equation.
```

This route is implemented without new `sorry` in the PowerGapBeam layer.

## What Remains Open

Two parts are deliberately not claimed as closed.

1. The exceptional cubic branch `q = 3`.

   The current valuation route assumes `q ∤ 3`, supplied in the ordinary branch
   by `q ≠ 3`.  Therefore `q = 3` should be handled by a separate context or a
   separate theorem family.

2. Automatic GN fuel supply.

   The context contradiction theorems currently require one of these as input:

   ```text
   v_q(GN(3, a-b, b)) ≤ 1
   Squarefree(|GN(3, a-b, b)|)
   ```

   Supplying these automatically from a broader primitive / Zsigmondy /
   squarefree pipeline is the next layer, not part of the ordinary branch engine
   itself.

## Research Claim

The strongest accurate claim at this point is:

```text
Chapter 2 extends the Pythagorean Gap/Beam viewpoint to the cubic FLT-shaped
difference route and closes the d=3 ordinary primitive branch (`q ≠ 3`) as a
no-sorry abstract contradiction engine.
```

The corresponding non-claim is:

```text
This does not yet close all of FLT d=3, because the exceptional branch `q = 3`
and automatic GN valuation/squarefree fuel supply remain separate tasks.
```
