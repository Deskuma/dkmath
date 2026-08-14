# IPSM-018 — D8 review and polarization/autocorrelation roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4B.3 product-bridge audit / no sign claim / no RH claim

## 0. Review result

D2–D8 are Green in `PascalCenteredXiPrimeSideQuadraticizationAudit`.

The implemented chain now contains exact finite-cutoff conjugation for the PHZ, elementary and archimedean terms, full vertical amplitude conjugation, coefficient/feature/BoxFeature conjugation, symmetric aggregate reality, and a hardened adjoint provider whose provenance is the reflected finite source `t ↦ -t`.

The new provider is materially stronger than the legacy `source_derived : Prop` audit structure. Its fields require equality with the concrete mirrored aggregate and then equality of that mirrored aggregate with the conjugate aggregate.

Current classification:

```text
finite source conjugation                 GREEN
aggregated source reality                 GREEN
source-derived adjoint provider           GREEN
continuous vertical Gram energy           GREEN
source autocorrelation product identity   NEXT
actual vertical source = linear u-average NEXT
polarization identity                     NEXT
whole scalar-excess quadraticization      OPEN
top-horizontal/radial compatibility       OPEN
prime-side sign                           NOT CLAIMED
RH                                        NOT CLAIMED
```

## 1. D8 is a genuine source-derived adjoint

The mirrored aggregate is defined from the finite source itself by replacing `t` with `-t` under the same finite interval integral. It is not defined by applying `starRingEnd` to the aggregate.

The theorem

```lean
pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature_eq_conj
```

then proves that this source reflection equals the conjugate aggregate. Therefore the new

```lean
PascalCenteredXiPrimeSideQuadraticizationSourceDerivedAdjointProvider
```

is an acceptable provenance-bearing contract.

This closes the adjoint search. It does not yet close quadraticization.

## 2. First product theorem: source autocorrelation

The next smallest theorem should multiply the aggregate by the concrete mirrored aggregate.

Suggested definition:

```lean
noncomputable def pascalCenteredXiPrimeSideQuadraticizationSourceAutocorrelation
    (W : PascalCenteredXiResidueTransportWindow) (X : ℕ) (u : ℝ) : ℂ :=
  pascalCenteredXiPrimeSideQuadraticizationAggregatedBoxFeature W X u *
    pascalCenteredXiPrimeSideQuadraticizationMirroredAggregatedBoxFeature W X u
```

Then prove the exact pointwise identity

$$
C_X(u)=|F_X(u)|^2.
$$

In Lean, the right side may be written as `(Complex.normSq (...) : ℂ)`.

After that, prove that the normalized `u`-integral of this source autocorrelation is exactly the existing continuous Gram energy cast to `ℂ`.

This theorem certifies that the already-positive Gram energy has a genuine source-derived product representation. It still does not identify the original linear explicit-formula source with that product.

## 3. Load-bearing bridge still missing: actual vertical source to linear aggregate

The pointwise theorem already gives

$$
\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}B_X(t,u)\,du=q_\varepsilon(z_W(t))A_X(t).
$$

The next source-level target is the integrated version

$$
V_{\varepsilon,X}(W)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}F_X(u)\,du.
$$

Here `V` must be the actual deoriented finite vertical source, not a newly defined surrogate.

This step requires an exact finite-rectangle `t/u` integral interchange, or an equivalent theorem chain. Do not invoke a limit theorem. Both variables remain on finite intervals.

Recommended proof architecture:

```text
actual deoriented vertical surface
  -> integral_t (weight * amplitude)
  -> integral_t (normalized integral_u BoxFeature)
  -> normalized integral_u (integral_t BoxFeature)
  -> normalized integral_u AggregatedBoxFeature
```

If the interchange requires new integrability lemmas, prove them explicitly. Do not leave equality justified only by totalized integrals.

## 4. The one-variable weight is a cross section, not a Gram diagonal

The correct structural interpretation is now visible.

Define the generic zero/vacuum section

```lean
mellinQuadraticBoxZeroSection ε z :=
  z * mellinQuadraticBoxMultiplier ε z
```

so that

```text
mellinQuadraticBoxWeight ε z
  = z * mellinQuadraticBoxZeroSection ε z.
```

The zero section has the exact box-average representation

$$
Z_\varepsilon(z)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}ze^{uz}\,du.
$$

This is the pairing of the Gram feature `z * exp(u*z)` with the constant reference function `1` in the normalized box space.

It is also the normalized zero-node section of the two-variable kernel in the formal sense suggested by

$$
\frac{K_\varepsilon(z,w)}{\overline w}=zH_\varepsilon(z+\overline w).
$$

A `w → 0` theorem may be added later, but it is not required to establish the exact constant-reference pairing. Avoid introducing a punctured-limit proof before the exact algebraic zero-section API is useful.

## 5. Polarization gives an exact difference of PSD energies, not a sign

Once the linear aggregate theorem is Green and aggregate reality is already Green, the vertical linear source is an inner product against the constant reference `1`.

For real-valued aggregate `F_X(u)`, the pointwise polarization identity is

$$
4F_X(u)=|F_X(u)+1|^2-|F_X(u)-1|^2.
$$

After normalized integration this expresses the actual vertical linear source as a difference of two nonnegative quadratic energies.

This is useful because it is an exact quadraticization identity, but it does not imply a sign. The difference of two PSD quantities is not PSD.

Therefore do not claim that polarization by itself closes Gate 4B.3.

A suitable named boundary after this theorem is established would be conceptually equivalent to:

```text
Linear source has an exact polarization representation,
but no source-derived dominance between the two PSD energies is known.
```

## 6. Autocorrelation and polarization are different bridges

Keep these two results separate.

```text
autocorrelation:
  F_X * mirrored(F_X)
  -> |F_X|^2
  -> positive Gram energy

polarization:
  linear average of F_X
  -> difference of shifted norm-square energies
  -> exact but sign-indefinite
```

The source-derived adjoint closes the first product construction. It does not turn the second construction into a positive quantity.

## 7. Whole-excess firewall

The scalar excess still has the exact form

```text
whole complex surface real part
  minus
π * fixed radial second moment.
```

The whole complex surface still contains the top-horizontal correction in addition to the vertical source.

Therefore, even after the vertical polarization theorem, the following remain independent obligations:

```text
top-horizontal contribution -> compatible quadratic/cross term   OPEN
radial subtraction -> compatible quadratic baseline              OPEN
whole scalar excess -> one PSD quantity or controlled difference OPEN
```

Do not use the zero-side anti-mirror positivity theorem to fill the radial slot; that would cross the existing circularity firewall.

## 8. Recommended next checkpoint

```text
P0  source autocorrelation = normSq aggregate
P1  normalized autocorrelation integral = continuous Gram energy
P2  actual deoriented vertical source = normalized linear u-average
P3  generic zero/vacuum section API
P4  exact constant-reference polarization identity
P5  classify the result:
      - exact difference-of-PSD only, or
      - source-derived dominance found
P6  only then audit top-horizontal and radial compatibility
```

Expected conservative outcome after P0–P4:

```text
source-derived adjoint             GREEN
source-derived autocorrelation     GREEN
vertical linear quadraticization   GREEN as polarization
vertical positivity                NOT IMPLIED
whole-excess positivity            OPEN
```

The current research question has therefore narrowed from “where is the adjoint?” to “what source-derived relation, if any, orders the two polarized energies or completes the whole excess into a single positive square?”
