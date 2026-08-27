# IPSM-013 — Gate 4B.2 closeout and prime-side quadraticization roadmap

Date: 2026-08-14

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: implementation review / Gate 4B.2 closeout / Gate 4B.3 roadmap / no RH claim

---

## 0. Review result

The generic fixed-`ε` Mellin Gram layer is now fully Green.

Current classification:

```text
pointwise Gram expansion
  GREEN

integrated common identity
  GREEN

kernel quadratic form = feature-map energy
  GREEN

quadratic-form reality
  GREEN

finite-family PSD
  GREEN

pointwise Hermitian symmetry
  GREEN

Gate 4B.2
  CLOSED

prime-side source quadraticization
  OPEN
```

The generic kernel may now be called a fixed-`ε` finite-family PSD-certified Hermitian Gram kernel.

This closeout does not imply any sign theorem for the finite prime-side scalar excess.

---

## 1. Hermitian closeout is source-independent

The new theorem

```lean
mellinQuadraticBoxMultiplier_conj
```

proves the conjugation law for the centered Mellin box multiplier directly from the logarithmic-average representation.

Conceptually:

$$
H_\varepsilon(\overline u)=\overline{H_\varepsilon(u)}.
$$

The theorem

```lean
mellinQuadraticBoxGramKernel_conj_symm
```

then proves the pointwise Hermitian law

$$
K_\varepsilon(w,z)=\overline{K_\varepsilon(z,w)}.
$$

This proof is generic Mellin analysis.  It does not use the centered-Xi functional equation, the prime-side mirror module, the zero-side mirror pairing, or an RH-specific symmetry premise.

That separation is correct and should be preserved.

---

## 2. What is now certified

For every fixed positive `ε`, every finite family `z : Fin n → ℂ`, and every coefficient family `c : Fin n → ℂ`, the kernel-generated quadratic form equals the feature-map energy.

Conceptually:

$$
Q_\varepsilon(z,c)=E_\varepsilon(z,c).
$$

The feature-map energy is a normalized finite-interval integral of a norm square, so

$$
0\le \operatorname{Re}Q_\varepsilon(z,c).
$$

The imaginary part vanishes exactly.

Therefore the PSD statement is no longer a candidate-level heuristic.  It is a proved finite-dimensional theorem surface.

No limiting process is used in this certification.

---

## 3. Gate 4B.3 is a different problem

The prime-side finite arithmetic surface does not currently have the same algebraic arity as the Gram energy.

The finite prime cutoff has the exact shape

```text
finite sum over n
  of
finite contour-height integral
  of
quadratic Mellin weight × von-Mangoldt mode
```

The existing theorem

```lean
pascalPrimePowerRightEdgeCutoffIntegral_eq_vonMangoldt_sum
```

exposes this as a finite one-index sum.

By contrast, the Gram quadratic form has the exact shape

```text
finite sum over i
  finite sum over j
    coefficient_i × conjugate coefficient_j × kernel(i,j)
```

and therefore contains diagonal terms and off-diagonal cross terms.

This mismatch is not a Lean API issue.  It is the mathematical content of Gate 4B.3.

---

## 4. Variable ledger — do not identify unrelated variables

Three distinct variables currently appear in the project and must remain separate unless an exact theorem connects them.

```text
u
  logarithmic box-average variable in the Mellin Gram feature map

t
  contour-height variable on the finite right edge

n
  finite arithmetic / von-Mangoldt mode index
```

The Gram feature map uses the `u`-average.

The prime-side cutoff uses the `t` contour integral and finite `n` sum.

Do not silently identify:

```text
u = t
z_j = log n
finite Gram family = contour-height discretization
```

None of these identifications is presently a theorem.

In particular, no numerical quadrature or discretization of the finite contour is acceptable as an exact quadraticization bridge.

---

## 5. First exact adapter: identify the one-variable weight only

The next RH/CFBRC module should import the certified generic kernel and the existing prime-side whole-surface audit.

Recommended module:

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideQuadraticizationAudit
```

The first checkpoint should prove only the exact weight adapter between the RH specialization and the generic box weight.

The existing RH weight at `τ = 0` is constructed from the same box family and should have the mathematical form

$$
q_\varepsilon(z)=z^2H_\varepsilon(z).
$$

The generic analysis object is

```lean
mellinQuadraticBoxWeight ε z
```

Do not assume definitional equality.  Prove the adapter using the current definitions and compiler-visible theorem names.

This adapter does not imply a Gram representation because the Gram diagonal is a different object.

---

## 6. Prime-mode ledger before any quadraticization claim

After the weight adapter is Green, expose the finite prime source at the mode level without changing its mathematics.

For fixed `ε`, residue window `W`, cutoff `X`, and contour height `t`, keep visible:

```text
centered contour point
ordinary right-edge point
quadratic Mellin weight
finite von-Mangoldt cutoff
archimedean correction
elementary correction
top-horizontal term
radial comparison
```

For the prime component, reuse the existing finite expansion rather than inventing a second prime representation.

The key discipline is that the prime component is a finite linear sum in the arithmetic modes.

No Gram coefficients should be introduced yet merely to manufacture a square.

---

## 7. Required quadraticization contract

A successful Gate 4B.3 provider must be source-derived.

It is not enough to assert existence of arbitrary families `z` and `c` satisfying the desired equality.

For example, the following would be circular and is forbidden:

```text
choose c from sqrt(scalarExcess)
then GramEnergy = scalarExcess
```

Likewise, a structure field whose content is equivalent to

```lean
0 ≤ pascalCenteredXiMellinQuadraticScalarExcess ε W X
```

is not an independent provider.

A legitimate construction must define its finite-family data from already available arithmetic / contour data and then prove the equality.

The strongest desired shape is:

$$
E_{\varepsilon,X}(W)=\operatorname{Re}Q_\varepsilon(Z_{\varepsilon,W,X},C_{\varepsilon,W,X}).
$$

If an exact equality is too strong but a decomposition appears naturally, an acceptable alternative is:

$$
E_{\varepsilon,X}(W)=\operatorname{Re}Q_\varepsilon(Z,C)+R_{\varepsilon,W,X}.
$$

The remainder can support a sign theorem only if its nonnegativity is proved independently from source mathematics.

---

## 8. Cross-term ledger is load-bearing

The current finite prime source is linear in the finite arithmetic modes.

The Gram quadratic form is quadratic and therefore produces off-diagonal cross terms.

Any exact source-derived bridge must explain those cross terms.

There are only a few mathematically honest possibilities:

```text
A. cross terms cancel exactly
B. cross terms combine into archimedean / elementary / horizontal terms
C. cross terms combine with the radial comparison
D. a source-derived orthogonality theorem kills them
E. the current Gram kernel is not the correct quadraticization carrier
```

Do not drop the off-diagonal terms by definition.

A useful audit theorem may explicitly split a finite Gram quadratic form into diagonal and off-diagonal parts.  If implemented, keep it generic or local to the audit; do not claim that the prime modes satisfy the required cancellation until Lean proves it.

---

## 9. Baseline-plus-energy possibility

The prime-side sign target is the scalar excess

$$
E_{\varepsilon,X}(W)=\operatorname{Re}\mathcal W_{\varepsilon,X}(W)-\pi Q(W.R).
$$

Therefore the most useful positive representation would not merely represent the whole surface.  It would represent the difference from the radial baseline.

The ideal provider shape is conceptually

$$
\operatorname{Re}\mathcal W_{\varepsilon,X}(W)=\pi Q(W.R)+\text{PSD energy}.
$$

If such an identity exists, positivity follows immediately.

However, generic polarization or completion-of-squares identities alone do not provide this orientation.  A difference of two norm squares can have either sign.

Therefore any baseline-plus-energy theorem must be derived from the actual finite arithmetic / contour source.

---

## 10. Recommended Gate 4B.3 checkpoint sequence

### Gate 4B.3a — weight adapter

Prove that the current fixed-`ε`, `τ = 0` Mellin quadratic weight is exactly the generic `mellinQuadraticBoxWeight`.

No sign claim.

### Gate 4B.3b — finite source ledger

Expose the finite prime-mode linear decomposition in the new audit module by reusing current theorems.

Keep all four arithmetic surface contributions and the radial comparison visible.

No top-term deletion.

### Gate 4B.3c — arity / cross-term audit

Define a mathematically natural candidate finite-family mapping only if the source itself supplies one.

Expand the resulting Gram form and record diagonal/off-diagonal terms explicitly.

Do not choose coefficients from the target excess.

### Gate 4B.3d — source quadraticization decision

One of two outcomes is acceptable.

```text
GREEN PATH
  source-derived exact Gram / PSD representation
  -> finite scalar excess nonnegative
  -> finite defect nonpositive
  -> only then pass to existing ordered-limit transport
```

or

```text
OBSTRUCTION PATH
  no source-derived cancellation / identification found
  -> record a named PrimeSideQuadraticizationObstruction
  -> do not manufacture a provider
```

---

## 11. Limit and contour firewall remains unchanged

Gate 4B.3 is entirely finite.

Maintain:

```text
fixed finite T
fixed positive ε
fixed finite X
all four finite arithmetic terms retained
no T -> infinity
no X/ε limit exchange
no joint limit
no reverse limit
```

If a finite sign theorem is eventually obtained, the existing Gate 2 transport already knows how to move the sign through the ordered limits.

Do not duplicate or modify that transport layer here.

---

## 12. Zero-side firewall remains unchanged

The existing zero-side anti-mirror energy is not a permitted proof of the prime-side finite sign.

It may be used only as a comparison target after an independent prime-side theorem exists.

Do not use:

```text
fixed defect >= 0 from the zero side
```

to derive the prime-side finite inequality.

That would reverse the intended logical direction of the audit.

---

## 13. Gate 4B.2 closeout summary

```text
Generic Mellin box multiplier
  exact log-average
  conjugation law

Generic Hermitian Gram kernel
  exact integral representation
  pointwise Hermitian symmetry

Finite Gram quadratic form
  exact feature-map energy identity
  real-valued
  PSD for every finite family

Gate 4B.2
  CLOSED
```

The project has now answered one question conclusively:

```text
Does the fixed-ε Mellin box carry an independent positive Hermitian kernel?
  YES
```

The next question is different:

```text
Does the actual finite prime-side explicit-formula excess arise from that PSD structure?
  OPEN
```

---

## 14. Non-goals

IPSM-013 introduces no claim of:

```text
prime-side scalar excess nonnegativity
finite arithmetic defect nonpositivity
finite-cutoff conjugate provider
prime-mode orthogonality
off-diagonal cancellation
source-derived Gram representation
limit exchange
joint limit
T -> infinity
fixed defect vanishing
Riemann Hypothesis
```
