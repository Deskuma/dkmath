# IPSM-007 — Gate 4A review and Gate 4B positive-kernel roadmap

Date: 2026-08-13

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-prime-side-sign-mechanism-260813-v0`

Status: Gate 4A review / Gate 4B provider audit roadmap / no RH claim

---

## 0. Review result

The new module

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideMirrorAudit
```

is Green as a Gate 4A source-symmetry audit.

The following are now available:

```text
canonical Mellin quadratic weight evenness
full decomposed source reflection under s <-> 1 - s
full fixed-Xi vertical mirror pairing
right-edge full-source decomposed representation
explicit separation from finite von-Mangoldt cutoff conjugation
```

The public import is also present in `DkMath.RH`.

Gate 4A correctly does not claim that the finite prime cutoff inherits a termwise conjugate or adjoint partner.

Therefore the status is:

```text
Gate 3B algebraic route
  CLOSED

Gate 4A full-source mirror audit
  GREEN

finite prime-cutoff adjoint partner
  NOT FOUND

independent positivity provider
  OPEN
```

---

## 1. What Gate 4A actually gives

The available functional-equation symmetry is a reflection of the full decomposed source.

$$
D(1-s)=-D(s).
$$

In centered coordinates `z = s - 1/2`, this is the reflection `z -> -z`.

The canonical quadratic Mellin weight is even, so the full fixed-Xi contour can exploit this reflection at the whole-source level.

This is a genuine structural symmetry, but it is not yet a Hermitian pairing.

In particular, the finite arithmetic cutoff

```text
pascalPrimePowerPHZFiniteUpTo X
```

has not acquired an exact source-level theorem identifying its reflected value with a complex conjugate or adjoint value at the same cutoff.

That distinction must remain explicit in Gate 4B.

---

## 2. Existing Mellin input for Gate 4B

The generic Mellin box module already gives the exact logarithmic average

$$
H_\varepsilon(z)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}e^{uz}\,du.
$$

For the patched quadratic specialization at `tau = 0`, the current CFBRC weight is

$$
q_\varepsilon(z)=z^2H_\varepsilon(z).
$$

This is the correct fixed Gate 4B object.  Do not reintroduce a `tau -> 0` limit inside the sign audit.

The symmetric box immediately suggests two mathematically different structures:

```text
one-variable multiplier
  q_epsilon(z)

two-variable Gram kernel candidate
  K_epsilon(z,w)
```

Gate 4B must not confuse them.

---

## 3. Positive-kernel candidate from the same box

The logarithmic box average is taken against a positive uniform measure on `[-epsilon, epsilon]`.

This suggests the source-independent two-variable kernel

$$
K_\varepsilon(z,w):=z\overline{w}\,H_\varepsilon(z+\overline{w}).
$$

Using the log-average representation, this has the formal Gram representation

$$
K_\varepsilon(z,w)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}(ze^{uz})\overline{(we^{uw})}\,du.
$$

Therefore, for any finite family of coefficients and complex points, the associated double sum is a natural positive-semidefinite candidate:

$$
\sum_{j,k}c_j\overline{c_k}K_\varepsilon(z_j,z_k)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}\left|\sum_j c_j z_j e^{u z_j}\right|^2du\ge0.
$$

This is a proposed Gate 4B theorem surface, not a theorem currently supplied by the prime-side module.

The recommended implementation location is a pure analysis layer, for example:

```text
DkMath.Analysis.MellinQuadraticGramKernel
```

if the proof is independent of Xi, zeta, and the finite explicit formula.

---

## 4. Critical mismatch: the current weight is not the Gram diagonal

The diagonal of the candidate Gram kernel is

$$
K_\varepsilon(z,z)=|z|^2H_\varepsilon(2\operatorname{Re}z).
$$

The actual explicit-formula multiplier is instead

$$
q_\varepsilon(z)=z^2H_\varepsilon(z).
$$

These are structurally different objects.

Thus positivity of the Gram kernel does not by itself imply positivity of the current linear prime-side surface.

This is the main Gate 4B contract:

```text
A positive kernel is useful only if an exact bridge rewrites the scalar excess,
or a lower bound for the scalar excess, in terms of that positive kernel.
```

Do not define an energy from `K_epsilon` and then merely note that it is nonnegative.  The load-bearing theorem must connect it to the existing finite scalar excess.

---

## 5. Why quadraticization is the missing operation

The current pointwise deoriented source has the form

$$
q_\varepsilon(z)\,S_X(s).
$$

This is linear in the arithmetic/decomposed source `S_X`.

A Gram energy has the schematic form

$$
\iint F(z)\overline{F(w)}K_\varepsilon(z,w).
$$

or, in a finite arithmetic mode expansion, a double sum over two source indices.

Therefore an actual positivity provider now requires a new identity of one of the following kinds:

```text
linear explicit-formula surface
  = exact Gram double pairing

linear scalar excess
  >= explicit Gram energy

linear scalar excess
  = positive bulk energy + independently controlled boundary term
```

None of these follows from Gate 4A reflection alone.

The missing mathematical step may reasonably be called a quadraticization, polarization, Parseval/Plancherel, or autocorrelation bridge depending on the final construction.

---

## 6. Integration-by-parts audit

The same box representation gives an exact differential identity in the logarithmic box variable `u`.

$$
z^2e^{uz}=\frac{d^2}{du^2}e^{uz}.
$$

Hence

$$
q_\varepsilon(z)=\frac{1}{2\varepsilon}\int_{-\varepsilon}^{\varepsilon}\frac{d^2}{du^2}e^{uz}\,du=\frac{z(e^{\varepsilon z}-e^{-\varepsilon z})}{2\varepsilon}.
$$

This is an exact boundary-difference representation.

By itself it is not a positive bulk integral.  Therefore integration by parts is a viable Gate 4B route only if a new `u`-dependent paired source permits derivatives to be transferred and the resulting bulk term becomes a norm square or other independently nonnegative quantity.

If the only result is endpoint terms with uncontrolled sign, record an integration-by-parts obstruction instead of calling the result an energy.

---

## 7. Recommended Gate 4B implementation sequence

### Gate 4B.0 — exact box/quadratic identities

Expose named theorems for the fixed positive `epsilon` canonical box:

```text
H_epsilon log-average
q_epsilon = z^2 * H_epsilon
q_epsilon boundary-derivative identity
conjugation compatibility of H_epsilon / q_epsilon when available
```

Keep this at fixed `epsilon > 0`.

### Gate 4B.1 — pure Gram kernel

Define the two-variable kernel candidate and prove its exact integral representation.

Then prove positive semidefiniteness for finite families.

This theorem is valuable even if it does not close RH because it identifies the actual positive structure carried by the Mellin box.

### Gate 4B.2 — mismatch audit

Prove explicitly that the Gram diagonal and the current one-variable quadratic multiplier are different theorem surfaces.

Do not silently substitute one for the other.

### Gate 4B.3 — quadraticization bridge search

Attempt to rewrite the finite prime-side whole surface or scalar excess using the Gram kernel.

Possible inputs to inspect:

```text
finite von-Mangoldt mode expansion
full-source mirror pairing
right/left vertical pairing
horizontal-pair contribution
CF2D radial mass comparison
```

A valid theorem must remain exact at finite `X` and finite contour height.

### Gate 4B.4 — provider or obstruction

There are only two acceptable outcomes:

```text
A. exact source-derived positive provider

B. named obstruction stating that the available linear surface has no
   established bridge to the positive Gram kernel / positive bulk identity
```

Do not insert the desired finite excess sign as a hypothesis disguised as an energy contract.

---

## 8. Important scope discipline

Gate 4B must preserve all existing order and contour constraints:

```text
fixed finite contour height T
finite top-horizontal correction retained
fixed positive epsilon
finite cutoff X before X -> infinity transport
no X <-> epsilon exchange
no joint limit
no T -> infinity
no use of zero-side defect nonnegativity as the prime-side provider
```

The prime-side provider must remain logically independent of the existing zero-side anti-mirror energy theorem.

---

## 9. Interpretation if the Gram kernel is Green but no bridge is found

This is not a failure of the audit.

It would establish a precise structural result:

```text
the Mellin box carries an intrinsic positive-semidefinite two-variable kernel,
but the present explicit-formula defect surface is a one-variable linear
functional and has not been quadraticized into that kernel.
```

That would identify the next missing theorem far more sharply than the generic statement "positivity is still open".

The named obstruction should then say that the missing object is a source-derived quadraticization/adjoint bridge, not that positive kernels do not exist.

---

## 10. Non-goals

IPSM-007 does not claim:

```text
q_epsilon is pointwise nonnegative
finite prime cutoff has a conjugate partner
Gram positivity implies scalar excess positivity
a quadraticization bridge already exists
finite scalar excess is nonnegative
finite arithmetic defect is nonpositive
any limit exchange
fixed defect vanishing
Riemann Hypothesis
```

---

## 11. Checkpoint summary

```text
Gate 3B algebraic route
  CLOSED

Gate 4A full-source mirror audit
  GREEN

Gate 4B next
  4B.0 exact box/quadratic identities
  4B.1 positive-semidefinite Mellin Gram kernel
  4B.2 Gram-diagonal vs q_epsilon mismatch audit
  4B.3 source quadraticization / integration-by-parts bridge search
  4B.4 independent provider OR named obstruction
```

The decisive question is now not whether a positive kernel exists abstractly, but whether the finite prime-side scalar excess can be connected to that positive structure by an exact source-derived theorem.
