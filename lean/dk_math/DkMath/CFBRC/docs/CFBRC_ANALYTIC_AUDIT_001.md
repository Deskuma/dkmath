# CFBRC Analytic Continuation Audit 001

## Native finite-difference recovery of `ζ(-1) = -1/12`

This audit begins with a deliberately small and non-circular Core.

```text
polynomial moment x^m
→ finite forward differences
→ finite Euler transform
→ parity normalization
→ native value at -m
```

For `m = 1`, the only nonzero forward differences are

```text
f(1) = 1
Δf(1) = 1
Δ²f = 0
```

Therefore the finite Euler value is

$$
\eta_{\mathrm{FD}}(-1)=\frac12-\frac14=\frac14.
$$

The parity normalization is

$$
1-2^{1-(-1)}=1-2^2=-3,
$$

so the native CFBRC value is

$$
\zeta_{\mathrm{FD}}(-1)=\frac{1/4}{-3}=-\frac1{12}.
$$

## Independence boundary

The native modules do not import or use:

- `riemannZeta`;
- Hurwitz zeta;
- the analytic continuation of zeta;
- any RH or RH-CFBRC theorem;
- any infinite sum assigned to `1 - 2 + 3 - 4 + ⋯`.

The first Core proves only a finite-difference regularization result.  A later,
separate module will compare it with an Abel boundary value, and another
quarantined oracle module will compare it with Mathlib's standard
`riemannZeta` value.

## Current guarantee

The finite CFBRC regularization distinguishes both branches of the negative
integer pattern in the first small cases:

```text
ζFD( 0) = -1/2
ζFD(-1) = -1/12
ζFD(-2) = 0
ζFD(-3) = 1/120
```

This is an audit of finite regularization structure, not yet a construction of
a holomorphic continuation on the full complex plane.
