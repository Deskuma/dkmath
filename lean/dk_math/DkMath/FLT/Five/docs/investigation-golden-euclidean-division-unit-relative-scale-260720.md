# Golden Euclidean Division from Unit-Relative Scaling

Date: 2026-07-20
Status: mathematical investigation and implementation design
Context: FLT5 cp-004g blocker, dynamic harmonic number theory, unit-relative scaling, Petal reuse

## 1. Current certified endpoint

The FLT5 tower has certified the following data for every stripped exceptional packet.

$$\beta\,\overline{\beta}=b^5$$

$$\operatorname{GoldenRelPrime}(\beta,\overline{\beta})$$

$$\beta_{\mathrm{snd}}=-5^7a^{10}$$

The remaining reusable factorization gate is:

```lean
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

The golden order already has an honest `CommRing`, `NoZeroDivisors`, and `IsDomain` instance. The missing structure is a certified gcd / factorization mechanism, not domainhood.

## 2. Red-ribbon model: unit-relative coordinates

Let `U` be an old unit ribbon and `V` a new unit ribbon with

$$U=3V.$$

For the same physical quantity `Q`, write

$$Q=x_UU=x_VV.$$

Then

$$x_V=3x_U.$$

The object is unchanged. Only its coordinate changes. In general, if

$$V=\lambda U,$$

then

$$x_V=\lambda^{-1}x_U.$$

For a degree-`d` quantity,

$$V^d=\lambda^dU^d$$

and therefore

$$x_V=\lambda^{-d}x_U.$$

The invariant quantity is

$$x_VV^d=x_UU^d.$$

This separates three meanings of `1`:

1. the coordinate `1` in a chosen unit world;
2. the concrete unit object itself;
3. the multiplicative identity action, which leaves every object unchanged.

The third is the genuinely world-independent `1`.

## 3. Golden units and the invariant observation world

For `x=a+bφ`, define

$$N(x)=a^2+ab-b^2.$$

Every golden unit `ε` has

$$N(\varepsilon)=\pm1.$$

Hence

$$|N(\varepsilon x)|=|N(x)|.$$

Coordinates change under a unit action, but the absolute norm does not. Therefore the absolute norm is the correct observation world in which unit-relative representations become invisible.

This is the multiplicative analogue of the ribbon invariant:

```text
coordinate changes
  + unit changes
  = invariant quantity
```

For the FLT5 tower, this suggests proving gcd and factorization through the Euclidean size

$$\delta(x)=|N(x)|.$$

## 4. Rational golden coordinates

Write a rational golden element as

$$q=A+B\varphi,\qquad A,B\in\mathbb Q.$$

For every rational number `A`, choose an integer `m` with

$$|A-m|\le\frac12.$$

Likewise choose `n` with

$$|B-n|\le\frac12.$$

Set

$$u=A-m,\qquad v=B-n.$$

Then

$$|u|\le\frac12,\qquad|v|\le\frac12.$$

The approximation error is

$$e=u+v\varphi.$$

Its norm is

$$N(e)=u^2+uv-v^2.$$

## 5. The `5/16` fundamental-cell bound

Two square completions give the sharp uniform estimate needed for division.

First,

$$u^2+uv-v^2=\frac54u^2-\left(v-\frac u2\right)^2.$$

Therefore

$$u^2+uv-v^2\le\frac54u^2\le\frac5{16}.$$

Second,

$$u^2+uv-v^2=\left(u+\frac v2\right)^2-\frac54v^2.$$

Therefore

$$u^2+uv-v^2\ge-\frac54v^2\ge-\frac5{16}.$$

Hence

$$|N(e)|\le\frac5{16}<1.$$

This is the central quantitative result.

Interpretation:

> Every rational golden element lies within absolute-norm distance at most `5/16` of an integral golden lattice point.

The square coordinate cell

$$[-1/2,1/2]\times[-1/2,1/2]$$

is therefore a strict contraction cell for the golden norm.

## 6. Explicit quotient coordinates

Let

$$x=a+b\varphi$$

and

$$y=c+d\varphi\ne0.$$

The conjugate is

$$\overline y=(c+d)-d\varphi$$

and

$$N(y)=c^2+cd-d^2\ne0.$$

Since

$$x/y=x\overline y/N(y),$$

the rational coordinates of the quotient are

$$A=\frac{a(c+d)-bd}{N(y)}$$

and

$$B=\frac{bc-ad}{N(y)}.$$

Choose nearest integers `m,n` to `A,B`, and set

$$q=m+n\varphi.$$

Then

$$e=x/y-q$$

has coordinate errors bounded by `1/2`, so

$$|N(e)|\le\frac5{16}<1.$$

Define

$$r=x-qy=ye.$$

By norm multiplicativity,

$$|N(r)|=|N(y)|\,|N(e)|<|N(y)|.$$

Thus

$$x=qy+r$$

with

$$r=0\quad\text{or}\quad|N(r)|<|N(y)|.$$

This is the desired Euclidean division theorem.

## 7. Expected algebraic consequences

Once a division theorem is certified with Euclidean measure

$$\delta(x)=\operatorname{natAbs}(N(x)),$$

one may construct or derive:

```text
Euclidean division
  -> gcd existence
  -> GCDMonoid / EuclideanDomain bridge
  -> coprime factors of a fifth power split up to units
  -> GoldenCoprimeFactorOfFifthPower
  -> beta = epsilon * gamma^5
```

The preferred route is to reuse Mathlib after the weakest honest standard instance has been constructed. No `GCDMonoid`, `EuclideanDomain`, `UniqueFactorizationMonoid`, or PID instance may be declared before the required laws are proved.

## 8. Relationship to unit classification

This investigation does not require classifying all units before constructing division.

Unit classification becomes relevant after the factorization theorem gives

$$\beta=\varepsilon\gamma^5.$$

If every unit is `±φ^n`, then modulo fifth powers the unit direction reduces to finitely many representatives

$$1,\varphi,\varphi^2,\varphi^3,\varphi^4.$$

The existing fifth-power coordinate formulas can then be compared with

$$\beta_{\mathrm{snd}}=-5^7a^{10}.$$

The order of attack should therefore be:

```text
absolute-norm division
  -> gcd / factor splitting
  -> beta = unit * fifth power
  -> unit classes modulo fifth powers
  -> coordinate contradiction or strict descent
```

## 9. Dynamic harmonic number theory reading

The quotient `x/y` is an observation in the scale determined by `y`. Rounding its two rational coordinates returns that observation to the nearest integral golden unit cell.

```text
arbitrary scale observation
  -> divide by the current unit
  -> rational golden coordinates
  -> nearest lattice representative
  -> fundamental error cell
  -> strict norm contraction
```

This is a multiplicative normalization process:

- scaling changes coordinates;
- inverse scaling restores the old coordinates;
- the invariant quantity is observed through absolute norm;
- the Euclidean remainder is the residual Gap after returning to the integral unit lattice.

The logarithmic analogue records repeated scale changes additively:

$$\log\prod_i\lambda_i=\sum_i\log\lambda_i.$$

Thus this division construction is compatible with the DkMath viewpoint that exponentials encode multiplicative scale and logarithms encode additive harmonic position.

## 10. Petal fallback value

Even if the full `EuclideanDomain GoldenInt` construction is blocked by Lean infrastructure, the following pieces remain independently valuable for Petal and other DkMath layers:

1. nearest-lattice normalization;
2. a finite fundamental observation cell;
3. a strict invariant-measure contraction;
4. coordinate/unit contravariance under scaling;
5. a canonical residual Gap after normalization;
6. termination of repeated normalization by a natural-valued measure.

This is directly analogous to Petal mechanisms in which a state is returned to a finite address window while a global scale counter records the removed magnitude.

A future generic API may abstract:

```lean
structure UnitRelativeLattice where
  Coord : Type _
  State : Type _
  scale : State → Coord
  normalize : Coord → State
  residual : Coord → Coord
  measure : Coord → ℕ
  residual_lt : ...
```

No such abstraction should be introduced inside cp-004i unless the concrete golden proof is already stable.

## 11. Lean targets

Suggested concrete declarations:

```lean
def GoldenRat := ℚ × ℚ

def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

```lean
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2
```

```lean
theorem goldenRat_norm_abs_le_five_sixteen
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| ≤ (5 : ℚ) / 16
```

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  ...
```

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt)
    (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ Int.natAbs (goldenNorm r) <
        Int.natAbs (goldenNorm y))
```

The exact names may change after repository reconnaissance. The mathematical contract should remain unchanged.

## 12. Success criterion

The strongest target is an honest standard algebraic instance sufficient to apply Mathlib's coprime-power factor theorem.

A valid narrower success is a direct proof of `GoldenCoprimeFactorOfFifthPower` using the certified division algorithm without installing a global instance.

A valid fallback success is a no-sorry golden quotient/remainder theorem plus a precise Lean-level report identifying the single remaining standard-structure bridge.

The campaign must not stop merely after restating that a Euclidean algorithm is needed. It must implement the nearest-lattice and `5/16` contraction core first.
