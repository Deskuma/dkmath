# Ultra-001C Report — Exact lifted-radical identity

Date: 2026-07-26  
Status: **complete**

## 実装結果

```lean
Triple.rad_gnPowerLift_eq_rad_mul_nonExceptionalSupport_of_prime
Triple.log_rad_gnPowerLift_eq_log_rad_add_log_nonExceptionalSupport_of_prime
Triple.oddPrimeJointPressure_iff_nonExceptionalChannelMass
```

正の ABC triple と素数指数 `p` について:

```text
rad(lift product)
  =
rad(original ABC product)
  * GNNonExceptionalSupportProduct
```

が exact に成立する。

odd 仮定は不要である。odd 性が必要なのは M1 の exceptional valuation
excess zero であり、radical support identity 自体は `p = 2` でも成立する。

## Mechanism

```text
lift support prime
  -> original coordinate prime
     or GN support prime

GN support prime q
  -> q ∤ p: fresh non-exceptional support
  -> q ∣ p: q = p and p ∣ GN -> p ∣ T.a
```

fresh support は original support と disjoint なので、support union の積が
そのまま radical の積になる。

従って joint predicate は exact に:

```text
S + E <= ρ R + C
```

へ正規化される。

## Scope

素数仮定を単なる `2 <= n` へ弱めることはできない。例えば
`T=(1,1,2), n=6` では exceptional composite support の吸収が崩れる。
