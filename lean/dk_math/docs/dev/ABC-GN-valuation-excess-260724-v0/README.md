# ABC–GN Valuation Excess Workbench

作成日: 2026-07-24  
Status: **deterministic spine complete / research paused**

Repository: `Deskuma/dkmath`  
Draft PR: `#67 WIP: ABC–GN valuation excess route`

## Final report

The complete implementation review, theorem map, remaining mathematical cores, and restart plan are recorded in:

```text
FINAL_REPORT.md
```

## 1. Closure summary

この workbench は、一般 `GN`、`padicValNat`、factorization、`rad`、primitive-prime bridge を ABC triple 上で再接続し、次の決定論的主線を Lean theorem として完成させた。

```text
ABC triple
  -> GN power lift
  -> boundary / GN p-adic split
  -> q | n / q ∤ n support split
  -> exact support / valuation-excess identity
  -> unconditional GN return
  -> exceptional support absorption
  -> fresh non-exceptional support return
  -> support budget + valuation budget
  -> explicit K_epsilon ABC bound
```

最終実装は、三つの一様 budget を与えれば、正の ABC triple 全体について一つの明示定数 `K >= 1` が存在し、

$$c\le K\operatorname{rad}(abc)^{1+\varepsilon}$$

が従うことを証明する。

ABC 予想そのものは未証明である。残る数学は次の三魔核へ分離された。

```text
1. uniform lifted-radical support growth
2. uniform exceptional valuation excess
3. uniform non-exceptional valuation excess
```

詳細は `FINAL_REPORT.md` を参照する。

## 2. Final reading order

```text
FINAL_REPORT.md
report-007.md
DkMath/ABC/GNFinalBudgetBridge.lean
DkMath/ABC/GNSupportReturn.lean
```

開発履歴を追う場合は、`instruction-001.md` から `instruction-006.md`、`report-001.md` から `report-007.md` を読む。

## 3. Completed checkpoints

```text
ABC-GN-001  GN power lift                                      complete
ABC-GN-002  coprime / support separation                       complete
ABC-GN-003  p-adic boundary–GN split                           complete
ABC-GN-004  q | n / q ∤ n exceptional split                    complete
ABC-GN-005  exact log(rad) + valuation-excess identity         complete
ABC-GN-006  unconditional GN return and quality bridge         complete
ABC-GN-007  finite high-lift carrier API                       complete
ABC-GN-008  exceptional support absorption / fresh return      complete
ABC-GN-009  two-budget composition / explicit K_epsilon        complete
ABC-GN-010  uniform budgets / abc_main_axiom replacement       paused
```

## 4. Main implementation modules

```text
DkMath/ABC/GNPowerLift.lean
DkMath/ABC/GNValuationSplit.lean
DkMath/ABC/GNExceptionalSplit.lean
DkMath/ABC/GNValuationExcess.lean
DkMath/ABC/GNHighLift.lean
DkMath/ABC/GNQualityExcessBridge.lean
DkMath/ABC/GNSupportReturn.lean
DkMath/ABC/GNFinalBudgetBridge.lean
```

## 5. Lean-confirmed mathematical chain

For `T : Triple`, `n >= 2`, `0 < T.a`, `0 < T.b`:

### GN return

$$ (n-1)\log T.c\le\log GN_n(T.a,T.b) $$

### Exact support / multiplicity identity

$$ \log GN_n=\log\operatorname{rad}(GN_n)+GNValuationExcess_n $$

### Exponent support split

$$ \operatorname{rad}(GN_n)=E_nN_n $$

$$ E_n\mid\operatorname{rad}(n) $$

### Fresh support return

$$ \operatorname{rad}(abc)N_n\mid\operatorname{rad}(\text{lifted }abc) $$

### Two-budget composition

If

$$\log\operatorname{rad}(\text{lifted }abc)\le(1+\sigma)\log R+C_s$$

and

$$GNValuationExcess\le\tau\log R+C_e$$

then

$$ (n-1)\log c\le(\sigma+\tau)\log R+C_s+C_e+\log\operatorname{rad}(n) $$

where `R = rad(a*b*c)`.

If additionally

$$\sigma+\tau\le(n-1)(1+\varepsilon)$$

then an explicit `K >= 1` gives

$$c\le K R^{1+\varepsilon}$$

for the positive triple.

## 6. Final theorem surface

```lean
Triple.pow_pred_c_le_GN
Triple.log_c_mul_pred_le_log_GN
Triple.log_GN_eq_log_rad_add_GNValuationExcess

GN_support_eq_exceptional_union_nonExceptional
rad_GN_eq_exceptional_mul_nonExceptional
GNExceptionalSupportProduct_dvd_rad
Triple.nonExceptionalSupport_fresh
Triple.rad_mul_nonExceptionalProduct_dvd_lift_rad
Triple.GNSupportBudgetAffine_of_liftGrowth

GNValuationExcessBudgetAffine.of_split
Triple.log_c_mul_pred_le_of_support_and_excessBudget
Triple.log_c_mul_pred_le_of_liftGrowth_and_excessBudget
Triple.abc_bound_of_liftGrowth_and_excessBudget
abc_positive_of_GNFinalBudgetContract
```

## 7. Validation

Final implementation checkpoint:

```text
commit 5f0b9f80cd6afc20692eb6f4670ea65c8872d5a2
```

Local build:

```text
lake build DkMath.ABC.GNFinalBudgetBridge
Build completed successfully (8343 jobs)
```

GitHub:

```text
Lean CI run 271
conclusion: success
```

Axiom audit for representative final endpoints:

```text
propext
Classical.choice
Quot.sound
```

No new `axiom`, `sorry`, or `native_decide` proof was added. `abc_main_axiom` was neither modified nor used as a proof input.

## 8. What is not claimed

```text
ABC conjecture is proved
abc_main_axiom is removed
uniform budgets exist
all high lifts are excluded
GN is generally squarefree
probability / density routes are unnecessary
```

The global contract currently covers positive triples. The thin endpoint bridge for `a = 0` or `b = 0` is not implemented.

## 9. Restart boundary

There is no active Codex instruction.

`CODEX_START.md` is set to paused state. Do not restart implementation until a new instruction is added and D. explicitly triggers it.

Recommended future attack order:

```text
A. exceptional valuation multiplicity
B. lifted-radical support growth
C. non-exceptional high-lift depth
D. support–multiplicity balance theorem
```

## 10. Branch boundaries

```text
develop
  └─ feature/ABC-GN-valuation-excess-260724-v0
       └─ wip/ABC-GN-valuation-excess-260724-Codex
```

Parallel FLT7 branch:

```text
wip/FLT7-magic-core-260722-WiseWolf
```

This workbench must not modify or import unmerged work from `DkMath/FLT/Seven/**`.

## 11. Closure

This project did not defeat the ABC conjecture.

It did complete the deterministic translation layer that exposes the remaining obstruction as explicit theorem contracts:

```text
support growth
exceptional multiplicity
non-exceptional multiplicity
```

The workbench is therefore sealed at a mathematically meaningful boundary. Future work begins from the three exposed cores, not from the original fog around `rad`, quality, and repeated prime powers.
