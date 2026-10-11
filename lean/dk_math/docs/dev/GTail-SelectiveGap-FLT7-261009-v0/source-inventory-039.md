# Step039 source inventory / type ledger

2026-10-11。Base HEAD `3644e9a7b272b587d90035f2fc585d5ab4202fe9`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
review-038 / report-038 / source-inventory-038 / frontier-038 と actual owners を確認した。
新 owner は Step038 のみ direct import。GTailBridge は既存 closure に含まれるので追加しない。

Q=a²+ab+b²:ℕ、T=GTail 7 1 g c:ℕ、Δ=(a:ℤ)⁷+(b:ℤ)⁷−(c:ℤ)⁷:ℤ。
Δ の natural subtraction は使わない。旧 E/R/C、nativeKernel、source ideal types を保持する。

| Source / target | Precise assumptions / owner | Implication / reverse boundary |
|---|---|---|
| hEq / Δ=0 | actual Fermat7Equation is a⁷+b⁷=c⁷ in ℕ | new zero-defect iff, focus 不要。exact casts で両向き |
| exact focused balance | hfocus; GTailBridge.gtail_seven_defect over CommRing | g*T=7ab(a+b)Q²+Δ。Step032 exact balance iff hEq |
| q∣Q / q²∣Δ | hfocus; no prime / primitive / positivity / hEq required | new q²∣Δ ↔ q²∣g*T, Int→Nat casts confirmed |
| q∣Δ / endpoint unit | q prime,hcop,hQ; focus 不要 | new ¬q∣c。Δ=0 / hEq は導かない |
| q² product / square branch | q prime≠7,hcop,hQ,hfocus,q²∣Δ | q²∣g with q∤T / ratio1 OR q²∣T with q∤g。entry hT / hEq なし |
| scalar valuation equality | Step010/031 exact focused hEq + nonzero / units, or explicitly supplied budget | q²∣Δ は下界であり budget equality の一般証拠ではない |
| canonical ratio | Step038 gap_ratio_eq_one: q prime,q∤c,q∣g | ratio1、canonical nonidentity guard fails。other supplied roots を否定しない |
| native C receiver | Step037 hQ,q∤b,c,g,hT | actual kernel / contractions / α,F0 membership; hEq 不要 |
| bounded native powers | Step037 native_square_support adds q≠3,q²∣T | one-way M²/M³/M⁴ lower bounds; exact valuation / reconstruction ではない |
| signed provider | old packet exact fields | local defect / ideal support は field construction ではない |

## Actual source signatures and proof overlap

- GTailBridge.gtail_seven_defect `{R} [CommRing R] (a b c g:R) (hsum:a+b=c+g)`:
  `g*GTail 7 1 g c = 7*a*b*(a+b)*(a²+a*b+b²)²+(a⁷+b⁷−c⁷)`。
  新 integer identity はこれと finite-sum GTail の Nat→Int cast のみを使う。
- Lib.Cosmic.GTailSeven の add_pow_seven_eq_gap_add_interior は任意 CommSemiring:
  `(a+b)⁷=(b⁷+a⁷)+7ab(a+b)Q²`。endpoint proof はこの既存 shell を使い再証明しない。
- Lib.Cosmic.GTailSevenArithmetic.coprime_product_seven_quadratic hcop:
  `Nat.Coprime (a*b*(a+b)) Q`。endpoint proof の coordinate exclusion はこの neutral owner から得る。
- Step010 not_prime_dvd_coordinate_product_of_quadratic は hq,hcop,hQ のみ。
  not_prime_dvd_endpoint_of_quadratic は hEq を要求する。
  prime_square_focused_allocation は a,b>0,hcop,hEq,hfocus,hq,q≠7,hQ を要求する。
  新 endpoint / square route は後者二つを使わない。
- Lib.Cosmic.GTailSevenPrimeAllocation.not_prime_dvd_gtail_seven_of_gap:
  hq,q≠7,q∣g,q∤c → q∤T。新 Gap branch はこれを使う。
- Step038 gap_ratio_eq_one は q prime,q∤c,q∣g のみ。
  focused_prime_route / tail_receiver は hEq を要求するので新 defect route では使わない。
- Step031 focused_norm_depth_guards / focused_norm_scalar_depth_readouts は hEq と hT を要求する。
  scalar_budget_depth_readouts は明示 supplied budget と nonzero inputs を要求する。
  新 route にこれらの equation-dependent guards/budget を持ち込まない。
- Step037 nativeKernel / native_square_support は実際の source guards のみ。
  optional q43 numeric receiver はこれらの hEq-free API を使う。

## Confirmed Mathlib signatures

`.lake/build/gtail-step039/api-probe.log`（actual #check、exit0）:

```lean
Int.natCast_dvd_natCast {m n : ℕ} : (m : ℤ) ∣ (n : ℤ) ↔ m ∣ n
Nat.Coprime.pow_left (n : ℕ) (H1 : m.Coprime k) : (m ^ n).Coprime k
Nat.Coprime.dvd_of_dvd_mul_left (H1 : k.Coprime m) (H2 : k ∣ m * n) : k ∣ n
Nat.Prime.coprime_iff_not_dvd (hp : Nat.Prime p) : p.Coprime n ↔ ¬ p ∣ n
```

`dvd_add` / `dvd_sub` / `Nat.Prime.dvd_of_dvd_pow` も #check した。
q²-only cancellation は coprime.pow_left 2 による既存 API の合成。
q is invertible mod q² という仮定はない。Int equality / divisibility は exact_mod_cast で移送する。

## Old reconstruction fields (read-only contract)

AwayDescentClosureProvider は nextX/Y/Z、nextPack:CounterexamplePack、
nextRoute:AwayValuationTransferPacket と
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd` を要する。
RamifiedSignedRootDepthPacket は balanced axis、signed roots と normPacket roots の一致、
IsCoprime、gapRoot / quotientRoot、signedGap=7⁴gapRoot、signedQuotient=7quotientRoot、
両 root の7-unit、normalizedEquation。
今回いずれの新 value も構成しない。既存 transitive signed imports の存在を新依存と取り違えない。
