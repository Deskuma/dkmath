# Ultra-001R Report — excess-active small/large profile pincer

Date: 2026-07-27

## 判定

full valuation profile を excess profile
`e_q = padicValNat q (GN p a b) - 1` に圧縮し、正の excess を持つ prime だけを
CRT modulus と root-address charge に残した。さらに profile を active modulus
が区間長以下の small 層と、それを超える large 層に分離した。

```text
finite excess-profile space                    complete
active-prime CRT modulus                        complete
active root-address charge                      complete
small/large modulus split                       complete
small-profile finite Euler density              complete
finite local-product factorization              complete
large-profile support + excess diagnosis        complete
```

実装は `DkMath.ABC.GNExcessActiveProfiles` に置いた。

## 1. Excess-active profile

```lean
def GNExcessDepthProfileAt
def GNExcessDepthProfileSpace
def GNExcessActivePrimeSet
def GNExcessProfileExtension
def GNExcessJointDepthModulus
def GNExactExcessProfileEvent
def GNExcessSmallProfileSpace
def GNExcessLargeProfileSpace
```

inactive component `e_q = 0` は modulus exponent `0` へ送り、active component
だけを `q^(e_q+1)` として保持する。従って exact fiber の count は
`(p - 1)^Q.card` ではなく、

```text
(p - 1)^(GNExcessActivePrimeSet Q excess).card
```

を支払う。

## 2. Small/large pincer

```lean
theorem card_GNExactExcessProfileEvent_le
theorem card_GNExactExcessProfileEvent_le_smallDensity
theorem card_GNExactExcessProfileEvent_le_largeBoundary
theorem exp_GNExcessMassAt_sum_le_small_add_large
theorem exp_GNExcessMassAt_sum_le_finiteEuler_add_large
```

small profile では active modulus `M ≤ X+1` を使い、
`(X + 1) / M + 1 ≤ 2 * (X + 1) / M` を実数密度へ移した。large profile の
boundary `+1` は無理に密度へ吸収せず、
`GNExcessLargeBoundaryProfileSum` に明示的に残した。

## 3. Finite Euler factorization

```lean
def GNExcessLocalDensityWeight
def GNExcessLocalDensityFactor
theorem GNExcessProfileDensityWeight_eq_prod_local
theorem sum_GNExcessProfileDensityWeight_eq_prod
```

unrestricted finite excess-profile density sumを、各 `q ∈ Q` の有限 local factor
の積へ exact factorization した。inactive excess `j = 0` の local weight は
定義上 `1` であり、active prime だけが `(p - 1)` charge を持つ。

## 4. Large boundary の正確な診断

```lean
theorem log_GNExcessJointDepthModulus_eq_support_add_excess
theorem GNExcessLargeProfile_jointMass_gt_log_interval
```

large profile `X+1 < M(e)` に対し、

```text
log (X + 1)
  < GNExcessActiveSupportMass Q e
      + GNExcessActiveProfileMass Q e
```

を証明した。large boundary は単なる誤差項ではなく、active support と
valuation excess の joint pressure が区間 scale を超えたことの証明書である。

## 境界

R の有限 combinatorial layer は閉じた。large boundary の joint
compensation、uniform joint contract、`abc_main_axiom` replacement は
証明していない。

## Local verification

```text
lake build DkMath.ABC.GNExcessActiveProfiles   success (8368 jobs)
representative axiom audit                      propext / Classical.choice / Quot.sound only
new production code                            no sorry / axiom / native_decide
```

push、PR 更新、CI 起動・確認は行っていない。
