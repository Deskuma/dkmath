# PRIM-L038 report — parity-safe Möbius divisor-floor ledger

## 判定

**Outcome A — EXACT MÖBIUS DIVISOR-FLOOR / CANCELLATION FRONTIER** と判定する。

今回閉じたのは有限 arithmetic の exact identity であり、Legendre 予想の証明ではない。
PNT、Mertens 型評価、Jacobsthal 型 bound、sieve、RH/CFBRC、または signed correction の一様評価は導入していない。

## 実装

追加した module は
`DkMath.NumberTheory.Legendre.ParitySafeMobiusWave` であり、facade
`DkMath.NumberTheory.Legendre` から import できる。

主な公開 theorem は次のとおり。

- `card_filter_coprime_Ioc_eq_sum_moebius_div`

  正の modulus `M` と `A ≤ B` に対し、
  `Ioc A B` の `Nat.Coprime M` filter の cardinalityを `ℤ` で
  `∑ d ∈ M.divisors, μ d * (B / d - A / d)` に一致させる。
  証明は `μ * ζ = 1` による gcd indicator、有限和交換、
  `Nat.Ioc_filter_dvd_card_eq_div` による倍数個数で構成した。

- `paritySafeActiveWave_card_eq_mobius_divisor_floor_sum`

  L037 の wave／reduced-quotient bijectionを使い、各 active wave の
  occupancyを modulus `2*n` の signed divisor-floor sumへ transportする。

- `paritySafeIncidenceCount_eq_mobius_wave_sum`

  global incidence countを wave ごとの Möbius sumへ書き換える。

- `paritySafeIncidenceCount_eq_mobius_divisor_first_sum`

  有限和を commuteし、`d` を先に走査する divisor-first signed ledgerを得る。

## witness

`paritySafeActiveWaveOffsets_five_three_card` は `(n,q)=(5,3)` の wave の
cardinalityが `2` であることを示す。
`paritySafeActiveWaveOffsets_five_three_mobius_sum` は同じ exact theoremを
逆向きに使い、対応する signed divisor-floor sideも `2` になることを確認する。
この例の interval は `25/3 < k ≤ 35/3`、modulus は `10` であり、
有限 Möbius 展開が単なる別名導入ではなく、符号付き cancellation を記録している。

## d = 1 と残る境界

`d = 1` の raw termだけを `Nat.divisors.erase 1` で分離する theorem は、
今回の exact divisor-first identityに必要ではないため追加しなかった。
従って、raw interval mass と signed correctionの分解は report 上の未実装項目として残す。

また、今回の theorem 群には signed correctionを十分小さくする universal boundはない。
したがって、L035/L036 の universal frontier、ひいては Legendre 予想へ進むには、
この exact ledgerとは独立の新しい estimate/provider が必要である。

## 検証範囲

次の targetを Lean 4.32.2 / Mathlib checkoutで検証した。

```text
lake build DkMath.NumberTheory.Legendre.ParitySafeMobiusWave
```

facade import後には、次の targetも検証する。

```text
lake build DkMath.NumberTheory.Legendre
```

full repository build、commit、push、CIは今回の bounded instruction の範囲外である。
