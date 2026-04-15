# DkMath.FLT Provider Route Note

`DkMath.FLT` を import したあと、
high-exponent / prime-ge5 側で
「どの theorem 名から入るべきか」を短く固定するためのメモ。

## 1. 最初に見る場所

- top-level import:
  `DkMath.FLT`
- theorem discovery 用 sample:
  `DkMath.FLT.Samples`
- 実体定義:
  `DkMath.FLT.Kummer.RegularPrimeRoute`

## 2. 入口の住み分け

- `d = 3` 公開面:
  `DkMath.FLT.Main`
- regular-prime / prime-ge5 の abstract route:
  `FLTPrimeGe5Target_of_refinedRegularPrimeRoute`
- regular-prime / prime-ge5 の provider concrete route:
  `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
  /
  `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`

## 3. どれを使うか

- `CyclotomicNormDescentTarget` を theorem parameter として受け取りたいだけなら、
  `FLTPrimeGe5Target_of_refinedRegularPrimeRoute`
  を使う。
- `TriominoSquarefreeGNBridgeProvider` を concrete に持てるなら、
  `FLTPrimeGe5Target_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
  ではなく、
  そのまま provider-facing wrapper
  `triominoCosmic_globalProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
  または
  `triominoPrimeProvider_of_refinedRegularPrimeRoute_and_squarefreeGNProvider`
  まで上げるのが推奨。

## 4. current open の意味

high-exponent 側の current open は、
provider route が無いことではない。
現在の open は、
**その provider concrete route を埋め切る数論核がまだ未完**
という点にある。

したがって、
導線としては
`RegularPrimeRoute`
    →
provider concrete wrapper
という public/provider route は既にある。
