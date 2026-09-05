# FLT3U-014 実装報告: Positive-Natural Normalization and Public FLT3 API

## 実装範囲

`instruction-014` の FLT3U-011 checkpoint を実装した。U013 の primitive theorem
`FLT_d3_unconditional` を使い、任意の positive natural cubic solution を
`gcd a b` で primitive pack に正規化したうえで、full positive-natural endpoint
`fermatThree_no_positive_solution` を追加した。

## gcd normalization

追加 module [PositiveCubicNormalization.lean](../../../DkMath/FLT/Three/PositiveCubicNormalization.lean)
では、

```text
d  := Nat.gcd a b
a' := a / d
b' := b / d
c' := c / d
```

と定めた。`ha : 0 < a` から
`Nat.gcd_pos_of_pos_left b ha` により `0 < d` を得る。

`Nat.gcd_dvd_left`、`Nat.gcd_dvd_right` から `d ∣ a`、`d ∣ b` を得て、
`pow_dvd_pow_of_dvd` と元の equation により

```text
d ^ 3 ∣ c ^ 3
```

を示した。その後 `Nat.dvd_pow_iff_ceilRoot_dvd` の指数 3 の instance で
`d ∣ c` を抽出している。

各座標について `Nat.mul_div_cancel'` により、次を exact equality として保持した。

```text
d * a' = a
d * b' = b
d * c' = c
```

## 正値性・互いに素・normalized equation

`Nat.div_pos` と `d > 0`、各座標への divisibility から
`0 < a'`、`0 < b'`、`0 < c'` を得た。

正規化後の互いに素性は、手作業の Bezout/gcd 証明を再実装せず、指定 API の

```text
Nat.coprime_div_gcd_div_gcd hdPos
```

を使って `Nat.Coprime a' b'` とした。

normalized equation は scaled cancellation で証明した。

```text
d ^ 3 * (a' ^ 3 + b' ^ 3) = d ^ 3 * c' ^ 3
```

を `d*a'=a`、`d*b'=b`、`d*c'=c` と元の equation から構成し、
`Nat.mul_left_cancel (pow_pos hdPos 3)` で

```text
a' ^ 3 + b' ^ 3 = c' ^ 3
```

を得た。

これらを `PrimitiveCubicPack` にまとめ、次の public theorem を追加した。

```text
exists_primitiveCubicPack_of_positive_solution
```

## Full positive-natural endpoint

次の theorem を追加した。

```text
theorem fermatThree_no_positive_solution
    (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3
```

仮に equation が成立すると、normalization theorem が primitive pack を返し、
U013 の `primitiveCubicPack_false` に渡して矛盾を得る。`hS0_not_sq`、
`NoSqOnS0` provider、completed FLT3 theorem は使用していない。

## Standalone public aggregator

[Three.lean](../../../DkMath/FLT/Three.lean) を追加し、direct import を

```text
import DkMath.FLT.Three.PositiveCubicNormalization
```

だけにした。`DkMath.FLT.Three` は GN3、signed 3-adic routing、Eisenstein
Euclidean arithmetic、unit sectors、strict descent を経由する独立 exponent-three
public surface であり、completed FLT3 theorem を proof step として import しない。

legacy top-level [DkMath/FLT.lean](../../../DkMath/FLT.lean) は変更していない。
そこは既存 `DkMath.FLT.Main` を含む legacy surface のまま保持し、独立 proof の
public import path は `DkMath.FLT.Three` とした。

## Dependency and axiom audit

新規 production source の direct import は次の通りである。

```text
PositiveCubicNormalization.lean
  -> DkMath.FLT.Three.PrimitiveCubicClosure

Three.lean
  -> DkMath.FLT.Three.PositiveCubicNormalization
```

source search では次への参照を確認していない。

- `DkMath.FLT.Main.FLT_d3_by_padicValNat`
- `hS0_not_sq`
- `NoSqOnS0`
- `DkMath.FLT.Basic`
- `DkMath.FLT.GEisensteinBridge`
- `DkMath.FLT.Five.*` / `DkMath.FLT.Seven.*`
- `FermatLastTheoremThree` など completed FLT3 theorem names

`#print axioms` の結果は次の通りである。

```text
exists_primitiveCubicPack_of_positive_solution:
  [propext, Classical.choice, Quot.sound]

fermatThree_no_positive_solution:
  [propext, Classical.choice, Quot.sound]
```

`sorryAx`、project-specific axiom、completed FLT3 theorem axiom はない。

既存 `DkMath.Basic` の広域 `import Mathlib` により、生成された transitive
import artifact には `Mathlib.NumberTheory.FLT.Three` が残る。しかし新規 source の
明示 import と proof term には completed Mathlib FLT3 theorem の依存はなく、
`#print axioms` と source search もそれを確認している。この artifact を除去する
ための `DkMath.Basic` import 分解は U014 の範囲外なので実施していない。

## Verification

次の focused build を実行した。

```text
lake build DkMath.FLT.Three.PositiveCubicNormalization
Build completed successfully (8723 jobs).

lake build DkMath.FLT.Three
Build completed successfully (8724 jobs).
```

さらに `import DkMath.FLT.Three` の smoke audit で、次を `#check` した。

```text
DkMath.FLT.Three.FLT_d3_unconditional
DkMath.FLT.Three.fermatThree_no_positive_solution
```

依存グラフ中の既存 `DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`
の `sorry` warning は継続しているが、新規 U014 source に `sorry` はない。

## Completion gate / Outcome

- primitive theorem `FLT_d3_unconditional`: 完了
- full positive-natural theorem `fermatThree_no_positive_solution`: 完了
- `hS0_not_sq` / `NoSqOnS0`: 非依存
- completed FLT3 theorem: proof step として非依存
- 新規 tower の project-specific axiom / `sorry`: なし
- standalone public import `DkMath.FLT.Three`: 完了
- focused builds: green
- final endpoint axiom audit: clean
- legacy conditional `DkMath.FLT.Main` の除去・移行: 非対象で未変更

Outcome A。FLT3-Unconditional の独立 proof tower と full positive-natural endpoint
を完成し、legacy Main の repository-wide cleanup は別作業として残した。
