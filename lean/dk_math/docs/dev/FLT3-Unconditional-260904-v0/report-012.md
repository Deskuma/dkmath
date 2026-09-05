# FLT3U-012 実装報告: Positive Strict Descent Reconstruction

## 実装範囲

`instruction-012` の FLT3U-009B checkpoint を実装した。011 の
`EisensteinSignedCubeFactors` が保持する signed relation を符号解析し、三つの
正の cube equation のいずれかから、pairwise-coprime な次の
`PrimitiveCubicPack` と strict product decrease を構成する。

well-founded closure、strong induction、最終 FLT3 theorem、public aggregator、
`NoSqOnS0` の変更はこの checkpoint の非対象である。

## 追加 module と import

[PrimitiveCubicDescent.lean](../../../DkMath/FLT/Three/PrimitiveCubicDescent.lean)
を追加した。direct import は次の一つだけである。

```text
import DkMath.FLT.Three.EisensteinDescentFactors
```

FLT3 Main/Basic/Core、GEisenstein bridge、FLT5、FLT7、
`Mathlib.NumberTheory.FLT.Three` は import していない。

## PrimitiveCubicPack と measure

次の最小 Prop surface を追加した。

```text
PrimitiveCubicPack x y z
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  coprime_xy : Nat.Coprime x y
  equation : x^3 + y^3 = z^3
```

`primitiveCubicPack_of_hypotheses` は元の positive primitive hypotheses を一つの
pack にまとめる。measure は

```text
primitiveCubicMeasure p = x * y * z
```

であり、座標積が定義上そのまま現れる。

## Signed-value recovery と符号 routing

```text
int_eq_cube_or_neg_cube_of_natAbs_eq
```

により `x.natAbs = n^3` から
`x = (n : ℤ)^3 ∨ x = -((n : ℤ)^3)` を得る。`Real.abs` は使用していない。

`signed_cube_roots_route` は、source の

```text
r * s * (r + s) = A^3 > 0
```

と `r`, `s`, `r+s` の非零性を使う。`r,s` がともに正なら `r+s` も正で route P、
`r` 正・`s` 負なら積の正性から `r+s` は負で route L、`r` 負・`s` 正なら同様に
route R となる。`r,s` がともに負の場合は `r+s<0` となり積が負になるため除外
する。従って kernel-checked に次のいずれかを得る。

```text
R^3 + S^3 = T^3
R^3 + T^3 = S^3
S^3 + T^3 = R^3
```

符号解析だけで route を選び、natAbs の等式だけから cube equation を仮定して
いない。

## 次の primitive pack

三つの route は、それぞれ次の pack を構成する。

```text
P: PrimitiveCubicPack R S T   using coprime_RS
L: PrimitiveCubicPack R T S   using coprime_RT
R: PrimitiveCubicPack S T R   using coprime_ST
```

各座標の positivity は `EisensteinSignedCubeFactors` の fields を直接使用し、
gcd の再正規化は行っていない。

## Strict descent packet

`PrimitiveCubicStrictDescent` は source pack、同じ source hypotheses から
`eisensteinSignedCubeFactors_of_primitive_solution` で構成した factors、次の
`x,y,z`、next pack を保持する。

```text
next_product_eq : x * y * z = factors.source.A
measure_lt       : x * y * z < a * b * c
```

三つの permutation すべてで可換性を使って `x*y*z = R*S*T` を示し、011 の
`root_product_eq` から厳密に `x*y*z = A` を得た。その後
`EisensteinSignedCubeFactors.strict_product_lt` から strict decrease を得ている。

closure-facing theorem として

```text
exists_smaller_primitiveCubicPack
```

を追加し、任意の source pack に対して

```text
∃ x y z, PrimitiveCubicPack x y z ∧ x*y*z < a*b*c
```

を公開した。

## Verification

`lean/dk_math` から次を実行した。

```text
lake build DkMath.FLT.Three.PrimitiveCubicDescent
```

focused build は `Build completed successfully (8721 jobs).` で終了した。新規
module 自身の warning はない。依存グラフ中の既存
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` の `sorry` warning は
継続しているが、今回の module には新しい `sorry` はない。

主要 declaration の `#print axioms` は `propext`、`Classical.choice`、
`Quot.sound` のみであり、`sorryAx`、project-specific axiom、完了済み FLT3 theorem
shortcut はない。禁止 import と新規 source 内の `sorry`/`axiom` も監査済みである。

## Outcome

- Outcome A: selected。すべての `PrimitiveCubicPack a b c` から、同一 source
  hypotheses に基づく positive primitive next pack と
  `x*y*z < a*b*c` を構成できる。FLT3U-009B の acceptance set は完了した。
- Outcome B: selected ではない。今回の実装を妨げる formal obstruction は確認され
  なかった。
- Outcome C: selected ではない。route saturation や future bridge への停止判定は
  発生していない。

次の U010 の closure task は、この `exists_smaller_primitiveCubicPack` を
`primitiveCubicMeasure` に対する well-founded / strong induction に接続し、最終的な
FLT3 contradiction を閉じることである。
