# 教科書の次章: 分岐剰余体と単元の一次正規化

2026-10-16 JST

## 今回学ぶこと

整数ノルムの根 t≡1 mod p から、円分整数環 R=𝓞 K に戻る。
λ=ζ−1 による剰余体を実際に F_p と同定し、剥離した商と単元の剰余を読む。

```
R/(λ) ≃ F_p
αᵢ = x+(1−ζ^i)u = λβᵢ
    ⇒ βᵢ ≡ −i*u mod λ
βᵢ = εᵢ γᵢ^p
    ⇒ γᵢ'≡1, εᵢ'≡−i*u mod λ と選び直せる
```

これは単元群の p 乗剰余類を消す定理ではない。
生成元の選択を整え、残る単元を高次合同式で調べるための第一段である。

## 1. λ で割る前と後では、見える先頭項が違う

ζ≡1 mod λ なので、すべての αᵢ は mod λ では x と一致する。
p∣x の分岐側では x≡0 であり、この段階では添字 i の違いが見えない。

そこで `Sᵢ=1+ζ+...+ζ^(i−1)` を使う。

```
ζ^i−1 = λSᵢ
Sᵢ ≡ i mod λ
λ(βᵢ+Sᵢ*u) = x
```

λ²∣x なら、非零な λ を一つ取り消して
`βᵢ+Sᵢ*u ≡ 0 mod λ`、従って `βᵢ≡−i*u mod λ` を得る。

`sub_one_dvd_geom_sum_sub_nat` と `stripped_phaseFactor_add_index_mul_dvd`
は任意の可換整域でこの議論を行う。
整数座標で p∣x,p≥3 なら、p と λ^(p−1) の同伴性から λ²∣x が従う。
この供給が `ramifier_sq_dvd_intCast_of_dvd_prime`。
剥離商の一次合同式には、正則性もイデアル根の主イデアル性も必要ない。

## 2. 分岐剰余体が F_p である理由

既存の整数ノルム定理 N(λ)=p と、主イデアルの指数の定理を合わせる。

```
#(R/(λ)) = |N(λ)| = p
```

`card_ramifiedResidue_eq_prime` がこの等式を証明する。
`ramifiedResidueEquiv` は、p 元の環に対する Mathlib の環同型を使い
`ZMod p ≃+* R/(λ)` を構成する。
Fintype の選択はこの実装内で行い、利用側には要求しない。

その逆と剰余写像を合成したものが `ramifiedReduction : R →+* ZMod p`。
整数の写像は通常の mod p であり、ζ は1へ移る。
`ramifiedReduction_eq_iff` は

```
reduction(a)=reduction(b) ↔ λ∣a−b
```

を返す。これで元の可除性・主イデアル所属・F_p の等式を往復できる。
`ramifiedReduction_stripped_phaseFactor` は先ほどの商の剰余を
F_p の等式 `reduction(βᵢ)=−i*u` として公開する。

## 3. 非零剰余を大域的な単元に持ち上げる

剰余が非零である元が大域的単元とは限らない。
ここでは円分体固有の幾何和を使って、必要な単元を別に構成する。

非零剰余の代表 r（1≤r<p）について、

```
ηᵣ = 1+ζ+...+ζ^(r−1)
```

は r と p が互いに素なので円分単元になる。
その剰余は r である。
`exists_unit_lift_ramifiedResidue` は、任意の a∈F_p^× に対して
実際の単元 e∈R^× と reduction(e)=a を返す。
Mathlib の `IsPrimitiveRoot.geom_sum_isUnit` により単元性を証明する。

## 4. 生成元の剰余を1にし、単元の剰余を取り出す

β=εγ^p、ε が単元、λ∤β とする。
λ∤γ も従うので、γ の非零剰余の逆数を単元 e で持ち上げる。

```
γ' = eγ
ε' = ε(e⁻¹)^p
β  = ε'(γ')^p
```

すると reduction(γ')=1。
等式を剰余体へ写せば reduction(ε')=reduction(β) となる。
`exists_residue_normalized_unit_mul_pow` はこれらと、
γ' と γ の同伴性、および補償に使った単元 e とその厳密な等式を返す。
ε に掛けた補償は単元の p 乗なので、単元群を p 乗で割った剰余類は保持される。

`RamifiedPrincipalPowerPacket.exists_residue_normalization` はこの操作を全非自明添字に実行する。
新パケットの基底が旧パケットの基底と等しいことも返す。
従って同じ βᵢ,Iᵢ、GN の主イデアル等式、整数の付値を保持する。
生成元の主イデアルは同伴性により同じ Iᵢ のままである。

基底パケットからの合成入口は
`RamifiedIdealPowerPacket.exists_residue_normalized_principal_extension`。
類数条件で主イデアル化した後に、円分単元で剰余を正規化する。
単元の p 乗写像が全射だという追加仮定は使わない。

## 5. FLT 座標に戻す

`DkMath.FLT.Kummer.GNRamifiedUnitResidue` の
`exists_GN_ramified_residue_normalized_packet` は、従来の原始的方程式、
p∣c の向き、c≠0、類数条件から正規化したパケットを構成する。
x=a+b,u=−b なので、出力は全非自明添字について

```
γᵢ ≡ 1 mod λ
εᵢ ≡ i*b mod λ
```

となる。`a+ζ^i b=λ(εᵢγᵢ^p)` もパケットから読める。
入口 `DkMath.FLT.Kummer` はこのモジュールを import し、従来の算術定理も到達可能。

## 検証と次の境界

新規12例は、一般環での剥離式、λ² 条件の必要性、p=3 の剰余体・整数・原始根、
円分単元による非零剰余の持ち上げ、実際の x=3,u=1 の二つの因子、
負の生成元の正規化と補償単元、および全パケットのイデアル根の保持を検証する。
FLT の仮想非自明解を実際に作ったというテストではない。
新規15定理と2定義を標準3公理の whitelist で監査する。
検証記録は `evidence/validation-ramified-unit-residue.txt`。

今回閉じたのは剰余一段の計算と生成元の正規化。
高次の λ 進合同、残る単元の p 乗剰余類の解析、任意の Case II の向きの正規化、
新しい方程式の構成と減少性を伴う無限降下は、引き続き別の証明を要する。
