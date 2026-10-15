# 教科書の次章: 正規化単元を mod λ² まで読む

2026-10-16 JST

## 結論と入口

λ=ζ−1 とする。前章の一次正規化 γᵢ≡1 mod λ に対して、今回は

```
βᵢ ≡ −i*u − choose i 2 * λ*u  mod λ²
εᵢ ≡ βᵢ                       mod λ²
```

を証明した。FLT 座標 x=a+b,u=−b では

```
εᵢ ≡ i*b + choose i 2 * λ*b     mod λ²
```

となる。入口は `DkMath.FLT.Kummer.GNRamifiedQuadratic`、主定理は
`exists_GN_ramified_quadratic_normalized_packet`。
`DkMath.FLT.Kummer` と `DkMath` からも import される。

共通ライブラリ `CosmicRamifiedQuadratic` は整数の付値保存、
有限幾何和、生成元の正規化を接続する。新定理には日本語 docstring を付けた。

## 1. 二次剰余環は体ではない

一次の剰余環 R/(λ) は前章で F_p と同定した。
二次の剰余環 R/(λ²) の元の数は p² である。
`card_ramifiedQuadraticResidue_eq_prime_sq` は

```
#R/(λ²) = |N(λ²)| = |N(λ)|² = p²
```

を証明する。ただし、p² 元だからといって有限体になるわけではない。
λ の像は零でないのに、その平方は零となる。
`prime_class_mod_square_nonzero_nilpotent` がこの事実を素元一般について返す。
以降は、体の非零元の逆数を使う代わりに、λ² 可除性を追う。

## 2. choose i 2 が現れる理由

Sᵢ=Σ k<i ζ^k とおく。
前章では Sᵢ≡i mod λ だった。
もう一段読むため、まず

```
ζ^k = 1 + k*λ + λ²*A_k
```

を有限幾何和から証明する。
`sub_one_sq_dvd_pow_sub_linear` はその剰余の可除性。

これを k<i について足すと、定数項は i、λ の係数は
Σ k<i k = choose i 2 となる。
実装ではこの係数を Pascal の漸化式で追い、
`sub_one_sq_dvd_geom_sum_sub_linear` が

```
Sᵢ = i + choose i 2 * λ + λ²*B_i
```

という mod λ² の情報を返す。
係数を choose i 2 のまま保持するため、2 で割る操作や体の仮定は不要。

## 3. 剥離前には λ³∣x が必要

厳密な剥離式から

```
αᵢ = x+(1−ζ^i)u = λβᵢ
λ(βᵢ+Sᵢ*u) = x
```

となる。λ³∣x なら、非零な λ を一つ取り消して
λ²∣βᵢ+Sᵢ*u を得る。前節の Sᵢ の展開を代入すれば

```
λ² ∣ βᵢ + i*u + choose i 2 * λ*u
```

が従う。これが `stripped_phaseFactor_quadratic_dvd`。

λ²∣x だけでは足りない。一般環の数値例でこの失敗を回帰テストに含めた。
p∣x だけの円分体の分岐条件から λ³∣x を結論することも、p=3 ではできない。

## 4. 既存の整数付値が不足する深度を供給する

パケットは既に

```
v_p(x)+1 = p*v_p(c)
```

を保持している。左辺は正なので v_p(c)≥1。
従って v_p(x)+1≥p、p≥3 より v_p(x)≥2 となる。
`RamifiedIdealPowerPacket.prime_sq_dvd_gap` は p²∣x を返す。
ここでは c≠0 を含む既存パケットを使い、零における付値の規約を混同しない。

p と λ^(p−1) の同伴性から、p² は λ^(2(p−1)) と同伴である。
2(p−1)≥4 なので、必要な λ³∣x が得られる。
`ramifier_cube_dvd_gap` と `quotient_quadratic_dvd` がこの接続を公開する。

この段階では正則性を使わない。
また、p=3 も整数の追加深度により含まれる。
テストでは実際の p=3,x=9,u=1 の剥離商を使って二次係数を確認する。

## 5. γ の p 乗が二次まで消える理由

γ≡1 mod λ とする。
有限展開の一次項は p*(γ−1)、残りは (γ−1)² の倍数である。
λ∣p と λ∣γ−1 を合わせると、どちらも λ² の倍数になる。

```
γ^p ≡ 1 mod λ²
β = εγ^p  ⇒  ε≡β mod λ²
```

一般環の定理は `square_dvd_pow_sub_one_of_dvd_natCast` と
`square_dvd_unit_sub_of_mul_pow`。
後者の合同式だけなら ε の単元性すら必要ない。

`RamifiedPrincipalPowerPacket.unit_sub_quotient_sq_dvd` は
一次正規化済みの **同じ** γᵢ を受け取り、λ²∣εᵢ−βᵢ を返す。
`unitFactor_quadratic_dvd` はそのまま単元の二次係数を返す。
既に正規化した生成元を、二次条件のためにさらに変える必要はない。

## 6. 全因子族と FLT への接続

`exists_quadratic_normalization` は前章の正規化を一度実行し、二次合同条件を追加する。
返すパケットの基底は元の基底に等しい。
同じ剥離商、イデアル根、GN の積等式、整数の付値が保存される。

FLT の主定理は従来と同じ原始性、方程式、p∣c の向き、c≠0、類数条件を受け取る。
追加の λ³∣(a+b) を仮定せずに、全非自明添字について

```
γᵢ≡1 mod λ
εᵢ≡i*b mod λ
λ² ∣ εᵢ − i*b − choose i 2 * λ*b
```

を同時に返す。

## 検証と残る課題

`DkMathTest/FLT/Kummer/GNRamifiedQuadratic.lean` に15例。
有限 Taylor 式、剥離前の深度条件、p 乗で一次項が消えるための両仮定、
零でない冪零元、二次剰余環の大きさ、実際の三次円分因子、
パケットの追加深度と同じイデアル根の保持を検査する。
新規14定理の公理依存を標準3公理の whitelist で監査する。
実行記録は `evidence/validation-ramified-quadratic.txt`。

単元の局所情報を二次まで固定したが、単元の p 乗剰余類は消去していない。
任意の Case II の向きの正規化、新しい方程式の構成、減少性を伴う無限降下も未証明。
今回の合同条件を FLT の矛盾や降下の存在と読み替えない。
