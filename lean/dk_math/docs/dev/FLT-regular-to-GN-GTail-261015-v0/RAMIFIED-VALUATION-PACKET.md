# 分岐側 GN の整数付値・ノルム復元・保存パケット

## 今回の到達点

提案された次段階を、整数上の定理と実際に構成できるパケットとして実装した。
円分体を使わない整数付値の段階と、類群条件を使う整数冪復元を分ける。
既存の自然数版 `GN_modEq_head_mod_sq_of_odd_prime_dvd_x` と
`padicValNat_GN_prime_eq_one_of_dvd_gap` は保持し、符号付き座標に対応した。

| 層 | ファイル | 入力と結論 |
|---|---|---|
| 整数の分岐深度 | `DkMath/Lib/NumberTheory/CosmicRamifiedValuation.lean` | p≥3, p∣x から GN の mod p² 先頭項。さらに p∤u から vₚ(GN)=1 |
| 分岐因子のノルム | `DkMath/Lib/NumberTheory/CosmicCyclotomicNorm.lean` | 奇素数円分体で N(ζ−1)=+p |
| 保存と主イデアル化 | `DkMath/Lib/NumberTheory/CosmicRamifiedPacket.lean` | 同じ βᵢ,Iᵢ と整数付値を保持し、類群条件の後にのみ単元・生成元を追加 |
| FLT 座標への接続 | `DkMath/FLT/Kummer/GNRamifiedArithmetic.lean` | x=a+b,u=−b、p∣c の向きの原始的方程式から指数配分と GN=p*tᵖ |

入口 `DkMath.FLT.Kummer` は新しい算術接続を import する。
すべての新定理に日本語 docstring を付けた。

## 1. GN の先頭項から mod p² へ

整数 x,u に対して再帰式を二回読む。

```
GN_p(x,u)     = p*u^(p-1) + x*GTail p 2 x u
GTail p 2 x u = choose p 2 * u^(p-2) + x*GTail p 3 x u
```

p≥3 なら p は `choose p 2` を割る。p∣x と合わせて
p∣GTail p 2 x u、従って p²∣x*GTail p 2 x u となる。
`integral_GN_eq_head_add_prime_sq_mul` は補正 M を返す。

```
GN_p(x,u) = p*u^(p-1) + p²*M
```

`integral_GN_modEq_head_mod_prime_sq` はその `Int.ModEq` 版。
u の非可除性や原始性はこの段階には必要ない。x=0 も許す。
LTE や冪差の付値定理は使っていない。

## 2. exact-one と指数配分

p∤u なら p² は先頭項 p*u^(p−1) を割らない。
したがって、`integral_GN_prime_dvd_and_not_sq` は
p∣GN と p²∤GN を同時に返す。
`padicValInt_GN_eq_one_of_dvd_gap` はそこから vₚ(GN)=1 を得る。
特に GN≠0 も非可除性により保証される。

非零の c と `x*GN=c^p` を与えると、積・冪の付値則により
`padicValInt_gap_add_one_eq_prime_mul` が

```
v_p(x) + 1 = p*v_p(c)
```

を返す。c≠0 は必須。Lean の `padicValInt p 0=0` という規約では、
x=c=0 を許すと積等式は成立してもこの付値等式は成立しない。

FLT 座標では、`padicValInt_gap_add_one_of_ramified_case` が
`v_p(a+b)+1=p*v_p(c)` を返す。
`padicValInt_gap_of_ramified_case` は自然数減算による教科書の形
`v_p(a+b)=p*v_p(c)-1`。どちらも円分体や正則性を仮定しない。

## 3. 同じデータを保持するパケット

`RamifiedIdealPowerPacket hζ x u c` は次を保持する。

- 入力の原始性、p∣x、p∤u、c≠0、`x*GN=c^p`。
- 全非自明添字 i の剥離商 βᵢ と非零イデアル根 Iᵢ。
- `αᵢ=(ζ−1)βᵢ`、`ζ−1∤βᵢ`、`(βᵢ)=Iᵢ^p`。
- 同じ Iᵢ の積 J による `(GN)=(p)J^p` と `(x)(p)J^p=(c)^p`。
- 先頭補正 M、その等式、GN の exact-one、全付値の保存等式。

λ=ζ−1 と αᵢ=x+(1−ζ^i)u は座標から固定される。
`rootProduct` は保存した Iᵢ の積として定義され、独立の J を選び直さない。
`rootProduct_ne_bot` が J≠⊥ を返す。

`nonempty_ramifiedIdealPowerPacket` は入力からこの構造を実際に構成する。
必要な冪性・付値関係を入力フィールドとして要求するだけの定理ではない。

類数と p が互いに素なら、`exists_principal_extension` は
`RamifiedPrincipalPowerPacket` を構成する。
元のパケットへの射影が入力 P と等しいことも返すので、Iᵢ の選択を変更しない。
追加するのは単元 εᵢ、生成元 γᵢ と
`(γᵢ)=Iᵢ`、`βᵢ=εᵢ γᵢ^p` の証明だけ。

## 4. 整数上の GN=p*tᵖ

`integral_norm_ramifier_eq_prime` は、既存の GN のノルム等式を
x=0,u=−1 に適用する。GN の零評価が p*(−1)^(p−1) を返すので、
p が奇数なら N(ζ−1)=+p となる。
既存 `CyclotomicPrincipalization.norm_int_zeta_sub_one_eq_p` の体ノルム経路と
同じ結論を、共通ライブラリ側で GN の先頭係数から計算する補題である。

```
α = (ζ−1)*(ε*γ^p)
  ⇒ GN = p * N(ε) * N(γ)^p
  ⇒ GN = p * t^p
```

N(ε)=±1 の符号は p が奇数なので t に吸収できる。
`exists_integral_GTail_eq_prime_mul_pow_of_ramified_factor` がこの汎用接続を返す。
`RamifiedPrincipalPowerPacket.exists_integral_root` は chosen factor i=1 に適用する。
p²∤GN から p∤t も証明し、`x*(p*t^p)=c^p` を保持する。

FLT 入口は `exists_GN_eq_prime_mul_pow_of_ramified_case`。
p∣c の向き、非零 c、原始性、方程式、類数条件から、

```
∃ t : ℤ, GN p (a+b) (-b) = p*t^p ∧ p∤t ∧ (a+b)*(p*t^p)=c^p
```

を返す。単元自体は円分整数環内に残っており、整数ノルムで符号を吸収したことと
単元合同解析による除去は異なる。

## 検証と境界

`DkMathTest/FLT/Kummer/GNRamifiedArithmetic.lean` に10例。
負の座標、零 gap、p=3,5、λ 自体のノルムと単元倍冪、
パケット拡張による同じイデアル根の保持を検証する。
p=2、p∣u、c=0 による失敗例で仮定の必要性も固定する。
新規15定理すべての公理依存を標準3公理に制限する自動検査を含む。
パケット構成定理は仮想 FLT 方程式を受け取る構造定理であり、
実在する非自明 FLT 解をテストで作ったという主張ではない。

正確なコマンド・結果は `evidence/validation-ramified-arithmetic.txt`。

残るのは円分単元の合同解析、任意の Case II の向きの正規化、
次の方程式の構成と減少性を伴う無限降下である。
今回の指数配分や整数ノルム復元は、それらの存在や FLT の矛盾を結論しない。
