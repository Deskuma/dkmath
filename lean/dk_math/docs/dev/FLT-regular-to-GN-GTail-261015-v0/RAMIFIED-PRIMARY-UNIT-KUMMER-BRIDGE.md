# 教科書の次章: λ^p の合同から Kummer 単元補題へ

2026-10-16 JST

## 到達点を区別する

| 段階 | 今回の結果 |
|---|---|
| γ≡1 mod λ ⇒ γ^p≡1 mod λ^p | DkMath 内で証明済み |
| p²∣x ⇒ εᵢ≡−Sᵢ*u mod λ^p | 同じ保存パケットから証明済み |
| δᵢ=εᵢ*Sᵢ⁻¹、δᵢ≡−u mod p | 単元群内で実際に構成、証明済み |
| 一般 p の単元除去 | 単元補題を明示的に供給する条件付き adapter を検証済み |
| p=3 の単元除去 | Mathlib の実際の単元補題から供給、検証済み |
| flt-regular の一般版を実 import | 未実施。依存パッケージ未導入。接続候補を別ファイルに用意 |

全ての新規 production 宣言に日本語 docstring を付けた。
通常入口は `DkMath.FLT.Kummer`、算術の到達点は `GNRamifiedPrimary`、
単元補題との適用境界は `GNKummerUnitAdapter` にある。

## 1. 内部係数を使えば一気に λ^p へ進める

共通ライブラリの
`prime_power_dvd_pow_sub_one_of_dvd_pred_power` は任意の可換環で次を証明する。

```
p prime, ell^(p−1)∣p, ell∣γ−1 ⇒ ell^p∣γ^p−1
```

γ=1+ell*z を二項展開し、定数項を除く。
内部項 1≤k<p の係数は p を含み、従って ell^(p−1) を含む。
さらに ell^k から最低一つを取れば ell^p が得られる。
最後の項 k=p は係数が1でも ell^p 自体を含む。

この証明は有限和と素数行の可除性だけを使い、単元性、零でない ell、
完備化、無限級数を必要としない。
仮定 ell∣p だけでは不足するので、その失敗例もテストした。

円分体では p と λ^(p−1) の同伴性が必要な入力を供給する。
`ramifier_pow_prime_dvd_generator_pow_sub_one` は前章の
`ramifiedReduction γ=1` を受け取って λ^p∣γ^p−1 を返す。

## 2. 幾何和を打ち切らず、丸ごと保存する

Sᵢ=Σ k<i ζ^k とおく。剥離式は厳密に

```
λ(βᵢ+Sᵢ*u)=x
```

となる。
`stripped_phaseFactor_geom_sum_dvd_pow` は λ^(n+1)∣x から
λ^n∣βᵢ+Sᵢ*u を得る一般の取消し補題。

既存の `prime_sq_dvd_gap` が p²∣x を返す。
p と λ^(p−1) の同伴性と p≥3 より

```
2(p−1) ≥ p+1
λ^(p+1)∣x
```

となる。`ramifier_pow_succ_dvd_gap` がこの深度を供給し、
`quotient_geom_sum_dvd_pow_prime` が βᵢ≡−Sᵢ*u mod λ^p を返す。
p=3 も含み、この場合は深度の不等式が等号になる。

βᵢ=εᵢγᵢ^p と前節の γᵢ^p≡1 を合わせると、
`unit_sub_quotient_dvd_pow_prime` と `unit_geom_sum_dvd_pow_prime` が

```
εᵢ≡βᵢ≡−Sᵢ*u mod λ^p
```

を返す。新しい高次の生成元正規化は仮定していない。

## 3. 幾何和を単元群で割る

非自明添字では Sᵢ は円分単元。
`ramifiedGeomUnit` は Mathlib の幾何和の単元性から実際の Rˣ の元を選び、
`ramifiedGeomUnit_val` がその値を Sᵢ と同定する。

`RamifiedPrincipalPowerPacket.primaryUnit` は

```
δᵢ = εᵢ * Sᵢ⁻¹ ∈ Rˣ
```

を構成する。Sᵢ⁻¹ は単元群の逆元であり、円分整数環で除算を追加していない。
`primaryUnit_mul_geom_sum` が δᵢ*Sᵢ=εᵢ を厳密に復元する。

合同式に Sᵢ の逆元を掛けると
`primaryUnit_add_parameter_dvd_pow_prime` が λ^p∣δᵢ+u を返す。
また p∼λ^(p−1) なので p∣λ^p。
`primaryUnit_congruent_integer` が

```
(p : R) ∣ δᵢ − (−u : ℤ)
```

という整数の証人を明示した条件を返す。

FLT 座標 u=−b では λ^p∣δᵢ−b および p∣δᵢ−b となる。
`exists_GN_ramified_primary_packet` は同じ Q のまま
εᵢ≡Sᵢ*b、δᵢ≡b、および

```
a+ζ^i b = (ζ^i−1)*(δᵢ*γᵢ^p)
```

を同時に返す。この定理は一般版の Kummer 単元補題を使わない。

## 4. 参照先の単元補題の実際の型

参照先の
[`eq_pow_prime_of_unit_of_congruent`](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/NumberTheory/KummersLemma/KummersLemma.lean)
を確認した。素数 p、p≠2、p 次円分体、類数との互いに素性の下で、
単元がある整数と mod p で合同なら、**単元群内の** p 乗根を返す。
今回の δᵢ と整数 b はこの入力形に一致する。

同じファイルは Hilbert92、Hilbert94、KummersLemma.Field 等を import している。
これらは現在の DkMath の Mathlib 依存内にはなく、`flt-regular` 自体も
Lake の require に入っていない。
参照した [上流 toolchain](https://github.com/leanprover-community/flt-regular/blob/master/lean-toolchain)
の表示は v4.34.0-rc2、ローカルは v4.34.1。
この差だけから互換・非互換を断定せず、依存グラフ全体の実コンパイルは未検証とする。

別ファイル `integration/FltRegularAdapter.lean` に、上流定理を1回適用して
ローカルの契約を満たす接続候補を書いた。
このファイルは通常 import に含めない。依存確認の結果と検証範囲は
`evidence/flt-regular-import-probe.txt` に記録する。
**この候補の証明本体を、上流依存込みで型検査したとは数えない。**

## 5. 検証済みの条件付き consumer

`KummerUnitPowerCriterion R p` は、上流定理が供給すべき命題そのものを表す。
新しい公理ではなく、後続定理で明示的に受け取る引数の型である。
単元群全体の p 乗写像の全射性を要求せず、整数と mod p で合同な単元に限定する。

`factor_eq_zeta_sub_one_mul_pow_of_unit_criterion` はこの入力を受け取り、
既に証明した合同条件で δᵢ=κᵢ^p を得る。
θᵢ=κᵢγᵢ と置き、λ*Sᵢ=ζ^i−1 を使えば

```
a+ζ^i b = (ζ^i−1)*θᵢ^p
```

となる。FLT 接続は
`exists_GN_factor_eq_zeta_sub_one_mul_pow_of_unit_criterion`。
一般 p のこの結論は **criterion を仮定した条件付き定理**。
類数条件から一般の criterion を証明したという主張ではない。

## 6. 三次では実際の単元補題まで供給できる

Mathlib の
`IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`
は、三次円分体で整数と mod λ² で合同な単元が ±1 であることを証明している。

`cubic_kummer_unit_power_criterion` は、mod 3 の合同を
λ²∣3 により mod λ² へ移し、この実際の定理を適用する。
±1 は自分自身の三乗なので、単元群内の三乗根を返す criterion が閉じる。

`exists_GN_cubic_factor_eq_zeta_sub_one_mul_cube` は
外部 criterion 引数なしで未解析単元を除いた因子表示を得る。
原始性、方程式、3∣c の向き、c≠0、そしてイデアルの主イデアル化用の類数条件は
従来どおり入力に残る。FLT の矛盾や降下の構成は結論しない。

## 検証と未完部分

新規15例と20宣言（17定理、3定義）の公理 whitelist を追加。
内部係数の深度条件、剥離で失う一段、p=3,5 の実際の生成元の p 乗、
幾何和の単元、三次の実際の単元補題の適用、δᵢ の型・復元・整数証人の符号を検証する。
パケットを受け取る例は条件付き API の確認であり、非自明 FLT 解の存在例ではない。
公理 whitelist は criterion 仮定を解消する検査でもない。
検証記録は `evidence/validation-ramified-primary.txt`。

一般 p で条件付き adapter を外すには、上流の依存を実導入し、
接続候補と推移的な公理依存を同じ環境で確認する必要がある。
任意の Case II の向きの正規化と無限降下も未証明。
