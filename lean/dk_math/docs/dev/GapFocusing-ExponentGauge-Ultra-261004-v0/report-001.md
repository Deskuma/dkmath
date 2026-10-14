# Gap focusing / exponent gauge — Report 001

Date: 2026-10-04. Branch: `research/GapFocusing-ExponentGauge-Ultra-261004-v0`.
Initial HEAD: `6187a0add`. Lean / Mathlib: `v4.34.1`.

**判定は Outcome B。** 固定した基点に対する Gap の標準分解、非自明位相を
保持する GN、素数次数の既約性を Lean で接続した。FLT の残余単数類は、
冪抽出と ramifier の規格化を追加した後の算術層である。
文書が予想した判定を前提にはせず、現在のソースと新しい証明で判定した。

公開入口は [DkMath.NumberTheory.GapFocusing](../../../DkMath/NumberTheory/GapFocusing.lean)。
既存定理の型と実際の環は [source inventory](source-inventory-001.md)、
検証の範囲と結果は [validation](evidence/MANIFEST.md#log-2a85498f28567ebe) に固定した。

## 1. 何が canonical なのか

`(a,b) ↦ (a-b,b)=(x,u)` は `focusCoordinates` という可逆な座標変換である。
座標変換だけでは情報を失わない。構造として新たに明示できるのは、
基点 `u` を係数環に固定し、Gap を形式変数 `X` とした次の唯一の分解である。

```text
(X+C u)^d-(C v)^d
  = X*GTail d 1 X (C u) + C(u^d-v^d).
```

任意の可換係数環で、`unfocused_constant_unique` が定数余剰の一意性を、
`focused_quotient_unique` が焦点化した商の一意性を証明する。
零因子を持つ係数環でも形式 `X` の乗法は単射であり、係数比較で証明できる。
したがって基点を固定した多項式の Gap 方向と余剰の分離は標準的である。
基点を選ばずに絶対的な幾何方向を与えるという主張は含まない。

`X_dvd_unfocused_iff` の厳密な判定は

```text
X ∣ ((X+C u)^d-(C v)^d)  ↔  u^d=v^d.
```

右辺は `u=v` を要求しない。例えば偶数次数では基点 `1,-1` が同じ冪を持つ。
数値 `x` に評価した後の正しい判定は `gap_dvd_iff_dvd_defect` の
`x ∣ u^d-v^d` である。整数の `x=2,u=1,v=5,d=2` は左の数値整除を満たすが、
余剰は `-24≠0`。この境界は回帰例でも検証した。

余剰を `focusDefect d u v` と名付けた。変換則も確認している。

```text
defect(u,w) = defect(u,v)+defect(v,w)
defect(cu,cv) = c^d*defect(u,v).
```

これは基点変更の cocycle と同次性である。基点の同時平行移動で値は一般に
変わるため、無条件の invariant とは呼ばない。

## 2. GN は何を消し、何を保持するか

新しい GN の定義は作っていない。既存の `GTail d 1` を使う。
`d>0`、可換整域、原始 `d` 乗根の存在を仮定すると、
`focused_pow_sub_pow_eq_prod` と `GN_eq_nontrivial_phase_prod` は

```text
(x+u)^d-u^d = ∏_{xi^d=1} (x+(1-xi)u)
GN_d(x,u)  = ∏_{xi^d=1, xi≠1} (x+(1-xi)u)
```

を証明する。積の添字は正確には `Polynomial.nthRootsFinset d 1` と
その `erase 1` である。原始根はその全 `d` 個の根を与える。
生成元による `zeta^i` のラベルは変わるが、根集合と除去する根 `1` は変わらない。

`phaseFactor_eq_gap_forall_iff` は、任意の可換環で
`(∀u, x+(1-xi)u=x) ↔ xi=1` を証明する。多項式としての同値もある。
非零基点を持つ整域なら点ごとの同値も成立するが、`u=0` では全位相因子が `x`
となるので、点ごとの一意性を無条件には述べない。

GN の位相積は形式多項式環で `X` を消去してから評価したので、`x=0` でも成立する。
GN が取り除くのは自明位相の明示的な一因子であり、残りの位相を隠して
捨てる操作ではない。特に `focused_quotient_eval_zero` は

```text
GN_d(X,u)|_{X=0} = d*u^(d-1)
X^2 ∣ ((X+u)^d-u^d) ↔ d*u^(d-1)=0
```

を確認する。後者は `X_sq_dvd_focused_iff`。基点と次数の情報は商に残る。
標数による多重性も残り、`ZMod 3` では `GN_3(X,1)=X^2` になる。
この環は原始三乗根を持つ整域という位相定理の仮定を満たさない。

## 3. 素数次数は定義以上の意味で rigid か

単に「`d=ab, a,b>1` がない」と述べれば素数性の言い換えに留まる。
今回は基点 `1` の整数係数多項式 `kernelPolynomial d := GN_d(X,1)` を取り、
既約性という実際の構造を証明した。

```text
2≤d → (Irreducible (GN_d(X,1) : ℤ[X]) ↔ Nat.Prime d).
```

`kernelPolynomial_monic` と Gauss の補題により、
`GN_polynomial_rat_irreducible_iff_prime` は同じ同値を `ℚ[X]` でも証明する。

`kernelPolynomial_eq_prod_cyclotomic` は

```text
GN_d(X,1) = ∏_{k∣d, k≠1} Φ_k(X+1),   d>0
```

を証明する。各非自明な次数約数が実際の多項式因子となる。
素数 `p` では一層 `Φ_p(X+1)` に縮まり、平行移動の環同型と
Mathlib の整数円分多項式の既約性から既約となる。
合成次数では既存 `GN_mul_degree` を使って二つの非単元因子を得る。
その非単元性は `X=0` での値 `a,b≥2` を整数単元 `±1` と比較して証明する。
これは次数分解の命名だけに依存しない既約性判定である。

この判定は係数環と基点を指定した結果である。任意の環・任意の基点へは
拡張していない。また多項式の既約性は整数評価値の素数性を意味しない。
既存の正自然数 GN API は「GN 値が素数なら次数が素数」という必要条件を
別途与える。

## 4. FLT の単数ゲージは phase focusing から降りるか

幾何級数は確かに接点を与える。`phase_geometric_sum_unit` は、
原始根、`2≤n`、`j.Coprime n` のもとで、実際の単数 `eta_j` を構成して

```text
1-zeta^j = (1-zeta)*eta_j
x+(1-zeta^j)u = x+(1-zeta)*eta_j*u
```

を証明する。しかしこれは線形因子全体から単数を取り出す式ではない。
`phase_polynomial_associated_iff` は、非零基点を持つ整域の形式多項式で
`X+C((1-zeta)u)` と `X+C((1-eta)u)` が同伴であることを、位相一致と同値にする。
基点係数の同伴関係は、monic な線形因子全体の同伴関係にならない。
数論環で評価した後の偶然の同伴関係については個別の算術解析が必要である。

既存 FLT357 監査の共通定理を production の `UnitGauge` に移した。
整閉整域、非零 source と固定非零 ramifier、正指数、および二つの抽出式

```text
A=lambda*u*beta^n=lambda*v*gamma^n
```

を入力すると、単数 `t` が存在して `u=v*t^n` となる。
`sameUnitPowerClass_of_fixed_extraction` はこれを実際の単数群の関係として表す。
抽出根の選択には依存しないが、抽出の存在は phase 分解から自動には得られない。

一般の load `r` では抽出式を `A=lambda^r*u*beta^n` と書く。
その基礎 ramifier の代表を `lambda'=w*lambda` に変えると

```text
u'=w^(-r)*u
[u']=[u] ↔ ∃t∈Rˣ, w^r=t^n.
```

`ramifier_rescaling` と `ramifier_rescaling_same_class_iff` がこの変換を証明する。
`ramifier_rescaling_can_change_cube_class` は `ZMod 7` の `w=2,n=3,r=1` で
単数類が変わることを kernel で検証する。これは有限環での一般 API の較正であり、
FLT の三つの整数環を同一視する例ではない。

実際の後続処理には ideal-power equality とその ideal root の主イデアル化、または
それを与える Euclidean/PID 算術が必要である。完全な冪への吸収にはさらに
単数冪類の除去が要る。現在の p=7 receiver も、理想七乗を生成してから
`A=lambda*u*beta^7` に進む。したがって phase のラベル選択と抽出後の単数類は
異なる型のデータであり、今回の一般的な自動同一視は成立しない。
より強い source 固有の橋の不存在まで証明したわけではない。

実際に current p=7 carrier には、同じ degree-six 環内での正の接続がある。
`L=ofReal p.rho`, `R₀=ofReal (rotateEquiv p.rho)` とすると

```text
currentLinearCarrier c = R₀-currentPhaseZeta c*L
                      = (R₀-L)+(1-currentPhaseZeta c)*L.
```

この Gap 座標への書き換えは既存
`phaseCarrier_eq_uniformizer_mul_quotient` の証明内で既に検証されている。
同じ source に対する位相座標と ramifier 抽出を結ぶ具体的な接点であり、
単なる norm 比較ではない。そこから unit-times-seventh-power へ進む部分が
追加の理想七乗／生成元算術を使う。したがって Outcome B はこの正の接続とも整合する。

[SevenCarrierBridge](checks/SevenCarrierBridge.lean) ではこの座標同一性を独立した
定理にし、同じ current packet の既存冪抽出と、新 production API による
固定 uniformizer の単数類独立性を検証した。三つの定理とも `sorryAx` 依存はない。

## 5. 次数 2p は何を意味するか

可換半環で、素数性を仮定せず両順序を確認した。

```text
p then 2:
GN_{2p}(x,u)=GN_p(x,u)*((x+u)^p+u^p)

2 then p:
GN_{2p}(x,u)=(x+2u)*GN_p(x*(x+2u),u^2).
```

前者は p 乗後の差を二次式に渡し、後者は二乗後の Gap と基点を p 次 GN に渡す。
`GN_two_mul_degree_orders` が積としての一致を証明する。
これは冪写像の合成に伴う異なる中間座標である。
指数 `2` を平面の次元と解釈する写像は与えない。

奇素数 `p` では、さらに `kernelPolynomial_two_mul_prime` が正確な三層を与える。

```text
GN_{2p}(X,1) = (X+2)*Φ_p(X+1)*Φ_{2p}(X+1).
degree Φ_2 = 1, degree Φ_p = p-1, degree Φ_{2p} = p-1.
```

根拠は `two_mul_prime_divisors_erase_one` による非自明約数集合 `{2,p,2p}`
と円分多項式の積である。次数は `two_mul_prime_cyclotomic_layer_degrees` で検証した。
`p=2` では約数の重複が集合として消え、`{2,4}` の二層になる。
したがって三層式は `p≠2` を明示し、generic な二つの合成式はこの場合も有効である。

平面 lifting / magic square との接続には、対象となる配置空間、その写像、
上の二つの中間座標との対応、および写像が保つ関係を明示して証明する必要がある。
今回の指定文書と現在のソースから、その精密な対象写像は特定できなかった。

## 6. 検証済み数学と残る解釈

| 主張 | 状態 |
| --- | --- |
| 固定基点の形式 Gap 分解・唯一の商と定数余剰 | 新規 Lean 証明 |
| 零余剰と形式 `X` 整除の同値 | 新規 Lean 証明 |
| GN が全非自明位相を保持 | 分裂する整域で新規 Lean 証明 |
| 自明位相だけが背景に依存しない | 普遍／多項式条件で新規 Lean 証明 |
| 基点1・整数／有理係数 GN の既約性と素数次数の同値 | 新規 Lean 証明 |
| 幾何級数による位相係数の単数変更 | 既存 Mathlib を新規 API へ接続 |
| 固定規格化での抽出根に依存しない単数冪類 | 既存監査から production に移して検証 |
| 規格化変更での残余単数類の変換則 | 新規 Lean 証明とクラス変更の反例 |
| 2p の二つの合成順序 | 新規 Lean 証明 |
| 奇素数2pの三つの円分層とそれぞれの次数 | 新規 Lean 証明 |
| 基点を選ばない絶対的 Gap 方向、一般的 phase–FLT 単数類の同一視 | 未確立 |
| 普遍的 moire 周期、平面・magic-square lifting、FLT 新下降 | 未確立 |

Outcome B は、上の前半の構造と後半に必要な追加算術データの区別による判定である。
