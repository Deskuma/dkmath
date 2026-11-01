# NOTE-032 — 巡回塔の全段で円分商を読む

2026-11-01。前章の具体的な捩れ extension を、第一段から全段へ進める。

## 1. 今回閉じた接続

同じ Frey 曲線の幾何学的点群内で、元の Cofixed 直線の点部分群を `B` とする。
`B` を含む Galois 安定な有限巡回群 `K` が、位数 `p^m`, `m≥1` を持つとき、

\[
P=[p]^{-1}K,\qquad V=P/K,\qquad C=\operatorname{im}(E[p]\to V)
\]

について次が Lean で証明された。

- `K[p]=B`。底への降下を別の仮定として要求しない。
- 実際の倍写像 `V → K/pK` の核が `C`。従って `V/C ≃ K/pK`。
- `V` は二次元、`C` は一次元で点ごとに固定され、`V/C` の作用は円分指標。
- `V` の表現の開核は、実際の高次捩れ表現の開核から供給される。
- 局所部分群 `F` が与えられれば、その像から局所安定な補直線を構成できる。
- `p` 以外の良還元素数での不分岐性を内部供給し、悪い素点の吸収だけを残す。
- 最終の慣性・Frobenius 矛盾から `hdown` を取り除く。

一般 `hno` はまだ完成していない。ここでは塔 `K` の存在を証明したのではなく、
各段で使う表現と輸送を完成させた。局所部分群、悪い素点での吸収、大域分裂、
実際の Frobenius 関係と Eisenstein 商の幾何学的適用は残る。

## 2. 第一段の倍写像をそのまま使えない理由

第一段では `pK=0` だから、`[y] ↦ py` は `P/K → K` を定義できた。
高い段では代表点を `y+k` に変えると、値は `py+pk` になる。
一般に `pk` は零でないため、値域を同じ `K` にしてはいけない。

全段に使える正しい写像は

\[
\mu:V\longrightarrow K/pK,\qquad [y]\longmapsto [py].
\]

コードは `DkMath/Lib/Algebra/TorsionPreimageScalar.lean`。
`multiples` は `K → K` の実際の倍写像の像、`quotientMultiplyMod` はその像による
実際の商への準同型である。`pK=0` を仮定する古い `quotientMultiply` とは型が違う。

`μ([y])=0` は、ある `k∈K` に対して `py=pk` が成立することと同値。
この場合 `e=y-k` は元の `E[p]` に入り、`[y]=[e]` なので `[y]∈C`。
逆に捩れ点の像なら倍写像は零になる。

周囲の倍写像の全射性から `μ` も全射となる。従って第一同型定理から

```lean
TorsionPreimageQuotient.torsionImageQuotientEquiv
```

が `V/C ≃+ K/pK` を構成する。型も写像も元の同じ点群に由来する。

## 3. 巡回群の底と最上商で同じスカラーを読む

コードは `DkMath/Lib/Algebra/CyclicPrimePowerScalar.lean`。

位数 `p^m` の有限巡回群では

\[
pK=K[p^{m-1}].
\]

包含は `p^m K=0` から従う。両群の濃度は、Mathlib の巡回群の倍写像公式から
それぞれ `p^(m-1)` なので、同じ実際の部分群として一致する。
`m=1` も含まれ、この場合の右辺は `K[1]={0}` である。

自己準同型 `f:K→K` が `K[p]` 上で自然数 `c` 倍とする。
任意の `x∈K` に対して `p^(m-1)x` は `K[p]` に入るから

\[
p^{m-1}(f(x)-cx)=f(p^{m-1}x)-c(p^{m-1}x)=0.
\]

従って `f(x)-cx∈pK`。これが `sub_nsmul_mem_range_of_socle` である。
`K` 全体で `f(x)=cx` と言っているのではない。

実際、`K=ZMod 9` の4倍写像は `K[3]` を固定し、`K/3K` 上でも恒等だが、
`1` 自体を固定しない。この違いを回帰例で確認している。
また `ZMod 9 × ZMod 3` の shear は底を固定しても最上商を固定しない。
巡回性を外せないことも、具体的な反例として Lean で確認した。

## 4. Frey の底を全段へ輸送する

コードは `DkMath/FLT/FreyCofixedTorsionTower.lean`。

元の `B=pointSubgroup ... L` は位数 `p` で、`p` 倍で消える。
`B≤K` なら `B→K[p]` は単射。巡回群の倍写像公式は `#K[p]=p` を供給するので、
この包含は全射でもある。従って `K[p]=B`。

元の直線上の円分作用は既存の Weil 対と Cofixed 性から証明済みである。
上のスカラー輸送を同じ座標作用へ適用すると

\[
\rho_V(\sigma)v-\chi_p(\sigma)v\in C
\]

が全段で得られる。

```lean
residual_cyclic_tower_socle_mem_base
residual_cofixed_cyclic_extension_quotient_cyclotomic
residual_cofixed_cyclic_extension_profile
```

必要な群の不変量は `Finite K`、`IsAddCyclic K`、`#K=p^m`、`m≥1`、`B≤K`、
および同じ Galois 作用による安定性。`K[p]` 上の円分作用、`p^m K=0`、
商の濃度、開核を利用側の provider として追加していない。

## 5. 局所部分群の像から補直線を構成する

コードは `DkMath/Lib/Algebra/TorsionPreimageLocalComplement.lean`。

局所部分群 `F` が `K≤F≤P` を満たすとする。
同じ商射影による像を `C'` と定義すると、逆像を取って点群へ戻した群は `F` そのもの。
この往復の等式から

\[
\#C'\,\#K=\#F
\]

が従う。さらに `F[p]≤K` なら `C∩C'={0}`。
実際、`[y]∈C'∩C` なら `y∈F` と `e∈E[p]` で `y-e∈K` を満たすものがある。
`K≤F` より `e∈F[p]≤K`、従って `[y]=0`。

`#F=p^(m+1)` なら `#C'=p`。`dim V=2` と `dim C=1` から、
この実際の像が `C` の補直線になる。

`F` がある分解群だけで安定なら、`C'` もその分解群だけで安定となる。
`residual_cyclic_extension_complement_of_local_subgroup` はこの局所結論と往復の等式を返す。
各素点で別々の局所補直線が存在することから、一つの大域安定な補直線を
選べるとは推論しない。これには別の大域算術が必要である。

## 6. 良い素点と最終矛盾

`residual_preimage_unramified_away_of_bad_inertia` は `q≠p` を明示し、
`q=2` または `q∣abc` の住所での `P` 上の吸収から、商表現の全ての `p` 外での
不分岐性を導く。良い素点では、`P` の点が `p^(m+1)` 倍で消えることを位数から
供給して、既存の prime-to-`q` 慣性固定性を適用する。

元の `E[p]` の不分岐性を `E[p^(m+1)]` にそのまま移してはいない。
悪い素点で必要な吸収は引き続き明示入力である。

`residual_cyclic_tower_inertia_frobenius_impossible` は、前章の最終矛盾に
`K[p]=B` を接続して、入力 `hdown` を除去する。Frobenius の実際の元と
Cayley–Hamilton 関係、悪い素点での高次捩れの吸収は入力として残る。

## 7. 次に必要な大域算術

模範解答の `AddSubgroup.exists_towerStep_of_extVanishingCts` と
`ExtCitation.extVanishingCts_of_five_le` の証明本体を照合した。
後者は円分体の類群の omega 二乗固有空間の消滅と、局所冪条件を持つ単数の
同じ固有成分の消滅を使う。単なる有限群の補空間選択ではない。
また全類群が `p` と互いに素という正則性を仮定する定理でもない。

今回、これらを未証明の `hEXT` として導入していない。
未実装の主要部分は次の通り。

1. `p` 上で必要な実際の局所部分群 `F` を、良還元・乗法還元の高次捩れから構成する。
2. 悪い素点で逆像上の慣性吸収を証明する。
3. 円分体の固有成分の算術から、局所分裂する extension の大域分裂を証明する。
4. 得られた補直線を前章の持ち上げに入れて塔を反復する。
5. 実際の Frobenius 関係と Eisenstein specialization の幾何学的入力を閉じる。

これらの存在を仮定したことを、一般 `hno` の完成と数えない。

## 8. 検証

有限群の正例・反例、主要15宣言の公理監査、6終点の型と opaque 証明本体の
再帰的依存監査、5終点の公開入力監査を通常のテスト入口へ追加した。
旧 FLT・Kummer 終点・外部 P2M/P2MW・独自未証明定数への依存を監査で排除する。

実行結果は `evidence/validation-note032-cyclic-tower.txt` に保存する。
