# NOTE-032 — 実点の捩れ extension と局所吸収の大域化

2026-11-01。前章の二アンカーと最終群論に続き、大域証明の間に必要な実際の商表現を構成した。

## 1. 今回完成した接続

- 同じ有限 `E[n]` 上で、全局所慣性の変化量が部分群 `K` に入れば、全 Galois 元の変化量も `K` に入る。
- 良還元かつ `q ∤ n` の慣性固定性を内部供給し、局所仮定を `q ∣ n` または `q ∣ Δ` の住所に限定。
- Frey ではその仮定を `2`、`p`、`abc` の素因子の住所へ限定し、前章の最終矛盾から大域固定性の仮定を除去。
- `p⁻¹K / K` を同じ点群から構成し、商の濃度・加群構造・実際の Galois 表現を証明。
- 有限巡回 `K` では二次元商と一次元の捩れ像を証明し、適切な指数で消える場合の開核を供給。
- 最初の Cofixed 直線から、固定直線と円分商を持つ実際の二次元 extension を構成。
- 安定な補直線が供給された場合、次段の包含・位数・巡回性・捩れ指数・安定性・底への降下を全て証明。

**一般 hno は未完成。** 安定な補直線の存在、必要な悪い住所での高位捩れの局所吸収、
実際の Frobenius 関係式、Mazur Step Three の幾何学的適用は残る。

## 2. 局所吸収から大域固定性へ

コード:

- `DkMath/Lib/NumberTheory/EllipticTorsionInertiaAbsorption.lean`
- `DkMath/FLT/FreyTorsionInertiaAbsorption.lean`

`K` は同じ `Points E` 内の任意の加法部分群とする。`K` を実際の `E[n]` へ引き戻して

```lean
AddSubgroup.toZModSubmodule n (K.comap (torsionGroup E n).subtype)
```

を作る。この部分加群への所属は、元の点が `K` に属することと同じである。
既存 `EllipticInertiaTransport.isCofixedOn_of_inertia` にこの部分加群を渡すと、
局所の変化量所属が全 Galois 元について成立する。

ここで使う既存の算術は、非零次数の幾何学的捩れ有限性、座標作用の連続性、開核、
および絶対慣性を含む開部分群が全群となる定理である。生成性や開核を新たな
provider として仮定していない。`K` 自体の有限性や安定性も不要である。

良い住所で `q ∤ n` なら、整数モデルの剰余判別式は非零で `n` は付値環の単元。
既存の prime-to-`q` 捩れの慣性固定性が変化量を零にする。従って利用側に残すのは
`q ∣ n` または `q ∣ Δ` の住所だけである。

Frey の整数モデルの判別式支持と `n=p^m` を使うと、残る住所は

\[
q=2\quad\text{または}\quad q=p\quad\text{または}\quad q\mid abc
\]

となる。全ての延長付値環についての条件を保ち、有限剰余体の濃度条件は導入しない。

前章の `residual_line_tower_frobenius_impossible` が受け取っていた大域条件
`hfixed` は、新しい `residual_line_tower_inertia_frobenius_impossible` では
これらの局所条件 `hbad` から証明される。

重要な境界: 既存の `E[p]` 上の不分岐性を、そのまま `E[p^m]` へ拡張してはいけない。
高位捩れにおける悪い住所の吸収は、この定理の明示入力として残している。

## 3. 倍写像の逆像と商

コード: `DkMath/Lib/Algebra/TorsionPreimageQuotient.lean`。

\[
P=[n]^{-1}K=\{y\mid ny\in K\},\qquad V=P/K
\]

を元の同じ群 `G` の部分群・商として作る。包含 `K → P` と倍写像 `P → K` を区別する。
前者が商の分母であり、後者の核が `G[n]`。

倍写像が全射なら、同じ写像の核と商の濃度公式から

\[
\#P=\#K\cdot\#G[n],\qquad \#P=\#V\cdot\#K.
\]

`K` が有限であれば `#K>0` なので約分でき、`#V=#G[n]` を得る。
無限型における `Nat.card=0` を約分することはない。

`n • [y]=[ny]=0` なので `V` には標準の `ZMod n` 加群構造が入る。
`K` を保存する準同型は `P` を保存し、そのまま `V` へ降りる。
群作用を降ろした表現は基底選択を用いず、代表点への作用と可換する。

## 4. 捩れ像と一次元性

元の `G[n]` の `V` における像を `C` とする。写像 `G[n] → C` の核は `K[n]`。
従って

\[
\#G[n]=\#C\cdot\#K[n].
\]

楕円曲線で `n=p` なら、既存の幾何学が `#E[p]=p²` を供給する。
`K` が位数 `p^m`, `m≥1` の有限巡回群なら、Mathlib の巡回群における倍写像の核の公式から

\[
\#K[p]=\gcd(p^m,p)=p.
\]

従って `#C=p`。`#V=p²` と併せて `dim V=2`, `dim C=1` が従う。

コード: `DkMath/Lib/NumberTheory/EllipticTorsionPreimageExtension.lean`。

`K` が `p^m` 倍で消えれば、`P` は `p^(m+1)` 倍で消える。
従って `E[p^(m+1)]` の表現の開核は、商表現の核に含まれる。
この包含から開核を証明し、有限レベルや連続性を外部仮定にしない。

## 5. Cofixed 直線から実際の第一段へ

コード: `DkMath/FLT/FreyCofixedTorsionExtension.lean`。

元の残余直線 `L` の実点群内の像を `K=pointSubgroup ... L` とする。
一次元性から `#K=p` と巡回性が、Cofixed 性から安定性が供給される。

`C` の各元は元の `E[p]` の点 `e` で代表される。
Cofixed 性は `σe-e ∈ K` を与えるから、同じ商では `[σe]=[e]`。
従って `C` は点ごとに固定される。

この第一段では `pK=0` なので、倍写像は商へ降りて全射 `V → K` を与え、その核は `C`。
既存 `residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul` により `K` 上の作用は円分指標。
倍写像と作用の可換性から

\[
\rho_V(\sigma)v-\chi_p(\sigma)v\in C
\]

が従う。Lean コードでは円分 scalar の自然数代表による `nsmul` で記述しており、
`ZMod p` の標準加群作用と同じものである。

従って最初の extension の二次元性、固定側の一次元性、商上の円分作用、開核は
実際の `Source` と `L` だけから構成済みである。
これらから安定な補直線が自動的に存在すると推論してはいけない。

## 6. 安定な補直線から次段へ

`C'` を `C` の安定な補部分加群とする。`P → V` による `C'` の逆像を、
元の同じ点群へ包含して `K'` を定義する。

標準射影の全射性と核の同定から

\[
K\subseteq K',\quad \#K'=\#C'\cdot\#K=p^{m+1}.
\]

`K'` の点は `P` に入るので `p^(m+1)` 倍で消える。
補部分加群の安定性から `K'` も安定。
`p` 捩れ点が `K'` に入れば、その商類は `C` と `C'` の両方に入る。
両者は交わらないので商類は零、元の点は `K` に戻る。

最後に巡回性を保持する。`K'[p]` は巡回 `K` の `K[p]` に入るので高々 `p` 個。
有限 `p` 群についての
`PrimePowerCyclicCriterion.isAddCyclic_and_card_dvd_of_prime_power_exponent`
により `K'` は巡回となる。位数と指数だけから巡回性を主張していない。

コード: `DkMath/Lib/Algebra/PrimePowerCyclicCriterion.lean`。
その証明は全ての `p^k` 捩れの濃度を帰納的に抑え、任意の `n` 捩れを gcd に対応する
`p` 冪捩れへ戻して、有限巡回群判定を適用する。

`exists_tower_step_of_stable_complement` はこの全不変量を返し、Frey の第一段では
`residual_preimage_stable_complement_lifts` が同じ Source 上の位数 `p²` の群を返す。

## 7. 残る算術

構成済みの二次元表現に対し、必要な局所分裂・不分岐条件を満たすことを証明し、
大域 extension 消滅から安定な補直線を得る工程が残る。
一般の Cofixed 性だけではその補直線を作っていない。
高い段での円分商作用の輸送も、第一段の `pK=0` の証明をそのまま使うことはできない。

また、Mazur Step Three を実際の Eisenstein 商と specialization に適用する大域幾何、
高位捩れの悪い住所での吸収、および実際の Frobenius の Cayley–Hamilton 関係も残る。

今回の実装は、これらを仮定した `hno` provider を新設する代わりに、具体的な商・像・
作用・持ち上げ・局所大域輸送を証明して、未実装の算術に必要な入力を狭めたものである。

## 8. 検証と証拠

- 有限群 `(ZMod 4)²` で、元の核で零になる点と、新しい非零捩れ像を区別。
- 補部分加群と捩れ像の disjointness を外すと降下が偽になる反例を確認。
- `y²=x³-x` の3上の任意の延長付値環で、実際の2捩れの慣性固定性を確認。
- 主要定理の型と opaque 本体を走査し、実際の絶対慣性生成・有限性・倍写像へ到達することを要求。
- 旧 FLT・Kummer 終点・外部 `P2M/P2MW`・独自の未証明定数による代替を排除。

検証結果は `evidence/validation-note032-torsion-extension-inertia.txt` と
`evidence/note032-torsion-extension-import-audit.json` に保存する。
