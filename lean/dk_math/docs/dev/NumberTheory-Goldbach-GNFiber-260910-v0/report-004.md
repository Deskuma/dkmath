# 全周期計数と単純 incidence 経路の反証

## 検証済み

`./lean-build.sh DkMath.NumberTheory.Goldbach.Cardinality DkMath.NumberTheory.Goldbach.Limitations` が成功。

CRT の写像について単射・全射を実際に証明し、全周期の生存数を

\[
\prod_{r\in S}\left(r-\begin{cases}1&r\mid2n\\2&r\nmid2n\end{cases}\right)
\]

と同定した。有限素数集合では各因子は正なので全周期の生存集合は非空。新素数の追加時の乗法的な計数式も証明。

## kernel で確定した不成立条件

1. `n=6`、標的 `12`: 候補数 5、被覆された候補数 4、incidence 5、生存数 1。したがって全称的な `incidence < n-1` は偽。`GoldbachPairAt 6` は正確な容量式から証明できる。
2. `n=2`: 真の生存集合は `{0}` で `2+2` を表すが、生の合同除外では候補が全滅する。
3. `n=10`, `r=3`: offset `4` は合成数障害を持ち、同じ剰余の offset `7` は端点 `3` の例外で障害を持たない。どちらも admissible であり、真の障害には単純周期性がない。
4. `9` は合成数だが次数 2 の正の GN signature を持つ。`n=6,u=3` では左側 `3` の素数性と signature から右側 `9` の素数性は導けない。

これらは Goldbach 自体の反例ではない。特定の中間命題を否定し、証明に必要な条件を明確にする結果である。

## 追加作業

剰余・商座標への単射から、各素数の区間障害数を `局所禁止数 * ((n-2)/r+1)` で抑える具体的な有限上界を追加中。公開 facade、従来の偶数表現との同値、有限決定手続き、回帰検証、および axiom 監査を最終検証にまとめる。
