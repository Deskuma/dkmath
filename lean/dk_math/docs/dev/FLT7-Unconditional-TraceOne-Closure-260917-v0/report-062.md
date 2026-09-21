# FLT7TC-005R56 — Fixed `n = 6` finite certificate bridge

## 実施範囲

`instruction-062.md` の Part A–E を確認し、R55 の `F5` 固定形式・三根の
分離データを再利用する新規 module
`DkMath.FLT.Seven.ThomasThueSixApproximation` を実装した。既存の
`SevenRealCubicThetaSeventhPower` へは追加していない。

## Part A–B: ordered roots and factorization

`ThomasSixRootPacket` を追加し、三つの root interval、`f5Real lambda_i = 0`、
`lambda1 < lambda2 < lambda3` を ordered packet として構成した。R55 で証明済みの
separation

```text
9/10  ≤ lambda2 - lambda1
61/10 ≤ lambda3 - lambda2
71/10 ≤ lambda3 - lambda1
```

も packet に昇格した。三根の symmetric sums を root equation から復元し、
`f5Real` の monic cubic factorization を kernel-check した。整数 `R,S` に対して

```text
F5(R,S) / S^3
  = (R/S-lambda1)*(R/S-lambda2)*(R/S-lambda3)
```

を証明し、`F5(R,S)=1` から

```text
|(R/S-lambda1)| * |(R/S-lambda2)| * |(R/S-lambda3)|
  = 1 / |S|^3
```

を得た。`S ≠ 0` は明示的に使用している。

## Part C: nearest-root approximation

`|S| ≥ 6` のとき、積の三因子の少なくとも一つが `≤ 1/|S|` であることを
三分岐として証明した。残り二因子には separation と `1/|S| ≤ 1/6` を使って
`11/15` 以上の下界を与えた。

その結果、最近接因子 `d` について

```text
d ≤ (225/121) / |S|^3 < 2 / |S|^3 < 1/(2*S^2)
```

を `linarith`、`norm_num`、正の分母に対する不等式変形、`ring` で kernel-check
した。したがって三根のいずれかについて、指定された explicit constant
`1/(2*S^2)` の strict approximation が得られる。

## Part D: Legendre bridge

`thomasSix_legendre_bridge` を追加した。分母の正規化を隠さず、次の順序で処理している。

1. 有理数を `q := Rat.divInt R S` とする。
2. `Int.isCoprime_iff_nat_coprime` で `Nat.Coprime R.natAbs S.natAbs` を得る。
3. `S > 0` の場合は `Rat.den_div_eq_of_coprime` を直接適用する。
4. `S < 0` の場合は `(-R)/(-S)` へ符号反転して正の分母へ戻す。
5. いずれの場合も `(q.den : ℝ) = |(S : ℝ)|` を証明する。
6. Part C の近似を `Real.exists_rat_eq_convergent` の仮定へ変換する。

この theorem は、`F5(R,S)=1`、`IsCoprime R S`、`|S| ≥ 6` から、`R/S` が
三根のいずれかの `Real.convergent` であることを返す。公開された Thomas 分類定理は
仮定していない。

## Part E: Thomas 1990 の一次資料確認

確認できた公開資料は、[ScienceDirect の論文ページ](https://www.sciencedirect.com/science/article/pii/0022314X9090154J)
（DOI `10.1016/0022-314X(90)90154-J`）と [Utah の公開 JNT volume PDF](https://ftp.math.utah.edu/pub/tex/bib/jnumbertheory1990.pdf)
である。前者には
書誌情報と abstract が掲載され、後者には当該論文の書誌項目が含まれるが、取得した
本文テキストは巻号の書誌・参考文献部分だった。

資料に明記されている事項は、`0 ≤ n ≤ 1000` で非自明解が現れるパラメータが
`n = 0,1,3` のみであること、および `n ≥ 1.365 × 10^7` の別の定理である。

一方、本文の theorem/lemma 番号、選択した root、収束分数の候補表、分母または
index の上界、n=6 の有限入力データは本文から取得できなかった。従ってこれらを
再構成・推測していない。また、abstract の分類結果を Lean の axiom、仮定、または
certificate bound として実装していない。

## Certificate ledger and boundary

|項目|R56 の結果|
|---|---|
|三根 ordered packet|kernel-check 済み|
|三根 factorization|kernel-check 済み|
|`F5=1` の absolute product identity|kernel-check 済み|
|explicit nearest-root bound|kernel-check 済み|
|Legendre / convergent bridge|kernel-check 済み|
|Thomas 1990 の本文由来 finite bound `B < 7^8`|本文データ未取得のため未実装|
|`7^8 \mid S` との最終矛盾|finite bound 未取得のため未接続|

従って R56 の実装結果は **Outcome C** である。Part A–D の exact analytic bridge は
完成したが、Thomas の本文に由来する finite certificate がないため、次の未解決境界は

```text
FixedThomasSixBound:
  F5(R,S)=1 -> |S| < 5764801
```

またはこれより強い、本文に基づく明示的な convergent-index / denominator bound
である。

## ビルド・scratch 検証

- `lake build DkMath.FLT.Seven.ThomasThueSixApproximation` 成功（9211 jobs）。
- `lake env lean docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/scratch-062-legendre-audit.lean` 成功。
- `scratch-062-legendre-audit.lean` で production theorem と Mathlib の
  `Real.exists_rat_eq_convergent`、`Real.convergent`、
  `Rat.den_div_eq_of_coprime` の宣言を確認する。
- 同 scratch の `#print axioms` で `thomasSix_legendre_bridge` を確認し、依存は
  `propext`、`Classical.choice`、`Quot.sound` の標準 kernel axioms のみだった。
