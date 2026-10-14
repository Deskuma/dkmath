# FLT7TC-005R55 — Fixed n=6 Thomas–Mignotte certificate extraction

## 調査開始時点

`instruction-061.md` と R54 の `report-060.md`、および
`SevenRealCubicHighDepthFive.lean` を確認した。R55 の必須 target は
`F5(R,S)=1` の非自明解排除であり、現在の `7^8` high-depth packet と接続する
fixed-parameter certificate が必要である。

公開された Thomas/Mignotte の分類定理を Lean の仮定として導入せず、まず
プロジェクトの Mathlib revision にある Diophantine approximation / continued
fraction API と、fixed `n=6` の exact certificate 境界を調査する。

## 実装進行

R55 用 report を作成した。続いて Mathlib capability audit と、production に
昇格可能な固定有限 certificate の候補を調査する。

## Mathlib capability audit

プロジェクトの `.lake/packages/mathlib` に対して、次の import を持つ scratch
file を作成し、`lake env lean` を単体実行した。

```lean
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
```

Lean v4.34.0 で次の宣言がすべて解決した。

- `Real.exists_rat_eq_convergent`
- `Real.exists_rat_eq_convergent'`
- `Real.convergent`
- `Real.convs_eq_convergent`
- `Real.exists_convs_eq_rat`
- `GenContFract.of`
- `GenContFract.convs`

したがって Legendre 型の「十分に良い有理近似は収束分数である」という入口と、
`GenContFract` の収束分数列は利用できる。ただし、この API の存在だけでは
Thue 方程式の有限探索上界、根の分離定数、または全候補の completeness は得られない。

## 固定 `n = 6` の exact audit module

`DkMath.FLT.Seven.ThomasThueSixAudit` を新設し、次を kernel checkable な形で
実装した。

- `thomasForm n R S` と `thomasForm_six_eq_F5` による Thomas 形式と既存 `F5` の
  literal な `n = 6` 同定。
- `thomasForm_six_eq_one_iff` による右辺 `1` の同値。
- `f5Poly X = X^3 - 5X^2 - 8X - 1` と、
  `[-6/5,-11/10]`, `[-1/5,-1/10]`, `[6,13/2]` の各端点での厳密な
  有理符号証明。各値は `norm_num` で検証した。
- 既存の `T5 = 0` shell を利用した
  `thomasForm_six_trivial_shell_of_product_zero`。これは全解分類ではなく、
  product-zero が別途得られた場合に三つの trivial solution へ落とす補題である。

この module は `DkMath.FLT.Seven` facade へは追加していない。全非自明解の排除が
未完了のため、公開 closure API として昇格させず、R55 の固定パラメータ証明の
再利用可能な監査成果に限定した。

## 根の存在と separation

`ThomasThueSixAudit.lean` に実係数版 `f5Real` を追加し、`intermediate_value_Icc`
および降順区間用の `intermediate_value_Icc'` を使用した。これにより次の三つの
区間にそれぞれ実根を置いた。

```text
[-6/5, -11/10], [-1/5, -1/10], [6, 13/2]
```

区間端点の符号は `norm_num`、連続性は多項式の `Continuous` 証明、存在は
Mathlib の中間値定理で kernel check した。さらに任意に選んだ三根について

```text
9/10  ≤ λ₂ - λ₁
61/10 ≤ λ₃ - λ₂
71/10 ≤ λ₃ - λ₁
```

を区間端点の線形算術から証明した。これは近似証明に使える固定 separation
ledger だが、まだ各有理近似を収束分数へ送る `|F5|=1` の評価補題そのものではない。

## 公開証明機構の調査

確認した公開資料では、Thomas/Mignotte の `n = 6` の結論自体は引用されているが、
R55 用にそのケースだけを取り出した Lean 検証可能な有限候補リストまでは掲載資料から
得られなかった。参照した Mignotte--Pethő--Lemmermeyer の論文は、Thomas/Mignotte
による `|F_n|=1` の完全解決を前提にし、関連する一般的な証明工程として
Siegel--Baker の三対数線形形式、二対数への整理、Baker--Davenport 型の continued
fraction reduction を説明している。

参照資料: [On the family of Thue equations](https://arato.inf.unideb.hu/petho.attila/cikkek/68_lemipe.pdf)。

R55 の certificate ledger は現時点で次の通りである。

|項目|n=6 の現状|不足する Lean lemma/data|
|---|---|---|
|固定形式|`thomasForm 6 = F5` を証明済み|なし|
|根区間|3区間、実根の存在、3つの separation を証明済み|なし|
|Legendre 入口|`Real.exists_rat_eq_convergent` を型検証済み|`F5=1` からの明示近似評価|
|有限探索|未着手|収束分数の完全な index/denominator 上界|
|全解分類|未着手|上界以下の recurrence と `F5` 評価の exhaustive certificate|

したがって本 R55 では、外部定理を仮定して `F5_eq_one_trivial` を追加せず、
固定形式・根分離・continued-fraction API の kernel-checkable 境界までを実装した。
`7^8` high-depth branch の closure には、なお `|S| < 7^8` または同等の有限
certificate が必要である。

## ビルド結果

- `lake env lean docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/scratch-061-mathlib-audit.lean` 成功。
- `lake build DkMath.FLT.Seven.ThomasThueSixAudit` 成功（9210 jobs）。
