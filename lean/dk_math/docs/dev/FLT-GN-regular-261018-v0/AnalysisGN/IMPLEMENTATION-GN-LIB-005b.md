# GN-LIB-005b — 強可除性から原始借入三項へ

2026-10-24。ブランチ：`lib/FLT-GN-Completion-261023-v0`。
3モジュール、4定義・25定理を実装し、対象モジュール単位で検証を完了した。
005bの加法公式、強可除性、正確な共通因子、原始三項、平方借入恒等式までを扱った。

## 加法と指数積の恒等式

[PowerDifferenceCofactorArithmetic.lean](../../../../DkMath/Lib/Cosmic/PowerDifferenceCofactorArithmetic.lean)
は任意の可換半環で次を証明する。

```text
R_n(x,y) = R_n(y,x)
R_(a+b)(x,y) = x^a R_b(x,y) + y^b R_a(x,y)
R_(ab)(x,y) = R_a(x^b,y^b) R_b(x,y)
R_(2m)(x,y) = (x+y) R_m(x²,y²)
R_(2k+3) + xy R_(2k+1) = (x+y)² R_(k+1)(x²,y²)
```

有限和の反転、既存の一階再帰、二階再帰を使う。
零次数・対角・零座標にも適用でき、gapを割って約分する証明を避けている。
平方借入では右辺にsum座標の平方が現れる。
次数を半減する式の底はx²,y²へ変わるため、整数高さの厳密降下を結論しない。

## 強可除性

[PowerDifferenceCofactorStrongDivisibility.lean](../../../../DkMath/Lib/NumberTheory/PowerDifferenceCofactorStrongDivisibility.lean)
に自然数版を実装した。

まず原始座標と正次数から `Coprime R_n y`、`Coprime R_n x`、`Coprime R_n (xy)` を得る。
加法公式に出るyの冪はこのcoprimeによりgcdから除けるため、
`gcd(R_m,R_(n+m))=gcd(R_m,R_n)` が成立する。
繰り返しの引き算と互除法の帰納から、

```text
Coprime x y → gcd(R_m,R_n) = R_gcd(m,n)
```

を証明し、`Nat.IsStrongDvdSequence` に接続した。
互除法の証明構成はローカルMathlibの `Mathlib.Data.Nat.Fib.Basic.fib_gcd` を参考にした。
Fibonacci固有の加法公式・互いに素性は使わず、R_nの加法公式と座標coprimeを供給している。

両指数の0を含み、座標の大小や正性は不要である。
一方、指数の可除性から値の可除性を得るだけなら、指数積の恒等式を使えるため原始性も不要である。
この弱い結果と、原始性が必要な強いgcd結果を別の型にした。

## 借入補正項との正確なgcd

`xy R_(n-2)` は完成不足D_nとは異なる。
座標因子xyとのcoprimeと強可除性を合わせ、

```text
gcd(R_(j+2), xy R_j) = R_gcd(j,2)
```

を証明した。従って原始座標では、奇数次数nで1、偶数次数nでx+yが正確な共通因子となる。
これを偶数次数の `gcd(R_n,D_n)` の公式へ流用していない。
(5,3)、n=4では借入補正とのgcdは8、D_4とのgcdは16となる例も確認した。

## 共通因子を除いて作る原始三項

[CompletionLoan.lean](../../../../DkMath/Lib/Cosmic/CompletionLoan.lean) の定義は資料v4に対応する。

```text
h_n = if n mod 2 = 0 then x+y else 1
A_n = R_n / h_n
B_n = xy R_(n-2) / h_n
C_n = (x+y) R_(n-1) / h_n
```

n≥2と原始性のもとで、h_nが先の正確なgcdに等しいことを最初に証明した。
次に三つの分子すべてがh_nで割れることを証明し、掛け戻しの再構成を与えた。
したがって自然数除算に余りを隠していない。

原始三項の公開終点 `completionLoan_primitive_triple` は、
`n≥3`、`0<x`、`0<y`、`Coprime x y` のもとで
A,B,Cの正性、A+B=C、三つのpairwise coprimeをまとめて返す。
資料のx>yという順序条件は不要で、x<yも扱える。
次数2ではB=0なので正の三項の終点には含めない。

| n | (x,y) | h_n | (A,B,C) |
| --- | --- | --- | --- |
| 3 | (5,3) | 1 | (49,15,64) |
| 4 | (5,3) | 8 | (34,15,49) |
| 6 | (5,3) | 8 | (931,510,1441) |
| 3 | (1,2) | 1 | (7,2,9) |
| 3 | (18,1) | 1 | (343,18,361) |

これらを含む16個のLean例を所有モジュール内に置いた。
非原始座標では正規化後にもgcdが4残る例、零座標でB=0となる例も含む。
343=7³の例を保持しており、完全冪の排除は主張していない。

## 検証・依存・残る境界

- 対象3モジュールのビルド：2796 jobs、成功、警告0。
- 新規29宣言と既存39宣言、計68宣言の型照会・公理監査：成功。
  許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
- 既存39宣言の所有3ファイルは本文を変更していない。
- 新定理・定義の教科書docstring、昇格マーカー、ファイルマーカー、禁止構文不在を確認。
- DkMathの依存閉包がLib内に留まること、元資料24ファイルのSHA256を確認。
- Lib集約入口とREADMEへの登録は静的確認。ユーザー指定によりフルビルド・DkMathTest・lake testは実行していない。

この三項は正の原始的な加法関係であり、ABC予想のradical評価ではない。
FLT反例状態の保存や厳密降下、hnoの非存在証明も供給していない。
偶数D_nの精密gcdは005cに残す。先に必要なLTE・素数住所の中立化を扱うGN-LIB-006へ進む。

[宣言・型・依存・ハッシュ](evidence/gn-lib-005b.json) と
[検証記録](evidence/validation-gn-lib-005b.txt) に証跡を記録した。
