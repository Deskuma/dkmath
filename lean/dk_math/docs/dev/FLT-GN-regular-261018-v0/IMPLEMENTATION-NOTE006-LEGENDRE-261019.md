# NOTE-006 §3: Legendre 中央席と Frey c₄ の接続

2026-10-19。今回の対象は [NOTE-006 §3](NOTE-006.md#3-今回見つかったlegendre-研究との接点) のみ。
公開モジュールは `DkMath.NumberTheory.Legendre.FreyC4CentralSeat`。
既存の `DkMath.NumberTheory.Legendre` と通常の `DkMath` import からも到達できる。
IRR-007、Frey の局所最小性・乗法的還元・ガロア表現の実装は今回の対象に含めない。

## 1. 同じ中央席を三つの対象で読む

自然数 n に対し、

\[
Q_n=n^2+n+1=n^2+(n+1)=n(n+1)+1
\]

を `centralSeat n` と定義した。n>0 なら既存の `SquareOffset n (n+1)` と
`SquareCell n (centralSeat n)` が成立する。n=0 の Q₀=1 は区間の上端である。

次に、実際の整数 Weierstrass 曲線を

\[
E_n:y^2=x(x-n)(x+1),\qquad [0,1-n,0,-n,0]
\]

とする。NOTE-005 の `FreyGapCubic.naive` に A=n,B=1 を代入して構成し、
既存の不変量の定理から

\[
\boxed{c_4(E_n)=16Q_n},\qquad
\boxed{\Delta(E_n)=16n^2(n+1)^2}
\]

を得た。

有理数上の正規化曲線 Wₙ には

\[
\boxed{c_4(W_n)=Q_n},\qquad
\Delta(W_n)=\frac{(n(n+1))^2}{256}
\]

が成立する。`rationalCurve_eq_change` は、Eₙ をℚへ写したものに
実際の許容変換 `(u,r,s,t)=(2,0,1,0)` を適用すると Wₙ になることを証明する。
二つの異なるモデルの c₄ を16倍の補正なしに同一視していない。

n>0 なら Wₙ はℚ上で `IsElliptic` を満たす。一方、この正規化モデルを
既存の整数モデルへ降ろせる分母条件は

\[
\operatorname{IntegralNormalization}(n,1)\iff16\mid n
\]

である。`integralNormalization_iff` でこの同値を証明し、条件成立時の
整数モデルについても c₄=Qₙ を証明した。任意の n の Wₙ を整係数とはしていない。

## 2. 素因子は判別式を割らない

Qₙ=n(n+1)+1 より、

\[
\boxed{\gcd(Q_n,n(n+1))=1}.
\]

また n(n+1) は偶数なので Qₙ は奇数である。
したがって素数 q が Qₙ を割るなら、q≠2、q∤n、q∤n+1 となり、

\[
\boxed{q\mid c_4(E_n)},\qquad\boxed{q\nmid\Delta(E_n)}
\]

を得る。NOTE の奇素数という条件は Qₙ の奇数性から内部で供給できる。
q=3 もこの判別式の非可除性については例外ではない。

`reduction_isElliptic` は、実際に Eₙ を `ZMod q` へ写した曲線について
`IsElliptic` を証明する。同じ曲線の c₄ は `reduction_c4_eq_zero` により0となる。
**c₄=0 と曲線の特異性は同じ条件ではない。** ここでは判別式が非零なので非特異である。

これは特定の整係数モデルの非特異な還元を述べる結果であり、最小性・導手や
楕円曲線のガロア表現を構成する結果ではない。

## 3. q≠3 の素因子は1 mod 3

q∣Qₙ を `ZMod q` に写すと、t=n mod q は

\[
t^2+t+1=0
\]

を満たす。恒等式 `(t−1)(t²+t+1)=t³−1` より t³=1。
t=1 なら3=0、従って q∣3 となるので、素数 q≠3 の場合には t≠1。
このため t の乗法位数が正確に3となる。

Mathlib の有限体の位数定理 `ZMod.orderOf_dvd_card_sub_one` を使うと、

\[
3\mid q-1,\qquad \boxed{q\equiv1\pmod3}
\]

が従う。公開した分類は

\[
q\text{ prime},\ q\mid Q_n\Longrightarrow q=3\ \lor\ q\bmod3=1
\]

であり、NOTE の q>3 の前提による `Nat.ModEq` 版も用意した。
素因子の存在や Qₙ 自身の素数性は結論していない。

## 4. 既存の Legendre 支持への入口

`mem_primeSupport_iff` により、

\[
q\in\operatorname{squareOffsetPrimeSupport}(n,n+1)
\iff q\text{ prime}\land q\le n\land q\mid Q_n
\]

を得る。`prime_bridge_of_mem_support` は同じ q≤n を保持したまま、
c₄ の可除性・判別式の非可除性・合同類の分類を取り出す。

例えば Q₄=21 の素因子3は旧支持に入るが、素因子7は上界4を越えるので入らない。
Qₙ の全素因子と平方殻の旧支持を混同しない。支持上の制約から、平方殻の
全被覆の排除や Legendre 予想の証明へ進んだとはしていない。

## 5. 回帰例と監査

- Q₃=13: 素数の中央席と二つの c₄ の倍率。
- Q₄=21: 合成数でも q=7 に対する全ての条件付き接続が成立。
- Q₁₈=7³: 平方自由性を仮定せず、同じ7が判別式を割らない。
- q=3,n=1: 判別式は割らないが n mod 3 の位数は1。q≠3 の条件の必要性を確認。
- n=0: 中央席の区間内所属と有理曲線の非特異性には n>0 が必要。
- n=1 と n=16: 正規化モデルの整係数条件の不成立／成立。
- `ZMod 7` の実際の曲線: 非特異性と c₄=0 が同時に成立。

各追加 Lean ファイルは import 直後に要求された `#print "file: モジュール名"` を持つ。
統合ビルド `lake build DkMath DkMath.NumberTheory.Legendre DkMathTest` は
**11,496 jobs** で成功した。公開宣言29件の公理監査と主要6経路の実依存監査が通過し、
標準の `propext`、`Classical.choice`、`Quot.sound` 以外の公理は検出していない。
通常入口の smoke と `DkMathTest.lean` の直接検査も通過した。
新規コードの警告はなく、トラッカーは 2,292 組について不一致なしであった。

ソース・回帰・公理と実依存・入口・マーカーの検証結果は
[evidence/validation-note006-legendre.txt](evidence/validation-note006-legendre.txt) に記録した。
