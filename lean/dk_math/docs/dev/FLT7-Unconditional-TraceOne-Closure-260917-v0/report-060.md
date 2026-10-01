# FLT7TC-005R54 — High-depth F5 packet and cyclic normalization

## 調査開始時点

`instruction-060.md`、R53 report、R53 production module、および R52 の
Eisenstein stripping API を確認した。今回の production 境界は、R53 の
`tauSq` packet から `T` を導入し、`F₅` の exact high-depth packet、linear-factor
primitive consequences、cyclic normalization、`q = 1 ↔ T = 0`、および `T = 0`
の有限 shell を kernel-check する範囲である。

外部 Thue 分類、有限 unbounded search、p-adic congruence からの整数等式化、
FLT3 terminal/descent、`C > 1` character work は production に導入しない。

## 実装進行

R54 用の調査・検証記録を作成した。R53 の重い coprimality module から切り離した
新規 production module に high-depth packet を追加する。

## 実装結果

新規 module `DkMath/FLT/Seven/SevenRealCubicHighDepthFive.lean` を追加し、
R53 の `EisensteinCurrentCubeSectorPacket` を `source` として保持する
`EisensteinCurrentHighDepthFivePacket` を定義した。packet の構成定理
`eisenstein_current_highDepthFivePacket_of_source` は、現行 packet の
`q > 0` を入力として、次を kernel-check する。

- `r = -1 + 8*T`、`s = 1 - 5*T`、`7^8 ∣ T`。
- `X = R^3 - 3*R*S^2 - S^3 = 1 - 5*T`、
  `Y = 3*R*S*(R+S) = -3*T`。
- `T = -R*S*(R+S)`、従って `7^8 ∣ R*S*(R+S)`。
- `F5(R,S) = R^3 - 5*R^2*S - 8*R*S^2 - S^3 = 1`。
- `q_norm : R^2 + R*S + S^2 = q` と
  `q^3 = 49*T^2 - 13*T + 1`。

同 module に、F5 からの三因子の pairwise coprimality、`7^8` の三分岐
(`R`、`S`、`R+S` のいずれか一つだけが深度を持つ)、
`sigma5(R,S)=(-R-S,R)` の order-three/invariant identities、deep-S の
factorization と gcd の `3` divisibility、mod-7 の cube-root branch、
`q=1 ↔ T=0`、`T=0` の三つの trivial shell、及び
`n5 = 5 + 49*R*S*(R+S)` の `7^10` arithmetic shadow を追加した。

`DkMath/FLT/Seven.lean` から新規 module を公開 import した。

## 検証結果

Lean は並列実行せず、次の順序で単体実行した。

1. `lake build DkMath.FLT.Seven.SevenRealCubicHighDepthFive`
   — `Build completed successfully (9209 jobs)`。
2. `lake build DkMath.FLT.Seven`
   — `Build completed successfully (9256 jobs)`。

新規 module は `sorry`、`admit`、`unsafe`、`native_decide` を使用していない。
禁止構文 scan は該当なし、`git diff --check` も問題なしだった。新規 report 自体も
`git diff --no-index --check /dev/null report-060.md` で whitespace 診断なしだった。

## 境界

この R54 実装は exact packet transport、有限 shell、cyclic normalization、
および arithmetic shadow までを扱う。外部 Thue 分類、Hensel lifting による
整数解の一意性、F5 の全非自明解の排除、FLT3 terminal/descent、及び
`C > 1` の closure は導入していない。

## Part I reconnaissance

既存の `SevenRealCubicInt` API は、`alpha`、整数埋め込み、積・norm・source
identity を提供するが、current R53 packet と `n5` の間の explicit
Tschirnhausen element、minimal-polynomial/field-isomorphism API は公開されて
いない。従ってこの checkpoint では外部の simplest-cubic field-isomorphism
定理を仮定せず、I の explicit polynomial theorem は production に追加しなかった。
これは R54 の exact arithmetic packet と独立した reconnaissance 結果である。
