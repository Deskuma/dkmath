# DkMath CF2D 研究資料 — 回転不変量・鏡映・角度二分割から π を構成する

**文書の位置付け**: 研究の数学的背景・既存実装との対応・検証すべき命題をまとめた資料。Lean の定理が既に完成したという報告ではない。  
**対象リポジトリ**: https://github.com/Deskuma/dkmath  
**対象ディレクトリ**: `lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/`  
**目的**: `Real.pi` を前提としない **内在的定数** `intrinsicPi` を、CF2D の保存量と回転核の二分割から構成し、最後の独立した橋渡し定理で Mathlib の `Real.pi` と一致することを証明する。

## 1. この研究が始まった背景

古代エジプトの円面積近似 `(8d/9)^2` の「円を正方格子で近似する」発想から、GeoGebra で正方形と円、45°の対角線、鏡映による対称性を作図した。次に90°→45°→22.5°→11.25°…と角度を二分し、対称性によって全円を復元する方法に注目した。

仮説の中核は以下。

1. 先に存在するのは円周率ではなく、二成分状態と二乗和の保存、鏡映・回転合成という **代数構造**。
2. 保存量 `q2(x,y)=x²+y²` の等値集合は、実数・ユークリッド距離の解釈の下で **円** になる。
3. 90°回転をその平方根で45°、22.5°…へ細分化できる。各段階の点は厳密に同じ `q2=1` を満たす。
4. 細分化して得られる内接正多角形の面積または周長の極限を、新たな実数定数として定義する。この定数を **最終段階でのみ** `Real.pi` と接続する。

**注意**: `π` は「保存量 q2 そのもの」ではない。πは、ユークリッド計量（長さ・面積）を持つ実数平面で、回転軌道の正規化された周長・面積を測ったときに現れる定数である。群の対称性だけからその数値は決まらない。

## 2. 既存 DkMath に存在する足場

確認した公開 `main` の実装（改修前に Codex が再読すること）。

- [`CF2D/Basic.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Basic.lean): `Vec`, `Vec.q2`, `Vec.star`, `Vec.q2_star`, `Vec.conj`, `Vec.q2_conj`, `UnitKernel`, `UnitKernel.q2_act`, `LevelSet`。純代数的に `q2(star r z)=q2(r)q2(z)`。
- [`CF2D/Trig.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Trig.lean): `KernelFamily`、座標関数 `C/S`、加法・倍角・偶奇性。三角関数を定義に使わない抽象層。
- [`CF2D/CFSinCos.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CFSinCos.lean): 抽象 `cfcos/cfsin`。
- [`CF2D/KernelPower.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/KernelPower.lean): `UnitKernel` の `CommGroup` と冪・反復作用。
- [`CF2D/CycleDivision.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean): 抽象周期分割と有限軌道。後半の実数正規化ブリッジでは既に `Real.pi` が登場するので、内在的構成からの依存に注意。
- [`CF2D/RegularOrbit.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/RegularOrbit.lean): 保存量を保つ有限軌道。多角形の辺・面積は未定義。
- [`CF2D/Topology.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Topology.lean): 座標からの積位相と連続性。
- [`DkReal/SemanticCF2DNormalize.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean): 4区間の連続閉路、正規化による `q2` 保存。**閉路であることと、単位円をちょうど一周することは別**（全射性・巻き数等の検証は別途必要）。
- [`CF2D/EuclideanPhase.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean): `LevelSet ℝ` と円方程式・距離球面との同相的解釈。標準角度を `Real.pi / 2` などで読んでいる。ここは **既存 π への比較側** に用いる。
- [`CF2D/EuclideanRegularOrbit.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanRegularOrbit.lean): 正多角形の頂点に相当する等角離散軌道・ユークリッド回転対応。標準角度 `2 * Real.pi / k` を使用。

ルート [`CF2D.lean`](https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D.lean) は上記の主要モジュールを束ねる。

## 3. 完全に π を使わない代数的構成

### 3.1 単位核

`u=(c,s)` とし、CF2D の乗法を

\[
(c,s)\star(x,y)=(cx-sy,\;cy+sx)
\]

とする。`q2(u)=c²+s²=1` の第一象限部分（`0≤c`, `0≤s`）に限定する。

初期核を `u₀=(0,1)` とする。これは、幾何的には四分の一回転に対応するが、**定義には角度を使わない**。

### 3.2 代数的半回転

各 `uₙ=(cₙ,sₙ)` に対し

\[
\begin{aligned}
c_{n+1}&=\sqrt{\frac{1+c_n}{2}},\\
s_{n+1}&=\sqrt{\frac{1-c_n}{2}}
\end{aligned}
\]

と定義する（非負の平方根を選ぶ）。次が証明目標。

\[
q2(u_n)=1,\qquad u_{n+1}\star u_{n+1}=u_n.
\]

また `0≤cₙ≤1`、`0≤sₙ≤1`、各有限段階で `sₙ>0`、`cₙ ↑ 1`、`sₙ ↓ 0` を証明する。幾何学的解釈は90°、45°、22.5°、11.25°…であるが、πは定義に入れない。

### 3.3 π-free 正多角形面積・半周長の数列

`Nₙ=4⋅2ⁿ` に対応する単位円内接正多角形の面積の **代数的候補** を

\[
A_n=2^{n+1}s_n
\]

と定義する。幾何的な面積としての解釈は、後のブリッジで証明する。

同じ多角形の周長の半分の **代数的候補** は

\[
P_n=2^{n+1}\sqrt{2-2c_n}.
\]

ここで二分角公式から

\[
s_{n+1}=\frac{\sqrt{2-2c_n}}{2}
\]

なので、厳密に

\[
\boxed{P_n=A_{n+1}}
\]

が成立する。**今の実装計画で最も重要な接続定理の一つ。** 「内接多角形の半周長」と「次段階の内接多角形の面積」が一致する。

初期値: `A₀=2`、`A₁=2√2`、`P₀=2√2`。これらはπ-freeに証明できる。

さらに

\[
A_n=c_{n+1}A_{n+1}
\]

であり、`0<cₙ₊₁≤1` なので `Aₙ` の単調非減少が得られる。面積候補の上界（例えば4）を **πに依存しない方法で** 証明し、極限の存在を確立すること。

上界の候補: 接線から構成した外接正多角形の代数的面積候補

\[
U_n=\frac{A_{n+1}}{c_{n+1}}
\]

を使い、`Aₙ≤Uₙ≤U₀=4`、必要なら `Uₙ` の単調減少を示す。これも最初は三角関数を使わず、平方根と単位核の恒等式で扱えるかを検証する。容易でなければ別の純代数的な有界性証明でもよい。

### 3.4 内在的定数

`Aₙ` が単調有界と証明できれば、次の定義ができる。

\[
\boxed{\Pi_{\mathrm{CF2D}}=\sup\{A_n\mid n\in\mathbb N\}}
\]

この定義の依存関係には `Real.pi` / `Real.sin` / `Real.cos` を **入れない**。数学的には `sSup (Set.range areaApprox)` が候補。

**注意**: 数式としての独立した定義と、数学史上の新規公式であることは別。これは既知の多角形近似を、CF2D の保存量から独立に実装する研究。

## 4. `Real.pi` と接続するのは最後の橋渡しだけ

新規の bridge モジュールに限り標準実解析を使う。正の実数 `π` について、まず

\[
c_n=\cos\!\left(\frac{\pi}{2^{n+1}}\right),\qquad
s_n=\sin\!\left(\frac{\pi}{2^{n+1}}\right)
\]

を示す（初期値と半角公式・第一象限の符号条件によって帰納）。すると

\[
A_n=2^{n+1}\sin\!\left(\frac{\pi}{2^{n+1}}\right)
=\pi\cdot\frac{\sin x_n}{x_n},
\qquad x_n=\frac{\pi}{2^{n+1}}\to0.
\]

標準定理 `sin x / x → 1` から

\[
\boxed{\lim_{n\to\infty}A_n=\mathrm{Real.pi}}
\]

が従い、先に定義した `Π_CF2D` と同一だと証明する。`Real.pi` の使用は **このブリッジだけ** に局所化する。Mathlib の既存定理名・仕様を実際に確認すること。証明を循環させないこと。

## 5. 位相的に何が言えるか

- 抽象 `q2` の等値集合は、係数環が一般の可換環ならば「円」とは限らない。
- `R=ℝ` とし通常の距離・位相を導入すると、`q2=ρ²` は半径 `ρ` の円を表す。
- 有限の規則的な軌道は **円上の有限点集合** であり、それだけでは円周全体にならない。
- 角度二分割の点集合（全レベルの合併）は、適切な証明により単位円上で稠密になる。この主張は **第二段階のトポロジー課題** として、周長極限の構成とは分ける。
- 連続閉路が存在するだけでは全射性・巻き数1は保証されない。必要なら明示的に証明する。
- 「πは連続不変量」という表現は、証明資料では「ユークリッド計量に基づく正規化周長／面積の極限定数」とする。

## 6. 数値確認（証明ではない）

|    n | 内接正多角形 |       `A_n` | `P_n=A_{n+1}` |
| ---: | -----------: | ----------: | ------------: |
|    0 |        4角形 | 2.000000000 |   2.828427125 |
|    1 |        8角形 | 2.828427125 |   3.061467459 |
|    2 |       16角形 | 3.061467459 |   3.121445152 |
|    3 |       32角形 | 3.121445152 |   3.136548491 |
|    4 |       64角形 | 3.136548491 |   3.140331157 |

浮動小数点による `sqrt(2-2cₙ)` は `cₙ→1` の際に桁落ちする。実装の数学的定義は維持しつつ、数値検証では `Pₙ=Aₙ₊₁` を使うか任意精度・安定な弦長反復を使う。

## 7. 判定基準

- **既証明**: `q2` の保存、鏡映、反復の群構造、離散軌道、連続正規化経路、ユークリッド解釈。
- **今回の実装目標**: 正の半回転核、反復列、面積と半周長の恒等式、π-free の極限定義。
- **最終目標**: `intrinsicPi = Real.pi` の bridge 定理。
- **追加研究**: 二分角で得た軌道の稠密性、既存閉路の全射性／巻き数、GeoGebra の正方形・円交点を CF2D の代数と結ぶ定理。

これらの段階を混同せず、成立した定理と未解決の補題を明示的に分けること。
