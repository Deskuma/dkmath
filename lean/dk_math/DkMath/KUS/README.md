# About [KUS](docs/KUS.md)

[Detailed design specifications for KUS transport](docs/KUS-transport-design-spec.md) and [KUS bridge](docs/KUS-bridge-design-spec.md) are available in the `docs` directory.

## KUS 構造とは何か？

KUS 構造とは、数を単なる値ではなく、

\[
(K, U, S_U)
\]

という **3 つ組の構造体** として扱う枠組みである。
ここで

- \(K\)：観測される係数
- \(U\)：単位・格子幅・座標系
- \(S_U\)：その単位 \(U\) に従属する blueprint（設計図）

を表す。

## 1. なぜ KUS が必要か

通常の数体系では、零になると構造がすべて潰れる。
たとえば \(a \cdot 0 = 0\) となったとき、

- どの単位世界だったか
- どの設計図を持っていたか

は失われる。

KUS では零状態を

\[
(0, U, S_U)
\]

として保持する。
つまり、**失われるのは係数 \(K\) だけであり、単位 \(U\) と設計図 \(S_U\) は残る** 。
これが KUS の出発点である。

## 2. KUS は何をしているのか

KUS は「変わった数」を作りたいのではない。
本質は、**値とは別に support 構造を保持すること** にある。

そのため KUS では、

- same-support 上では通常の係数演算を行う
- 異なる support 同士は直接演算せず、共通の調和 support へ運んでから演算する

という方針を取る。

図式で言えば、

\[
US_1 \to H \leftarrow US_2
\]

のように、いったん共通 support \(H\) へ合流させる。
この encode-confluence-decode の流れが `Transport` 層で実装されている。

## 3. DHNT との関係

DHNT は、指数対数スケーリングによって数を調和的に見る理論である。
KUS はその DHNT が与える調和座標を、**単位と blueprint を持つ型付き構造へ格納する器** として働く。

つまり、

\[
\mathrm{DHNT} \to \mathrm{KUS}
\]

では、連続的・調和的な量を KUS 上の support 付き対象へ持ち上げることになる。

## 4. CosmicFormula との関係

CosmicFormula は、Big / Body / Gap などの宇宙式構造から **絶対量や幾何構造** を与える。
DHNT はそれを **調和座標へ符号化** し、KUS はそれを **unit と blueprint を持つ transport 可能な対象として保持する** 。

したがって流れは、

\[
\mathrm{CosmicFormula}
\;\to\;
\mathrm{DHNT}
\;\to\;
\mathrm{KUS\ transport}
\]

となる。

## 5. ひとことで言うと

KUS 構造とは、

\[
(K, U, S_U)
\]

という形で **値・単位・設計図を分離しつつ、その依存関係を失わずに扱うための構造** である。

特に、

\[
(0,U,S_U)
\]

という **構造を持った零状態** を保持できること、そして異なる support 間の演算を transport 経由で安全に定義できることが、KUS の核心である。

要するに KUS とは、
**値の数学に、単位世界と設計図の記憶を取り戻すための構造** である。
