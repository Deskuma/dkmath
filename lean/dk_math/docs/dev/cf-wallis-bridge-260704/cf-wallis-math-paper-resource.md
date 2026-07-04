# 数学論文資料

## タイトル案

数学者向けなら、宇宙式語彙を避けて、次のあたりが興味を引きやすいと思う。

## 第一候補

**A Wallis-Product Derivation of the Central Binomial Asymptotic Without Stirling’s Formula**

日本語なら：

**スターリング公式を用いない Wallis 積による中央二項係数漸近公式の導出**

これは一番伝わりやすい。
数学者がすぐに「え、中央二項係数の漸近を Stirling なしで？」と反応しやすい。

## 少し強め

**Extracting Central Binomial Growth from a Finite Wallis Identity**

日本語：

**有限 Wallis 恒等式から中央二項係数の成長を抽出する**

今回の本質にかなり合う。
「近似」ではなく「有限恒等式から成長を読む」という主張が出る。

## 論文風

**A Finite Wallis Identity for the Central Binomial Coefficient and Its Asymptotic Consequence**

日本語：

**中央二項係数に対する有限 Wallis 恒等式とその漸近的帰結**

いちばん安全で数学論文っぽい。

## 推しタイトル

わっちなら、最初の投稿・解説記事にはこれを推す。

**A Finite Wallis Identity Behind the Central Binomial Coefficient**

副題：

**Deriving \(\binom{2m}{m}\sim 4^m/\sqrt{\pi m}\) without Stirling’s formula**

日本語なら：

**中央二項係数の背後にある有限 Wallis 恒等式**

副題：

**スターリング公式を使わずに \(\binom{2m}{m}\sim 4^m/\sqrt{\pi m}\) を導く**

## 数学的解説案

以下は、宇宙式語彙を避けた数学者向けの説明じゃ。
識別子風の文字列は \(\mathrm{...}\) で立てておく。

## 1. 中央比率の定義

中央二項係数そのものではなく、まず逆比率

$$
\mathrm{C}(m)=\frac{4^m}{\binom{2m}{m}}
$$

を考える。

目的は、スターリング公式を用いずに

$$
\mathrm{C}(m)\sim \sqrt{\pi m}
$$

を導き、そこから反転して

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

を得ることである。

## 2. Wallis 型の有限積

次に、有限 Wallis 積

$$
\mathrm{W}(m)=\prod_{k=0}^{m-1}\frac{(2k+2)^2}{(2k+1)(2k+3)}
$$

を置く。

古典的な Wallis 積より、

$$
\mathrm{W}(m)\to \frac{\pi}{2}
$$

である。

ここまでは標準的な対象だが、重要なのは \(\mathrm{W}(m)\) を中央比率 \(\mathrm{C}(m)\) と直接結ぶ有限恒等式である。

## 3. 鏡像積を導入する

補助的に

$$
\mathrm{M}(m)=\prod_{k=0}^{m-1}\frac{2k+2}{2k+3}
$$

を置く。

このとき、有限積の直接計算により

$$
\mathrm{C}(m)\mathrm{M}(m)=\mathrm{W}(m)
$$

が成り立つ。

また、同じく積の望遠的消去から

$$
\frac{\mathrm{C}(m)}{\mathrm{M}(m)}=2m+1
$$

が成り立つ。

この 2 つの有限恒等式を掛け合わせると、

$$
\mathrm{C}(m)^2=(2m+1)\mathrm{W}(m)
$$

を得る。

ここが中心である。
スターリング公式も階乗の漸近評価もまだ使っていない。必要なのは有限積の整理だけである。

## 4. 漸近評価

上の恒等式を \(m\) で割ると、

$$
\frac{\mathrm{C}(m)^2}{m}=\frac{2m+1}{m}\mathrm{W}(m)
$$

である。

右辺では

$$
\frac{2m+1}{m}\to 2
$$

かつ

$$
\mathrm{W}(m)\to \frac{\pi}{2}
$$

なので、

$$
\frac{\mathrm{C}(m)^2}{m}\to \pi
$$

を得る。

\(\mathrm{C}(m)>0\) であるから、平方根を取って

$$
\frac{\mathrm{C}(m)}{\sqrt{\pi m}}\to 1
$$

すなわち

$$
\mathrm{C}(m)\sim \sqrt{\pi m}
$$

となる。

最後に \(\mathrm{C}(m)=4^m/\binom{2m}{m}\) を反転すれば、

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

が従う。

## 何が面白いか

通常、この漸近公式はスターリング公式

$$
n!\sim \sqrt{2\pi n}\left(\frac{n}{e}\right)^n
$$

から得られる。

しかし上の導出では、階乗全体の漸近評価を経由しない。
中央二項係数に固有の比率 \(\mathrm{C}(m)\) を導入し、それを有限 Wallis 積 \(\mathrm{W}(m)\) に接続することで、成長率を直接抽出している。

Lean 形式化では、この流れは `centralRatioQ` の平方成長から中央二項係数の漸近形へ進む定理列として no-sorry で実装されており、最終的に `isEquivalent_real_centralBinomial_sqrt_pi_mul_nat` により \(\binom{2m}{m}\sim 4^m/\sqrt{\pi m}\) が固定されている。

## 数学者向けの短い要旨

より短く書くなら、こうじゃ。

中央比率 \(\mathrm{C}(m)=4^m/\binom{2m}{m}\) と有限 Wallis 積 \(\mathrm{W}(m)\) を考える。適切な補助積 \(\mathrm{M}(m)\) を導入すると、有限恒等式

$$
\mathrm{C}(m)\mathrm{M}(m)=\mathrm{W}(m)
$$

および

$$
\frac{\mathrm{C}(m)}{\mathrm{M}(m)}=2m+1
$$

が成り立つ。従って

$$
\mathrm{C}(m)^2=(2m+1)\mathrm{W}(m)
$$

である。Wallis の極限 \(\mathrm{W}(m)\to \pi/2\) より

$$
\frac{\mathrm{C}(m)^2}{m}\to \pi
$$

したがって

$$
\mathrm{C}(m)\sim \sqrt{\pi m}
$$

となる。これを \(\mathrm{C}(m)=4^m/\binom{2m}{m}\) に代入して反転すれば、

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

を得る。
この導出はスターリング公式を入力として用いず、有限 Wallis 恒等式から中央二項係数の成長を抽出する。

## この記事の売り文句

数学者向けに一言で刺すなら、こうじゃな。

**中央二項係数の漸近公式を、階乗のスターリング近似ではなく、有限 Wallis 恒等式から導く。**

あるいはもう少し強く：

**スターリング公式の背後に隠れて見えにくい中央二項係数固有の成長構造を、有限 Wallis 積として取り出す。**
