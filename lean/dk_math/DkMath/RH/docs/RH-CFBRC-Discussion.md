# RH-CFBRC Discussion

> 👩‍⚕️私D.:

ちょっと FLT 離れて CFBRC から RH への道筋を歩もうかと思ってるのだが。
オイラーゼータ関数

<https://github.com/Deskuma/dkmath/tree/nightly/lean/dk_math/DkMath/RH>

少し触りを入れただけだが #HOPC-RH 構造を明確化していこうかと。
ここで何か FLT や ABC予想、コラッツ予想関連のヒントが得られるかもしれないかなあ。とか。

気分もリフレッシュで。

GN 構造の本質探り的な寄り道のような本筋ルート。

> 🐺賢狼:

よし、それは良い寄り道じゃ。FLT の戦場からいったん離れて、`CFBRC → RH` の骨格を先に立てるのは、逃避ではなく **本質の抽出作業** じゃよ。いまから GitHub 側の `DkMath/RH` と手元スナップショットの両方を見て、`#HOPC-RH` をどう育てると他予想への橋になるかを整理する。

> 🐺賢狼:

方向性はかなり良いぞ。いま見えている `RH` 側は、もう単なる思いつき置き場ではなく、**位相ドリフト骨格 → EulerZeta magnitude 収束 → phase 接続待ち** という三段構えになっておる。ここを明確化すると、`GN` の「局所因子の挙動を見る目」が別の形で洗練されるはずじゃ。

> 🐺賢狼:

## 1. . それ、かなり良い手じゃ

わっちは **賛成** じゃ。
これは FLT からの逃避ではなく、むしろ **`GN` の本質を別の光で炙り出す本筋寄りの寄り道** じゃよ。

いまの `RH` ディレクトリは、すでに

- 位相ドリフト骨格
- EulerZeta の magnitude / phase 分離
- magnitude 側の \(\sigma > 1\) における無限積収束と正値

まで意図が明確に書かれておる。README でも、「ゼータへ差し込む前段として、位相速度を Lean で扱う骨格を作り、その骨格上で EulerZeta の無限積を収束・正値まで固める」と整理されておるし、位相は `arg` 直打ちではなく積分によるアンラップで扱う方針だと明記されておる。

## 2. . なぜ CFBRC から RH へ行くのが筋が良いのか

理由は、両者とも **素数ごとの局所因子を見て、全体を組み立てる学問の顔** をしておるからじゃ。

`CFBRC` 側は README で、

\[
(x+u)^d-u^d = x \cdot \mathrm{core}_d(x,u)
\]

を核にして、

- 代数恒等式層
- 円分多項式層
- 数論層

を橋渡しする実装だと明言しておる。しかも `cyclotomicPrimeCore` と `GN` の同一化、除法判定、`padicValNat`、primitive prime existence までを視野に入れておる。

一方 `RH` 側は、`vertical`, `torque`, `phaseVel`, `phaseUnwrap` を導入し、EulerZeta を

\[
\zeta_e(s)=\prod_p \frac{p^s}{p^s-1}
\]

の位相つき再編として置き、その magnitude 版

\[
a_p(\sigma,t)=\frac{e^{\sigma \log p}}{\left\|e^{(\sigma+it)\log p}-1\right\|}
\]

の無限積を formalize しておる。さらに README では、\(\sigma>1\) で `Multipliable` と \(0<eulerZetaMag\) を確定したと書いてある。

つまり両者とも、乱暴に言えば

\[
\text{局所素数因子} \;\to\; \text{全体構造}
\]

の型をしておる。
ここが同じ匂いなのじゃ。なかなか旨い匂いじゃろ。

## 3. . どこが「本質の共通核」になりそうか

わっちの見立てでは、共通核は **幾何級数骨格** じゃ。

`GN` は差冪の商としての有限幾何和じゃな。

\[
GN(d,x,u)=\sum_{k=0}^{d-1}(x+u)^{d-1-k}u^k
\]

一方、Euler 因子は収束域で無限幾何和を持つ。

\[
\frac{1}{1-p^{-s}}=\sum_{n\ge 0} p^{-ns}
\]

この二つは、有限か無限かの違いはあれど、どちらも **「1 個の核から反復構造を起こす」** という顔をしておる。
CFBRC ではそれが差冪・円分・valuation に現れ、RH ではそれが局所位相・局所振幅・全体位相に現れる。

なので、`CFBRC → RH` の橋は

\[
\text{差冪の有限幾何和}
\longleftrightarrow
\text{Euler 因子の無限幾何和}
\]

として見るのが一番自然じゃ。
ここは論文の大看板にしやすい。

## 4. . ただし、ここで酔ってはいかぬ点

ここは冷酒でいこう。

いまの `RH` 実装は README の言葉どおり **前段骨格** じゃ。
位相ドリフト骨格はできており、EulerZeta も magnitude 版の収束までは固まっている。だが phase 側は「`arg` を直接使わずアンラップへ接続する予定」と書かれておるので、**まだ #HOPC-RH の核心は入口に立った段階** と見るのが正確じゃ。

ゆえに、ここからすぐ

\[
\text{RH} \Rightarrow \text{FLT/ABC/Collatz の鍵}
\]

と言うのは、ちと酒が回りすぎじゃ。
正しくは、

\[
\text{RH 側で prime-local phase の観測装置を作る}
\]

その結果として、

- FLT / ABC には **prime-local obstruction の見え方**
- Collatz には **離散写像の位相的再符号化のヒント**

が出る **かもしれぬ** 、くらいが誠実じゃな。

特に相性の良さで言えば、

\[
\text{FLT} \approx \text{ABC} \;>\; \text{Collatz}
\]

とわっちは見る。
Collatz は prime factor より **2 進的・離散写像的な癖** が強いので、直接の橋は少し遠い。

## 5. . いま進めるなら、#HOPC-RH はこう刻むのがよい

わっちなら、次の 4 段で刻む。

### 5.1. . 単一素数因子の位相力学を完成させる

まず \(p\) 固定で

\[
w_p(\sigma,t)=e^{(\sigma+it)\log p}-1
\]

を主役にする。
`phaseVel`, `torque`, `phaseUnwrap` をこの \(w_p\) に差し込み、

\[
\theta_p'(t)=\Im\!\left(\frac{w_p'(t)}{w_p(t)}\right)
\]

を Lean で一本化する。
いまの RH 骨格は、まさにここへ行くために作られておる。

### 5.2. . 有限 Euler 積で HOPC を作る

無限積へ飛ぶ前に、まず

\[
Z_N(s)=\prod_{p\le N}\frac{p^s}{p^s-1}
\]

で位相ドリフトを観測する。
有限積なら、局所因子の寄与を足し合わせる構図が明瞭じゃ。

ここで大事なのは、積を微分すると和になることじゃ。

\[
\frac{d}{dt}\log Z_N(\sigma+it)=
\sum_{p\le N}\frac{d}{dt}\log\!\left(\frac{p^s}{p^s-1}\right)
\]

この「積を和へほどく」視点は、CFBRC の `core` / `GN` / `valuation` の組立て感覚とも相性が良い。

### 5.3. . phase と magnitude の分業を明確化する

README にあるように、いま magnitude 側は \(\sigma>1\) で収束と正値まで押さえてある。なら next step は、

- magnitude は **安定性・収束性**
- phase は **零点検出・共鳴検出**

と役割分担を明確にすることじゃ。

この切り分けができると、#HOPC-RH は単なる「ゼータの別表現」ではなく、

\[
\text{安定な振幅} + \text{情報を運ぶ位相}
\]

という研究プログラムになる。これは強い。

### 5.4. . CFBRC と接続する「素数局所寄与 API」を作る

ここが一番おもしろいところじゃ。

`CFBRC` には既に

- core
- divisibility
- valuation
- primitive prime

の API がある。

`RH` 側にも、これに対応する抽象 API を作るのじゃ。たとえば概念的には、

- `PrimeLocalPhaseKernel`
- `PrimeLocalMagKernel`
- `PrimeScaleResonance`
- `PrimeContributionSum`

のようなものじゃな。

そうすると CFBRC 側の

\[
\text{prime divides / lifts / primitive}
\]

という言葉と、RH 側の

\[
\text{prime rotates / resonates / cancels}
\]

という言葉を、**同じ prime-local contribution language** で語れるようになる。
ここまで来ると、寄り道ではなく堂々たる本丸の別門じゃ。

## 6. . ぬしの問いへの、賢狼の答え

答えはこうじゃ。

\[
\boxed{
\text{CFBRC から RH へ進むのは、かなり筋が良い。}
}
\]

ただし目的は「いきなり RH を証明する」ことではなく、

\[
\boxed{
\text{GN 構造の本質を、prime-local phase / magnitude の言葉で再定式化すること}
}
\]

じゃ。

その副産物として、

- FLT には **primitive prime の“新規寄与” の見え方**
- ABC には **radical と局所増幅の見え方**
- Collatz には **離散写像の位相的圧縮表現のヒント**

が出る可能性はある。
だが、最も見込みが高いのはまず FLT と ABC じゃな。

要するに、これは気分転換の顔をした **研究の地盤改良** じゃよ。
実に良い酒の抜き方じゃ。

次にやるなら、わっちは
**`#HOPC-RH` の 1 枚設計図 `RH/docs/HOPC-RH-Roadmap.md` の素案** を起こして、`single-prime → finite Euler product → unwrap phase → zeta insertion` の 4 段を明文化するのを勧める。

## Appendix

### HOPC-RH

see: [HOPC-RH](HOPC-RH.txt)

> HOPC-RH = Holo Orthogonal Phase–Curvature method
> 日本語では「偏角直交・停留・曲率法」と呼ぶ。
>
> このタグの意味は、ゼータや Euler 因子の prime-local な寄与を、
> 単なる複素数評価ではなく
>
> - 位相速度
> - 位相の停留
> - 曲率
> - 局所寄与の干渉
> - それらの総和としての零点候補

> という観点で整理する方法論である。

### Implementation Bridge (RH-H1/H2)

CFBRC 側から RH 側を参照する際の、現行公開 API の最短導線:

- 定義:
  - `hopcPrimeLocalContribution`
  - `hopcPrimeContributionSum`
  - file: `DkMath/RH/EulerZeta.lean`
- 同一化補題:
  - `eulerZetaFactorPhaseVelFinite_eq_hopcPrimeContributionSum`
  - file: `DkMath/RH/EulerZetaLemmas.lean`
- 停留判定:
  - `driftFreeAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `stationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum_eq_zero`
  - `nondegenerateStationaryAt_eulerZetaFinite_onVertical_iff_hopcPrimeContributionSum`
  - file: `DkMath/RH/EulerZetaLemmas.lean`

対応する読み順:

1. `hopcPrimeLocalContribution` / `hopcPrimeContributionSum`（観測量名）
2. `...eq_hopcPrimeContributionSum`（既存位相速度和との同一化）
3. `driftFreeAt` / `stationaryAt` / `nondegenerateStationaryAt` の同値補題

これで CFBRC 側の「prime-local contribution language」から、
RH 側の停留・曲率 API へ直接接続できる。
