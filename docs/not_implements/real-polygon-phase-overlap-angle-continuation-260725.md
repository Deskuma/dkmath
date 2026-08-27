# 実数正多角位相・重なり偏角・連続化観測

## Status

この文書は 2026-07-25 時点の観測事実と研究仮説を固定する。

実装はまだ行わない。厳密な Lean 実装設計は次を参照する。

[Real Polygon Phase Overlap and Continuous Theta Implementation Plan](../../lean/dk_math/DkMath/Analysis/docs/real-polygon-phase-overlap-theta-implementation-plan-260725.md)

この観測は、単位円上の正多角形、対角線扇、Gauss-Wantzel 型有限軌道、CF2D の `q2` 保存作用、DkMath.Analysis の連続位相課題を一つの位相座標へまとめる試みである。

## 1. 出発点

古典的な正多角形では、頂点数は自然数である。

しかし DkMath の対象は、最初から多角形の見た目ではない。

中心にあるのは、二成分平方質量、単位核作用、有限または連続の位相進行である。

$$
q2(r \star z)=q2(r)\,q2(z)
$$

単位核なら `q2(r) = 1` なので、作用軌道は同じ `q2` 境界から出ない。

したがって正多角形は本体ではなく、保存軌道を特定の座標格子から観測した有限表示である。

## 2. 単位円と対角線扇の古典的観測

正 $n$ 角形の一頂点から、他の頂点へ辺と対角線を引く。

隣接する二本の放射線が作る角は、円周角の定理により等しい。

正 $n$ 角形の内角は $n-2$ 個の等しい区間へ分割される。

$$
\alpha_n=\frac{(n-2)\pi}{n}
$$

一区間の幅は次である。

$$
\delta_n=\frac{\pi}{n}
$$

したがって内角全体に対する一区間の比は次となる。

$$
\frac{\delta_n}{\alpha_n}=\frac{1}{n-2}
$$

正方形、正五角形、正六角形、正七角形では、それぞれ $1/2$、$1/3$、$1/4$、$1/5$ となる。

頂点で外接円の接線も加えると、半回転全体が $n$ 個の等しい区間へ分かれる。

$$
\pi=n\frac{\pi}{n}
$$

これは Euclidean geometry における表示結果であり、DkMath の内部では「半周期 Big の有限等分」と読む。

## 3. 角度を捨てた位相 Primitive

一周を $1$ に正規化する。

実数スケール $n>0$ に対する基本位相区画を次で表す。

$$
\operatorname{cellWidth}(n)=\frac{1}{n}
$$

局所区画の座標域は次である。

$$
\frac{[0,1)}{n}=\left[0,\frac{1}{n}\right)
$$

ここでは $n$ を頂点集合の濃度として先に解釈しない。

$n$ は、一周 Big を何単位分の位相進行で閉じるかを表す実数スケールである。

整数 $n$ を整数時刻で観測した場合に限り、標準 Euclidean geometry はその軌道を正 $n$ 角形の頂点として読む。

## 4. 実数 $n$ の整数部と重なり部

$n>0$ を次のように分解する。

$$
n=m+\alpha
$$

ここで $m$ は整数部、$\alpha$ は局所端数である。

$$
m=\lfloor n\rfloor
$$

$$
\alpha=n-\lfloor n\rfloor
$$

$$
0\leq\alpha<1
$$

Euclidean projection では、$m$ 個の完成した位相区画が分離した頂点として見える。

残る $\alpha$ は独立した一頂点ではなく、基準頂点周囲の重なり部として見えると予想する。

この読みは現時点では幾何表示仮説である。

一方、重なり幅そのものは正確に定義できる。

$$
\operatorname{overlapWidth}(n)=\frac{\alpha}{n}
$$

実際に占有される局所重なり区間は次である。

$$
\operatorname{OverlapCell}(n)=\left[0,\frac{\alpha}{n}\right)
$$

## 5. Closing Overlap 恒等式

完成した $m$ 区画の総幅は次である。

$$
\operatorname{completeWidth}(n)=\frac{m}{n}
$$

これに重なり幅を加える。

$$
\frac{m}{n}+\frac{\alpha}{n}=\frac{m+\alpha}{n}=1
$$

したがって端数は余りではない。

端数は、一周 Big を過不足なく閉じる Closing Overlap である。

DkMath 語彙では次のように読む。

| 層 | 内容 |
|---|---|
| Big | 正規化一周期 $1$ |
| Core | $m$ 個の完成区画 |
| Gap | 次の一区画内にある局所端数 $\alpha$ |
| Closing overlap | 円周へ射影された幅 $\alpha/n$ |
| Body | 完成区画と Closing overlap の総和 |

ここでは Gap は欠損ではなく、Big を閉じるために必要な未繰上げ位相である。

## 6. $n=4.7$ の観測モデル

$$
n=4.7
$$

$$
m=4
$$

$$
\alpha=0.7
$$

基本区画幅は次である。

$$
\frac{1}{4.7}
$$

四つの完成区画と重なり幅は次の恒等式を満たす。

$$
\frac{4}{4.7}+\frac{0.7}{4.7}=1
$$

標準座標では四つの完成頂点と、一つの頂点周囲へ重なる $0.7$ 区画として見えると予想する。

座標系を一緒に動かせば、重なり位置は別の頂点周囲へ移る。

保存されるのは場所ではなく幅 $0.7/4.7$ である。

## 7. 繰上げと連続性

局所端数 $\alpha$ が $1$ に達すると、一つの完成区画へ繰り上がる。

$$
(m,1)\sim(m+1,0)
$$

生の fractional-part 関数だけを見ると整数境界で $1$ から $0$ へ飛ぶ。

しかし完成区画数と局所端数を組にし、上の同値関係で継ぐと、総位相状態は連続に読める。

したがって連続化で重要なのは、単独の $\alpha$ ではなく carry seam を持つ局所座標系である。

これは複数の座標 chart による円周観測に近い。

## 8. DkMath の偏角情報

DkMath の偏角を、最初から度数法やラジアンで定義しない。

基本となるのは正規化位相である。

時刻 $t$ における一周期座標を次とする。

$$
\operatorname{phase}(n,t)=\frac{t}{n}\pmod 1
$$

特に実数スケール $n$ 自身が持つ局所端数の円周射影は次である。

$$
\operatorname{overlapArg}(n)=\frac{n-\lfloor n\rfloor}{n}
$$

この値は区間 $[0,1/n)$ に入る。

$$
\operatorname{overlapArg}(n)\in\left[0,\frac{1}{n}\right)
$$

これが今回の観測で得た DkMath 偏角情報の最小候補である。

Euclidean angle は最後に正規化位相を読む外部射影として導入する。

$$
\theta=2\pi\,\operatorname{phase}(n,t)
$$

`Real.pi` は DkMath 位相の生成元ではなく、Euclidean interpretation の尺度である。

## 9. 半周期と鏡写し

向きのない対角線方向では、正反対の二つのベクトルを同じ直線として読む。

$$
z\sim-z
$$

そのため方向 Big は一周 $1$ ではなく半周期 $1/2$ になる。

基本方向区画と重なり幅は次となる。

$$
\operatorname{directionCellWidth}(n)=\frac{1}{2n}
$$

$$
\operatorname{directionOverlapWidth}(n)=\frac{\alpha}{2n}
$$

Closing Overlap 恒等式は次である。

$$
\frac{m}{2n}+\frac{\alpha}{2n}=\frac{1}{2}
$$

半周期を越えた位相は新しい方向を作らず、符号反転した既存方向として帰還する。

これが $180^\circ$ で鏡写しになる Euclidean reading の pre-geometric 内容である。

## 10. `q2_star` による軌道表現

正規化周期核族を $K$ とし、加法パラメータを star 積へ移す。

$$
K(a+b)=K(a)\star K(b)
$$

完成区画核と重なり核を次で表す。

$$
R_n=K\left(\frac{1}{n}\right)
$$

$$
G_n=K\left(\frac{\alpha}{n}\right)
$$

Closing Overlap 恒等式は核積へ移る。

$$
R_n^m\star G_n=K(1)
$$

周期 $1$ の核が中立核なら次となる。

$$
R_n^m\star G_n=1
$$

この $G_n$ は誤差補正ではなく、一周を閉じる非自明な位相核である。

## 11. 座標系が動くこと

位相状態を次とする。

$$
P_n(t;z)=K\left(\frac{t}{n}\right)\star z
$$

同時に逆方向へ動く観測座標を次とする。

$$
C_{n,t}(w)=K\left(-\frac{t}{n}\right)\star w
$$

すると状態は移動座標内で静止する。

$$
C_{n,t}(P_n(t;z))=z
$$

固定座標で見える頂点、重なり、回転は観測結果である。

不変な本体は位相作用、`q2` 保存、Closing Overlap 幅である。

## 12. 既存 DkMath 実装との接続

現在の関連実装は次にある。

| 役割 | 場所 |
|---|---|
| 四相 affine transition と `q2` depth | [`SemanticCF2DPhase.lean`](../../lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhase.lean) |
| 位相中心と座標 shift | [`SemanticCF2DPhaseShift.lean`](../../lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DPhaseShift.lean) |
| 連続位相課題 | [`task-trig-continuous-phase-065.md`](../../lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md) |
| 三角関数仕様 | [`trigonometric-spec-103.md`](../../lean/dk_math/DkMath/Analysis/docs/trigonometric-spec-103.md) |
| 抽象 cycle division | [`CycleDivision.lean`](../../lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/CycleDivision.lean) |
| 有限 regular orbit | [`RegularOrbit.lean`](../../lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/RegularOrbit.lean) |
| Euclidean regular orbit | [`EuclideanRegularOrbit.lean`](../../lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanRegularOrbit.lean) |
| Gauss-Wantzel 公開入口 | [`EuclideanGeometry.lean`](../../lean/dk_math/DkMath/EuclideanGeometry.lean) |

現在の `CycleDivision.lean` は自然数 $k$ による有限 return を持つ。

今回の観測は、その下にある位相パラメータを実数スケール $n>0$ へ解放し、自然数 regular orbit を整数標本として回収する設計を与える。

## 13. Gauss-Wantzel 定理との関係

現在の `DkMath.EuclideanGeometry` は次を分離している。

1. `IsGaussWantzelIndex` による算術条件。
2. `regularKernel k` による exact finite orbit。
3. Euclidean plane における等間隔回転の読み。
4. `QuadraticExpr` による代数的二次構成可能性。

現在不足している主要 bridge は次である。

1. Gauss-Wantzel index から `regularKernel k` の二座標が quadratic expression で得られること。
2. quadratic expression semantics と定規・コンパス作図の incidence geometry を結ぶこと。
3. 必要に応じた converse の素因子分類。

今回の Real Polygon Phase Overlap は、これらを直接証明しない。

しかし次の不足を埋める可能性がある。

1. 有限 regular orbit と連続位相座標の共通 parameter model。
2. 自然数 $k$ を実数 phase scale の整数標本として回収する theorem。
3. 辺、凸包、内角を前提にしない regular-orbit interpretation。
4. `theta` を正規化位相から Euclidean angle へ射影する明確な module boundary。
5. constructible finite samples と非構成可能または連続な semantic samples を同じ `q2` boundary API で扱う入口。

したがって、この観測は Gauss-Wantzel の arithmetic-to-constructibility gap そのものを解決するものではない。

一方で、現在の有限 regular orbit の外側に欠けていた「位相座標と連続化」の層を与え、Gauss-Wantzel 実装を DkMath.Analysis へ接続する役割を持つ。

## 14. 実装上の最重要 Guardrail

1. 実数 $n$ を literal な頂点集合の濃度として定義しない。
2. Euclidean vertex count は projection result として扱う。
3. 重なり位置と重なり幅を区別する。
4. 生の fractional part は整数境界で不連続なので、carry seam を明示する。
5. `Real.pi` を scalar phase core へ持ち込まない。
6. `normalizedRealKernelFamily` は最初の semantic realization として利用できるが、intrinsic DkMath kernel continuum と同一視しない。
7. この観測だけで完全な Gauss-Wantzel theorem を主張しない。

## 15. 研究結論

今回の中心式は次である。

$$
\lfloor n\rfloor\frac{1}{n}+\frac{n-\lfloor n\rfloor}{n}=1
$$

局所偏角領域は次である。

$$
\frac{[0,1)}{n}=\left[0,\frac{1}{n}\right)
$$

実際の重なり偏角は次である。

$$
\operatorname{overlapArg}(n)=\frac{n-\lfloor n\rfloor}{n}
$$

正多角形とは、整数個の頂点を先に持つ形ではない。

DkMath では、実数周期スケールを持つ `q2` 保存位相体を、整数格子から観測した有限像として読む。

整数部は完成区画として頂点へ射影され、小数部は一つの局所区画内の重なり偏角として射影される。

その端数が $1$ に達したとき、carry seam を越えて次の完成頂点へ昇格する。

これを連続位相の Primitive として固定する。