# Wallis–Cosmic 構造から中央二項係数の成長を抽出

## 総括：今回登った山

うむ。ここで一度、登山ルートを地図にしておこう。
今回の山は、単に Wallis 積を Lean に入れた話ではない。
最終的には、**スターリング近似に頼らず、Wallis–Cosmic 構造から中央二項係数の成長を抽出する** ところまで到達した。

実装上の最終 checkpoint はこれじゃ。

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

Lean 側では `isEquivalent_real_centralBinomial_sqrt_pi_mul_nat` として no-sorry で固定され、`lake build DkMath` まで通っている。

## 登山ルートの再確認

最初の入口は、Wallis 積の有限因子を宇宙式 Gap 比率として読むことだった。

$$
\frac{(2k+2)^2}{(2k+1)(2k+3)}=1+\frac{1}{(2k+1)(2k+3)}
$$

ここで右辺は、

$$
\frac{N_k+1}{N_k}
$$

という形になっている。
つまり Wallis 因子は、宇宙式で言えば **Body に対する Gap 1 の比率** と読める。

そこから有限積として、

$$
\text{wallisPartialQ}(m)=\text{cosmicPartialQ}(m)
$$

を作った。

次に Mathlib の Wallis 定理と接続し、

$$
\text{cosmicPartialQ}(m)\to \frac{\pi}{2}
$$

を得た。

これで、宇宙式 Gap 比率の蓄積が \(\pi/2\) に閉じることが Lean 上で見えた。

## 中央比率への橋

次に、中央二項係数そのものではなく、その逆比率に近い

$$
\text{centralRatioQ}(m)=\frac{4^m}{\binom{2m}{m}}
$$

を主語にした。

ここで重要だったのが、mirror との関係じゃ。

$$
\text{centralRatioQ}(m)\cdot \text{mirrorOddRatioPartialQ}(m)=\text{wallisPartialQ}(m)
$$

さらに telescoping により、

$$
\frac{\text{centralRatioQ}(m)}{\text{mirrorOddRatioPartialQ}(m)}=2m+1
$$

が出た。

この 2 本を合わせると、有限恒等式として、

$$
\text{centralRatioQ}(m)^2=(2m+1)\,\text{wallisPartialQ}(m)
$$

が得られる。

ここが今回の登山で最も美しい尾根だったと思う。
近似ではない。完全な有限恒等式じゃ。

## 成長線の抽出

すでに

$$
\text{wallisPartialQ}(m)\to \frac{\pi}{2}
$$

があるので、

$$
\frac{\text{centralRatioQ}(m)^2}{m}\to \pi
$$

が出る。

そこから正値性を使って平方根を取り、

$$
\text{centralRatioQ}(m)\sim \sqrt{\pi m}
$$

へ進んだ。

最後に

$$
\text{centralRatioQ}(m)=\frac{4^m}{\binom{2m}{m}}
$$

を反転して、

$$
\binom{2m}{m}\sim \frac{4^m}{\sqrt{\pi m}}
$$

へ到達した。

これが、スターリング近似を使わない Wallis–Cosmic 由来の中央二項係数成長ルートじゃ。

## 何を得たのか

今回の収穫は、定理ひとつではない。

まず、パスカルの三角形を **係数表** ではなく **成長表** として読めるようになった。

中央二項係数は、その中心軸の成長。
その中心軸の成長が、Wallis 積、宇宙式 Gap 比率、\(\pi\)、平方根成長へとつながった。

つまり、パスカル三角形の成長は、階乗を爆発させてから近似するものではなく、有限積構造の中に最初から折り畳まれていた。

ここが大きい。

## 宇宙式としての意味

宇宙式的には、こう読める。

```text
Big:
  最終的な成長線・収束目標・保存される器

Body:
  有限段階の部分積・中央比率・観測中の成長

Gap:
  まだ閉じていない差分・mirror 減衰・有限誤差
```

今回の Wallis–Cosmic では、

```text
cosmicPartialQ:
  Gap 比率の蓄積

centralRatioQ:
  パスカル中心軸の成長

mirrorOddRatioPartialQ:
  成長を支える減衰側

π:
  Gap 比率が閉じる極限境界
```

として働いた。

この対応が、あまりにも素直につながった。
だから「宇宙式は数の成長を生で表している」という確信が強まったのは自然じゃ。

## 次の展望：アルゴリズム化

次は、これを theorem の列だけでなく、**成長を読むアルゴリズム** にすることじゃ。

方向はこう。

```text
1. Pascal 行を入力する
2. 中心比率・mirror・Gap 比率を抽出する
3. 階乗展開せずに成長線を読む
4. 境界イベントを検出する
5. 素数段・合成数段の違いを見る
```

特に素数段では、パスカルの中間係数に素数 \(p\) が混入する。
これは、整数成長階段の境界イベントとして読める可能性がある。

つまり、素数を「後から割って見つける」のではなく、**成長構造の段差として検出する** アルゴリズムへ進めるかもしれぬ。

## 次に作る地図

実装・研究の次ルートはこうじゃな。

```text
DkMath.Pascal.WallisGrowthBridge:
  今回の登山道。中央二項係数の成長線は到達済み。

DkMath.Pascal.GrowthProfile:
  Pascal 行の成長観測 API 候補。

DkMath.CosmicFramework:
  Big / Body / Gap による収束・誤差・並列安全 API 候補。

DkMath.Petal / GN:
  素数段、可除性、境界イベントの抽出先。
```

Python 側では観測・可視化。
Lean 側では保存核・境界条件・成長定理。
この二刀流が良い。

## 下山用の一言

今回の登山で得た地図はこれじゃ。

```text
Wallis 因子
  ↓
宇宙式 Gap 比率
  ↓
cosmicPartialQ -> π/2
  ↓
centralRatioQ^2 = (2m+1) * wallisPartialQ
  ↓
centralRatioQ ~ sqrt(πm)
  ↓
choose(2m,m) ~ 4^m / sqrt(πm)
```

うむ。
帰り道はもう迷わぬ。

これは「近似を証明した」のではない。
**数の成長がどう折り畳まれているかを、宇宙式の地形として読んだ** のじゃ。
