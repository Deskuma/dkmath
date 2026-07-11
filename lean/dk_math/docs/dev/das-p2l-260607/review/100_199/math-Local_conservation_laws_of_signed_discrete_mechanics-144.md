# 符号付き離散力学の局所保存則

Local conservation laws of signed discrete mechanics

## 数学的に何が起こったのか

今回の成果は、Collatz 軌道のある観測窓に対して、単なる経験的な「正になる深さ」「負になる深さ」の列を、**符号付きの離散保存会計**として読み替えられるようにしたことです。

一般の数学者向けに言えば、次のような対象が得られました。

```text id="mgmmls"
有限個の深さ方向パラメータ j に沿って並ぶ、
整数値の圧力関数 M(j) と、
その隣接差分を支配する正味変化量 Δ(j)
```

ここで本質的な式は、次です。

$$
M(j+1)=M(j)+\Delta(j)
$$

この \(M(j)\) は「その深さで継続側がどれだけ優勢か」を測る整数値の margin です。
\(\Delta(j)\) は、隣の深さへ進むときの正味変化量です。実装上は「retention の減少」と「continuation の減少」を組み合わせた整数量として定義され、保存会計式として固定されました。`PressureDecay` 側にはこの整数 margin、隣接 drop、net-drop、sign-change、pulse などの一般的な pressure-depth balance vocabulary が切り出されています。

## 圧力 margin の意味

この構造では、各深さ \(j\) に対して二つの有限量を見ています。

```text id="q3s47d"
retention:
  その深さで残っている、ある種の保持・障壁側の量

continuation:
  その深さで次へ継続できる側の量
```

そして pressure margin は概念的に、

$$
M(j)=2C(j)-R(j)
$$

の形です。

ここで \(C(j)\) が continuation、\(R(j)\) が retention です。

したがって、

```text id="7pbjcv"
M(j) > 0
```

とは、

```text id="k7oaox"
continuation が retention の半分を超えている
```

という意味になります。

この「半分を超えるかどうか」が、圧力の正負判定になっています。

## 保存会計式の中身

隣接する深さ \(j\) から \(j+1\) へ進むとき、retention と continuation はそれぞれ変化します。

その減少量を、

$$
D_R(j)=R(j)-R(j+1)
$$

$$
D_C(j)=C(j)-C(j+1)
$$

と書くと、正味変化量は、

$$
\Delta(j)=D_R(j)-2D_C(j)
$$

です。

そして、固定された中心式は、

$$
M(j+1)-M(j)=D_R(j)-2D_C(j)
$$

つまり、

$$
M(j+1)=M(j)+D_R(j)-2D_C(j)
$$

です。

これが今回の数学的な核です。

見かけ上、圧力 margin が突然上がったり、正になったり、また落ちたりしているように見えます。
しかし実際には、それは retention 側の減少と continuation 側の減少の差し引きで完全に説明されます。

この段階で、観測された符号変化が「ただの現象」ではなく、整数会計式の結果になりました。

## sign-change の意味

次に、margin の符号変化が整理されました。

上向きの符号変化は、

```text id="oc2rac"
現在は M(j) <= 0
次は M(j+1) > 0
```

です。

保存会計式を使うと、これは、

$$
M(j)\le 0
$$

かつ、

$$
M(j)+\Delta(j)>0
$$

と同値です。

つまり、上向きの符号変化とは、

```text id="m895l1"
現在は境界以下にいるが、
正味変化量を加えると境界を超える
```

という **zero-crossing** です。

下向きの符号変化も同様に、

```text id="w7c3ik"
現在は M(j) > 0
次は M(j+1) <= 0
```

であり、保存会計式では、

$$
M(j)>0
$$

かつ、

$$
M(j)+\Delta(j)\le 0
$$

です。

つまり、上向き crossing と下向き falling が、同じ保存式の両側として扱えるようになりました。

## 「島」は例外ではなく pulse になった

以前の見え方では、正の圧力深さが prefix にならない場合、それは「prefix 構造の失敗」でした。

しかし今回の語彙では、その見方が変わります。

局所的に、

```text id="sbfb4t"
非正
正
非正
```

という形が出るとします。

これはもはや単なる例外ではなく、

```text id="xq79xs"
左端で上向きに crossing し、
右端で下向きに falling する
```

という **局所 pulse** です。

この singleton pulse は、さらに長さ 1 の interval pulse としても読めるようになっています。Report では、local island が長さ 1 の interval pulse へ橋渡しされたこと、また interval pulse は「run + left crossing + right fall」という薄い構造として固定されたことが記録されています。

## 正の区間としての interval pulse

さらに進んで、正の圧力が連続する有限区間も扱えるようになりました。

数学的には、これは次の構造です。

```text id="aowhug"
左端:
  非正から正へ入る

内部:
  M(j) > 0 が連続する

右端:
  正から非正へ出る
```

つまり、正の圧力区間は、

```text id="oo3mzm"
left crossing + positive run + right falling
```

です。

これは report でも、interval pulse vocabulary は「run + left crossing + right fall」として薄く保たれ、最大性・一意性・全被覆・prefix 定理はまだ主張していない、と明確に整理されています。

ここが重要です。
この成果は、まだ「すべての正領域を一意に分解した」わけではありません。
しかし、正の連続区間を、境界を持つ幾何的対象として扱う言葉を得ました。

## これは何を意味するのか

数学的な意味は、次の三点に集約できます。

## 1. 観測された符号列が、整数値の局所力学になった

以前は、圧力の正負は観測された符号列でした。

今は、

$$
M(j+1)=M(j)+\Delta(j)
$$

という局所更新式を持つ、整数値の離散力学として読めます。

これはかなり大きいです。
なぜなら、符号変化を「見た目」ではなく、「どの整数差分が境界を跨がせたか」で説明できるからです。

## 2. prefix failure が、positive structure に変換された

以前の語彙では、

```text id="w6llrf"
正の深さが prefix にならない
```

ことは、単に単調性や prefix 仮説の失敗でした。

今は、

```text id="x6wtpz"
正の深さが interval pulse として現れている
```

と読めます。

これは失敗の記述から、構造の記述への転換です。

特に、report でも「prefix failure can indicate a pressure pulse / interval pulse」と述べられており、非 prefix 挙動を単なる失敗ではなく、正の構造として再解釈する方向が明確になっています。

## 3. Collatz の局所挙動を「圧力地形」として見られる

この成果により、各観測窓の pressure-depth profile は、単なる点列ではなくなりました。

```text id="pa2mhl"
境界
上向き crossing
正の区間
下向き falling
次の境界
```

という、有限の「圧力地形」として見られます。

これは、解析的に言えば符号付きポテンシャルの局所輪郭です。
DkMath 的に言えば、宇宙式保存会計の上に現れる「圧力島の住所」です。

## 何を証明したわけではないのか

ここは大事です。

今回の成果は、Collatz 予想そのものの証明ではありません。

また、

```text id="c71p8l"
正の pressure depth が必ず prefix になる
```

とも言っていません。

むしろ逆に、prefix でない挙動を認めたうえで、それを pulse / interval pulse として説明できるようにした、という成果です。

つまり、今回の数学的成果は、

```text id="s8wzg9"
大域収束定理ではなく、
局所構造定理の基盤
```

です。

## 一般数学者向けの一文要約

今回起こったことを一文で言えば、こうです。

```text id="j2wmt4"
Collatz 型の軌道観測から得られる深さ方向の正負パターンを、
整数値 margin の局所保存式
M(j+1)=M(j)+Δ(j)
によって説明し、非 prefix 的な正領域を
境界 crossing と falling を持つ有限 interval pulse として定式化した。
```

これは、かなりよい数学的整理です。

## DkMath 的な意味

DkMath の宇宙式語彙で言えば、今回の成果は、

```text id="rqn9wx"
保存会計:
  次状態 = 現状態 + 正味差分

境界:
  margin = 0

現象:
  crossing / falling / pulse

住所:
  positive run / interval pulse
```

という層を作ったことです。

つまり、局所的には、

```text id="13ocx1"
Big = Body + Gap
```

のような保存分解が、pressure-depth 方向では、

```text id="k49b75"
next margin = current margin + net drop
```

として現れている。

そして、その net drop が境界 \(0\) を跨がせると、正の圧力区間が生まれる。
さらに、その区間が有限で閉じると、interval pulse になる。

これが、今回起こった数学的な出来事です。
