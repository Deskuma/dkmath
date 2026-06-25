# review

うむ、S2-U 確認したぞ。
これはとてもよい「シメ」の入り方じゃ。いま必要だったのは新しい補題ではなく、**何が閉じて、何がまだ開いているか** を明文化することだった。`RouteMap.md` はその役割をきちんと果たしておる。

## 1. 状況分析

今回の `RouteMap.md` で、Chapter 2 の到達点が明確になった。

閉じた範囲は、

$$
d=3
$$

の ordinary primitive branch、つまり

$$
q\ne3
$$

の枝じゃ。標準入口は `CubicPrimitiveFLTContext` とされ、その context が primitive witness、(b<a)、coprime 条件、FLT-shaped equation、(y\ne0)、(q\ne3) を束ねることが明記された。

そして、この context に GN 側 fuel として

$$
v_q(GN(3,a-b,b))\le1
$$

または

$$
Squarefree(|GN(3,a-b,b)|)
$$

を渡せば `False` へ進む、という到達点も文書化された。

つまり、研究上の言い方としては、

> (d=3) ordinary primitive branch の no-sorry 抽象反駁エンジンは閉じた

が正確じゃ。

## 2. 「征した」の範囲

前の問いに続けて言えば、ピタゴラス宇宙式は **(d=3) の通常枝を征した** と言ってよい。

ただし `RouteMap.md` にも明記された通り、まだ

1. exceptional branch (q=3)
2. GN 側 valuation / squarefree fuel の自動供給

は残っておる。

ゆえに、いま言える最強の主張はこれじゃ。

$$
\text{Pythagorean Gap/Beam}
\Rightarrow
\text{cubic PowerBeam}
\Rightarrow
\text{ordinary primitive branch contradiction engine}
$$

これは no-sorry で接続済み。

一方で、

$$
\text{FLT } d=3 \text{ 全体の完全反駁}
$$

とはまだ言わない。
この切り分けはとても健全じゃ。

## 3. Route Map の価値

今回の文書で特に良いのは、層が表で整理された点じゃ。`PowerGapBeam.lean` は代数層、`PowerGapBeamGN.lean` は GN bridge、`PowerGapBeamGcd.lean` は gcd / valuation contradiction、`PowerGapBeamPrimitive.lean` は primitive-prime bridge、そして `CubicPrimitiveFLTContext` が bundled ordinary cubic context として整理されている。

これは後で再開するときに効く。
数日後、あるいは数か月後に見ても、

```text
PrimitiveBeam -> GN -> PowerBeam -> gcd / p-adic valuation -> contradiction
```

という道筋が追える。

こういう route map は、Lean 開発では単なる文書ではない。
**定理探索の地図** じゃ。

## 4. 次の 6 回の締め段取り

S2-U で route map が入ったので、残りはこう進めるのがよい。

### S2-V. Open tasks 文書化

`RouteMap.md` にすでに open tasks はあるが、次は `OpenProblems.md` か History の章末に、次章送りをもう少し整理する。

* (q=3) exceptional branch
* GN fuel 自動供給
* 一般次数 bridge
* d=4 route
* `CosmicFormula.All` 分離案

このあたりを「次章候補」として並べる。

### S2-W. import / warning 境界の最終確認

`PowerGapBeamGN` では warning が流入せず、`PowerGapBeamPrimitive` 側だけに既存 `sorry` warning が出る、という状態は理想に近い。
これを History に最終確認として固定する。

### S2-X. Smoke checks

`#check` か小さな examples file で、標準入口を確認する。

```lean
#check DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext.val_le_one_contradiction
#check DkMath.CosmicFormula.PowerGapBeam.CubicPrimitiveFLTContext.squarefree_contradiction
```

重いなら文書だけでもよい。

### S2-Y. Chapter 2 summary 草稿

ここで最終まとめ文を作る。
「何をしたか」「何をしていないか」を明記する。

### S2-Z. Chapter 2 closure

History に最終節を追加して閉じる。
ここで開発ブランチとしては一旦収穫じゃ。

## 5. 現時点の評価

S2-U は成功じゃ。

Chapter 2 はもう、次のようにまとめられる。

> ピタゴラス宇宙式の Gap/Beam 視点を高次差冪へ拡張し、(d=3) ordinary primitive branch (q\ne3) について、PrimitiveBeam → GN → PowerBeam → p-adic valuation contradiction までを no-sorry で接続した。

これは十分に成果じゃ。
あとは S2-Z まで、収穫物を乾かし、束ね、蔵にしまう段階じゃな。
