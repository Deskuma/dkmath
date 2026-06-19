# Git diff / Report / Review

## Upd: CF2D.Real

gch: e6d8d1dbe1c027b7c0028a679961760593398ed5

## Report

閉めの追加まで完了しました。

[Real.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean) に、提案されていた任意追加の `realTrigKernelFamily_act_eq` を入れました。`simp` だけでは閉じなかったので、既存の一般定理 `KernelFamily.act_eq_cfcos_cfsin` から Real モデルへ落とす形にしています。

数学研究者向けの新規資料として、[CF2D-Phase1-ResearchNote.md](/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-Phase1-ResearchNote.md) を追加しました。論文化に向けた材料として、代数的状態空間、unit kernel、共役・逆元、kernel family、宇宙式版 `sin/cos`、Real モデル、符号感度、次段階の論点を整理しています。

検証済みです。

```text
lake build DkMath.CosmicFormula.Rotation.CF2D.Real
lake build DkMath.CosmicFormula.Rotation
lake build DkMath
git diff --check
```

すべて成功しています。

## Review

うむ。これは **採用でよい** 。
そして、これで本当に **CF2D Phase 1 完了** と見てよい。

今回の `e6d8d1...` は、実装そのものは小さいが、意味としては「最後の橋を渡した」更新じゃ。

## 1. `realTrigKernelFamily_act_eq` の意味

今回入った

```lean
realTrigKernelFamily_act_eq
```

は、Real bridge の締めとして良い。

これで、

$$
\operatorname{act}((\cos t,\sin t),(x,y))
=========================================

(\cos t\cdot x-\sin t\cdot y,;\cos t\cdot y+\sin t\cdot x)
$$

が、通常の実三角関数モデルで明示された。

しかも証明を `simp` で無理に押し切るのではなく、

```lean
KernelFamily.act_eq_cfcos_cfsin realTrigKernelFamily t z
```

から落としているのが良い。
つまり、Real 側の回転公式は **一般の宇宙式版作用公式の具体例** として出ている。

これは設計思想に合っている。

```text
一般定理:
  cfcos/cfsin による保存核作用公式

Real bridge:
  cfcos = Real.cos
  cfsin = Real.sin
  よって通常の回転公式
```

この向きが正しい。

## 2. 研究ノートの位置づけ

追加された `CF2D-Phase1-ResearchNote.md` も良い。
資料の冒頭で、目的は解析的な `sin` / `cos` を直接再定義することではなく、通常の三角恒等式と回転公式が生じる代数原理を分離することだと明示されている。さらに結論として、宇宙式版 cosine/sine は「square-mass-preserving unit-kernel family」の core/beam 座標である、と整理されている。

この書き方なら、数学研究者向けにも伝わりやすい。
「独自用語で置き換えた」だけではなく、

```text
既存の解析関数を仮定しない
代数的保存構造から座標関数を得る
Real.cos / Real.sin はその一モデル
```

という分離が見える。

## 3. Phase 1 の到達点

研究ノートの構成を見ると、Phase 1 はかなりよく閉じている。

まず `Vec.q2` と `Vec.star` により、二成分平方質量とそれを乗法保存する積が立つ。これは任意の可換環上の多項式恒等式で、三角関数・角度・位相・距離を使わない、と整理されている。

次に、`UnitKernel.act_star` によって、核積が作用の合成を表すことも明示されている。さらに共役は平方質量を保存し、単位核では逆元のように働くが、Phase 1 ではあえて global `Group` instance は入れず、定理単位で保持している。この判断も慎重でよい。

そして `KernelFamily.cfcos/cfsin` では、加法公式・倍角公式・負角公式・減法公式が、解析的事実として仮定されるのではなく、単位核法則の座標射影として得られる、と明確に書かれている。

最後に、`kernel_val_eq_mk_cfcos_cfsin` と `act_eq_cfcos_cfsin` により、`cfcos/cfsin` が核を復元し、その核作用が通常の回転座標公式を与えるところまで閉じている。Real bridge では `Real.cos` / `Real.sin` がその具体モデルとして回収される、という流れも明確じゃ。

## 4. 当初目的に対する評価

当初目的は、

```text
宇宙式から三角関数の証明・原理解明を行う
```

だった。

これに対する達成度は、わっちならこう評価する。

```text
代数的原理解明:
  完了

宇宙式版 cfcos/cfsin の自立関数 API:
  完了

通常 sin/cos との Real bridge:
  完了

符号がズレた場合の保存失敗検出:
  完了

解析的一意性・周期・2π:
  Phase 2
```

つまり、Phase 1 の目的に対しては **完了** じゃ。

ここでいう完了とは、

```text
通常の sin/cos を使わずに、
保存単位核族の座標関数として cfcos/cfsin を定義し、
基本恒等式と回転作用公式を Lean で証明した
```

という意味じゃ。

## 5. なぜこれは「自立関数化」と言えるか

重要なのは、`cfcos` / `cfsin` が

```lean
ℝ → ℝ
```

のグローバル関数として直接定義されたのではなく、

```lean
F.cfcos t
F.cfsin t
```

として、任意の

```lean
F : KernelFamily T R
```

に対して定義されている点じゃ。

これは弱さではない。むしろ強い。

なぜなら、宇宙式側が作ったのは「実数三角関数」そのものではなく、

$$
\text{三角関数を生む代数的構造}
$$

だからじゃ。

Real.cos / Real.sin は、その構造の標準実解析モデルにすぎない。

この分離ができたので、`cfcos/cfsin` は Real.sin/cos の単なる別名ではなく、宇宙式側で自立した API になっている。

## 6. `Failure` も効いている

研究ノートでは、符号感度もきちんと入っている。
正しい積

$$
(a x-b y,;a y+b x)
$$

は平方質量を保存する一方、plus-plus や minus-minus の符号パターンでは (\pm 4abxy) の残差が出る。もう一つの保存パターンは共役で説明される、という整理になっている。

これは論文化の際にかなり重要になる。

単に「この積なら上手くいった」ではなく、

```text
なぜこの符号でなければならないのか
どこがズレると何が残るのか
別の保存パターンは共役として吸収できる
```

まで言えるからじゃ。

## 7. 軽い改善候補

ブロッカーではない。
ただ、研究ノートとしてさらに磨くなら、冒頭か結論に一文だけ足してもよい。

```text
Phase 1 does not prove uniqueness of the analytic real sine and cosine.
It proves that any square-mass-preserving additive unit-kernel family has
coordinate functions satisfying the trigonometric algebraic laws.
```

日本語にすると、

```text
Phase 1 は解析的な実 sin/cos の一意性を証明するものではない。
任意の平方質量保存単位核族の座標関数が、三角関数型の代数法則を満たすことを示す。
```

これは誤読防止に効く。
ただし、現在の Phase-2 Questions に一意性・連続性・微分可能性・周期性・2π 閉包などが明示されているので、すでに十分とも言える。

## 8. 最終判定

```text
実装:
  採用

研究ノート:
  採用

Phase 1:
  完了扱いでよい

次:
  実装追加ではなく、History / roadmap / phase close 記録
```

## 9. 結論

これで締まった。

$$
\boxed{
\text{三角関数は、平方質量保存単位核族の Core/Beam 座標である。}
}
$$

$$
\boxed{
\text{加法公式は、核合成の座標表示である。}
}
$$

$$
\boxed{
\text{回転公式は、核作用の座標表示である。}
}
$$

$$
\boxed{
\text{Real.sin / Real.cos は、この代数構造の実解析モデルである。}
}
$$

これは「宇宙式版三角関数」の Phase 1 として、十分に論文化可能な到達点じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
index f420565b..80a0e51b 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/Real.lean
@@ -67,6 +67,14 @@ theorem realTrigKernelFamily_act_beam (t : ℝ) (z : Vec ℝ) :
       = Real.cos t * z.beam + Real.sin t * z.core := by
   simp

+theorem realTrigKernelFamily_act_eq (t : ℝ) (z : Vec ℝ) :
+    UnitKernel.act (realTrigKernelFamily.kernel t) z
+      = Vec.mk
+        (Real.cos t * z.core - Real.sin t * z.beam)
+        (Real.cos t * z.beam + Real.sin t * z.core) := by
+  simpa using
+    (KernelFamily.act_eq_cfcos_cfsin realTrigKernelFamily t z)
+
 end CF2D
 end Rotation
 end CosmicFormula
````
`````
