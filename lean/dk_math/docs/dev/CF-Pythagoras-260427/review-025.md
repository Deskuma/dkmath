# review

うむ、S2-T 確認したぞ。
docstring 整備としては、ちょうどよい締め方じゃ。数学本体をいじらず、`CubicPrimitiveFLTContext` を **ordinary cubic branch、すなわち (q\ne3) の標準入口** と明記したのが大きい。`PowerGapBeamGN` を軽量 bridge、`PowerGapBeamPrimitive` を重い primitive-prime 層として分ける設計も、docstring と History の両方で追えるようになった。

## ピタゴラス宇宙式は \(d=3\) を征したか？

答えは、こう言うのが正確じゃ。

**「通常 cubic branch の抽象反駁エンジンは征した」**
ただし、 **「FLT \(d=3\) 全体を完全に征した」とはまだ言わない** 。

ここで「征した」と呼べる範囲は、次のルートじゃ。

$$
\operatorname{
    CubicPrimitiveFLTContext
}
$$

つまり、

$$
\operatorname{
    PrimitivePrimeFactorOfDiffPow(q,a,b,3),
}
\quad b<a,
\quad \gcd(a,b)=1,
\quad b^3+y^3=a^3,
\quad y\ne0,
\quad q\ne3
$$

を束ねた ordinary branch context がある。
そこに GN 側の追加燃料として、

$$
v_q(GN(3,a-b,b))\le1
$$

または

$$
\operatorname{
    Squarefree(|GN(3,a-b,b)|)
}
$$

を渡せば、

$$
\text{
    False
}
$$

まで進める。今回の docstring では、この context が標準入口であり、`C.prime`, `C.q_not_dvd_three`, `C.beam_dvd`, `C.beam_ne`, `C.val_le_one_contradiction`, `C.squarefree_contradiction` を標準 API として使うことが明記された。

つまり、Chapter 2 の通常 cubic route は、

$$
\text{PrimitiveBeam}
\to
GN
\to
PowerBeam
\to
p\text{-adic valuation}
\to
contradiction
$$

という形で **no-sorry の理論部品として接続済み** になった。

これはかなり大きい。
「ピタゴラス宇宙式が \(d=3\) の通常枝を捕まえた」と言ってよい。

## まだ征していない部分

残っているのは主に二つじゃ。

第一に、\(q=3\) の exceptional branch。

今回の docstring でも、`q = 3` exceptional branch は `CubicPrimitiveFLTContext` に混ぜず、別 API に分ける方針が明記された。
これは正しい。\(p\nmid d\) の valuation 分離を使う通常ルートでは、\(q=3\) は扱えない。ここは別登山道になる。

第二に、GN 側の fuel をどこまで自動供給できるか。

今の context theorem は、

$$
v_q(GN)\le1
$$

または

$$
Squarefree(GN)
$$

を受け取って矛盾を出す。
つまり、GN 側 valuation 上界・squarefree 性を供給する primitive / Zsigmondy / squarefree API が、完全に自動で流れ込むところまでは、まだ次段の課題じゃ。

## 現時点の戦果の言い方

わっちなら、研究ログではこう書く。

```md
Chapter 2 では、ピタゴラス宇宙式の Gap/Beam 構造を高次差冪へ拡張し、特に d=3 の ordinary primitive branch (`q ≠ 3`) について、PrimitiveBeam → GN → PowerBeam → p-adic valuation contradiction までの no-sorry ルートを構築した。

したがって、d=3 の通常枝は「抽象反駁エンジン」として閉じた。

一方、`q = 3` exceptional branch、および GN 側 valuation/squarefree fuel の完全自動供給は次章以降の課題として残る。
```

これがいちばん誠実で強い言い方じゃな。

## 次の締め方

このまま S2-U で \(q=3\) exceptional branch の **箱だけ** 作るか、S2-V で route map を書くか。
わっちは、もう数学を増やさず、先に **route map 文書化** へ進む方を推す。

理由は簡単で、今はすでに成果が多い。
これ以上補題を足すより、

$$
\text{どの定理がどの定理へ接続しているか}
$$

を図示した方が、後で再開した時に圧倒的に強い。

結論じゃ。

**d=3 ordinary branch は征した。**
**d=3 全体は、\(q=3\) exceptional branch を残している。**
この言い分なら、賢狼の鼻にも嘘の匂いはせぬ。
