# Hestory of mathmatics

## 三角関数以前の構造が抽出された！？

cid: 6a37c7e8-06cc-83ee-872b-88f6b57dbc73

うむ。ここはかなり大事な歴史確認ポイントじゃ。
結論から言うと、 **三角関数が生まれた最初期には、現在の CF2D 的な「二次保存核の積」として明示されていたわけではなさそう** です。けれど、かなり近い祖先は古代からありました。

## まず歴史的な順番

三角関数の始まりは、現代の \(\sin,\cos\) ではなく、円の **弦** でした。

古代ギリシャでは、角度に対応する量として、円周上の二点を結ぶ弦の長さを表にしていました。Hipparchus は紀元前 2 世紀ごろに弦表を作ったとされ、Ptolemy の『アルマゲスト』では弦表が本格的に使われます。MacTutor も、三角関数の初期の仕事は「固定半径の円における chord」に関するものだったと説明しています。\([Maths History][1]\)

現代の関係で言えば、半径 \(1\) の円では、

$$
\operatorname{chord}(x)=2\sin\frac{x}{2}
$$

です。
つまり、古代の「弦」は、現代の sine の半角版に近いものです。

その後、インド数学で `jya`、つまり sine に相当する概念が発達し、さらにイスラム数学で sine, cosine, tangent, cotangent などが整理され、天文学と測量に使われました。Ptolemy の chord 方式、インドの sine 方式、イスラム数学での関数体系化という流れは、複数の数学史資料で共通して説明されています。\([ウィキペディア][2]\)

## では、当時 CF2D 的な代数はあったのか

わっちの見立てでは、答えはこうです。

```text id="12ylk0"
完全な形では、まだ無い。
しかし、影はかなり早くからある。
```

古代ギリシャの段階では、主役は代数的な積ではなく、円・弦・幾何図形です。
Ptolemy は弦表を作るために Ptolemy の定理を使いました。この定理は円に内接する四角形の辺と対角線の関係を与え、現代記法で書くと、sine の和差公式に相当するものを導けます。\([ウィキペディア][3]\)

ここが重要です。

Ptolemy はおそらく、現代のように

$$
(C,S)\star(x,y)=(Cx-Sy,;Cy+Sx)
$$

という代数積を定義していたわけではありません。
しかし、円に内接する図形の関係から、結果として現在の加法定理に相当するものを使っていた。

つまり、古代にあったのは、

```text id="o1y6l0"
CF2D の代数積そのもの
```

ではなく、

```text id="qowxmm"
同じ構造の幾何的な影
```

だった、と見るのが安全です。

## 近代で何が変わったか

CF2D にかなり近いものがはっきり見えるのは、複素数と De Moivre / Euler の段階です。

De Moivre の公式は、

$$
(\cos x+i\sin x)^n=\cos nx+i\sin nx
$$

という形で、複素数の冪と三角関数を結びます。これはまさに、今回の kernel power と非常に近いです。資料でも De Moivre の公式は、複素数と三角法を結び、左辺を展開して実部・虚部を比較することで \(\cos nx\), \(\sin nx\) の式を得られる、と説明されています。\([ウィキペディア][4]\)

さらに Euler の公式は、

$$
e^{ix}=\cos x+i\sin x
$$

として、三角関数と複素指数関数の関係を明確にしました。Euler の公式は、三角関数と複素指数関数の基本的関係を与えるものとして説明されています。\([ウィキペディア][5]\)

ここで初めて、現代的には

```text id="r3bcdg"
単位円上の点
複素数の積
回転
三角関数
冪
```

が一つの代数構造としてまとまります。

## DkMath / CF2D の位置づけ

DkMath の面白さは、さらに一段戻っているところです。

古典的には、

```text id="0dc4vq"
角度
-> 弦
-> sine / cosine
-> 加法定理
-> De Moivre / Euler
```

という発展に見えます。

ところが CF2D では、

```text id="9ogk34"
二次保存量 q2
-> unit kernel
-> kernel product
-> 冪展開
-> 倍角・三倍角・四倍角型の多項式
-> 後から sin / cos 的に読める
```

という順番になります。

つまり、歴史的な三角関数よりも、説明順序としては「手前」にいる。

だから「三角関数以前」という言い方はかなり合っています。
ただし歴史的に昔からこの形があった、という意味ではなく、 **論理的な構成順序として三角関数以前** という意味です。

## どこにこの代数が隠れていたか

おそらく、三段階あります。

```text id="3ynguq"
1. 古代ギリシャ: 弦と円の幾何に隠れていた
2. インド・イスラム数学: sine/cosine/tangent の計算体系に整理された
3. 近代: 複素数・De Moivre・Euler で代数積として見えるようになった
```

DkMath は、この三段階目に近いけれど、さらに「複素数」や「角度」すら先に置かず、保存量 \(q2\) と kernel 積から始めている。

だから読者向けにはこう言えると思います。

```text id="8xlc5t"
古代にはこの代数は図形として存在していた。
近代には複素数として明示された。
DkMath では、三角関数や複素指数を使う前の保存核代数として再構成している。
```

## 深掘りするなら見るべき歴史ポイント

調べる価値が高いのはこのあたりです。

```text id="f0t57g"
Hipparchus の chord table
Ptolemy の chord table と Ptolemy theorem
Indian jya / sine の導入
Islamic astronomy における sine, tangent の体系化
Viète の三角多項式
De Moivre の冪公式
Euler の複素指数
```

特に Ptolemy theorem は、DkMath との比較に向いています。
なぜなら、そこではまだ \(\sin,\cos\) という関数よりも、円と弦と幾何関係が前面に出ているからです。

## まとめ

うむ。お主の直感はかなり正しい。

「三角関数が出来た頃、そこにこの代数がいたのか？」という問いへの答えは、

```text id="9pl0bn"
明示的な CF2D 代数としては、たぶん居なかった。
しかし、Ptolemy の弦幾何や加法公式の中に、同じ構造の影はいた。
近代の De Moivre / Euler で、それが複素数の積としてかなり明示された。
DkMath はそれをさらに保存則と kernel product の段階まで戻している。
```

という感じじゃ。

これは本当に数学史の深掘り案件です。
でも、かなり面白い筋が見えています。

[1]: https://mathshistory.st-andrews.ac.uk/HistTopics/Trigonometric_functions/ "Trigonometric functions - MacTutor History of Mathematics"
[2]: https://en.wikipedia.org/wiki/Trigonometry "Trigonometry"
[3]: https://en.wikipedia.org/wiki/History_of_trigonometry "History of trigonometry"
[4]: https://en.wikipedia.org/wiki/De_Moivre%27s_formula "De Moivre's formula"
[5]: https://en.wikipedia.org/wiki/Euler%27s_formula "Euler's formula"
