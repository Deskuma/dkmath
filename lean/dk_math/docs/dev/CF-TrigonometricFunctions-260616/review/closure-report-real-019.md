# Closure Reports: Step No.019

DkMath.Analysis.DkReal

うむ、ここは一旦キャンプを張ってよい。
わっちの判定では、`DkMath.Analysis.DkReal` は **構想段階を抜けて、最初の演算閉性を持つ計算可能実数近似体系** まで来た。

数学用語でまとめると、ここまでの成果はこうじゃ。

## 1. 代数恒等式から解析核を作った

中心に置いたのは、冪差分の厳密分解じゃ。

$$
(base+\delta)^d-base^d=\delta,gapGN_d(base,\delta)
$$

これは Taylor 近似ではなく、有限多項式恒等式じゃ。
数学用語では、`gapGN` は **冪写像の有限差分商をゼロ増分まで延長した差分核** と呼べる。

$$
gapGN_d(base,\delta)
$$

は、\(\delta\ne0\) では通常の差分商と一致し、\(\delta=0\) では微分係数に接続する。

$$
gapGN_d(base,0)=d,base^{d-1}
$$

つまり、ここで得たものは **代数的差分核から微分係数への橋** じゃ。

## 2. Residual と Drift を分離した

単位宇宙式について、

$$
cosmicGap(x,u)=(x+u)^2-x(x+2u)
$$

を定義し、

$$
cosmicGap(x,u)=u^2
$$

を示した。

そこから、

$$
cosmicResidual(x,u)=cosmicGap(x,u)-u^2
$$

と、

$$
cosmicDrift(x,y,u)=cosmicResidual(x,u)-cosmicResidual(y,u)
$$

を分けた。

数学的にはこれは、 **絶対残差** と **二点差分残差** の分離じゃ。
重要なのは、二点 drift が 0 でも、共通 bias は検出できないという点じゃな。

これは観測理論で言えば、

```text
絶対誤差:
  基準値からのズレ

二点 drift:
  観測点間の相対ズレ
```

を分けたことになる。

## 3. GapFill と区間写像を作った

二点 \(u_1,u_2\) の間を affine scan で埋めた。

$$
gapLine(u_1,u_2,t)=u_1+t(u_2-u_1)
$$

そして、

$$
gapFill_d(u_1,u_2,t)=gapLine(u_1,u_2,t)^d
$$

を定義した。

数学的には、これは **区間の連続的パラメータ化** と **冪写像による区間像** じゃ。

非負順序区間では、

$$
t\in[0,1]\quad\Rightarrow\quad gapFill_d(u_1,u_2,t)\in[u_1^d,u_2^d]
$$

が出た。
これは標準実数上では **単調連続写像による区間保存** に相当する。

## 4. TaylorBridge で差分商と微分へ接続した

`TaylorBridge` では、`gapGN` が差分商の穴埋めであることを示した。

$$
\frac{(base+\delta)^d-base^d}{\delta}=gapGN_d(base,\delta)\quad(\delta\ne0)
$$

さらに \(\delta\to0\) で、

$$
gapGN_d(base,\delta)\to d,base^{d-1}
$$

を得て、`HasDerivAt` へ接続した。

数学用語では、これは **穿孔近傍での差分商極限** から **Fréchet ではなく一変数実微分** への接続じゃ。

大事なのは、微分から `gapGN` を定義したのではないこと。
順序は逆じゃ。

```text
有限代数恒等式
→ 差分核
→ 差分商
→ 極限
→ 微分
```

ここが DkMath.Analysis の特徴じゃな。

## 5. DkReal を入れ子有理区間列として定義した

`DkReal` は、標準実数 \(\mathbb{R}\) の点そのものではなく、有理閉区間列として定義した。

$$
I_n=[a_n,b_n]
$$

条件は三つ。

```text
各 Iₙ は有理閉区間
Iₙ₊₁ ⊆ Iₙ
width(Iₙ) → 0
```

数学用語では、これは **入れ子区間列による計算可能実数表現** じゃ。
Dedekind 切断よりも、計算可能解析に近い構成じゃな。

標準実数への評価写像はまだ作っていない。
つまり、これはまだ **意味論的実数** ではなく、 **構文的・計算可能近似実数** と言うべき段階じゃ。

## 6. 非負 DkReal の自然数冪写像を構成した

ここが今回の一区切りじゃ。

非負 `DkReal` について、各区間を

$$
[a_n,b_n]\mapsto[a_n^d,b_n^d]
$$

で写した。

非負性により、冪写像 \(x\mapsto x^d\) は単調なので、入れ子性が保たれる。

問題は幅収束だった。

新しい幅は、

$$
b_n^d-a_n^d=(b_n-a_n),gapGN_d(a_n,b_n-a_n)
$$

ここで、

$$
w_n=b_n-a_n\to0
$$

は `DkReal` の定義からある。
残るのは \(gapGN_d(a_n,w_n)\) の有界性。

今回 `PowBound` で、非負入れ子区間列では、

$$
gapGN_d(a_n,w_n)\le gapGN_d(b_0,b_0)
$$

を示した。
よって (gapGN) 因子は一様有界。

したがって、

$$
w_n,gapGN_d(a_n,w_n)\to0
$$

が成立し、冪写像後の区間列も `DkReal` になる。

数学用語では、これは **非負計算可能実数近似が自然数冪で閉じることの構成的証明** じゃ。

## 7. ここまでの到達点を一文で言うなら

$$
\boxed{\text{DkReal の非負部分は、自然数冪写像に対して閉じる。}}
$$

より詳しく言えば、

$$
\boxed{\text{入れ子有理区間列として表された非負計算可能実数に対し、冪写像は GN による幅制御で再び入れ子有理区間列を返す。}}
$$

これじゃ。

## 8. 数学的な分類

ここまでの成果を既存数学の言葉へ翻訳すると、こうなる。

| DkMath 用語    | 数学用語                |
| ------------ | ------------------- |
| Gap          | 基準値、端点、保存される出力      |
| Body         | 差分区間、冪差分、区間像の幅      |
| GN           | 有限差分核、割差核、差分商の連続延長  |
| GapFill      | 区間パラメータ化、連続補間       |
| DkReal       | 入れ子有理区間列による計算可能実数表現 |
| powNonneg    | 非負区間上の単調写像による冪演算    |
| PowBound     | 有限多項式核の一様有界性証明      |
| TaylorBridge | 差分商極限と微分の接続         |

特に `gapGN` は、数学的には **divided difference kernel** と言ってよい。
ただし DkMath では、それを単なる解析補助ではなく、Gap と Body をつなぐ中核として扱っている。

## 9. まだ未完の山

ここでキャンプを張るなら、未完の山も見えるようにしておくべきじゃ。

まだ閉じていないのは主にこれ。

```text
DkReal の加算
DkReal の乗算
DkReal の順序
DkReal の同値関係または extensional equality
DkReal → ℝ の意味論評価
powNonneg の ofRat 簡約
負区間や一般区間での冪写像
```

いま閉じたのは、 **非負領域の自然数冪** じゃ。
しかしこれは、後続の乗算・多項式評価・連続関数近似へ進むための大きな足場になる。

## 10. キャンプ地点の名前

わっちなら、この到達点をこう呼ぶ。

$$
\boxed{\text{DkReal 非負冪閉包キャンプ}}
$$

または論文風なら、

$$
\boxed{\text{Constructive closure of nonnegative nested rational intervals under natural powers via a finite difference kernel}}
$$

日本語では、

$$
\boxed{\text{有限差分核による非負入れ子有理区間実数の自然数冪閉包}}
$$

じゃな。

うむ、良いキャンプ地じゃ。
背後には代数恒等式、足元には有理区間、前方には加算・乗算・意味論写像の山稜が見えておる。ここで火を焚き、りんごでも齧りながら地図を広げるには、ちょうどよい場所じゃ。
