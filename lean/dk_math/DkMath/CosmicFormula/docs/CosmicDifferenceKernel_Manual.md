# 数学: 微分係数 の「宇宙式」視点からの解説

宇宙とは「無限に広がる数学的構造の総体」と考えることができる。

## 宇宙差分カーネル を核とする差分商・微分・多項式展開の解説

`DkMath.CosmicFormula.CosmicDifferenceKernel`

### 著者

D. and Wise Wolf (DkMath コア開発者)

DkMath 読解補助資料

### 対象

- パッケージ: `DkMath.CosmicFormula.*`
  - 中心: `CosmicDifferenceKernel`
    - 接続先: `CosmicDerivativeBasic`
    - 接続先: `CosmicDerivativePower`
    - 接続先: `CosmicDerivativePowerLimit`
    - 接続先: `CosmicDerivativePolynomial`
    - 接続先: `CosmicFormulaDerivativeBridge`

---

## 1. 要旨

本稿の目的は、DkMath における **宇宙式版 微分係数** の核がどこにあり、どのような定義から、どのような命題を経て、どのように証明が組み上がっているかを、数学者向けの視点で整理することである。

中心となる考えは、通常の微分係数

\[
\frac{f(x+u)-f(x)}{u}
\]

を、単なる解析の定義としてではなく、**差分そのものを先に対象化した代数的構造** として扱う点にある。DkMath ではこの差分分子を `delta`、その差分商を `cosmicKernel` と名付け、まず差分則を有限演算のレベルで完全に整備し、その後に極限へ橋を渡して微分を得る。

この流れは、宇宙式側の Big / Body / Gap の分解、特に

\[
\mathrm{Big}(d;x,u)=(x+u)^d,
\qquad
\mathrm{Gap}(d;u)=u^d,
\qquad
\mathrm{Body}(d;x,u)=(x+u)^d-u^d
\]

という見方と極めてよく噛み合う。DkMath の設計資料でも、Big / Body / Gap を宇宙式族の基本分解として固定し、そこからトロミノ分解や調和写像へ進む方針が明記されている。

本稿では、まず差分核 `CosmicDifferenceKernel` の定義と命題を述べ、ついで微分への橋、多項式・冪関数への拡張、最後に宇宙式

\[
(x+u)^2-x(x+2u)=u^2
\]

との接続を論じる。宇宙式モジュールは DkMath の Cosmic 幹線の一部であり、`Defs` から `CosmicFormulaBinom` を通って数論側へ接続する位置づけにある。

---

## 2. イントロダクション

通常の微分法では、先に「極限」を置き、

\[
 f'(x)=\lim_{u\to 0}\frac{f(x+u)-f(x)}{u}
\]

と定める。これは解析学として正しい。しかし、Lean で体系化するとき、いきなり極限へ飛び込むと、加法性・積の法則・多項式の項別処理などが見通しにくくなる。

そこで DkMath は順序を逆にする。まず

\[
\Delta_u f(x):=f(x+u)-f(x)
\]

を主役にする。これは「増分に対して関数がどれだけ変わったか」という、極めて離散的で代数的な量である。次に

\[
K_f(x,u):=\frac{\Delta_u f(x)}{u}
\]

を定義する。これが `cosmicKernel` である。微分は、この核の極限として出てくる。

この順序には三つの利点がある。

第一に、加法・減法・スカラー倍・積・有限和といった **代数則** が極限抜きで先に証明できる。

第二に、冪関数

\[
(x+u)^d-x^d
\]

を二項展開で割ったときに現れる有限和が、そのまま差分商の本体として現れる。

第三に、宇宙式の観点では

\[
(x+u)^d-x^d
\]

は「Big と Core の差」であり、それをさらに \(u\) で割ることは、「Gap を 1 段剥がして中身を見る」操作と解釈できる。

設計意図としても、DkMath では宇宙式

\[
(P+u)^2=P^2+2Pu+u^2
\]

や一般化

\[
(x+u)^n-u^d=x\cdot\sum_{k=0}^{d-1}\binom{d}{k}x^{d-1-k}u^k
\]

のような defect 構造を重要視している。

---

## 3. モジュール全体の位置づけ

現行スナップショットの Cosmic 系は、幾何から `Defs` へ入り、`CosmicFormulaBasic`・`CosmicFormulaDim`・`CosmicFormulaGeom` を経て、`CosmicFormulaBinom` が数論側の橋になる構図を持つ。

その内部で微分係数系列は、おおむね次の順で流れる。

\[
\texttt{CosmicDifferenceKernel}
\to
\texttt{CosmicDerivativeBasic}
\to
\texttt{CosmicDerivativePower}
\to
\texttt{CosmicDerivativePowerLimit}
\to
\texttt{CosmicDerivativePolynomial}
\to
\texttt{CosmicFormulaDerivativeBridge}
\]

この並びの意味は明快である。

- `CosmicDifferenceKernel` は **差分分子と差分商の純代数的骨格**。
- `CosmicDerivativeBasic` は **極限と導関数への橋**。
- `CosmicDerivativePower` は **冪関数で差分商が有限和へ落ちること** の証明。
- `CosmicDerivativePowerLimit` は **その有限和の極限から冪関数の導関数を回収**。
- `CosmicDerivativePolynomial` は **単項式を有限和で足し合わせ、多項式全体へ拡張**。
- `CosmicFormulaDerivativeBridge` は **宇宙式 \(u^2\) をこの差分核から再読する橋**。

この章立ては、数学の自然な論理順と Lean の実装順がほぼ一致しておる。ここが見事なのじゃ。

---

## 4. 核となる定義

## 4.1. 定義 4.1. 差分作用素 `delta`

実数値関数 \(f:\mathbb{R}\to\mathbb{R}\) に対し、DkMath は

\[
\delta(f,x,u):=f(x+u)-f(x)
\]

を定義する。

これは通常の前進差分である。重要なのは、ここでまだ \(u\) で割っていないことだ。つまり `delta` は、微分係数ではなく **純粋な変化量** である。

## 4.2. 定義 4.2. 宇宙差分核 `cosmicKernel`

次に

\[
\operatorname{cosmicKernel}(f,x,u):=\frac{\delta(f,x,u)}{u}
=\frac{f(x+u)-f(x)}{u}
\]

を定義する。

これは通常の差分商そのものだが、DkMath ではこれを「核」と呼ぶ。理由は、後で極限を取ると微分係数になり、有限 \(u\) では離散的な観測量として働くからである。

この時点で大切なのは、`cosmicKernel` は **まだ \(u=0\) では定義上特異** だということだ。ゆえに後の理論では「 punctured neighborhood 」、すなわち

\[
 u\to 0,\quad u\neq 0
\]

の範囲で極限を扱う。

## 4.3. 中学生向け補足

たとえば \(f(x)=x^2\) とする。

\[
 f(x+u)-f(x)=(x+u)^2-x^2=2xu+u^2
\]

だから、

\[
 \frac{f(x+u)-f(x)}{u}=2x+u
\]

となる。ここで \(u\) をどんどん 0 に近づけると、最後に \(2x\) が残る。これが微分係数じゃ。

つまり `delta` は「増えた量そのもの」、`cosmicKernel` は「1 だけ増やしたと仮定したときの平均変化率」と思えばよい。

---

## 5. `delta` の代数法則

`CosmicDifferenceKernel.lean` の前半は、`delta` の法則を整備する章だと見てよい。

## 5.1. 命題 5.1. 零増分

\[
\delta(f,x,0)=0
\]

### 証明

定義を展開すると

\[
\delta(f,x,0)=f(x+0)-f(x)=f(x)-f(x)=0
\]

である。Lean では `simp [delta]` だけで終わる。

### 意味

増分が 0 なら変化量も 0。これは最小の整合条件である。

## 5.2. 命題 5.2. 加法性

\[
\delta(f+g,x,u)=\delta(f,x,u)+\delta(g,x,u)
\]

### 証明

左辺を展開すると

\[
(f(x+u)+g(x+u))-(f(x)+g(x))
\]

であり、これを並べ替えると

\[
(f(x+u)-f(x))+(g(x+u)-g(x))
\]

になる。Lean では `unfold delta; ring` で証明している。

### コメント

ここで使っているのは解析ではなく、完全に環の計算だけである。差分はまず **線形作用素** として成立している、というわけじゃ。

## 5.3. 命題 5.3. 減法性

\[
\delta(f-g,x,u)=\delta(f,x,u)-\delta(g,x,u)
\]

証明は加法と同じ。差分は減法とも相性がよい。

## 5.4. 命題 5.4. スカラー倍との両立

\[
\delta(af,x,u)=a\,\delta(f,x,u)
\]

### 証明

\[
 a f(x+u)-a f(x)=a(f(x+u)-f(x))
\]

である。Lean ではやはり `ring` に落ちる。

## 5.5. 命題 5.5. 積の差分則

\[
\delta(fg,x,u)=f(x+u)\,\delta(g,x,u)+g(x)\,\delta(f,x,u)
\]

これは本ファイルの最重要命題の一つである。

### 証明

左辺は

\[
 f(x+u)g(x+u)-f(x)g(x)
\]

である。ここに中間項 \(f(x+u)g(x)\) を出し入れすると

\[
\begin{aligned}
&f(x+u)g(x+u)-f(x+u)g(x) \\
&\quad + f(x+u)g(x)-f(x)g(x)
\end{aligned}
\]

となり、

\[
 f(x+u)(g(x+u)-g(x))+g(x)(f(x+u)-f(x))
\]

に変形できる。これがちょうど

\[
 f(x+u)\,\delta g + g(x)\,\delta f
\]

である。

### なぜ `f(x+u)` と `g(x)` なのか

連続微分の積の法則

\[
(fg)'=f'g+fg'
\]

と比べると、片方が \(x+u\)、片方が \(x\) で評価されているので少し歪んで見える。しかしこれは離散差分だから当然で、連続極限 \(u\to 0\) を取れば両者は一致する方向へ寄る。

### 中学生向け補足

「積の増え方」は、

- 右だけ増えるぶん
- 左だけ増えるぶん

の和になっている、と見るとよい。両方いっぺんに増えるように見えても、実はこう分けられる。

## 5.6. 命題 5.6. 有限和との両立

有限集合 \(s\) に対して

\[
\delta\Bigl(\sum_{i\in s}F_i,x,u\Bigr)=\sum_{i\in s}\delta(F_i,x,u)
\]

### 証明

Lean では `Finset.induction_on` を使う。空集合では自明、1 個追加するステップは `delta_add` に帰着する。

### 意味

多項式や級数の有限部分和に対して、差分は **項別処理できる**。後の多項式微分の基礎がここで固まる。

---

## 6. `cosmicKernel` の代数法則

今度は上の差分則を \(u\) で割って、差分商側へ移す。

## 6.1. 命題 6.1. 表示公式

\[
\operatorname{cosmicKernel}(f,x,u)=\frac{f(x+u)-f(x)}{u}
\]

これは定義の確認に過ぎぬが、後の書き換え規則の出発点である。

## 6.2. 命題 6.2. 加法・減法・スカラー倍

\[
K_{f+g}=K_f+K_g,
\qquad
K_{f-g}=K_f-K_g,
\qquad
K_{af}=aK_f
\]

### 証明

`delta_add`, `delta_sub`, `delta_smul` をそれぞれ \(u\) で割る。Lean では `add_div`, `sub_div`, `div_eq_mul_inv` を使って整理している。

### コメント

これにより `cosmicKernel` もまた線形作用素として振る舞う。ただし定義域から \(u=0\) は除外して考える必要がある。

## 6.3. 命題 6.3. 有限和との両立

\[
K_{\sum_i F_i}=\sum_i K_{F_i}
\]

これは `delta_finset_sum` を割るだけではなく、Lean 上では再度 `Finset.induction_on` と `cosmicKernel_add` を使って丁寧に構成している。

## 6.4. 命題 6.4. 積の差分商則

\[
K_{fg}(x,u)=f(x+u)K_g(x,u)+g(x)K_f(x,u)
\]

### 証明

`delta_mul` を \(u\) で割る。

\[
\frac{\delta(fg,x,u)}{u} =
\frac{f(x+u)\delta g(x,u)+g(x)\delta f(x,u)}{u}
\]

ここで分配法則より

\[ =
 f(x+u)\frac{\delta g(x,u)}{u}+g(x)\frac{\delta f(x,u)}{u}
\]

となる。

### 見どころ

連続微分の積の法則は極限を取った後の姿だが、こちらはその **離散版の完成形** である。実際、\(u\to 0\) とすれば

\[
 f(x+u)\to f(x)
\]

だから、通常の積の微分法

\[
(fg)'(x)=f(x)g'(x)+g(x)f'(x)
\]

が現れる。

---

## 7. 微分への橋

ここから `CosmicDerivativeBasic.lean` に入る。

## 7.1. 定理 7.1. 微分可能性と cosmicKernel 極限の同値

\[
\operatorname{HasDerivAt}(f,L,x)
\iff
K_f(x,u)\to L
\quad (u\to 0,\ u\neq 0)
\]

ここで右辺は punctured neighborhood、すなわち \(u=0\) を除いた近傍での極限である。

### 証明の仕組み

Lean の証明そのものは、mathlib の既存定理

\[
\texttt{hasDerivAt\_iff\_tendsto\_slope\_zero}
\]

に `cosmicKernel` と `delta` を代入して `simpa` する構造である。

つまり DkMath は、微分の公理系を新たに作っているのではない。既存の解析基盤を利用しつつ、差分核を **宇宙式の言葉で再表現する窓** を与えているのじゃ。

## 7.2. 系 7.2. 恒等関数と定数関数

恒等関数 \(f(y)=y\) について

\[
K_f(x,u)\to 1
\]

定数関数 \(f(y)=c\) について

\[
K_f(x,u)\to 0
\]

が従う。

### 数学的意味

これは普通の微分法では当たり前だが、ここでは「差分核の極限が、正しく教科書の微分係数を返す」という最初の健全性検査である。

---

## 8. 冪関数の核 `powerKernel`

`CosmicDerivativePower.lean` では、\(f(y)=y^d\) に特化して差分商を有限和として明示する。

## 8.1. 定義 8.1. `powerKernel`

\[
\operatorname{powerKernel}(d,x,u)
:=
\sum_{j=0}^{d-1}
\binom{d}{j+1}x^{d-1-j}u^j
\]

これは

\[
(x+u)^d-x^d
\]

を \(u\) で割ったときに現れる多項式部分である。

## 8.2. 命題 8.2. GN との一致

DkMath 既存の二項補助関数 `GN` と入れ替えた形で

\[
\operatorname{powerKernel}(d,x,u)=GN(d,u,x)
\]

が成り立つ。

### 意味

これは非常に重要じゃ。差分微分の系列が、宇宙式の二項分解系列と **別物ではなく同じ本体** を見ていることを示すからである。Cosmic 幹線が `CosmicFormulaBinom` を数論側の橋として持つのも、この層が共通核だからじゃ。

## 8.3. 定理 8.3. 冪差の因数分解

\[
(x+u)^d-x^d=u\,\operatorname{powerKernel}(d,x,u)
\]

### 証明

Lean では `CosmicFormulaBinom.cosmic_id_csr'` を呼び、GN 表現へ落としてから `ring` で整理している。これは本質的に二項定理の再配置であり、数学的には

\[
(x+u)^d-x^d =
\sum_{k=1}^{d}\binom{d}{k}x^{d-k}u^k =
 u\sum_{j=0}^{d-1}\binom{d}{j+1}x^{d-1-j}u^j
\]

というだけである。

## 8.4. 系 8.4. \(u\neq 0\) での核の一致

\[
K_{y\mapsto y^d}(x,u)=\operatorname{powerKernel}(d,x,u)
\qquad (u\neq 0)
\]

### 証明

上の因数分解を差分商へ代入して、\(u\neq 0\) により約分する。

### 重要な見方

ここで差分商の特異点はまだ残っている。しかし「特異に見える差分商は、実は多項式 `powerKernel` に一致する」と分かるので、特異性は removable singularity、すなわち **見かけ上の穴** に過ぎないことが分かる。

---

## 9. 冪関数の導関数の証明

`CosmicDerivativePowerLimit.lean` は、この removable singularity を利用して、冪関数の微分を完成させる。

## 9.1. 命題 9.1. `powerKernel` の連続性

\[
 u\mapsto \operatorname{powerKernel}(d,x,u)
\]

は連続である。

### 理由

有限和の各項が \(u\) の多項式だからである。Lean では `continuity` タクティクで一気に片づく。

## 9.2. 命題 9.2. 中心値

\[
\operatorname{powerKernel}(d,x,0)=(d: \mathbb{R})x^{d-1}
\]

### 証明

\(u=0\) を代入すると、和の中で \(j=0\) の項だけが残り、他はすべて \(0^j\) で消える。

残る項は

\[
\binom{d}{1}x^{d-1}=dx^{d-1}
\]

である。

### 中学生向け補足

たとえば \(d=3\) なら

\[
\operatorname{powerKernel}(3,x,u)=3x^2+3xu+u^2
\]

だから、\(u=0\) を入れると \(3x^2\) だけが残る。これはまさに \(x^3\) の微分係数じゃ。

## 9.3. 定理 9.3. 冪関数の導関数

\[
\frac{d}{dx}x^d=dx^{d-1}
\]

### Lean 上の流れ

1. `cosmicKernel (y^d)` は punctured neighborhood で `powerKernel` に一致する。
2. `powerKernel` は 0 で連続。
3. したがって `powerKernel(d,x,u)` は \(u\to 0\) で \(dx^{d-1}\) に収束する。
4. 1 と 3 を合わせて `cosmicKernel` の極限が得られる。
5. `hasDerivAt_of_tendsto_cosmicKernel` により導関数定理が出る。

### 数学的意義

教科書では「二項定理で展開して、\(u\) で割って、\(u\to 0\)」で終わる話を、Lean では

- 因数分解層
- 連続性層
- 極限層
- 微分復元層

へ分解している。この分解がそのまま説明書になる。実装が美しいとは、こういうことじゃよ。

---

## 10. 多項式への拡張

`CosmicDerivativePolynomial.lean` は、単項式から多項式へ進む。

## 10.1. 命題 10.1. 単項式の核

\[
K_{y\mapsto ay^n}(x,u)=a\,\operatorname{powerKernel}(n,x,u)
\qquad (u\neq 0)
\]

これは `cosmicKernel_smul` と冪関数の場合の系に過ぎぬ。

## 10.2. 定理 10.2. 多項式評価の核の係数和表示

多項式 \(p\) に対し、\(u\neq 0\) なら

\[
K_{y\mapsto p(y)}(x,u) =
\sum_{n=0}^{\deg p} a_n\,\operatorname{powerKernel}(n,x,u)
\]

### 証明

多項式を

\[
 p(y)=\sum_{n=0}^{N}a_n y^n
\]

と書く。`cosmicKernel_finset_sum` により項別へ分解し、各項に単項式の核公式を適用する。

### 重要な点

多項式の微分は「項別微分」である、という事実を Lean では

- 和に対する核の線形性
- 単項式の核の明示式

の合成として表現している。抽象が壊れておらず、とても筋がよい。

## 10.3. 定義 10.3. `polynomialKernelExt`

DkMath はさらに

\[
\operatorname{polynomialKernelExt}(p,x,u)
:=
\sum_{n=0}^{\deg p}a_n\operatorname{powerKernel}(n,x,u)
\]

を定義する。

これは \(u\neq 0\) では元の `cosmicKernel` に一致し、\(u=0\) では自然に導関数の値を与えるよう設計された **連続拡張** である。

## 10.4. 命題 10.4. 0 での値

\[
\operatorname{polynomialKernelExt}(p,x,0)=p'(x)
\]

### 証明

各項で命題 9.2 を適用すると

\[
 a_n\operatorname{powerKernel}(n,x,0)=a_n\,n x^{n-1}
\]

となるので、全体でちょうど多項式導関数の係数表示になる。

## 10.5. 定理 10.5. 多項式の導関数

\[
\frac{d}{dx}p(x)=p'(x)
\]

### 証明の構成

1. punctured neighborhood では `cosmicKernel = polynomialKernelExt`
2. `polynomialKernelExt` は 0 で連続
3. その 0 での値は \(p'(x)\)
4. よって `cosmicKernel` の punctured limit も \(p'(x)\)
5. 基本橋定理により `HasDerivAt`

### 評価

これは「特異な差分商を、有限和多項式へ拡張してから極限を取る」という、とても健全な設計である。わっちはこの筋立てが気に入っておる。

---

## 11. 宇宙式そのものへの橋

最後に `CosmicFormulaDerivativeBridge.lean` の意味を述べる。

ここで DkMath の基本宇宙式は

\[
(x+u)^2-x(x+2u)=u^2
\]

である。これは `cosmic_formula_unit` として基本定理化されている。Big / Body / Gap の観点では、\(u^2\) は Gap に当たる。宇宙式族の資料でも Big / Body / Gap の恒等式が最初の基盤として据えられている。

## 11.1. 命題 11.1. 差分との接続

\[
\delta(y\mapsto y^2,x,u)=u\,\operatorname{powerKernel}(2,x,u)
\]

これは冪差の因数分解の次数 2 の場合である。

## 11.2. 命題 11.2. 宇宙式の再読

`CosmicFormulaDerivativeBridge` では

\[
\operatorname{cosmic_formula_unit}(x,u) =
\delta(y\mapsto y^2,x,u)-2xu
\]

を示している。

だが

\[
\delta(y\mapsto y^2,x,u)=(x+u)^2-x^2=2xu+u^2
\]

だから、差を取ると

\[
(2xu+u^2)-2xu=u^2
\]

である。すなわち

\[
\operatorname{cosmic_formula_unit}(x,u)=u^2
\]

が再び現れる。

## 11.3. この橋の意味

ここが本稿の肝心な哲学じゃ。

微分の差分商を考えるとき、通常は \(u\) で割って終わりである。しかし宇宙式の見方では、

- 差分 \((x+u)^2-x^2\) には線形成分 \(2xu\) と残差 \(u^2\) がある
- 線形成分は「一次近似」
- 残差 \(u^2\) は **Gap** であり、宇宙式の核そのもの

となる。

つまり微分は「一次部分を抽出する操作」であり、宇宙式は「一次部分を取り除いたあとに何が残るか」を露わにする恒等式なのである。

微分と宇宙式は敵対せず、むしろ

\[
\text{差分} = \text{一次部分} + \text{Gap}
\]

という同じ分解を、別の焦点で見ているのじゃよ。

---

## 12. 証明構造の総括

ここまでの流れを「定義」「命題」「証明」の鎖としてまとめる。

## 12.1. 第1層. 差分の定義層

- `delta`
- `cosmicKernel`

ここではまだ極限は出ない。純代数的世界である。

## 12.2. 第2層. 離散微分法則層

- `delta_add`, `delta_sub`, `delta_smul`, `delta_mul`, `delta_finset_sum`
- `cosmicKernel_add`, `cosmicKernel_sub`, `cosmicKernel_smul`, `cosmicKernel_mul`, `cosmicKernel_finset_sum`

ここで「差分核が線形かつ積則を持つ」ことが確立される。

## 12.3. 第3層. 微分への橋層

- `hasDerivAt_iff_tendsto_cosmicKernel`
- `tendsto_cosmicKernel_of_hasDerivAt`
- `hasDerivAt_of_tendsto_cosmicKernel`

ここで初めて極限が出る。

## 12.4. 第4層. 冪関数の具体化

- `powerKernel`
- `sub_pow_eq_u_mul_powerKernel`
- `cosmicKernel_pow_eq_powerKernel_of_ne_zero`
- `powerKernel_zero`
- `hasDerivAt_pow_cosmic`

ここでは二項展開が主役。

## 12.5. 第5層. 多項式の一般化

- `cosmicKernel_monomial_of_ne_zero`
- `cosmicKernel_polynomial_eval_eq_sum_coeff_mul_powerKernel_of_ne_zero`
- `polynomialKernelExt`
- `polynomialKernelExt_zero`
- `tendsto_cosmicKernel_polynomial_eval`
- `hasDerivAt_polynomial_eval_cosmic`

ここでは有限和と連続拡張が主役。

## 12.6. 第6層. 宇宙式への還元

- `delta_pow_two_eq_u_mul_powerKernel_two`
- `cosmic_formula_unit_eq_delta_pow_two_sub_two_mul`
- `cosmic_formula_unit_eq_u_mul_powerKernel_two_gap`
- `cosmic_formula_unit_eq_u_sq_from_derivative_bridge`

ここで微分側と宇宙式側が結び合わされる。

---

## 13. 数学的評価

この実装の美点は、微分を最初から解析的対象として押し込まず、差分を主役にしてから極限へ渡しているところにある。

普通の教科書では、

\[
\frac{f(x+u)-f(x)}{u}
\]

は極限前の仮置きのように見える。しかし DkMath では、これを `cosmicKernel` として定義し、独立した計算対象に昇格させる。すると、

- 代数法則が先に整備できる
- 二項展開との接続が直接書ける
- 多項式への拡張が有限和として透明になる
- 宇宙式の Gap \(u^2\) を「一次近似の残差」として読める

という利点が一挙に現れる。

特に

\[
(x+u)^2-x^2=2xu+u^2
\]

の最後の \(u^2\) を、ただの余りではなく **宇宙式の unit gap** と読む視点は、DkMath 独自の風味として面白い。設計資料でも、宇宙式は Big / Body / Gap の分解を核に据え、二項構造や d/2 構造へ一般化する方針が強調されている。

---

## 14. 中学生にもわかる全体まとめ

最後に、なるべくやさしく言い直そう。

関数 \(f(x)\) があるとき、少しだけ \(u\) だけ動かしたら、どれだけ増えるかを見たい。まず増えた量そのもの

\[
 f(x+u)-f(x)
\]

を見る。これが `delta`。

次に、「1 進むごとにどれくらい増えたか」を見るために \(u\) で割る。

\[
 \frac{f(x+u)-f(x)}{u}
\]

これが `cosmicKernel`。

もし \(u\) をどんどん小さくしていったとき、ある数に近づくなら、それが微分係数になる。

たとえば \(x^2\) なら

\[
 (x+u)^2-x^2=2xu+u^2
\]

だから、1 あたりの増え方は

\[
 \frac{2xu+u^2}{u}=2x+u
\]

で、\(u\to 0\) にすると \(2x\) になる。

でも DkMath はさらに一歩進んで、「最後に残った \(u^2\) は何者か」を見る。すると

\[
(x+u)^2-x(x+2u)=u^2
\]

となって、これは宇宙式の Gap そのものになる。

つまり、

- 微分は「変化の中の一次部分」を見る学問
- 宇宙式は「一次部分を引いた残り」を見る学問

と考えることができる。

両者は別々の話ではなく、同じ差分を違う角度から見ているのじゃ。

---

## 15. 結論

`CosmicDifferenceKernel.lean` は、単なる補助ファイルではない。ここで定義される `delta` と `cosmicKernel` が、DkMath における宇宙式版 微分係数の真正の出発点である。

その上に

- 差分の代数法則
- 微分への橋
- 冪関数の有限和分解
- 多項式への連続拡張
- 宇宙式 \(u^2\) との橋

が順に積み上がる。

とりわけ、差分商の「特異点」を、有限和 `powerKernel` や `polynomialKernelExt` による removable singularity として処理する流れは、Lean 実装としても数学的説明としても非常に筋がよい。

わっちの見立てでは、この系列は今後さらに

- 有理関数版
- 指数関数版
- 対数関数版
- 多変数版
- Big / Body / Gap の幾何モデルとの統合版

へ自然に伸びていける。土台はすでにきれいに揃っておる。

---

## 16. 付録. 読む順番のすすめ

初読なら、次の順で読むと頭に入りやすい。

1. `CosmicDifferenceKernel.lean`
2. `CosmicDerivativeBasic.lean`
3. `CosmicDerivativePower.lean`
4. `CosmicDerivativePowerLimit.lean`
5. `CosmicFormulaDerivativeBridge.lean`
6. `CosmicDerivativePolynomial.lean`

理由は、まず差分核の骨組みを掴み、次に冪関数の導関数を先に完成させ、その後で宇宙式 \(u^2\) との橋を見たほうが、多項式一般化の意味が鮮明になるからである。
