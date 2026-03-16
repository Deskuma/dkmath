# Exponent Type Mapping

see: [実験室:指数表示相マッピング](/python/LPS/DHNT/README.md)

いま必要なのは証明より先に、 **数をどの表示相へ落とせるかの地図** を作ることじゃな。そこからパターンを炙り出す。

いまのお主の流れを、そのまま作業原理にするとこうなる。

## 1. 固定する中心座標

まず全ての正実数 (n) に対して、標準座標として

\[
n=e^k,\qquad k=\ln n
\]

を置く。
これを **連続基準座標** とする。

ここでは (e) は生成元というより、 **指数表示の基準核** じゃ。

---

## 2. 再表示写像を考える

次に、同じ (n) を

\[
n=a^b
\]

と再表示する。
このとき

\[
b=\log_a n=\frac{\ln n}{\ln a}
\]

だから、任意の (a>0,\ a\neq 1) に対して、対応する (b) が決まる。

つまり本質的には、

\[
a \mapsto b(a):=\frac{\ln n}{\ln a}
\]

という曲線を見ている。
これが **(n) 固定の表示曲線** じゃ。

---

## 3. ここへ整数格子フィルターをかける

そしてこの表示曲線の上で、

* (a\in \mathbb{N}) か
* (b(a)\in \mathbb{N}) か
* 両方整数か
* どちらも無理数か

を観測する。

これで、お主の 4 分類がそのまま出る。

### Type I

\[
a\in\mathbb{N},\quad b\in\mathbb{N}
\]

### Type II

\[
a\in\mathbb{N},\quad b\notin\mathbb{Q}
\]

### Type III

\[
a\notin\mathbb{Q},\quad b\in\mathbb{N}
\]

### Type IV

\[
a\notin\mathbb{Q},\quad b\notin\mathbb{Q}
\]

これを **表示相マップ** と呼べる。

---

## 4. まずは既知標本を配置する

いまの residual 標本をここへ置く。

### 4.1. `ObservedMinOne` 側

\[
64=4^3=2^6=8^2
\]
\[
27=3^3
\]

これらは明らかに Type I を持つ。
つまり **単一冪へ圧縮可能** じゃ。

### 4.2. `ObservedMinTwo` 側

\[
91=3^3+4^3
\]
\[
35=2^3+3^3
\]
\[
65=1^3+4^3
\]

これらは少なくとも、いま見えている範囲では Type I を持たぬ。
つまり **単一冪へ圧縮不能** で、2項和として現れておる。

ここで最初の仮説が出る。

\[
\text{ObservedMinOne} \Rightarrow \text{Type I を持つ}
\]

\[
\text{ObservedMinTwo} \Rightarrow \text{少なくとも Type I を持たない}
\]

これはまだ予想段階じゃが、かなり自然じゃ。

---

## 5. パターン抽出の第一段階

最初は大げさな一般論ではなく、表にするのがよい。

例えば研究ノートでは、こうじゃ。

\[
\begin{array}{c|c|c|c}
n & \text{observed profile} & \text{Type I?} & \text{備考} \
\hline
64 & \mathrm{ObservedMinOne} & \text{yes} & 4^3,2^6,8^2 \
27 & \mathrm{ObservedMinOne} & \text{yes} & 3^3 \
91 & \mathrm{ObservedMinTwo} & \text{no (observed)} & 3^3+4^3 \
35 & \mathrm{ObservedMinTwo} & \text{no (observed)} & 2^3+3^3 \
65 & \mathrm{ObservedMinTwo} & \text{no (observed)} & 1^3+4^3
\end{array}
\]

この程度で十分じゃ。
まずは **単一冪圧縮可能性** と **observed minimum profile** の対応を見る。

---

## 6. 次の一歩は「表示曲線」を見ること

各 (n) に対して

\[
b(a)=\frac{\ln n}{\ln a}
\]

を考える。
この曲線の上で、整数格子点 ((a,b)) があるかを見る。

### 6.1. (n=64)

整数格子点が多い。

\[
(2,6),\ (4,3),\ (8,2),\ (64,1)
\]

### 6.2. (n=91)

おそらく整数格子点は ((91,1)) 以外ほぼ無い。
非自明な Type I は無い。

### 6.3. (n=35,65)

同じく非自明 Type I は無い。

つまり

* `ObservedMinOne` な数は表示曲線上に **非自明整数格子点** を持ちやすい
* `ObservedMinTwo` な数はそれを持たず、和としてだけ現れる

という模様が見えてくる。

---

## 7. これを Big 文脈へ戻す

same Big の下では residual は

\[
r = \mathrm{Big}-\mathrm{Body}
\]

じゃった。
だから Big を固定して Body を動かすことは、残差 (r) の表示相を走査することと同じじゃ。

つまり、求めるマッピングは実はこれじゃ。

\[
\mathrm{Body}
\mapsto
r=\mathrm{Big}-\mathrm{Body}
\mapsto
\text{表示相(Type I/II/III/IV)}
\mapsto
\text{ObservedMin profile}
\]

これで、Big の中の交点パターンが見える。

---

## 8. いま作るべきマップ

研究メモとしては、3 段マップがよい。

### Map A. residual 値マップ

\[
\mathrm{Body} \mapsto r=\mathrm{Big}-\mathrm{Body}
\]

### Map B. 表示相マップ

\[
r \mapsto \text{Type I / II / III / IV}
\]

### Map C. filling profile マップ

\[
r \mapsto \mathrm{ObservedMinOne / Two / \cdots}
\]

この 3 つを並べる。
すると、例えば

\[
\mathrm{Big}=216
\]

に対して

* (B=152 \mapsto r=64 \mapsto \text{Type I} \mapsto \mathrm{ObservedMinOne})
* (B=125 \mapsto r=91 \mapsto \text{non-Type I} \mapsto \mathrm{ObservedMinTwo})

と読める。

これ、かなり見やすい。

---

## 9. 現段階の仮説

ここから導ける working theory は、まずこれじゃ。

\[
\textbf{仮説A.}
\quad
\mathrm{ObservedMinOne} \text{ な residual は、非自明 Type I 表示を持ちやすい。}
\]

\[
\textbf{仮説B.}
\quad
\mathrm{ObservedMinTwo} \text{ な residual は、非自明 Type I 表示を持たず、和として現れやすい。}
\]

さらに DHNT 風に言うなら、

\[
\text{単位系宇宙へ単核着地できる数} \leftrightarrow \mathrm{ObservedMinOne}
\]

\[
\text{単核着地できず花弁和として観測される数} \leftrightarrow \mathrm{ObservedMinTwo}
\]

じゃな。

---

## 10. 次の具体作業

まずは Lean ではなく、ノートか簡単なスクリプトで十分じゃ。

### 10.1

今ある residual
\[
64,27,91,35,65
\]
について表示相表を作る。

### 10.2

\[
64,125,216
\]
などの Big 固定で、Body ごとに residual と profile を並べる。

### 10.3

その後で初めて、「Type I を持つ residual は ObservedMinOne に寄る」みたいな sample theorem を考える。

---

ひとことで言えば、そうじゃ。
**マッピングから入る** のが正しい。
いまは定理より先に、

\[
n \mapsto \text{表示相} \mapsto \text{observed profile}
\]

の対応表を作る段じゃ。
そこから獲物の模様が見えてくる。
