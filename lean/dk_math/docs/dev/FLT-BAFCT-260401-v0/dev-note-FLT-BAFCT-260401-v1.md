# Branch A の詰まりから Gamma 連続化・CFBRC 解析接続へ向かう設計整理

## 1. 現在地

FLT Branch A の `FringeDescent` 側は、証明の骨格そのものはかなり見えている。

現状の spine は次の形である。

\[
\text{fringe bundle}
\to
\text{smaller packet}
\to
\text{new witness } q'
\to
\text{smaller fringe}
\to
\text{minimal } z \text{ contradiction}
\]

しかし、実際に詰まっている核は次の 2 点に圧縮されている。

- `branchA_smallerPacket_p_not_dvd_t`
- `branchA_restoreWitness_of_smallerPacket`

これは、実装技術の不足というより、供給すべき数学の形がまだ定まっていないことを意味する。

---

## 2. 発想の転換

ここで重要なのは、整数次数 \(d\) と実数次数 \(d\) の差を、単なる「離散 vs 連続」として雑に見るのではなく、

\[
d \longmapsto d+\varepsilon
\]

という **整数次数の近傍** として見ることである。

見るべき位置は

\[
d+0 \leftarrow d+\varepsilon \to d+1
\]

であり、先に考えるべきなのは \(d \to \infty\) ではなく、この \(d+\varepsilon\) の局所変形である。

---

## 3. 整数次数と実数次数の差

整数 \(d=n\) では、二項展開は有限和で終わる。

\[
(x+u)^n = \sum_{m=0}^{n}\binom{n}{m}x^m u^{n-m}
\]

したがって標準 GN も有限多項式である。

\[
GN_n(x,u) = \frac{(x+u)^n-u^n}{x}
\]

一方、実数 \(d\) では、これを有限和のまま扱うことはできない。  
ここで必要になるのが Gamma による連続化である。

一般化二項係数を

\[
\binom{d}{m}_{\Gamma}
:=
\frac{\Gamma(d+1)}{\Gamma(m+1)\Gamma(d-m+1)}
\]

とおくと、Gamma-GN は

\[
G_d^{(\Gamma)}(x,u)
:=
\frac{(x+u)^d-u^d}{x} = \sum_{m=1}^{\infty} \binom{d}{m}_{\Gamma} x^{m-1} u^{d-m}
\]

と書ける。

したがって、本質は

\[
\text{整数では有限多項式}
\quad\rightsquigarrow\quad
\text{実数では無限 Tail を持つ解析的級数}
\]

への遷移である。

この意味で

\[
\text{無限級数} \approx \text{無限多項式}
\]

という見方は、かなり良い直感である。

---

## 4. 本当に見るべき量

本当に観測すべきなのは、Gamma-GN そのものというよりも、整数次数との差分 defect である。

### 4.1. Gamma-GN

\[
G_d^{(\Gamma)}(x,u)
\]

### 4.2. 整数次数 defect

\[
\Delta_n(\varepsilon;x,u)
:=
G_{n+\varepsilon}^{(\Gamma)}(x,u)-GN_n(x,u)
\]

### 4.3. 一次 defect

\[
\mathcal D_n(x,u)
:=
\frac{\partial}{\partial d}G_d^{(\Gamma)}(x,u)\Big|_{d=n}
\]

正則性が成り立つなら、近傍では

\[
\Delta_n(\varepsilon;x,u) = \varepsilon\,\mathcal D_n(x,u)+O(\varepsilon^2)
\]

と展開できる。

ここで \(\mathcal D_n(x,u)\) が、「整数では不要、実数では必要になる補正」の局所的な姿である。

---

## 5. 下界候補の形

Gamma 連続化や正則性だけで、ただちに FLT の整数解禁止が出るわけではない。  
しかし、下界候補の **形** はかなり絞れる。

もっとも自然なのは対数 defect である。

\[
\Lambda_m(d)
:=
\log(x^d+y^d)-d\log m
\qquad (m\in\mathbb{N})
\]

すると

\[
\Lambda_m(n)=0
\iff
x^n+y^n=m^n
\]

であるから、FLT で禁止したいのは

\[
\Lambda_m(n)\neq 0
\]

である。

さらに

\[
x^n+y^n-m^n = m^n\bigl(e^{\Lambda_m(n)}-1\bigr)
\]

だから、\(|\Lambda_m(n)|\) に下界がつけば、そのまま perfect-power gap の下界候補になる。

したがって解析側が与えるもっとも自然な候補量は

\[
|\Lambda_m(n)|
\]

である。

---

## 6. それでも離散情報が必要な理由

正則性・微分・曲率は、

- defect の形
- ずれの一次項
- 接し方
- 近づき方

を与えてくれる。

しかし、それだけでは

\[
\Lambda_m(n)\neq 0
\]

は自動では出ない。  
必要なのは「連続枝がある」ことではなく、

\[
\text{その枝が整数格子に着地できない}
\]

ことである。

ゆえに役割分担は次のようになる。

\[
\text{解析側}
\;=\;
\text{defect と下界候補の形を決める}
\]

\[
\text{離散側}
\;=\;
\text{整数格子への着地を禁止する}
\]

この二つを繋ぐ橋が、今後の核心になる。

---

## 7. CFBRC / RH 側へ先に回る理由

ここで、宇宙式の微分 kernel から CFBRC、さらに RH 側の解析接続へ向かう設計が意味を持つ。

流れは概ね次のように整理できる。

\[
\text{差分 kernel}
\to
\text{微分 kernel}
\to
\text{CFBRC の複素 kernel}
\to
\text{局所正則性}
\to
\text{解析接続の transport}
\]

ここでの狙いは、FLT を解析だけで直接証明することではない。  
むしろ、

- defect の形
- 局所的なずれの一次項
- 偏角・曲率・複素変形
- branch をまたぐ transport

を、複素正則モデルの中で読むことにある。

したがって、CFBRC / RH 側へ先に回るのは回り道ではあるが、数学的にはかなり筋が良い。

---

## 8. 添付図の世界観の意味

複素写像

\[
f(z)=e^{c\log z}=z^c
\]

による格子変形は、今の構想を幾何的によく表している。

これは単なる「曲がった格子」ではなく、

- \(\log z\) による線形化
- 複素係数 \(c\) による回転・伸縮・せん断
- \(\exp\) による再配置

からなる正則 deformation である。

図としては

\[
\text{離散 dyadic 格子}
\quad\rightsquigarrow\quad
\text{螺旋化した自己相似格子}
\]

という像になっている。

この図は、\(d+\varepsilon\) によって

- 整数では閉じていた格子が
- 少しずつ開き
- ねじれ
- 曲率を持ち
- 隠れていた無限 Tail を露出する

という世界観の幾何モデルと見なせる。

---

## 9. いまの一番よい整理

ここまでを一言で言えば、次のようになる。

\[
\boxed{
\text{整数次数 } d=n \text{ の有限構造を、}
d=n+\varepsilon
\text{ で連続化し、その defect を正則量として読む}
}
\]

さらに

\[
\boxed{
\text{離散情報は、その defect が整数格子へ着地しないことを保証する}
}
\]

これが現時点での主筋である。

---

## 10. 次の作業方針

### 10.1. 解析側で固定する対象

- `Gamma-GN`
- `GammaTailDefect_nearInteger`
- `log_defect_gap_bridge`

### 10.2. CFBRC 側で書く設計メモ

題名案：

\[
\texttt{CFBRC\_analyticContinuation\_bridge\_design}
\]

中身：

- 微分 kernel の複素化
- CFBRC 局所 model との一致
- 局所正則性
- 偏角・曲率との橋
- 解析接続の local transport 条件

### 10.3. FLT 側の扱い

`FringeDescent` はこれ以上局所的に掘らず、未解決核を target 化して条件付き spine として閉じる。

たとえば：

- `BranchASmallerPacketPNotDvdTTarget`
- `BranchARestoreWitnessOfSmallerPacketTarget`

を仮定した conditional theorem として整理する。

---

## 11. 最終結論

最終的な整理は次の三点に尽きる。

\[
\boxed{
\text{先に見るべきは } d\to\infty \text{ ではなく } d=n+\varepsilon \text{ の近傍である}
}
\]

\[
\boxed{
\text{そこで現れる無限 Tail の defect が、下界候補の形を与える}
}
\]

\[
\boxed{
\text{離散情報は、その候補が整数格子へ着地しないことを保証する}
}
\]

したがって、次は FLT Branch A の末端を無理に掘り続けるよりも、Gamma 連続化・CFBRC・解析接続の側で defect の形を固定し、その後に離散情報との橋を作るのが自然である。
