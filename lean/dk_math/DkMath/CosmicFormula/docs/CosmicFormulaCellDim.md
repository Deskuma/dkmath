# 無次元化された宇宙式

Lean Code: [CosmicFormulaCellDim](./CosmicFormulaCellDim.lean)

## README / 論文向け

了解じゃ。以下はそのまま README や論文 Appendix に貼れるように、**「何を定義し、何を示し、なぜ重要か」** の順で整理した **定理リスト** じゃ。
（名前はお主の実装に合わせて調整できるよう、*概念名＋代表的な定理名候補* の形で書く）

---

## 定理リスト

本節では、**格子セルの有限集合（Finset）** として宇宙式構造を実装し、2次元平面から **任意次元 (d)** へ無次元一般化したうえで、**Big/Body/Gap 分解**と **二項定理との同値**、さらに **構成的（disjoint union）分解**までを Lean で形式証明した成果を列挙する。

---

## 0. 基本設定：無次元セル空間

### 定義：d 次元セル

* `Cell (d : ℕ) := Fin d → ℤ`

**意味**：座標系に依存せず、(d) 次元格子点を一様に扱うための基本型。

---

## 1. 平行移動と濃度（card）の不変性

### 定義：平行移動の埋め込みと translate

* `addEmb (v : Cell d) : Cell d ↪ Cell d`
* `translate (v : Cell d) (S : Finset (Cell d)) : Finset (Cell d)`

### 補題：平行移動は濃度を保存する

* `card_translate : (translate v S).card = S.card`

**意味**：配置（原点や位置）は本質ではなく、以後の議論は “形（集合）” のみに依存する。

---

## 2. 直方体（Box）とその濃度計算

### 定義：原点箱 Box

* `Box (a : Fin d → ℕ) : Finset (Cell d)`

  * 各軸で `0 ≤ coord < a(i)` を満たすセル集合

### 補題：箱の濃度は軸長の積

* `card_Box_eq_prod : (Box a).card = ∏ i : Fin d, a i`

### 定義：平行移動箱 BoxAt

* `BoxAt (o : Cell d) (a : Fin d → ℕ) : Finset (Cell d)`

### 補題：BoxAt の濃度は Box と同じ

* `card_BoxAt : (BoxAt o a).card = (Box a).card`

**意味**：幾何（箱）を “有限集合の濃度” に落とすことで、次元一般化された面積・体積に相当する量を扱える。

---

## 3. Big / Gap / Body（宇宙式の三分割）

### 定義：定数ベクトル

* `constVec (d : ℕ) (n : ℕ) : Fin d → ℕ`

### 定義：全体 Big と余白 Gap

* `Big (d x u : ℕ) := Box (constVec d (x+u))`
* `Gap (d u : ℕ) := Box (constVec d u)`

### 定義：実体 Body（差集合）

* `Body (d x u : ℕ) := Big (d,x,u) \ Gap (d,u)`

---

## 4. 集合としての分解（Big = Body ∪ Gap）

### 補題：Gap ⊆ Big

* `Gap_subset_Big`

### 定理：Big の分解（集合等式）

* `Big_eq_Body_union_Gap : Big = Body ∪ Gap`

### 定理：Body と Gap は交わらない

* `Disjoint_Body_Gap : Disjoint Body Gap`

### 定理：濃度の加法則

* `card_Big_eq_card_Body_add_card_Gap :
    card Big = card Body + card Gap`

**意味**：宇宙式の「全体＝実体＋余白」が、集合論（Finset）として厳密に成立する。

---

## 5. 積をべきへ畳み、Body を差で表す

### 補題：定数積はべき

* `prod_const_fin : (∏ _ : Fin d, n) = n^d`

### 定理：Big と Gap の濃度はべき

* `card_Big_pow : card Big = (x+u)^d`
* `card_Gap_pow : card Gap = u^d`

### 定理：Body の濃度は差

* `card_Body_pow_form : card Body = (x+u)^d - u^d`

**意味**：Big/Gap/Body を、次元 (d) のべきとして明示化し、宇宙式の “濃度差” を確定する。

---

## 6. 差のべき因数分解：幾何和版 (G)

### 定義：幾何和（差のべき因数分解に現れる和）

* `G (d x u : ℕ) := ∑ k < d, (x+u)^(d-1-k) * u^k`（実装形に従う）

### 定理：差のべきの因数分解

* `pow_sub_pow_eq_mul_G :
    (x+u)^d - u^d = x * G d x u`

### 定理：Body の最終形（幾何和版）

* `card_Body_eq_mul_G :
    card Body = x * G d x u`

**意味**：余白を除いた実体は **必ず (x) 倍**になり、実体の構造は (G) に全て吸収される。

---

## 7. 二項定理版 \(G_{\mathrm{binom}}\) と同値性

### 定義：choose（係数）版

* `Gbinom (d x u : ℕ) := ∑ k < d, choose d (k+1) * x^k * u^(d-1-k)`

### 定理：二項定理からの因数分解

* `pow_sub_pow_eq_mul_Gbinom :
    (x+u)^d - u^d = x * Gbinom d x u`

### 定理：両者は（少なくとも x を掛けると）一致

* `mul_G_eq_mul_Gbinom :
    x * G d x u = x * Gbinom d x u`

### 定理：(x > 0) なら (G) 自体が一致

* `G_eq_Gbinom_of_pos (hx : 0 < x) :
    G d x u = Gbinom d x u`

**意味**：**幾何（幾何和）** と **代数（二項係数）** が同一対象を表していることを形式的に確定。
choose は単なる計算係数ではなく、後述の“分類数”として現れる基盤となる。

---

## 8. 2D 手本（Cell2）と平面への橋渡し

### 定義：2D の略記と座標関数

* `Cell2 := Cell 2`
* `x2`, `y2`, `mk2`, `mk2_eta`

### 定義：Cell2 と (ℤ×ℤ) の同値

* `cell2EquivProd : Cell2 ≃ (ℤ × ℤ)`

### 2D 手本：矩形の濃度と L 字分解（card）

* `Rect2`, `RectAt2`
* `card_Rect2`, `card_RectAt2`
* `G_two_dim_eval : G 2 x u = x + 2u`
* `card_Body2_eq_x_mul : card Body = x*(x+2u)`
* `card_Body2_as_two_rects`（矩形2枚の濃度和として）

**意味**：平面の直観（L字＝2矩形）を “手本の皮” として確立し、一般次元への読み替えの足場を作る。

---

## 9. 構成的分解（Slab）による Body の disjoint union（本命）

### 定義：Slab（最小軸ルールによる層）

* `Slab0`, `slabShift`, `Slab` など（実装形に従う）

### 定理：Slab は互いに交わらない

* `Slab_pairwise_disjoint`（あるいは `Pairwise (Disjoint ...)`）

### 定理：Body は Slab の disjoint union

* `Body_eq_iUnion_Slab` あるいは `Body_eq_biUnion_Slab`（実装に従う）

### 定理：濃度は Slab 濃度の和

* `card_Body_eq_sum_card_Slab`

### 定理：この構成的和は (x\cdot G) に一致

* `card_Body_eq_mul_G_constructive`（命名は任意）

**意味**：choose 係数が **「分類数（構成的分割の数え上げ）」** として現れる段階。
差集合による存在証明ではなく、**分割＝構成**として宇宙式を確立する。

---

## 最終到達点（宇宙式：無次元 Finset 版）

以上を総合し、任意の \(d,x,u\in\mathbb{N}\) に対して

\[
\mathrm{Big}=\mathrm{Body}\sqcup\mathrm{Gap},\qquad
\#\mathrm{Big}=(x+u)^d,\quad \#\mathrm{Gap}=u^d,
\]

\[
\boxed{\ \#\mathrm{Body}=(x+u)^d-u^d = x\cdot G(d,x,u)=x\cdot G_{\mathrm{binom}}(d,x,u)\ }
\]

が Lean により形式証明された。

---

## 付記（読む人へのガイド）

* **幾何的側面**：Box / translate / disjoint union（Slab）
* **代数的側面**：べきの差の因数分解（幾何和）と二項係数（choose）
* **橋渡し**：card（濃度）が両者を同一視する

---

必要なら、このリストをそのまま **README セクション構成**（Motivation → Definitions → Main Theorems → 2D Example → Constructive Decomposition → Outlook）に整形して、ファイルに貼れる Markdown にも仕上げられるぞ。

---

$$
◇\qquad\qquad～\qquad\qquad◇\qquad\qquad～\qquad\qquad◇
$$

---

## 最終結論

ぬしよ……やりおったな！🎉
**“差集合で存在を言う”** から **“分解で構成を見せる”** へ――ここを Lean で完走できたのは、研究としても実装としても一段格が上がった証じゃ。

ここで、いま「何が確定したか」を短く太く刻んでおくぞ。

---

## 何が確定したのか（今回の“完全に通した”の意味）

### 1. Body は「作れる」だけでなく「分解して作れる」

これまで：
\[
\mathrm{Body} := \mathrm{Big}\setminus \mathrm{Gap}
\]
という **差集合**で定義して、card の式を導いた。

今回：
\[
\mathrm{Body} = \bigsqcup_{i \in \mathrm{Fin}\ d} \mathrm{Slab}(i)
\]
のように、**Slab（層）たちの disjoint union**として「構成的に」作れた。

これは直観的には「余白の外側を、最小軸ルールで一意に分類した」というやつじゃ。

---

### 2. 係数が“分類数”になった（choose の正体が見えた）

Slab 分解が通ると、card は

\[
\#\mathrm{Body}=\sum_i \#\mathrm{Slab}(i)
\]

という **数え上げ**に落ちる。
そしてこれが最終的に

\[
\#\mathrm{Body} = (x+u)^d-u^d = x\cdot G(d,x,u)
\]
さらに
\[
x\cdot G(d,x,u)=x\cdot G_{\mathrm{binom}}(d,x,u)
\]
へ接続される。

つまり二項係数（choose）は「計算上の係数」ではなく、**“層の分類を数えた結果”** として出てくる、という構造が Lean 上で固定された。

---

### 3) 2D トロミノの手本は、d 次元の影として正当化された

`Cell2` 整備 → 2D の L字手本 → d次元 Slab 構成、が一本の道になった。
平面の絵は“比喩”ではなく、**一般次元の特例**として扱える状態になったわけじゃ。

---

## 次にやると「成果が論文/README として光る」整備

ここからは新しい定理を増やすより、**見せ方の仕上げ**が効く。

* 定理カタログ化：
  `Body_decomp`, `Slab_pairwise_disjoint`, `card_Body_eq_sum`, `card_Body_eq_mul_G`, `G_eq_Gbinom` を “章立て” で並べる
* 命名と配置：`CellDim` / `CosmicFormulaCellDim` の API を固定（`abbrev`/`def` の公開範囲）
* 2D への投影補題：`d=2` を `cell2EquivProd` 経由で旧コードへ橋渡し（必要なら）

ここまで整えると、読む者が「何が新しいのか」を一発で理解できる。

---

いやはや、わっちは賢狼じゃが、これは素直に祝杯じゃの🍎🍷
“理屈が通る”だけでなく、“構成が通る”――これが形式化の醍醐味じゃ。

次は、成果の **定理リスト（README/論文向け）** を、そのまま貼れる形で作ってしまうのが一番うまい流れじゃな。

---

$$
◇\qquad\qquad～\qquad\qquad◇\qquad\qquad～\qquad\qquad◇
$$

---

## Cell/Finset 版のまとめ

よし、ぬしよ。ここまでで Lean 上に「無次元化された宇宙式（Cell/Finset 版）」が **“集合として”** も **“数式として”** も噛み合って閉じた。
つまり――“平面のトロミノ絵”から始まった話が、**任意次元 (d)** の抽象格子で **不変量の法則**として成立した、ということじゃ。

以下、ここでの到達点を一旦まとめるぞ。

---

### 1. 何を作ったか：無次元 Cell と translate の核

* 2次元 \((\mathbb{Z}\times\mathbb{Z})\) に縛られず、一般形として
  \[
  \mathrm{Cell}\ d := \mathrm{Fin}\ d \to \mathbb{Z}
  \]
  を採用した。
* 平行移動 `translate` を `Finset.map`（埋め込み）で実装し、**card が保存される**ことを証明した：
  \[
  \#(\mathrm{translate}\ v\ S)=\#S
  \]
  これは「座標原点や位置は本質ではない」という、無次元化の土台になっておる。

---

### 2. “箱” Box と “量＝card” の次元一般化

* 各軸で区間 ([0,a_i)) を取る直方体（箱）`Box` を Finset として定義した。
* その card を “軸ごとの積” に落とせる（仕上げた補題群で）：
  \[
  \#\mathrm{Box}(a)=\prod_{i\in \mathrm{Fin}\ d} a_i
  \]
  特に `constVec` で全軸同一長を与えると、
  \[
  \prod_{i\in\mathrm{Fin}\ d} n = n^d
  \]
  が確立し、箱の card が **べき**として畳めるようになった。

---

### 3. Big / Gap / Body の三分割を“集合”で作り、分解法則を得た

* 全体：
  \[
  \mathrm{Big}(d,x,u)=\mathrm{Box}(x+u)
  \]
* 余白：
  \[
  \mathrm{Gap}(d,u)=\mathrm{Box}(u)
  \]
* 実体：
  \[
  \mathrm{Body}=\mathrm{Big}\setminus \mathrm{Gap}
  \]
  そして、**集合として**
  \[
  \mathrm{Big}=\mathrm{Body}\cup \mathrm{Gap},\qquad
  \mathrm{Body}\cap\mathrm{Gap}=\varnothing
  \]
  が成り立つので、card による加法則：
  \[
  \#\mathrm{Big}=\#\mathrm{Body}+\#\mathrm{Gap}
  \]
  が出た。

これは「#Big = #Body + #Gap」という、あなたの言う **“Big/Body/Gap の構造”** を、完全に Lean の定理として固定した瞬間じゃ。

---

### 4. card を次元 (d) のべきへ畳み、Body を差で表した

あなたが仕上げた補題群で、
\[
\#\mathrm{Big}=(x+u)^d,\quad \#\mathrm{Gap}=u^d
\]
ゆえに
\[
\#\mathrm{Body}=(x+u)^d-u^d
\]
が確定した。

ここまででも「余白を引くと実体が出る」が、次元に依存せず成立する、と解ったわけじゃな。

---

### 5. 差のべき因数分解で “本体は必ず x 倍” が確定した

そして核心。あなたが通した：

\[
(x+u)^d-u^d = x\cdot G(d,x,u)
\]
（幾何和補題を用いた差のべき因数分解）

これと、上の \(\#\mathrm{Body}=(x+u)^d-u^d\) が繋がって、

\[
\boxed{\ \#\mathrm{Body} = x\cdot G(d,x,u)\ }
\]

が Lean 上で確定した。

#### ここで解った“本質”

* Body は「Big から Gap を引いた残り」だが、その濃度は **常に x の倍数**になる。
* つまり、**余白 (u^d) を除いた実体は、必ず x 個ぶんの“層/束”に分解できる**。
* あなたの言葉で言えば
  **「#Body := xG_{d-1}(x,u) が、次元一般化の複雑さの受け皿」**
  が、単なる直観ではなく “定理” になった。

---

### 6. 何が嬉しいか：平面の絵から、次元不変の法則へ

この一連の成果は、単に \((x+u)^d-u^d\) を計算しただけではない。

* **集合（タイル）側**で Big/Body/Gap の分解が成り立ち、
* **数式側**で差のべきが (x) を因数にもつことが証明され、
* その二つが **card を介して完全に一致**した。

ゆえに、あなたの宇宙式は「図の比喩」ではなく、

> **“格子上の有限集合の不変量（card）として成立する、次元 (d) によらない保存則”**

として確立された、ということじゃ。

---

### 7. 次の展望（ここから先に何が乗るか）

ここまでで「無次元化の骨」が通ったので、次は二方向に伸ばせる：

1. **Body の“構成”を改善**
   いまは `sdiff`（差集合）で Body を定義している。
   これを、あなたの本命どおり「軸の最小位置で分類した disjoint union」として **明示構成**に置換すると、
   `x * G` が “数式” ではなく “タイルの実分解” として見えるようになる。

2. **二項係数版 (G_{d-1}) との同値**
   今の `G` は幾何和型。
   二項定理版の
   \[
   \sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}
   \]
   と同値を示すと、あなたの「情報増加＝係数構造」の物語が、そのまま Lean の定理カタログになる。

---

まとめると、こうじゃ：

**“Cell を d 次元へ無次元化しても、Big/Body/Gap の分解保存則は壊れない。
そして Body の濃度は必ず x 倍で、差のべき因数分解がその理由である。”**

これが今回の到達点じゃよ。
リンゴ酒でも開けたい気分じゃの🍎🍷

---

## 二項定理版 G_{d-1} との同値証明

よし……**二項定理との同値まで、Lean が「はい、真」ですと言った**わけじゃな。これは相当でかい。

ここで解ったことを、いまの成果の“意味”が一発で見える形にまとめるぞ。

---

### 今回確定した事実の核

### 1. 同じ差 ((x+u)^d-u^d) が「二つの顔」を持つ

まず、あなたが既に通していた幾何和（差のべき因数分解）版：

\[
(x+u)^d-u^d = x \cdot G(d,x,u)
\]

そして今回、新たに通した二項定理（choose）版：

\[
(x+u)^d-u^d = x \cdot G_{\mathrm{binom}}(d,x,u)
\]

よって、両者は **同じ量を別表現しただけ**だと Lean が確定した：

\[
x\cdot G(d,x,u)=x\cdot G_{\mathrm{binom}}(d,x,u)
\]

さらに (x>0) なら、乗法キャンセルで

\[
G(d,x,u)=G_{\mathrm{binom}}(d,x,u)
\]

まで落ちる。

> つまり **「幾何学的（幾何和）に定義した (G) と、係数論（choose）で定義した (G_{d-1}) は同じもの」**
> が、完全に形式化された。

---

### 2. “情報が増えるのは Body 側” が、係数として固定された

二項定理版の (G_{\mathrm{binom}}) は（本質的に）

\[
G_{\mathrm{binom}}(d,x,u) =
\sum_{k=0}^{d-1} \binom{d}{k+1} x^k u^{d-1-k}
\]

という形をしておる。ここで見えるのは：

* 余白（Gap）は \(u^d\) という **単一の項**
* 実体（Body）は choose が並ぶ **多項の束**

この「Body 側に係数情報が展開される」という直観が、もう比喩ではなく、**定理の形**になった。

---

### 3. しかもこれは “Cell/Finset 宇宙” と直結している

あなたはすでに

\[
\#\mathrm{Body} = (x+u)^d-u^d
\]
\[
\#\mathrm{Body} = x\cdot G(d,x,u)
\]

も通している。

だから今や、**集合（タイル）** の世界で

\[
\boxed{\ \#\mathrm{Body} = x \cdot G_{\mathrm{binom}}(d,x,u)\ }
\]

が確定したことになる。

> つまり「二項係数（choose）は、単なる解析の係数ではなく、
> d次元の箱から余白を引いた“実体タイル”の濃度として現れる」

この接続が今回の最大の収穫じゃ。

---

## いま何が完成したのか（短い総括）

* 無次元 Cell \( \mathrm{Cell}\ d := \mathrm{Fin}\ d\to\mathbb{Z} \) の上で
  Big/Gap/Body を Finset として構成し、
* その card が \((x+u)^d, u^d, (x+u)^d-u^d\) に一致し、
* さらに差のべき因数分解で \(\#\mathrm{Body}\) が必ず (x) 倍で、
* その (G) が二項定理の \(G_{\mathrm{binom}}\) と同値であることまで示せた。

これで、「宇宙式の #Body = xG_{d-1}」が **幾何（箱のタイル）↔ 代数（二項係数）** の両側から、同一物として確立されたわけじゃ。

---

## 次に何が“自然に”言えるか（展望）

ここまで来ると、次の二つはほぼ一本道になる：

1. **Body を差集合ではなく “disjoint union の明示構成” に置換**
   そうすると choose が「分類数」として現れ、係数が“数える構造”として視覚化される。

2. **あなたの (xG_{d-1}(x,u)) を “本体項” として宇宙式一般形へ統合**
   すなわち
   \[
   (x+u)^d = xG_{d-1}(x,u) + u^d
   \]
   を「タイル分解定理」として磨き上げ、2D（トロミノ）を (d=2) 特例として位置づけ直せる。

---

ふふ、ここまで通ると、もはや “二項定理は計算” ではなく、**構造の告白**じゃな。
choose は「増えた情報の個数」そのもの——そしてその増え方が、ぬしの #Body の正体だった。

---

## 次の展開

「この段階の目標」を **“二項定理との同値まで”** と定義するなら――**完了じゃ。OK✅️**
しかも、ただ等式が並んだだけでなく、

* 幾何和（差のべき因数分解）で定義した (G)
* 二項定理（choose）で定義した (G_{\mathrm{binom}})

が **同じ対象**であることを Lean で確定し、さらに

\[
\#\mathrm{Body} = x\cdot G(d,x,u) = x\cdot G_{\mathrm{binom}}(d,x,u)
\]

まで繋がった。ここは “無次元化プランの核心の一つ” が閉じた、と言ってよい。

---

ただし「プロジェクト全体が完了か？」という意味なら、まだ“次の完成度の段”が残る。代表的にはこの2つじゃ：

1. **Body を差集合 `sdiff` ではなく、明示的な disjoint union で構成する**
   　いまは「存在はする」を示した段。次は「どう分かれるか」を構成して、choose が“分類数”として出る姿にする。

2. **2次元（トロミノ）とのリンク定理の格上げ**
   　(d=2) が既存の平面図形・トロミノ世界と同型であることを、必要な範囲で橋渡しして“手本”として確定させる。

---

なので結論はこうじゃ：

* **二項定理同値のタスク：完了**
* **無次元 Cell 宇宙式を「構成的タイル分解」として完成：次の章**

ぬしが「完了」をどちらの意味で言ったかに合わせて、次に進むなら最短コース（disjoint union で Body を作る側）をそのまま書き起こせるぞ。

---

VSCode Style Markdown and \(\LaTeX\) Extensions

This document uses VSCode style markdown with \(\LaTeX\) extensions for mathematical notation. Ensure your markdown viewer supports these features for optimal readability.
