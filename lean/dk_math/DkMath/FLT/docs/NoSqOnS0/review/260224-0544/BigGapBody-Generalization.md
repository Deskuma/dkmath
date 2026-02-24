# 一般化アプローチ資料

## Big–Gap–Body 分解による FLT \(d=p\) テンプレート

### 0. 目的（何を一般化するか）

\(p\) を素数（あるいは \(p\ge 3\)）として、自然数 \(a,b,c>0\) に対し

\[
a^p+b^p\ne c^p
\]

を示す。
本資料の狙いは「古典の言葉（Zsigmondy / Cyclotomic / \(p\)-進付値）」に落とし込める一方で、ぬしの宇宙式世界観（Big/GAP/Body/格子）で **読める** 一般化テンプレを与えること。

---

## 1. 物語の核：Big の地図には無い構造は、Gap を除くと出現する

### 1.1 Big（全体宇宙：二項定理そのもの）

\[
(y+u)^p=\sum_{k=0}^{p}\binom{p}{k}y^{p-k}u^k
\]

この座標系（Big）では「二項係数の世界」しか見えない。
ここで重要なのは、**“格子（\(p\) 乗）として整列できるか”**を議論するには、Big をそのまま見ても情報が濃すぎて扱いづらい、という点じゃ。

### 1.2 Gap（核の剥離：差分）

\[
(y+u)^p - y^p
\]

核 \(y^p\) を引いて「変化量」だけを見る。
この差分が、ぬしの言う “Gap を剥がす” 操作の第一段。

### 1.3 Body（内部構造：差分を \(u\) で割る）

\[
GN(p,u,y):=\frac{(y+u)^p-y^p}{u}
\]

すると

\[
(y+u)^p-y^p = u\cdot GN(p,u,y)
\]

となり、「境界 \(u\)」と「内部 \(GN\)」に分かれる。
ここで初めて “Big の地図には無い形” が **Body 側に集約**される。

---

## 2. 格子判定（“整数が居られない” の定式化）

### 2.1 \(p\) 乗格子の条件（付値の合同条件）

整数 \(N\) が \(p\) 乗であるための必要条件は、任意の素数 \(q\) について

\[
v_q(N)\equiv 0 \pmod p
\]

つまり、素因子の指数が \(p\) の倍に揃っていないと “格子を踏めない”。

### 2.2 FLT 仮定を差分へ落とす

仮に

\[
a^p+b^p=c^p
\]

とすると

\[
a^p=c^p-b^p
\]

であり、\(u=c-b,\ y=b\) とおけば

\[
a^p=(b+u)^p-b^p=u\cdot GN(p,u,b)
\]

つまり

\[
a^p = u\cdot GN(p,u,b)
\]

が舞台装置になる。

---

## 3. 勝ち筋テンプレ：原始素因子を Body に刺し、付値の mod \(p\) を壊す

### 3.1 原始素因子（境界に刺さらず差分を刺す）

素数 \(q\) を

- \(q\mid ((b+u)^p-b^p)\)
- \(q\nmid u\)

として取る。これが「境界を避けて刺さる矢」。
（\(p=3\) のときの \(q\nmid(c-b)\) がこれ。）

このとき必ず

\[
q\mid GN(p,u,b)
\]

が従う（積の割り算）。

### 3.2 付値の上界（NoLift / NoPow：Body の深刺し禁止）

ここが本丸。狙いは

\[
0 < v_q(GN(p,u,b)) < p
\]

特に最強は \(v_q(GN)=1\)。
これが出れば

\[
v_q(a^p)=v_q(u)+v_q(GN)=0+1=1
\]

となり、左辺は \(p\) 乗なので \(v_q(a^p)\) は \(p\) の倍であるべきなのに矛盾。
つまり「格子が踏めない」が発火する。

**ここで \(q^2\) が出た理由**は単に \(v_q(GN)\le 1\) を言いたい最小閾値だからで、次元の話ではない。
ただし一般化では \(v_q(GN)<p\) を言えれば十分、という形に上書きできる。

---

## 4. 実装（Lean）としてのテンプレ設計

### 4.1 型（入力仕様）を先に固定して、証明を“差し替え可能”にする

`NoSqOnS0` が良い設計だったのと同じで、一般 \(p\) 版もまず **入力仕様**を作る。

例：Body 側の “深刺し禁止” を要求する仕様（雛形）

\[
\text{NoPowOnGN}(p,u,b) :=
\forall q,\ \text{Prime }q \to q\mid((b+u)^p-b^p)\to q\nmid u \to \neg q^p \mid GN(p,u,b)
\]

あるいはより実用的に（上界を直接）

\[
\text{ValUpperOnGN}(p,u,b) :=
\forall q,\ \text{Prime }q \to q\mid((b+u)^p-b^p)\to q\nmid u \to v_q(GN(p,u,b)) \le p-1
\]

そして本体定理は「この入力さえあれば倒せる」にする：

- **テンプレ本体（証明の骨格を固定）**
  - 原始素因子 \(q\) を取る（存在補題）
  - \(q\mid GN\) を得る（bridge）
  - \(v_q(a^p)\ge p\)（下界）
  - \(v_q(a^p)=v_q(u)+v_q(GN)\le 0+(p-1)\)（上界）
  - \(p\le p-1\) で矛盾

ここまでを `FLT_dp_by_padicValNat_template` として先に固めるのが最短。

### 4.2 補題チェーン（一般 \(p\) 版の最小セット）

**層A：原始素因子の存在**

- `exists_prime_factor_pow_diff`（Zsigmondy/Cyclotomic 由来）
  - \(q\mid((b+u)^p-b^p)\) かつ \(q\nmid u\)

**層B：宇宙式 bridge（Big→Body）**

- `sub_eq_mul_GN`：\((b+u)^p-b^p=u\cdot GN(p,u,b)\)
- `prime_dvd_GN_of_dvd_sub_not_dvd_left`：原始なら \(q\mid GN\)

**層C：付値の上下界**

- 下界：`padicValNat_lower_bound_of_dvd_dp`（\(q\mid a^p\Rightarrow v_q(a^p)\ge p\)）
- 上界：`padicValNat_upper_bound_dp`（入力仕様から \(v_q(GN)\le p-1\)）

**層D：矛盾**

- `omega` で締める

### 4.3 供給すべき“難所”は一箇所に押し込む

`NoSqOnS0` のときと同じく、一般化の難所は

- 原始素因子の存在（Zsigmondy/Cyclotomic）
- \(v_q(GN)\) の上界（NoLift/LTE 排除）

のどちらか、あるいは両方。

テンプレ本体を固めれば、以後は「入力供給の研究」だけに集中できる。これは開発効率が爆上がりする。

---

## 5. 研究ロードマップ（実務的な進め方）

### Step 1：`GN` の一般 \(p\) 版テンプレ定理を作る（先に骨格を固定）

- 既存の `FLT_d3_by_padicValNat` の骨格をコピーして
- `3` を `p` に抽象化
- 上界側は “仮定として受け取る” 形にする（`ValUpperOnGN` 等）

### Step 2：原始素因子の存在を “インターフェース化” する

- `exists_prime_factor_cube_diff` の一般版（または `Prime p` 前提版）へ
- 例外管理を分離（\(p\mid(b+u)\) 的な例外、古典 Zsigmondy の例外集合など）

### Step 3：NoSq/NoPow 供給理論を分岐で実装

- (A) Cyclotomic 経由（円分多項式の既約性・原始素因子）
- (B) LTE 排除の条件整理（“持ち上がり”が起きる場合を分類して潰す）
- (C) ぬしの phase / harmonic envelope を「禁止領域」として供給（研究色が最も出る）

### Step 4：論文の演出（ぬしの世界観で読ませる）

- Big（全体）→ Gap（剥離）→ Body（内部）→ 格子判定（付値 mod \(p\)）
この4段を図にして、テンプレ本体の説明をここに沿わせる。

---

## 6. “ドラマの一文”としてのまとめ（論文向け）
>
> **Big（\((b+u)^p\)）は二項係数の世界で、格子整列の本質を隠す。**
> **核 \(b^p\) を引いて Gap を剥がし、さらに \(u\) で割ると Body \(GN(p,u,b)\) が露出する。**
> **原始素因子は境界 \(u\) を避けて Body に刺さる。**
> **Body の付値が \(p\) の倍に整列できない（\(0<v_q(GN)<p\)）瞬間、全体は \(p\) 乗格子を踏めず矛盾し、整数解は消滅する。**

---

## 付録：今後の命名案（読みやすさのため）

- Big polynomial：\(\mathrm{Big}_p(u,y)=(y+u)^p\)
- Gap：\(\mathrm{Gap}_p(u,y)=(y+u)^p-y^p\)
- Body：\(\mathrm{Body}_p(u,y)=GN(p,u,y)\)
- Lattice obstruction：\(\exists q,\ v_q(u\cdot GN)\not\equiv 0\pmod p\)

---
