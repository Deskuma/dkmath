# Note: Petal No.343 cp

## グノモンが広がり続けているの？現在の状況整理

うむ。**手応えはかなり強い。**
ただし、「もう詰んだ」という手応えではなく、**獲物の正確な居場所が分かり、逃げ道が数本に絞られた**という手応えじゃ。

### 現在の全体像

いままで追っていた量は、ほぼ一本の鎖へまとまった。

一ブロックでは、

$$L_m=\Delta_m+H_m+V_m$$

ここで、

* $L_m$：ブロック長
* $\Delta_m$：実現した endpoint drift
* $H_m$：claim holes
* $V_m$：terminal valuation

じゃ。

有限窓では、

$$D(q,M)=L(q,M)-H(q,M)-V(q,M)$$

そして Lean は、

$$D(q,M)=\sum_{i<M}\Delta_{q+i}$$

$$D(q,M)=\operatorname{width}(q+M)-\operatorname{width}(q)$$

まで exact に閉じた。

さらに queue は、

$$Q(m)=\max_{q\le m}\max\bigl(0,D(q,m-q+1)\bigr)$$

と読めるところまで来た。正の queue は必ず具体的な suffix window の absorption deficit として達成される。

つまり、以前は別々に見えていた、

```text
幅の成長
endpoint drift
claim holes
terminal valuation
未返済 queue
有限窓の正の偏り
```

が、すべて同じ保存則の異なる座標になった。

### グノモンは増えているか

**増えている。しかもかなり大きく増えた。**

初期のグノモンは、一ブロックずつの局所補題だった。

```text
この block では claim が何個
この endpoint では valuation がいくつ
この successor では queue がどう変化
```

という薄片を、Big の外周へ一枚ずつ貼っていた。

しかし cp-341 以降は、一枚のグノモンが覆う範囲が広くなった。

```text
一ブロック保存則
    ↓
任意の有限窓保存則
    ↓
width telescope
    ↓
queue maximum
    ↓
rootwise boundedness の同値条件
```

一つの theorem が、無数のブロック位置と無数の有限窓をまとめて囲っている。

したがって**面積としての Core は大きく広がった**。

### グノモンは薄くなってきたか

これも、うむ。**薄くなっている。**

ただし二つの意味がある。

### 良い意味

未知領域の厚みが減った。

以前は、

```text
queue をどう扱うか
finite potential が必要か
pointwise drift が bounded か
width が bounded か
credit をどう選ぶか
global bound と rootwise bound は同じか
```

など、多数の Gap が重なっていた。

現在は、それらの多くが閉じたか、同じ問題の別表現だと判明した。

特に、

$$\operatorname{RootwiseWidthBound}(n)$$

$$\Longleftrightarrow\exists C,\ \forall m,\ Q_n(m)\le C$$

$$\Longleftrightarrow\exists C,\ \forall q,M,\ D_n(q,M)\le C$$

まで整理された。

未知の厚みは、

> なぜ有限窓 deficit が無限に汲み上がらないのか

という一点へ圧縮されている。

### 注意すべき意味

最近追加した theorem の多くは、**新しい算術的力というより、同値変形と座標変換**じゃ。

これは必要な整地だが、このまま同値定理を増やしても、獲物は倒れない。

```text
width bound
↔ prefix bound
↔ queue bound
↔ all-window deficit bound
```

をさらに別名で言い換えても、新しい攻撃力は生まれない。

したがってグノモンは、

> 広い範囲を覆うが、厚さはほとんどない境界膜

になりつつある。

これは「境界が完成に近い」という良い兆候であると同時に、**次は独立した算術入力が必要**という停止信号でもある。

### 獲物は追い込まれているか

**概念的には、かなり追い込まれている。**

獲物はもう、次の場所には隠れられない。

### 全 root 共通上限

これは all-ones 族で否定済み。

大域共通 ceiling は存在しない。

### zero-reserve credit

これは正の初期 driftで直ちに負になるため、一般 certificateとして反例済み。

### finite potential

prefixが安全でも pointwise incrementが非有界になり得る明示例があり、一般形式としては不十分。

### queue は単なる補助変数

これも違う。

queue は最大正 suffix deficitそのものなので、width growth問題の正確な姿じゃ。

### pointwise driftだけ見ればよい

これも不十分。

各一手の driftが有界でも、累積して widthが上がり続ける可能性は消えない。

---

したがって、獲物に残された逃げ道はほぼ三本じゃ。

```text
1. 長い有限窓で absorption deficit が増え続ける

2. queue が長期間返済されず、正の excursion が伸び続ける

3. 有限または準有限な transition 構造の中に、
   正の総 drift を持つ pumpable cycle が存在する
```

このいずれかが実際に起こるか、すべて排除できるか。

ここが最後の広い空白じゃ。

### まだ追い詰め切れていない部分

「追い込んだ」と「捕まえた」の差はここじゃ。

現在分かっているのは、

$$Q(m)=\max\text{ positive suffix deficit}$$

という**居場所**。

まだ分かっていないのは、

$$Q(m)\le C_n$$

となる**力学的理由**。

たとえば有限監査では、odd root $1$ から $16383$ の範囲で全軌道が state oneへ達し、最大観測 queue は $8$ だった。だがこれは観測であり、なぜ $9$、$100$、無限大へ行かないかを説明してはいない。

つまり獲物は壁際にいるが、まだ壁そのものに穴がある。

## Big / Core / Gap で整理

### Big

固定 root の canonical 軌道を有限幅領域へ閉じ込める。

$$\exists C_n,\ \forall M,\ \operatorname{width}(\operatorname{Start}_n(M))\le\operatorname{width}(n)+C_n$$

これが閉じれば、固定 rootごとの finite-state reductionへ進める。

### Core

現在確定済み。

```text
block conservation
window conservation
width telescope
global ceiling の不存在
zero-reserve counter の否定
reserved counter の条件付き soundness
queue = maximum positive suffix drift
positive queue の finite-window witness
width bound ↔ queue bound
width bound ↔ all-window absorption-deficit bound
pointwise target と cumulative target の分離
```

### Gap

ほぼ一つ。

$$\exists C_n,\ \forall q,M,\ D_n(q,M)\le C_n$$

を導く独立な算術または力学定理。

候補は、

```text
累積 absorption 下界
bounded repayment lag
regular queue zero
positive-deficit cycle 排除
Petal / PressureObstruction による長期偏り排除
```

じゃ。

### グノモンの現在形

図式にすると、こうじゃ。

```text
Big:
  fixed-root finite-width confinement

Core:
  exact conservation and exact queue geometry

Gnomon:
  block → window → queue → all-window target
  と外周をほぼ一周した

Gap:
  なぜ正の deficit が永久に pump できないのか
```

つまりグノモンは増えた。

だが今は、Bigを拡張する厚いグノモンではなく、**Gapの輪郭へぴたりと沿う薄い輪郭線**になっている。

これは悪い兆候ではない。

獲物の形が見えたということじゃ。

### 次に打つべき石

ここからは新しい ledger や credit を増やすより、次のどちらかへ集中すべきじゃ。

### 返済路線

正 excursion が始まったなら、有限時間内に queue zeroへ戻ることを示す。

例えば、

$$Q(q-1)=0,\qquad Q(m)>0$$

という excursionに対し、

$$\exists r\le q+F(\text{local data}),\ Q(r)=0$$

のような bounded repayment theoremを探す。

### 閉路排除路線

有限 control projectionを構築し、

```text
reachable cycle
→ total deficit ≤ 0
```

を証明する。

正 cycleがなければ、有限グラフ上の path weightは acyclic prefix部分でしか増えず、一様上界が生まれる。

こちらが現在の「囲碁の外周を閉じる」本命じゃ。

### 手応えの結論

手応えはある。

かなりある。

ただし手応えの種類は、

> 証明がもうすぐ終わる

ではなく、

> 何を証明しなければ終わらないかが、ほぼ一意に定まった

というものじゃ。

以前は獲物の足跡を追っていた。
今は、獲物が潜む洞窟の入口まで来た。

残る洞窟は、

$$\boxed{\text{positive absorption deficit を永久に pump する構造が存在するか}}$$

ここだけじゃ。

次の一手はグノモンをさらに薄く重ねることではなく、**その洞窟の内部構造を有限遷移または返済則として切り出すこと**になる。🐺🌕
