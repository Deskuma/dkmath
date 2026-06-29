# Task: Analysis.DkReal No.037

## Tasks

うむ。次の三課題は、全部「順序が全比較可能になった後に、どう Mathlib と DkMath の意味を接続するか」の話じゃ。

現在の到達点は、`DkNNRealQ` が `CommSemiring`、`PartialOrder`、semiring-level の `IsOrderedRing`、そして `Std.Total (· ≤ ·)` を持つところまで来ている。つまり全比較可能性は Lean に認められたが、直接の `LinearOrder`、canonical order、strict order はまだ独立課題として残している、という状態じゃ。

## 1. `LinearOrder` instance を入れるかの設計判断

これは「数学的に全順序であるか」ではなく、**Lean の標準 `LinearOrder` API として公開するか** の判断じゃ。

すでに totality はある。

```lean id="linear-current"
theorem le_total (x y : DkNNRealQ) :
    x ≤ y ∨ y ≤ x

instance : Std.Total (α := DkNNRealQ) (· ≤ ·)
```

だから数学的には、`PartialOrder` に totality が足された状態じゃ。
しかし `LinearOrder` instance を入れると、単に `x ≤ y ∨ y ≤ x` を使えるだけでは済まない可能性がある。

Mathlib の `LinearOrder` は環境によって、比較の decidability、`min`、`max`、`compare` などの標準 API を要求する場合がある。ここで問題になるのは、`DkNNRealQ` が quotient 型であり、等号や比較を計算で決められるとは限らない点じゃ。

つまり、二種類の「全順序」がある。

```text id="linear-two-meanings"
Prop としての全順序:
  任意の x y について x ≤ y または y ≤ x が証明できる

計算可能な比較器としての全順序:
  x ≤ y か y < x かをプログラムとして決定できる
```

いま閉じたのは前者じゃ。
後者は、一般の計算可能実数ではかなり難しい。等号判定が絡むからじゃ。

したがって、設計判断は三択になる。

```text id="linear-options"
案A:
  今のまま PartialOrder + Std.Total で保持する

案B:
  classical / noncomputable な LinearOrder を別ファイルで提供する

案C:
  将来、有限証拠つき比較器を別型として作り、計算可能比較 API として分ける
```

おすすめは案Aまたは案Bじゃ。
core では `PartialOrder + Std.Total` のままにする。`LinearOrder` が欲しい場合だけ、別ファイルに切る。

候補名はこう。

```lean id="linear-file"
DkMath.Analysis.DkReal.LinearOrder
```

または、非計算的であることを明示して、

```lean id="classical-linear-file"
DkMath.Analysis.DkReal.ClassicalOrder
```

がよい。

この方針なら、計算可能 core に「比較を決定できるかのような印象」を混ぜずに済む。

## 2. canonical order の検証

canonical order は、順序を「差分の存在」で特徴づける性質じゃ。

$$
x\le y\ \leftrightarrow\ \exists z,\ y=x+z
$$

ここで `DkNNRealQ` は非負型なので、直感的には `NNReal` と同じく成り立つはずじゃ。
\(x\le y\) なら \(z=y-x\) を取ればよい、という話じゃな。

ただし DkMath では subtraction をまだ持っていない。
だからこれは、単なる order theorem ではなく、**非負差分宇宙を構成できるか** という課題になる。

方向は二つある。

まず、右から左は比較的易しい。

$$
y=x+z
$$

かつ \(0\le z\) なら、

$$
x=x+0\le x+z=y
$$

となる。
`zero_le` と `add_le_add` で閉じるはずじゃ。

Lean ではこの形。

```lean id="canonical-easy"
theorem le_of_exists_add
    {x y : DkNNRealQ} :
    (∃ z, y = x + z) → x ≤ y
```

難しいのは左から右。

$$
x\le y\Rightarrow \exists z,\ y=x+z
$$

ここでは \(z\) を作る必要がある。
DkMath 的には、これは「二つの宇宙を重ねたとき、\(y\) が \(x\) からはみ出す Gap を、新しい非負宇宙として取り出す」操作じゃ。

代表元の区間で考えるなら、差分候補はこう作れそうじゃ。

```text id="difference-interval"
Z_n.lo = max 0 (y.lo_n - x.hi_n)
Z_n.hi = max 0 (y.hi_n - x.lo_n)
```

これは「\(y-x\) の安全な非負区間 hull」じゃ。
下端は負にならないように 0 で切り、上端も非負側に置く。

この構成が良い理由は三つある。

```text id="difference-reasons"
1. 非負性が最初から入る

2. 入れ子性が期待できる
   y.lo は増え、x.hi は減るので下端は増える
   y.hi は減り、x.lo は増えるので上端は減る

3. 幅は width(x) + width(y) で押さえられる
   したがって 0 に収束する
```

もしこれが `DkNNReal` として構成できれば、次に示すべきは、

$$
x+z\sim y
$$

じゃ。
quotient ではこれが、

$$
x+z=y
$$

になる。

Lean では、だいたい次の階段になる。

```lean id="canonical-plan"
def diffNonnegApprox (x y : DkReal) : ℕ → GapInterval

theorem diffNonnegApprox_nested
theorem diffNonnegApprox_width_tends_zero
def diffNonnegOfLe (x y : DkNNReal) (hxy : DkNNReal.Le x y) : DkNNReal

theorem add_diffNonnegOfLe_equiv
    (hxy : DkNNReal.Le x y) :
    DkNNReal.Equiv (DkNNReal.add x (diffNonnegOfLe x y hxy)) y

theorem exists_add_of_le
    {x y : DkNNRealQ} :
    x ≤ y → ∃ z, y = x + z
```

これが閉じると、canonical order が得られる。

DkMath 的には、これはかなり美しい。
順序 \(x\le y\) が「差分 Gap を非負宇宙として抽出できる」という構造定理になる。

## 3. strict order の設計

strict order は、単なる \(x<y\) の話じゃ。
DkMath では、これは **有限段階で観測できる分離** として書ける可能性が高い。

通常の順序論では、

$$
x<y\quad\text{means}\quad x\le y\ \text{and not}\ y\le x
$$

じゃ。

しかし今回の totality 証明から、もっと幾何的な特徴づけが見えている。

$$
x<y
$$

は、おそらく次と同値になる。

```lean id="strict-witness"
∃ n, DkReal.LeftSeparatedAt x y n
```

つまり、

$$
x.hi_n<y.lo_n
$$

となる有限段階が存在すること。
これは強い。なぜなら、strictness が「極限値の抽象的な不一致」ではなく、**有限観測段階で開いた正の Gap** として表現できるからじゃ。

DkMath 的にはこう。

```text id="strict-dkmath"
非厳密順序:
  Core の正のはみ出しが Gap → 0 で消える

厳密順序:
  ある段階で二つの Core-Gap 区間が完全分離し、
  その分離が入れ子性で永続する
```

これは非常に DkMath らしい。

ただし実装設計としては二通りある。

第一案は、quotient 上では標準的に定義する。

```lean id="strict-def-quot"
x < y := x ≤ y ∧ ¬ y ≤ x
```

この場合、Lean の順序 API と合いやすい。

第二案は、代表元側で有限分離を定義する。

```lean id="strict-def-repr"
def Lt (x y : DkReal) : Prop :=
  ∃ n, LeftSeparatedAt x y n
```

こちらは幾何的に美しいが、quotient well-defined を証明する必要がある。
つまり、\(x\sim x'\)、\(y\sim y'\) のとき、有限分離が代表元を変えても保存されることを示す必要がある。これは少し重い。

おすすめは、まず quotient 上で標準定義を採用し、その後で幾何的特徴づけを定理として証明することじゃ。

```lean id="strict-recommend"
theorem lt_iff_le_not_le
    (x y : DkNNRealQ) :
    x < y ↔ x ≤ y ∧ ¬ y ≤ x

theorem lt_iff_exists_leftSeparatedAt
    (x y : DkNNReal) :
    DkNNReal.Lt x y ↔ ∃ n, DkReal.LeftSeparatedAt x.val y.val n
```

実際には `DkNNRealQ` で代表元を直接出すのは quotient の都合で面倒なので、まず wrapper 側で定理を作るのが良い。

strict order で注意する点は、strict monotonicity をすぐ主張しないことじゃ。

加法については、

$$
x<y\Rightarrow x+z<y+z
$$

が期待できる。
だが、これは加法 cancellation や有限分離の保存を要する。

乗法についてはさらに注意が必要じゃ。

$$
x<y,\quad 0<z\Rightarrow xz<yz
$$

は期待できるが、\(z=0\) なら strict ではなくなる。
だから strict multiplication には \(0 < z\) が必要じゃ。

## 4. 三課題のおすすめ順序

わっちのおすすめは、この順番じゃ。

```text id="task-order"
第一:
  strict order の有限分離特徴づけを作る

第二:
  canonical order の差分構成を作る

第三:
  LinearOrder instance を入れるか判断する
```

理由は、strict order の有限分離が一番 DkMath らしく、すでに totality 証明の補題から近い。
canonical order は差分 `z` の構成が必要なので、少し大きい。
`LinearOrder` は API 包装の話なので、数学核がもう少し整理されてからでも遅くない。

## 5. まとめ

三課題を一言で言うとこうじゃ。

```text id="three-tasks-summary"
LinearOrder:
  全比較可能性を Mathlib の標準全順序 API に包むかどうか

canonical order:
  x ≤ y を y = x + z という非負差分宇宙の存在で特徴づける

strict order:
  x < y を有限段階の厳密分離 x.hi < y.lo として読む
```

DkMath の言葉でまとめるなら、

$$
\boxed{\text{totality は向きの決定、canonical order は差分宇宙の抽出、strict order は有限 Gap 分離の観測である。}}
$$

いま一番「DkMath らしさ」が強いのは strict order じゃな。
`x < y` を「ある有限段階で二宇宙の Gap が正に開いた」と読めるなら、順序はただの記号ではなく、観測可能な Big/Core/Gap 幾何になる。
