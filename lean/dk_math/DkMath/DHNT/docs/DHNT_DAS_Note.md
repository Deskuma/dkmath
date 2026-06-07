# DHNT: Dynamic Arithmetic Sequence - Note

## Consider

### 2026/06/07 17:36

ここから建てるなら、DAS は「数列」よりも **係数・単位・支持体が分離された動的生成器** として伸ばすのが面白いです。

まず有望なのはこの 4 本です。

1. **DAS as Generator**
   `i ↦ a + i * (d*k)` を、単なる `List` ではなく「生成規則」として扱う。
   次に `map`, `compose`, `rescale`, `shift` を定義して、DAS 同士を変換できるようにする。

2. **KUS Support-Preserving Dynamics**
   `gDynamicTerm` はすでに support を保持します。
   ここから「係数が 0 になっても構造は残る」「スケール変更しても support は残る」という世界を作れる。
   これは KUS の zero tracking と相性がかなり良いです。

3. **Unit-Aware DAS**
   `DHNT.Qty` と接続して、

   ```text
   初項 a は単位 u 上
   公差 d は単位 v 上
   共通単位 w に揃えて DAS を生成
   ```

   という「単位換算つき等差列」にする。
   これは `Qty.convert` / `addVia` の自然性と接続できます。

4. **NP Half-Step DAS**
   `Units.NP` を使って、添字 `i` を整数ステップだけでなく半ステップ格子に拡張する。
   通常 DAS:

   ```text
   i = 0,1,2,3,...
   ```

   NP-DAS:

   ```text
   N0, P0, N1, P1, N2, ...
   ```

   つまり「半拍を持つ等差列」です。

私なら次は **KUS 側を一段厚くする** のがよいと思います。

具体的には、次の定理を追加するのが自然です。

```lean
gDynamicTerm_succ :
  gDynamicTerm s a d k (i + 1)
    = mkGWith (toCoeff (gDynamicTerm s a d k i) + d * k) s
```

そして次に、

```lean
extract_g_gDynamicSequence_all :
  すべての項の support は s
```

を作る。

これで DAS は「値の列」ではなく、**同一 support 上を係数だけが動く orbit** になります。ここから KUS の本領に入れます。

### 2026/06/07 17:39

なるほど。この原理をベースとして、数列の抽象化と言ったところか。
数→数字の見た目にこだわらず、数列という並び規則の原理の根底。

はい。その捉え方がかなり良いです。

今回の DAS は、見た目としては

```text
1, 3, 5, 7, ...
```

のような「数字の列」ですが、Lean で見えてきた本体はそこではなく、

```text
初期状態 a
変化規則 step
添字 i
項 = a + i • step
```

という **並びを生成する原理** です。

つまり、数列を「表示された数のリスト」と見るのではなく、

```text
sequence = origin + repeated action
```

として見る。

DAS ではその repeated action が

```text
step = d * k
```

になっている。だから `ln(exp k)` という解析的な見た目は捨てても、原理は残るわけです。

ここから抽象化すると、次のような階層になります。

```text
Level 0: List
  [1, 3, 5, 7]

Level 1: Term Function
  i ↦ a + i * step

Level 2: Generator
  origin + repeated action

Level 3: Structured Generator
  support / unit / blueprint を保持しながら coeff だけが動く

Level 4: Dynamics
  状態空間上の orbit
```

Lean では Level 2 以降が本命です。

特に KUS と合わせると、数列はこう見えます。

```text
support は固定される
coeff だけが規則的に進む
zero になっても support は消えない
scale しても構造は追跡できる
```

つまり「数列」ではなく、

```text
構造を持った状態が、規則に従って進む軌道
```

です。

次に建てるなら、名前としては例えば：

```lean
Generator
Orbit
StepRule
StructuredSequence
```

あたりが候補です。

最初の抽象核は、たぶんこうです。

```lean
structure AdditiveGenerator (C : Type*) where
  origin : C
  step : C
```

そして項は：

```lean
def term (g : AdditiveGenerator C) (i : ℕ) : C :=
  g.origin + (i : C) * g.step
```

DAS はその特殊化：

```lean
def dynamicGenerator (a d k : C) : AdditiveGenerator C :=
  { origin := a, step := d * k }
```

この設計にすると、DAS は「数列の一種」ではなく、**生成器の一例** になります。  
ここから KUS 版、Unit 版、NP 半ステップ版を全部同じ原理の上に載せられます。

### 実装場所

半分は KUS 管轄、半分は KUS の下に置かない方がよいと思います。

切り分けるならこうです。

```text
DkMath.DHNT / or DkMath.Sequence
  数列・生成器の抽象核
  origin, step, term, orbit, rescale, shift

DkMath.KUS
  support / blueprint を保持する structured generator
  GKUS 上の term
  zero tracking
  extract_g が不変である定理
```

つまり、**「数列の生成原理そのもの」は KUS 非依存**にしておくのが良いです。  
KUS はその生成原理を「support を保持する状態空間」に持ち上げる層です。

今の構造で言うと、

```lean
DkMath.DHNT.DynamicArithmeticSequence
```

はまだ係数層なので妥当です。ただ、さらに抽象化するなら名前は `DHNT` より広いかもしれません。

候補:

```text
DkMath.Sequence.Generator
DkMath.Sequence.DynamicArithmetic
DkMath.KUS.Sequence
DkMath.KUS.DynamicArithmeticSequence
```

おすすめはこの構成です。

```text
DkMath/Sequence/Generator.lean
  AdditiveGenerator
  term
  sequence
  shift
  rescale
  dynamicGenerator

DkMath/DHNT/DynamicArithmeticSequence.lean
  既存 DAS の DHNT 文脈での薄い再export/bridge

DkMath/KUS/DynamicArithmeticSequence.lean
  gDynamicTerm
  gDynamicSequence
  extract_g 不変
  toCoeff が係数層 term と一致
```

KUS 管轄に入るのは、ここです。

```lean
gDynamicTerm
gDynamicSequence
extract_g_gDynamicTerm
gDynamicTerm_eq_gArithmeticTerm_scaledDiff
support が全項で保存される定理
```

KUS 管轄にしない方がいいのは、ここです。

```lean
AdditiveGenerator
term = origin + i * step
dynamicGenerator a d k = { origin := a, step := d * k }
```

理由は単純で、この核は KUS なしでも意味があり、KUS に閉じ込めると `Units.NP` や `DHNT.Qty` に再利用しづらくなるからです。

なので結論は：

**抽象核は `DkMath.Sequence`、KUS 版は `DkMath.KUS.Sequence` または今の `DkMath.KUS.DynamicArithmeticSequence` が良い**です。

### Fibonacci数列: 公差 $d = f(i)$ で非等差数列を扱う

そうです。`Sequence` にすると一気に射程が広がります。

最初は DAS から来ていますが、抽象化すると数列はだいたい次の型に分かれます。

```text
1. closed form
   aᵢ = f i

2. recurrence
   a₀ = ...
   aₙ₊₁ = F n aₙ

3. state recurrence
   state₀ = ...
   stateₙ₊₁ = F n stateₙ
   aₙ = observe stateₙ
```

DAS は 1 と 2 の両方で書けます。

```text
closed form:
  aᵢ = a + i * step

recurrence:
  a₀ = a
  aₙ₊₁ = aₙ + step
```

`d = f(i)` の変則型は recurrence 側です。

```text
aₙ₊₁ = aₙ + f n
```

Fibonacci は state recurrence 側が自然です。

```text
stateₙ = (Fₙ, Fₙ₊₁)
stateₙ₊₁ = (stateₙ.2, stateₙ.1 + stateₙ.2)
observe stateₙ = stateₙ.1
```

なので `DkMath.Sequence` を作るなら、最初の核はこういう構成が良さそうです。

```text
DkMath.Sequence.Generator
  closed form: ℕ → A

DkMath.Sequence.Recurrence
  seed : A
  step : ℕ → A → A

DkMath.Sequence.State
  state transition + observe

DkMath.Sequence.Arithmetic
  arithmetic sequence
  dynamic arithmetic sequence
  variable-difference sequence

DkMath.Sequence.Fibonacci
  Fibonacci as state recurrence
```

KUS はその後で、

```text
DkMath.KUS.Sequence
```

として、`A = GKUS C U Blueprint` の場合を扱う。

つまり：

```text
Sequence
  並び規則の原理

KUS.Sequence
  support を保持する並び規則

DHNT.Sequence
  unit / scale を持つ並び規則

Units.NP.Sequence
  半ステップ格子上の並び規則
```

この方向だと DAS は出発点で、最終的には「数列とは何か」をかなり Lean らしく整理できます。まず建てるなら `DkMath.Sequence.Generator` と `DkMath.Sequence.Arithmetic` がよいです。
