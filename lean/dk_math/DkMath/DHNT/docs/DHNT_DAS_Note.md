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

### 数列から環群体への展望

このプロトタイプDAS構造のテンプレートがあれば、
数列世界の演算→環群体論へ広げられそうです。
まだ、欲張ってそこへは足を突っ込みませんが。

はい、かなり良い足場になりました。

今回の `Sequence` はまだ軽量ですが、構造としてはもう次の拡張に耐えます。

```text
Closed              : ℕ → A
AdditiveGenerator   : origin + i * step
Recurrence          : seed + next
StateRecurrence     : hidden state + observe
```

この 4 つがあるので、将来的には自然に、

```text
sequence の map
sequence の zip/add/mul
pointwise 演算
畳み込み
線形再帰
生成関数
module / group / ring 上の列
KUS support-preserving orbit
```

へ広げられます。

ただ、今の時点では欲張らないのが正解だと思います。まずは DAS 由来の「生成原理」を `Sequence` に切り出せたことが大きいです。KUS 側も `support を固定した係数軌道` として乗っていますし、Fibonacci も `StateRecurrence` で入ったので、世界観の輪郭はできています。

次にやるなら小さく、

```lean
Closed.map
Closed.zipWith
AdditiveGenerator.toRecurrence
```

くらいですね。環・群・体は、その API が自然に必要になったタイミングで載せるのがよさそうです。

### Mul の抽象演算

`d * k` は数値演算の積にとどまらない。

```lean
/-- The homogeneous version of `HMul`: `a * b : α` where `a b : α`. -/
class Mul (α : Type u) where
  /-- `a * b` computes the product of `a` and `b`. See `HMul`. -/
  mul : α → α → α
```

はい、`[Mul C]` を使っている時点で、かなり抽象化済みです。

```lean
def dynamicStep [Mul C] (d k : C) : C :=
  d * k
```

これは「`C` が何であるか」は問わず、`*` が定義されていればよい、という意味です。だから `C` は `ℕ`, `ℤ`, `ℚ`, `ℝ` でもよいし、行列、関数、ある種の作用素でもよいです。

ただし、ここで抽象化されているのは **二項演算としての積** までです。

もう一段抽象化すると、`k` は `C` の元である必要すらなくなります。例えば「係数型 `C` に、スケール型 `K` が作用する」と見るなら、

```lean
def dynamicStep [SMul K C] (d : C) (k : K) : C :=
  k • d
```

になります。

こちらはもっと広いです。

```text
Mul C
  d : C, k : C
  d * k : C

SMul K C
  k : K, d : C
  k • d : C
```

つまり、

```text
Mul C は「同じ世界の中で掛ける」
SMul K C は「外部スケールが係数世界に作用する」
```

です。

DAS の意味を考えると、本当は `SMul` 版の方が概念的にはきれいかもしれません。

```lean
def dynamicStep [SMul K C] (k : K) (d : C) : C :=
  k • d
```

ただし今の

```lean
d * k
```

も悪くありません。理由は、Python 由来の `d * k` という直感に近く、`Semiring C` の中では自然だからです。

今後の拡張としては、こういう二層設計が良さそうです。

```lean
-- 現在の同型スケール
def dynamicStep [Mul C] (d k : C) : C :=
  d * k

-- 将来の外部スケール
def scaledStep [SMul K C] (k : K) (d : C) : C :=
  k • d
```

そして DAS は、

```lean
dynamicGenerator a d k
```

を `scaledStep` ベースに一般化できる。

つまり結論は：

**`Mul C` でかなり抽象化されている。ただし「スケール係数」と「公差」が別世界に属する可能性まで考えるなら、次の抽象化は `SMul K C` です。**

### SMul に向けて

なるほど。早急に手を打つ必要ないですね。素晴らしい。
SMul に備えて、準備する感じでよいか。

外部スケール。異なる数宇宙との接続か。
ここは宇宙式の概念持ち込みで、２つの閉じた宇宙を突き合わせる。
そのような土台が必要なのかもな。

はい、今すぐ `SMul` に置き換えなくていいです。むしろ今は `Mul C` のままにして、設計上だけ「外部スケールに開ける」と見ておくのが良いです。

今の構造はこうです。

```lean
d : C
k : C
d * k : C
```

これは **同じ宇宙 `C` の中でのスケール** です。

次の段階はこうなります。

```lean
d : C
k : K
k • d : C
```

これは **スケール宇宙 `K` が、係数宇宙 `C` に作用する** という見方です。

かなり良い表現をすると、

```text
K : 外部スケール宇宙
C : 係数宇宙
SMul K C : K が C に触れるための接続法則
```

です。

「2つの閉じた宇宙を突き合わせる」という感覚は、Lean 的にはかなり自然にこう表現できます。

```lean
class ScaleAction (K C : Type*) where
  act : K → C → C
```

ただ、Lean にはすでにこれに近い標準構造として

```lean
SMul K C
```

があります。

そして、さらに法則まで欲しくなったら、

```lean
MulAction K C
DistribMulAction K C
Module K C
```

へ進めます。

段階としては：

```text
SMul K C
  ただ作用できる

MulAction K C
  1 • x = x
  (k₁ * k₂) • x = k₁ • (k₂ • x)

DistribMulAction K C
  加法構造を保つ
  k • (x + y) = k • x + k • y

Module K C
  線形空間・加群
```

なので、宇宙式っぽく言うなら：

```text
SMul              接触
MulAction         接触の合成法則
DistribMulAction 係数構造を保つ接触
Module           線形宇宙としての統合
```

今の `dynamicStep d k = d * k` は、同一宇宙内の最小プロトタイプです。  
将来 `SMul` を入れるなら、たぶん名前は `externalDynamicStep` か `scaledStep` がよいです。

```lean
def scaledStep [SMul K C] (k : K) (d : C) : C :=
  k • d
```

そして今の `dynamicStep` は、その特殊ケースとして残せます。

```lean
def dynamicStep [Mul C] (d k : C) : C :=
  d * k
```

このまま進めれば、後で「異なる数宇宙の接続」を追加しても、現在の DAS は壊さずに拡張できます。

### PowerSwap との接続

宇宙式の閉じた世界は (x+u)^d という多次元幾何構造です。
それを１本の軸として並べ替える。だけ。と言ってしまえばそうなのですが…。

この (x+u)^d → n^1 への変換は、DkMath.PowerSwap の世界です。
つまり、異なる宇宙も、いちど互いに型を揃える必要がある。

PowerSwap は a^b = b^a を示しています。
積構造、積演算をこの概念と繋ぐ実装になるかと思います。

積を施した後 xy → z^n と正規化する。新たな宇宙です。

はい。ここで見えているのは、単なる `Mul` 抽象ではなく、もう一段上の構造ですね。

今の DAS は：

```lean
d * k
```

つまり、

```text
同じ宇宙 C の中で積を作る
```

でした。

でも今話している PowerSwap 接続は、

```text
x y という積を作る
→ それを z^n という別宇宙の正規形へ送る
→ その正規形を新しい軸として Sequence 化する
```

という流れです。

かなり自然に分けると、こうです。

```text
Sequence
  並び規則

Mul / SMul
  一つの宇宙内、または外部宇宙からの作用

PowerSwap
  冪宇宙間の交換・正規化

Normalizer / Transport
  xy → z^n のような宇宙変換

KUS
  変換後も support / blueprint を失わない構造保持
```

なので、`d * k` の次に建てるべき抽象はたぶん `SMul` そのものではなく、

```lean
structure PowerNormalize (A B : Type*) where
  sourceMul : A → A → A
  normalize : A → B
```

のような「積後の正規化」層です。

ただし、もっと Lean らしく小さく始めるなら：

```lean
structure NormalizedProduct (A B : Type*) where
  mulForm : A
  normalForm : B
```

または PowerSwap に寄せて：

```lean
structure PowNormalForm where
  base : ℕ
  exponent : ℕ

def eval (p : PowNormalForm) : ℕ :=
  p.base ^ p.exponent
```

そして、

```lean
xy = z^n
```

は

```lean
eval normalForm = x * y
```

として持つ。

これはかなり良いです。なぜなら `PowerSwap.Exchange` にはすでに、

```lean
A = a^t → A^m = a^(t*m)
```

があります。つまり `A` を一度 `a^t` へ正規化できれば、その後の冪操作は指数側の積 `t*m` に移せます。

概念的には：

```text
積の世界:
  x * y

冪の世界:
  z ^ n

PowerSwap:
  冪表現同士の交換・同値

Sequence:
  正規化された冪表現を軸に並べる
```

です。

だから「積を施した後 `xy → z^n` と正規化する。新たな宇宙です」という見方はかなり正しいです。

今すぐ実装するなら、まだ大きな PowerSwap-Sequence 統合には行かず、次の小さな型だけが良いと思います。

```lean
structure PowNormalForm where
  base : ℕ
  exponent : ℕ

def PowNormalForm.eval (p : PowNormalForm) : ℕ :=
  p.base ^ p.exponent

structure HasPowNormalForm (n : ℕ) where
  form : PowNormalForm
  eval_eq : form.eval = n
```

これができると、

```text
xy を作る
xy の PowNormalForm を持つ
その normalForm の exponent 側を Sequence として動かす
```

という橋ができます。

ここは面白いですが、確かに慎重にやる場所です。`Sequence` の次に直接「環群体論」へ行くより、まず `PowerNormalize` / `PowNormalForm` という宇宙変換の薄い中間層を置くのがよさそうです。

### PowerSwap 強化

はい。その順番がよいです。

`Sequence` 側は今の時点で十分な足場があります。ここから無理に `PowerSwap` と接続すると、未成熟な正規化概念を `Sequence` に持ち込んで、両方が重くなります。

先にやるべきは `PowerSwap` の増強です。

具体的には、次の薄い層からが良いです。

```lean
structure PowNormalForm where
  base : ℕ
  exponent : ℕ

def PowNormalForm.eval (p : PowNormalForm) : ℕ :=
  p.base ^ p.exponent
```

次に、

```lean
structure HasPowNormalForm (n : ℕ) where
  form : PowNormalForm
  eval_eq : form.eval = n
```

そして PowerSwap 側に、

```lean
theorem eval_mk (a n : ℕ) :
  PowNormalForm.eval ⟨a, n⟩ = a ^ n

theorem exchange_of_normalized :
  A = a ^ t →
  A ^ m = PowNormalForm.eval ⟨a, t * m⟩
```

のような補題を置く。

これで `PowerSwap.Exchange` の現在の

```lean
A = a^t → A^m = a^(t*m)
```

を、単なる等式補題から「正規形への移送」として見られるようになります。

その後に、

```text
xy の正規形
冪正規形の列
正規形列の KUS support
```

へ進むのが自然です。

つまり順序は：

```text
1. PowerSwap に PowNormalForm を追加
2. exchange_condition を normal-form API に言い換える
3. 積 xy → normal form の保持構造を作る
4. それを Sequence に持ち上げる
5. 必要なら KUS support を載せる
```

です。

今は `Sequence` は触らず、次の工事は [`DkMath.PowerSwap.NormalForm`](/lean/dk_math/DkMath/PowerSwap/NormalForm.lean) あたりがちょうどよいと思います。

### 解説書の整備

少し、解説ドキュメントを書き残しておいたほうが良いかな。
ここまでの作業のメモは取ってあるのだけども。

そもそも何でこんな構造で再解釈して構築しているのか？
だよねぇ…。

発端は DHNT 動的調和数論という概念。
指数対数法則を利用した、異単位調和演算という概念か。
オイラーの等式から得た、無限に分岐する単位。
しかし、それらの異なる単位群も、複素数を通じて束ねて演算ができる。
この原理を、指数対数の法則で行う視点で開発している。

$$
e^{i\pi} = -1 → f(x)=(x+1)^2-x(x+2)=1
$$

この関係は、繋がっている。ということ。

そんな感じの説明からのDASへの繋がり。

[DHNT-DAS-reinterpretation.md](lean/dk_math/DkMath/Sequence/docs/DHNT-DAS-reinterpretation.md)
