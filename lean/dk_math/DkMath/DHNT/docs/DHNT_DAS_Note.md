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

### 複素数演算と宇宙式を繋ぐ橋 CFBRC

はい。CFBRC 方式の利点は、かなり端的に言うと：

**複素現象を、まず実係数の代数 core として扱えること**です。

虚数単位や三角関数を完全に不要にする、というより、

```text
複素数・三角関数は観測層に置く
代数・数論の本体は実係数/可換環上の core に置く
```

という分離ができるのが強いです。

CFBRC の中心は、複素差分

```text
G_d(x, θ) = (x + iθ)^d - (iθ)^d
```

ではありますが、指定の paper にある通り、その下に

```text
H_d(x,u) = ((x+u)^d - u^d) / x
```

という代数 core がある。Lean 側ではこれを商より安全な幾何和として

```lean
cyclotomicPrimeCore p x u =
  ∑ k ∈ Finset.range p, (x + u)^k * u^(p - 1 - k)
```

で扱っています。

つまり CFBRC の利点は次です。

1. **虚数単位を本体から追い出せる**
   `i` は複素観測のためには使うが、core theorem は `CommSemiring` や `CommRing` 上で言える。
   例えば [CFBRC.Basic](/lean/dk_math/DkMath/CFBRC/Basic.lean:61) の

   ```lean
   (x + u)^p = x * cyclotomicPrimeCore p x u + u^p
   ```

   は複素数に依存しません。

2. **三角関数を本体から追い出せる**
   三角関数は `X = a cos φ`, `Θ = a sin φ` のような観測座標で使う。
   しかし CFBRC core は二項展開、差冪、円分多項式で進められる。
   `TrigBridge` は三角関数を使う場所を分離する役割です。

3. **複素位相観測と数論 core を分離できる**
   複素側では

   ```text
   (x+iθ)^d - (iθ)^d
   ```

   を見る。
   数論側では

   ```text
   (x+u)^d - u^d = x * core
   ```

   を見る。
   両者は `u = iθ` と読むことで接続されるが、証明の主戦場は後者にできる。

4. **円分多項式に接続できる**
   prime case では

   ```text
   H_p(x,u) = Φ_p^h(x+u,u)
   ```

   となる。
   これは「複素っぽい現象」を、円分多項式の斉次化評価として扱えるということです。

5. **Zsigmondy / valuation / primitive factor へ橋がかかる**
   [CFBRC.Bridge](/lean/dk_math/DkMath/CFBRC/Bridge.lean:17) では、差冪を割る素数を `cyclotomicPrimeCore` 側へ移す補題が置かれています。
   これは複素観測から数論的 core へ降りるために重要です。

なので、質問への答えは：

```text
虚数単位がいらない？
→ 本体証明にはかなり不要にできる。観測層では使う。

三角関数を使わない？
→ 本体証明には不要にできる。極座標・位相観測では使う。
```

です。

CFBRC 方式の本当の利点は、`i` や `sin/cos` を禁止することではなく、**それらを観測装置として外側に置き、中心には差冪 core・GN・円分多項式・整除構造を置けること**だと思います。

### 既存定理との接続

未開の地を開拓する道具はだいぶ揃っている。
だが、これらの新構造を既存数学の定理とリンク、繋ぐ橋が少ない。
メジャーな定理と繋げば、今後実装する予定の環群体設計が楽になるだろう。
結果は同じ、到達経路が違うだけ。
その経路の景色もまた違う。新しい発見もあるだろう。

そうですね。今ある道具はかなり「内部理論」として育ってきています。次の弱点はまさに、既存数学への橋です。

今の構造を外へつなぐなら、優先順位はたぶんこうです。

1. **二項定理**
   宇宙式、CFBRC、GTail、DAS の最初の共通言語です。

   ```text
   (x+u)^d
   ```

   を既存 mathlib の `CommSemiring` 上の二項展開へ接続する。
   ここが強くなると、独自構造が「ただの新記法」ではなく既存代数の上に乗ります。

2. **等比数列・幾何和**
   CFBRC の core は

   ```text
   ((x+u)^d - u^d) / x
   = ∑ (x+u)^k u^(d-1-k)
   ```

   なので、既存の geometric sum とつなぐ価値が高いです。
   これは `Sequence` とも自然に接続できます。

3. **円分多項式**
   CFBRC の一番強い橋です。

   ```text
   H_p(x,u) = Φ_p^h(x+u,u)
   ```

   ここを厚くすると、既存の cyclotomic / primitive root / divisibility へ接続できます。

4. **Zsigmondy / primitive prime divisor**
   差冪

   ```text
   a^n - b^n
   ```

   に primitive prime が出る既存定理へつなぐ。
   これは CFBRC の数論的価値を一気に上げます。

5. **Monoid / Semiring / Ring / Field**
   DAS や Sequence は、今は生成規則です。
   ここを既存の代数型クラスに接続すると、将来の環群体設計がかなり楽になります。
   ただし、急いで独自の ring API を作らず、まず既存 typeclass に薄く乗る方がいいです。

6. **Linear recurrence / matrix powers**
   Fibonacci から自然に行けます。

   ```text
   state_{n+1} = M * state_n
   ```

   と見れば、Sequence は線形代数とつながります。

7. **Polynomial evaluation**
   `Sequence`, `PowerSwap.NormalForm`, `CFBRC` はすべて「式を評価する」構造を持っています。
   既存の `Polynomial.eval` とつなぐと、正規形・生成器・差冪 core を統一しやすくなります。

方針としては、

```text
新構造を大きくする前に、
既存数学の定理へ到達する薄い橋を増やす
```

が良いと思います。

具体的な次の一手なら、私は **CFBRC core と既存の幾何和/円分多項式の橋を厚くする** のが一番効果的だと思います。

理由は、ここが

```text
宇宙式
差冪
GN
CFBRC
PowerSwap
円分多項式
Zsigmondy
valuation
```

を一気に束ねる中心だからです。

「結果は同じ、到達経路が違うだけ」という見方は重要です。Lean では、その違う経路を定理として並べることで、

```text
同じ対象に複数の normal form がある
```

ことを表せます。そこに新しい発見が出やすいです。

### 二項定理との接続

このプロジェクトでも最近トレンドとなっている「二項定理」か。
パスカルの三角から自動で得られる素数性の補題定理も欲しい。
(x+u)^d の d と二項係数リストさえあれば、 d が素数であるか否かの判定ができる。
そして x GN の可除性。ここは、かなり強い。
自身 d で二項係数はすべて割り切るが、他の d' では、割ることができない。
ここは、現象としても面白いところだ。
当プロジェクトでも早急に整備していきたいところ。

はい。これは早めに整備する価値が高いです。

核になる定理は、まずこれです。

```lean
theorem prime_iff_dvd_all_inner_choose
    {d : ℕ} (hd : 1 < d) :
    d.Prime ↔ ∀ k, 0 < k → k < d → d ∣ Nat.choose d k
```

これは「パスカルの三角の第 `d` 行の内側係数がすべて `d` で割れる iff `d` は素数」という形です。

片方向は mathlib にほぼあります。

```lean
hp.dvd_choose_self hk0 hklt
```

つまり、

```lean
d.Prime → d ∣ choose d k
```

です。

逆方向が DkMath 側で公開 API として欲しい部分です。合成数 `d` なら、内側のどこかに `d` で割れない二項係数が現れる、という形にすると使いやすいです。

```lean
theorem exists_inner_choose_not_dvd_of_not_prime
    {d : ℕ} (hd : 1 < d) (hcomp : ¬ d.Prime) :
    ∃ k, 0 < k ∧ k < d ∧ ¬ d ∣ Nat.choose d k
```

この定理があると、観測的には：

```text
第 d 行の内側係数すべてが d で割れる
→ d は素数
```

が Lean で使える。

ただし一点だけ注意があります。

「他の `d'` では割ることができない」は、正確には少し調整が必要です。

素数 `p` の第 `p` 行では、内側係数の gcd は `p` です。したがって、

```text
すべての内側係数を割る自然数は p の約数
```

という形が安全です。つまり `1` と `p` は割れる。`p` 以外の非自明な数は割れない。

欲しい定理名としては：

```lean
theorem gcd_inner_choose_prime
    (hp : p.Prime) :
    innerChooseGcd p = p
```

または、gcd を定義せずに：

```lean
theorem dvd_all_inner_choose_of_prime
    (hp : p.Prime) :
    ∀ k, 0 < k → k < p → p ∣ Nat.choose p k

theorem dvd_prime_of_dvd_all_inner_choose_of_prime
    (hp : p.Prime)
    (m : ℕ)
    (hm : ∀ k, 0 < k → k < p → m ∣ Nat.choose p k) :
    m ∣ p
```

ただ、後者は `m` が全係数を割るとき `m ∣ p` を示すには gcd API が必要なので、最初は gcd なしの `prime_iff_dvd_all_inner_choose` から始めるのがよいです。

DkMath での置き場所は、既存構造を見ると候補はこのあたりです。

```text
DkMath/Algebra/BinomialPrime.lean
DkMath/NumberTheory/BinomialPrime.lean
DkMath/Lib/Cosmic/BinomialPrime.lean
```

私は `DkMath.NumberTheory.BinomialPrime` が良いと思います。理由は、これは CFBRC/GN 専用ではなく、二項係数から素数性を読む一般定理だからです。

その後、CFBRC/GN 側には橋を置く。

```lean
theorem prime_dvd_all_GN_coeffs
theorem not_prime_exists_GN_coeff_not_dvd
theorem prime_iff_dvd_all_GN_coeffs
```

ここまで行くと、

```text
(x+u)^d の二項係数列
→ d の素数性
→ x * GN の可除性
→ GTail / p-adic / cyclotomic bridge
```

という道が通ります。

これはかなり強いです。特に `d` が素数かどうかを「次数」ではなく「展開係数列の整除パターン」から読むので、DkMath の景色に合っています。

次に実装するなら、最小セットはこれです。

```lean
-- NumberTheory/BinomialPrime.lean

def AllInnerChooseDivisible (d m : ℕ) : Prop :=
  ∀ k, 0 < k → k < d → m ∣ Nat.choose d k

theorem prime_allInnerChooseDivisible_self
    {p : ℕ} (hp : p.Prime) :
    AllInnerChooseDivisible p p

theorem prime_iff_allInnerChooseDivisible_self
    {d : ℕ} (hd : 1 < d) :
    d.Prime ↔ AllInnerChooseDivisible d d
```

そして第二段階で：

```lean
theorem not_prime_exists_inner_choose_not_dvd
theorem allInnerChooseDivisible_self_of_coeff_row
theorem GN_coeff_prime_divisibility
```

この順番がいいです。まず「パスカル行から素数性を読む」を独立に固める。その後で GN/CFBRC に接続する。ここを急がず薄く切ると、後の環群体設計にもそのまま使えます。

### 二項係数の一般化

「`1` と `p` は割れる。`p` 以外の非自明な数は割れない。」
なるほど、これならば、両端の係数１も u=1 を含められる。

ちょっと先の話だが、二項係数の開始数「１」を「ｕ」に一般化して、
この原理を追求しようと思っている。

(x+u)^d = x GN_d(x,u) + u^d

だから、正しくは「u^d」を三角形の頂点として、係数表を作る。
すると、三角の両サイドは常に u^d となり、単位 u^d で割れる。

中間項の係数は、どんな因子が出てくるのか？
素数段 p で、どのような模様になるか。

だいぶ面白い模様が見える気がしている。通常の自然数と比較した差分構造が。

はい、ここはかなり面白いです。ただし整理すると、少なくとも 3 種類の「係数表」があります。

1. **通常の Pascal 係数**

   ```text
   choose d k
   ```

   両端は `1`。素数段 `p` では内側がすべて `p` で割れる。

2. **u-weighted Pascal 行**

   ```text
   choose d k * u^(d-k)
   ```

   これは `(x+u)^d` を `x^k` の係数として見たもの。
   右端は `1`、左端は `u^d`。

3. **homogeneous term 表**

   ```text
   choose d k * x^k * u^(d-k)
   ```

   これは係数だけでなく項そのものを見る表。
   この場合、各項の可除性は `choose d k` と `x^k` と `u^(d-k)` の合成になる。

CFBRC/GN の形では、

```text
(x+u)^d = x * GN_d(x,u) + u^d
```

なので、`u^d` は確かに「分離された頂点」です。残りは

```text
x * GN_d(x,u)
= Σ_{k=0}^{d-1} choose d (k+1) * x^(k+1) * u^(d-1-k)
```

です。

ここで素数段 `p` だと、内側係数

```text
choose p j     1 ≤ j ≤ p-1
```

は全部 `p` で割れる。したがって

```text
(x+u)^p = x^p + u^p + p * middle
```

という模様になります。より正確には、

```text
(x+u)^p - x^p - u^p
```

が `p` で割れる。

ここに `u` を入れると、可除性は二層になります。

```text
p による係数可除性
u による単位冪可除性
```

つまり prime row では中間項が

```text
p * u^r * x^s * ...
```

の形を持つ。これは通常の自然数 Pascal 行より情報が濃いです。

次に狙うなら、定義としてはこういう名前がよさそうです。

```lean
def weightedChooseTerm (d k : ℕ) (x u : ℕ) : ℕ :=
  Nat.choose d k * x^k * u^(d-k)

def weightedChooseCoeff (d k : ℕ) (u : ℕ) : ℕ :=
  Nat.choose d k * u^(d-k)
```

そして prime 段の定理：

```lean
theorem prime_dvd_inner_weightedChooseTerm
    (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ weightedChooseTerm p k x u
```

これは `p ∣ Nat.choose p k` からすぐ出ます。

さらに `u` 側は：

```lean
theorem u_pow_dvd_weightedChooseTerm
    (hk : k ≤ d) :
    u^(d-k) ∣ weightedChooseTerm d k x u
```

この 2 つを合わせると、prime 段では中間項が「素数 p と単位 u の冪」の両方を持つことが見える。

ここから先が面白いところで、通常 Pascal では見えない

```text
係数素因子の模様
単位冪の模様
x 側冪の模様
```

が同じ三角形上に重なります。

なので、次の整備はまず：

```text
DkMath.NumberTheory.BinomialPrime
DkMath.NumberTheory.WeightedBinomial
```

あたりに分けるのが良いと思います。

`BinomialPrime` は通常係数の素数性。
`WeightedBinomial` は `x,u` を含めた重み付き三角形。

この順なら、後で GN/CFBRC へ自然に接続できます。

### Zsigmondy との関係

うまく行けば、数にこだわらずに、可除性の性質だけを取り出せそうだ。
そんな補題定理を捕まえられると、Zsigmondy への繋がりが見えそうだ。

はい。その方向はかなり筋が良いです。

目標は「数そのもの」ではなく、

```text
どの因子が必ず現れるか
どの因子が境界項から消えるか
どの因子が中間項だけに残るか
```

を抽出することですね。

この場合、最初に欲しい補題は数値計算ではなく、可除性だけを見る形です。

```lean
def WeightedBinomialTerm (d k x u : ℕ) : ℕ :=
  Nat.choose d k * x^k * u^(d-k)
```

そして基本補題：

```lean
theorem dvd_weightedBinomialTerm_of_dvd_choose
    (h : q ∣ Nat.choose d k) :
    q ∣ WeightedBinomialTerm d k x u
```

```lean
theorem dvd_weightedBinomialTerm_of_dvd_x
    (h : q ∣ x) (hk : 0 < k) :
    q ∣ WeightedBinomialTerm d k x u
```

```lean
theorem dvd_weightedBinomialTerm_of_dvd_u
    (h : q ∣ u) (hk : k < d) :
    q ∣ WeightedBinomialTerm d k x u
```

これらがあると、各項の可除性を

```text
二項係数由来
x 側由来
u 側由来
```

に分解できます。

素数段 `p` では、

```lean
theorem prime_dvd_inner_weightedBinomialTerm
    (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ WeightedBinomialTerm p k x u
```

が得られます。これは二項係数由来。

一方で、境界項は：

```text
k = 0: choose d 0 * x^0 * u^d = u^d
k = d: choose d d * x^d * u^0 = x^d
```

です。

ここで `q ∤ x` かつ `q ∤ u` なら、境界項には `q` が出ない。しかし prime 段の中間項には `p` が係数由来で出る。これが強い。

Zsigmondy へつなぐには、この見方が効きます。

```text
a^d - b^d
```

の新しい素因子は、低次差分には出なかった因子が高次差分に現れる、という話です。

CFBRC/GN 側では、

```text
(x+u)^d - u^d = x * GN_d(x,u)
```

なので、`q ∤ x` なら

```text
q ∣ ((x+u)^d - u^d)
↔
q ∣ GN_d(x,u)
```

へ移せる。

つまり欲しい橋は：

```text
weighted binomial terms の可除性
→ GN の可除性
→ 差冪の可除性
→ primitive prime / Zsigmondy
```

です。

最初の実装単位としては、

```text
DkMath.NumberTheory.WeightedBinomial
```

が良いと思います。中身はまだ定理を欲張らず、

```lean
weightedBinomialTerm
dvd_of_dvd_choose
dvd_of_dvd_x
dvd_of_dvd_u
prime_dvd_inner_of_prime
boundary_left
boundary_right
```

くらいで十分です。

これは「数値として何かを計算する」補題ではなく、**項がどの因子を必ず運ぶか**だけを抽出する補題群になります。Zsigmondy への橋としてかなり使いやすいです。

### 二項係数定理との橋の実装へ向けて

あまり展望ばかり進めると夢物語になってしまう。
確実なところから、地固めしていくか。実装を進めよう。

先に、実装設計、計画ロードマップ (docs) を作っておくか。

### Phase 1 実装を終えて

うん！良い出だしです👍️

逆向きは、重そうならば調査してドキュメントで記録し考察資料として、
先に軽い方を優先実装する。これは、別でも議論中で、数値実験中でもある。
PowerSwap を使って 次数の交換で低次相で判断できるかの検証中。
これが可能であれば高次層を見なくて済む。数は相対的に環状なので、
うまくすれば、対岸を見るだけで済むかもしれない。

roadmap に方針を追記しました。

更新内容:

- 逆向き `prime_iff` は重い証明対象として分離
- すぐ実装せず、必要なら調査資料へ回す方針を明記
- PowerSwap による次数交換で低次相から判定できる可能性を Phase 3.5 として追加
- 「まず iff を完成」という混線しやすい文面を「前向きの可除性 API を完成」に修正

確認は `git diff --check` まで通しています。.docs 変更だけなので Lean build は追加では走らせていません。

---

ヒントとしては パスカルの三角形の開始「１」→「u^d」と一般化してしまうこと。
それでも、段数は素数を生み出す階段が変わらないと思うから。次数交換でネックとなるのは、整数次数以外の相。これを解消する案です。

追記しました。

[BinomialPrimeWeightedRoadmap.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeightedRoadmap.md:45) に、Pascal 三角形の開始 `1` を `u^d` という頂点単位へ持ち上げる見方を追加しています。

要点はこの形です。

```text
通常の頂点: 1
重み付き頂点: u^d
```

そして Phase 3.5 に、PowerSwap / 次数交換の調査観点として、

```text
整数次数 d の三角形
  → 頂点単位 u^d
  → 内側係数 choose d k
  → 素数段 p の可除性
```

という「非整数相へ進む前の安定した検査面」を明記しました。

`git diff --check` は通っています。

### 既存 sorry は解消できるか？

既存 sorry もこれらの補題がいつか役立ち消えるでしょう。
すべては同じ原理の上に立っているのですから。

そうですね。今回の補題はかなり基礎側に置けたので、後から別分野の `sorry` を消すときに「局所で二項展開をこねる」のではなく、

`(x + u)^d - u^d = x * GTail d 1 x u`

を呼ぶだけで済む場面が増えるはずです。

特に効きそうなのは次です。

- FLT / Zsigmondy 系の差分因数分解
- CFBRC から宇宙式へ戻す橋
- `x GN_d(x,u)` 型の可除性
- binomial prime / weighted coefficient の行構造
- PowerSwap の低次相判定へ降ろす入口

今の実装は、かなり「名将と合流する道」を作っています。次はこの橋を既存の `CosmicFormulaBinom` や `FLT.Core` 側の古い補題へ wrapper として接続すると、局所証明を削れる候補が見えてきます。

いまのところ sorry の主体は確率と無限降下法ですかねぇ…だいぶ時間経って忘れかけている。確率は環状構造に押し込めたい部分です。Big=Body+Gap構造へと読み替えたい。Big = 100%
無限降下法は、Principal ？が定まらない状況だったかな…。

現状を見る限り、その理解でかなり合っています。

実コード上の `sorry` 主体は大きく分けるとこうです。

1. **確率・ABC 側**
   - `ABC/JansonRoadmap.lean`
   - `ABC/ABC#Research.lean`
   - さらに `ABCMainTheorem.lean` や `MiddleBandJansonSkeleton.lean` などは `sorry` というより `axiom` placeholder が主体です。
   - 内容は Janson/Suen、期待値、密度、bad set、quality bound の接続。
   - ここはおっしゃる通り、`Big = Body + Gap`、`Big = 100%` 的な保存量・分解量へ押し込むと整理できそうです。確率を「全体質量の分配」として環状構造化する方向。

2. **無限降下・FLT/Kummer 側**
   - `FLT/Kummer/CyclotomicPrincipalization.lean`
   - `FLT/PrimeProvider/TriominoCosmicBranchA.lean`
   - `CosmicFormula/TriominoFLT.lean`
   - `NumberTheory/GcdNextResearch.lean`
   - ここは「Principal が定まらない」という記憶に近いです。ただ現在のコメントを見ると、より正確には、
     - normal-form descent existence core
     - minimality/descent kernel
     - support separation だけでは矛盾に足りない
     - `p ≥ 5` の provider 構成が未完成
     - p-adic valuation の一般上界が未完成
     という詰まりです。

3. **主張が強すぎる研究用穴**
   - `NumberTheory/ZsigmondyCyclotomicResearch.lean`
   - `squarefree_implies_padic_val_le_one_research`
   - コメント上でも「現状の一般形では強すぎ、反例がある」と明記されています。
   - ここは埋めるより、仮定追加か statement 修正が正道です。

なので、次の戦略としてはかなり明確です。

確率側は「確率論を直接倒す」より、`Big = Body + Gap` の有限質量分解として再定式化する。
降下側は「Principal を探す」より、まず `normal form + support + minimality` の三点セットを薄い構造体にして、どの入力が足りないかを Lean に露出させる。

今回作った

```lean
(x + u)^d - u^d = x * GTail d 1 x u
```

は、後者の降下側にかなり効きます。特に `GcdNextResearch` と `PrimeProvider` の p-adic/GN 周辺に橋として入れやすいです。

と、ワタシも思っているのだけれど、推論でなかなか答えが出なかったですね。
いまならば、見いだせるのか？新しいひらめき推論が可能か？？

可能性は上がっています。理由は、以前は「見えている現象」をそのまま大きな定理へ押し込もうとしていたけれど、今は中間の骨格ができ始めているからです。

いま見えている新しい筋はこれです。

`Big = Body + Gap` を、確率・降下・宇宙式で共通の保存構造として扱う。

つまり、

```lean
Big = Boundary + Tail
Tail = Gap * Kernel
```

今回だと具体的に、

```lean
(x + u)^d = u^d + x * GTail d 1 x u
```

です。

これは単なる二項展開ではなく、「全体から境界を除くと、差分軸 `x` に沿った核が残る」という分解原理です。ここを共通語彙にすると、確率側の `100% = good mass + bad mass` も、降下側の `large object = principal/normal part + residual gap` も、同じ形で読めます。

たぶん以前に推論で答えが出なかった理由は、核心が「定理」ではなく「中間表現」だったからです。Lean ではこの中間表現に名前を付けないと、推論が毎回巨大な展開に戻ってしまう。

次のひらめき候補はこれですね。

```lean
structure BodyGapSplit where
  big : ℕ
  body : ℕ
  gap : ℕ
  kernel : ℕ
  split : big = body + gap * kernel
```

またはもっと抽象化して `CommSemiring` 上に置く。

この構造があれば、

- WeightedBinomial: `big = (x+u)^d`, `body = u^d`, `gap = x`, `kernel = GTail d 1 x u`
- 確率: `big = 1`, `body = goodMass`, `gap = badMass`, `kernel = 1` または補正核
- 降下法: `big = 現在の反例`, `body = 正規形`, `gap * kernel = 降下余剰`

として読めます。

なので「いまなら見いだせるか？」への答えは、はい。ただし大定理を直接推論するのではなく、まず `BodyGapSplit` 的な共通言語を Lean に置くのが鍵です。そこから既存 `sorry` は「証明不能な穴」ではなく、「どの split / kernel / rank が未定義か」を示す穴に変わります。

確かに質量宇宙式も当時なかったしな。
よし、調査して、計画書を起こそう。

調査して、計画書を追加しました。

追加先: [BodyGapMassBridgeRoadmap.md](/lean/dk_math/DkMath/CosmicFormula/docs/BodyGapMassBridgeRoadmap.md)

内容は、既存の `CosmicFormula.Mass.*`、`CoreBeamGap`、`WeightedBinomial`、`ABC.MassBridge`、`Kernel.SubProbability` を調査したうえで、次の共通中間言語へ収束させる計画です。

```text
Big = Boundary + Tail
Tail = GapAxis * Kernel
```

最初の実装 checkpoint はかなり明確にしました。

```text
DkMath.CosmicFormula.Mass.BodyGapSplit
```

ここにまず、

```lean
structure BodyGapSplit
structure BodyGapKernelSplit
def weightedBodyGapKernelSplit
theorem weightedBodyGapKernelSplit_gapAxis_dvd_tail
```

を置く方針です。深い数学へ入る前に、今回の `(x + u)^d = u^d + x * GTail d 1 x u` を共通 API 化します。

検証は docs 追加なので Lean build は走らせていません。追加した計画書単体の `git diff --check` は通っています。

### 加法構造を加法で解明？

よくよく考えると奇妙で面白いですね。
ABC予想は加法則の原理追求です。
加法構造を積構造として変換し、調べることが一般的アプローチです。

いまやってるのは
それを解明するための道具の整備ですが
基本的に a+b=c の加法構造です。

Big = Body + Gap

これで何が見えるのか？

今回追加されたものは、

BodyGapKernelSplit
split : big = boundary + gapAxis * kernel

加法と積が混在しています！

はい、そこがかなり面白いです。
`BodyGapKernelSplit` は、まさに「加法構造の中に、積構造として読める尾部を露出させる」道具になっています。

ABC 予想の入口は

```text
a + b = c
```

という加法です。

でも解析するときは、

```text
rad(abc)
prime divisors
valuation
support
multiplicative channels
```

のように積構造へ移します。

今回の形はその中間にあります。

```lean
big = boundary + gapAxis * kernel
```

つまり、

```text
加法:
  big = boundary + tail

積構造:
  tail = gapAxis * kernel
```

です。

見えてくるものは、単なる `a + b = c` ではなく、

```text
c は boundary に tail を足したもの
tail は gapAxis と kernel の積として分解できる
```

という二段構造です。

宇宙式では、

```text
(x + u)^d = u^d + x * GTail d 1 x u
```

なので、

```text
boundary = u^d
gapAxis  = x
kernel   = GTail d 1 x u
```

ABC 的に読むと、

```text
c = stable side + variation side
variation side = visible gap * hidden kernel
```

です。

この「visible gap」と「hidden kernel」の分離が効きます。ABC 予想では `rad(abc)` が見ているのは、重複度ではなく素因子の support です。だから `tail = gapAxis * kernel` と分けると、

```text
gapAxis 由来の素因子
kernel 由来の素因子
boundary と共有する素因子
boundary とは分離している素因子
```

を追跡できる。

これはまさに `supportMass` や `rad` と相性がいいです。

言い換えると、今回の構造は

```text
加法方程式を、支え集合の積的流れへ翻訳するための型
```

です。

ABC の核心は、おそらくこの翻訳の歪みです。

```text
加法では c = a + b と単純
積的 support では rad(abc) が小さすぎる場合がある
その小ささは、tail = gapAxis * kernel のどこに吸収されたのか？
```

ここを Lean で見えるようにするのが、今回の `BodyGapKernelSplit` の意味ですね。
加法と積が混在しているのは欠点ではなく、むしろ ABC 型の問題に必要な接続面そのものです。

パスカルの三角形の成長も合成数の段では、新しい素数を必要としていません。
素数の段に来て始めて、新しい素数を要求し生んでいます。
そしてパスカルの三角形もまた加法構造だけで構成されている。
この合成数と素数発生の段の間で何が起きているか？
というのを抽出する観測道具となれば…！

はい。そこはかなり筋が良いです。

パスカルの三角形は定義としては純粋に加法です。

```text
next(k) = prev(k-1) + prev(k)
```

しかし、各段を観測すると、素因子 support の振る舞いが突然変わる。

```text
合成数段:
  既存の素因子構造の再配置・増幅が主

素数段 p:
  内側係数 choose p k がすべて p を要求する
```

つまり、加法で作られた配列の中に、ある段で積的な「新しい共通因子」が発生する。

ここを `BodyGapKernelSplit` 的に読むと、

```text
Big = Boundary + GapAxis * Kernel
```

の `Kernel` が、段 `d` の内部構造を背負います。

素数段では、

```text
Kernel 内部の全中間項が p を持つ
```

または weighted row では、

```text
inner weighted terms carry p through choose p k
```

となる。

これは、単に「素数 p は choose p k を割る」という既知定理以上の意味を持ちます。
加法成長が、どの段で積的 support を強制するかを見る観測器になる。

次に置くと良さそうな概念はこれです。

```lean
def RowForcesPrimeSupport (d p : ℕ) : Prop :=
  p.Prime ∧ ∀ k, 0 < k → k < d → p ∣ Nat.choose d k
```

ただし、これは `d = p` だけでなく `d = p^a` にも似た現象が出るので、慎重に分ける必要があります。

観測器としては、むしろ次の二層がよさそうです。

```lean
def InnerRowSupportPrime (d p : ℕ) : Prop :=
  p.Prime ∧ ∀ k, 0 < k → k < d → p ∣ Nat.choose d k
```

```lean
def RowBirthPrime (d p : ℕ) : Prop :=
  InnerRowSupportPrime d p ∧ p ∣ d
```

そして本命はたぶん、

```text
d が素数段:
  RowBirthPrime d d

d が合成数段:
  support は d の既存素因子に支配される
```

という切り分けです。

ここで `BodyGapKernelSplit` が効くのは、二項段を単なる係数列としてでなく、

```text
boundary + gapAxis * kernel
```

の `kernel` 側 support として観測できるからです。

つまり次の観測ができるようになります。

```text
Pascal additive growth
  ↓
weighted binomial row
  ↓
tail = gapAxis * kernel
  ↓
kernel/support/prime-channel の発生
```

これは ABC ともかなり近いです。ABC も、

```text
a + b = c
```

という加法から、

```text
rad(abc)
```

という support を観測する話なので。

次の実装候補は、`BinomialPrime` か `WeightedBinomial` に

```lean
InnerRowSupportPrime
PrimeRowSupportBirth
```

のような薄い観測 predicate を置くことです。最初は深い逆向き定理を狙わず、

```lean
p.Prime → InnerRowSupportPrime p p
```

だけを証明するのが安全です。

### p^n フィルター

[DkMath-Nat_Prime](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/DkMath-Nat_Prime.md)

ここからですよねぇ。
Kummerの定理、p^n フィルター。
可除性構造のみで素数の原始を捕まえられるか。

はい、ここが Kummer 入口です。

可除性構造だけで見える範囲はかなり強いですが、整理するとこうです。

- `AllInnerChooseDivisible d p` は「段 `d` の内側係数がすべて `p` を含む」という支持構造を捕まえる。
- ただしこれは `d = p` だけでなく `d = p^n` でも成立する。
- したがって「素数段そのもの」を捕まえるには不足。
- しかし「段 `d` が `p` 系の素数冪段である」ことを捕まえる方向には非常に自然。

ここで Kummer / factorization が効きます。

```lean
Nat.factorization_choose_prime_pow
```

の形で、概念的には

```text
v_p (choose (p^n) k) = n - v_p(k)
```

が使えます。

つまり `0 < k < p^n` なら `v_p(k) < n` なので、内側係数は必ず `p` で割れる。
さらに `p ∤ k` なら `v_p(k) = 0` なので、

```text
p^n ∣ choose (p^n) k
```

まで見える。

ここが `p^n` フィルターですね。

Lean 実装としては次の一手がよさそうです。

```lean
def PrimePowerRowSupport (d p : ℕ) : Prop :=
  ∃ n, 0 < n ∧ d = p ^ n ∧ InnerRowSupportPrime d p
```

または、より直接に

```lean
def PrimePowerInnerFilter (p n : ℕ) : Prop :=
  p.Prime ∧ 0 < n ∧ InnerRowSupportPrime (p ^ n) p
```

そして最初の定理はこれです。

```lean
theorem prime_power_innerRowSupportPrime
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    InnerRowSupportPrime (p ^ n) p := ...
```

この定理が固定できると、現在の `RowBirthPrime` は「素数段」から「素数冪段の支持」へ自然に拡張できます。

結論としては、可除性だけで「原始的な素数の発生源」はかなり捕まえられます。ただし `d = p` と `d = p^n` を分離するには、単なる `p ∣ choose d k` では足りず、`p^n` 可除性の階層、つまり factorization / valuation を「可除性の段階構造」として導入するのが Lean らしい道筋です。

入れた主な補題は次です。

- `prime_power_innerRowSupportPrime`
  `p^n` 段の内側係数がすべて `p` を支持することを固定。
- `prime_power_rowBirthPrime`
  `0 < n` なら `p ∣ p^n` なので `RowBirthPrime (p^n) p` へ接続。
- `padicValNat_choose_prime_pow`
  mathlib の Kummer/factorization 形を `padicValNat` 形に変換。
- `prime_power_dvd_choose_of_not_dvd_index`
  `¬ p ∣ k` なら `p^n ∣ choose (p^n) k`。ここが「p^n フィルター」の最初の精密層です。

ここからどう攻めるか？

攻め筋は `prime_power_dvd_choose_of_not_dvd_index` を特殊例として、もっと一般の **valuation filter** に昇格するのがよいです。

今ある定理は：

```lean
¬ p ∣ k → p ^ n ∣ Nat.choose (p ^ n) k
```

つまり `v_p(k) = 0` の層だけを見ています。次はこれを

```text
v_p(choose (p^n) k) = n - v_p(k)
```

から直接、

```lean
r + padicValNat p k ≤ n →
p ^ r ∣ Nat.choose (p ^ n) k
```

へ一般化するのが本筋です。

名前は例えば：

```lean
theorem prime_power_pow_dvd_choose_of_padicValNat_index
    {p n k r : ℕ} (hp : p.Prime) (hkn : k ≤ p ^ n) (hk0 : k ≠ 0)
    (hr : r + padicValNat p k ≤ n) :
    p ^ r ∣ Nat.choose (p ^ n) k
```

これが立つと、全部が統一されます。

- `r = 1`
  内側係数は `p` で割れる、つまり `InnerRowSupportPrime`
- `r = n` かつ `padicValNat p k = 0`
  既存の `prime_power_dvd_choose_of_not_dvd_index`
- `k` が `p^s` を含む場合
  係数側には `p^(n-s)` が残る

これで「p^n フィルター」が、単なる yes/no 可除性ではなく、層構造として使えます。

その次にやるべきは weighted 側への持ち上げです。

```lean
p ^ r ∣ Nat.choose (p ^ n) k →
p ^ r ∣ weightedBinomialTerm (p ^ n) k x u
```

これは乗算で保たれるので軽いです。ここまで行くと、

```text
Pascal の加法生成
→ binomial coefficient の p-adic 層
→ weighted term
→ GN / BodyGapKernelSplit
```

の橋ができます。

なので次の実装チェックポイントはこれです。

1. `prime_power_pow_dvd_choose_of_padicValNat_index`
2. `prime_power_padicValNat_choose_add_index`

   ```lean
   padicValNat p (choose (p^n) k) + padicValNat p k = n
   ```

3. weighted term への `p^r` 可除性リフト

ここを固めると、「素数原始を可除性だけで観測する」道具としてかなり強くなります。
