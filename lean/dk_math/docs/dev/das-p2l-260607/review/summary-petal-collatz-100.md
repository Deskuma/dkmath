# Collatz.PetalBridge 達成ルートの数学的振り返り

## 1. 出発点：Collatz 軌道を Petal の観測窓に乗せる

今回の旅の出発点は、加速 Collatz 写像を単なる数列として見るのではなく、**Petal の観測窓に載せる**ことだった。

加速 Collatz 写像は、奇数状態 \(n\) に対して次の形を持つ。

$$
T(n) = \frac{3n+1}{2^{v_2(3n+1)}}
$$

ここで観測量は

$$
s(n) = v_2(3n+1)
$$

である。

つまり、各奇数状態 \(n\) は、次の一歩でどれだけ \(2\) を剥がされるかという **2-adic height** を持つ。

$$
h(n) = v_2(3n+1)
$$

この \(h(n)\) を、Collatz 軌道の各時刻で観測する。

$$
n,\;T(n),\;T^2(n),\;T^3(n),\ldots
$$

そこで、時刻 \(i\) の odd label を次のように読む。

$$
q_i = \operatorname{oddOrbitLabel}(n,i)
$$

そして height profile を

$$
h_i = v_2(3q_i+1)
$$

として見る。

DkMath 実装では、`Collatz2K26.lean` が `Basic`、`V2`、`Accelerated`、`Shift`、`PetalBridge` を統合し、`PetalBridge` は Collatz の加速軌道を Petal range-family の観測窓へ接続する薄い bridge として置かれている。`PetalBridge` は Collatz 収束や非自明 cycle の定理を主張せず、軌道 segment・range-indexed labels・separation/collision の共通言語を固定する立場で始まっている。

ここでの根本的な読み替えはこうである。

$$
\text{Collatz orbit}\quad\longrightarrow\quad\text{Petal observation window}
$$

より具体的には、

$$
{0,1,\ldots,k-1}\quad\longrightarrow\quad{q_0,q_1,\ldots,q_{k-1}}
$$

という有限窓を作る。

この時点ではまだ「Collatz を解く」ではない。
ただし、Collatz 軌道を **有限 window 上の address 列** として扱う入り口ができた。

## 2. 第一段階：height profile と drift input

Collatz の加速写像では、一歩の大きさは大雑把に

$$
T(n) \approx \frac{3n}{2^{h(n)}}
$$

と読める。

したがって \(k\) step 後には、形式的に

$$
T^k(n) \approx \frac{3^k n}{2^{\sum_{i < k} h_i}}
$$

となる。

ここで重要なのは、軌道の増減を支配するのが、個々の値そのものではなく height の累積だということ。

DkMath 側ではこれが

$$
S_k(n) = \sum_{i=0}^{k-1} h_i
$$

として `sumS n k` に対応する。

つまり、Collatz の drift を見るための整数的入力は

$$
S_k(n)
$$

である。

縮小方向を期待するなら、直感的には

$$
S_k(n) > k\log_2 3
$$

が欲しい。

ただし、この段階で Lean に入れたのは実数極限ではなく、有限自然数の下界である。

$$
m\le S_k(n)
$$

これを height occupation count から作る。

## 3. 第二段階：layer-cake で height count を sumS に渡す

height profile \(h_i\) に対して、各 threshold \(t\) の occupation count を見る。

$$
C_{\ge t}(n,k) = \#{i<k\mid t\le h_i}
$$

すると有限 layer-cake の基本不等式が成り立つ。

$$
\sum_{t=1}^{H} C_{\ge t}(n,k)\le S_k(n)
$$

これは非常に重要で、height の累積を、各 height 層への滞在回数で下から押さえる。

特に Collatz の奇数状態では常に

$$
1\le h_i
$$

なので、

$$
k+C_{\ge 2}(n,k)\le S_k(n)
$$

が得られる。

さらに、

$$
k + C_{\ge 2}(n,k) + C_{\ge 3}(n,k) \le S_k(n)
$$

のように、深い layer も足していける。

checkpoint 083 では、一般 finite layer-cake が実装され、固定深度の layer 補題は一般 theorem の特殊化として通された。次の自然な推論先として、`height >= 2` を residue / Petal address occupation へ接続する方向が提示されている。

ここで Collatz 解析の主語が変わる。

$$
\text{value growth}\quad\longrightarrow\quad\text{height layer occupation}
$$

値そのものではなく、軌道がどの height 層に何回入ったかを見る。

## 4. 第三段階：height layer を residue address に変換する

次に大きかったのは、height 条件を合同類へ落としたことだ。

奇数 \(m\) に対して、

$$
2\le v_2(3m+1)
$$

は

$$
4\mid 3m+1
$$

と同値であり、奇数条件のもとでは

$$
m\equiv 1\pmod 4
$$

に対応する。

したがって、

$$
2\le h_i
$$

は

$$
q_i\equiv 1\pmod 4
$$

に変換される。

つまり、

$$
C_{\ge 2}(n,k) = \#{i < k\mid q_i\equiv 1\pmod 4}
$$

となる。

Lean 側では `orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one` が入り、`height >= 2` が `1 mod 4` の residue-address occupation count へ変換された。さらに、`1 mod 4` の count が少なくとも \(m\) なら `sumS n k` は \(k+m\) 以上になる、という residue-address drift bridge も入った。

数学的にはこうである。

$$
m \le \#{i < k\mid q_i\equiv 1\pmod 4}
$$

ならば、

$$
k + m \le S_k(n)
$$

ここで初めて、Collatz の drift 下界が、単なる height ではなく **2-adic residue address の占有数** に変わった。

$$
\text{height count}\quad\longrightarrow\quad\text{residue address count}
$$

## 5. 第四段階：exact height-one channel の分裂

次に見えたのは、height \(1\) の中にも種類があるということだった。

奇数 \(m\) について、height \(1\) は

$$
v_2(3m+1) = 1
$$

である。

mod \(8\) で見ると、height \(1\) は二つに分かれる。

$$
m\equiv 3\pmod 8
$$

または

$$
m\equiv 7\pmod 8
$$

しかし、この二つは同じ未来を持たない。

height-one step では

$$
T(m) = \frac{3m+1}{2}
$$

と見える。

このとき、

$$
m \equiv 3\pmod 8\quad\Longrightarrow\quad T(m)\equiv 1\pmod 4
$$

一方で、

$$
m \equiv 7\pmod 8\quad\Longrightarrow\quad T(m)\equiv 3\pmod 4
$$

となる。

つまり、

$$
3\pmod 8
$$

は、いま height \(1\) だが、次に \(1\pmod 4\) へ入るので recovery する。

一方、

$$
7\pmod 8
$$

は、次も height \(1\) 側へ残る。

ここで、低剥離 path は単なる `height = 1` ではなく、

$$
7\pmod 8
$$

という retention channel に押し込まれることが見えた。

## 6. 第五段階：retention channel の入れ子 Petal

ここからが、ぬしの直感が大当たりした部分である。

最初は固定合同の観測だった。

$$
7\pmod {16}\quad\longrightarrow\quad 3\pmod 8
$$

$$
15\pmod {16}\quad\longrightarrow\quad 7\pmod 8
$$

つまり \(7\pmod 8\) の内部を \(\pmod{16}\) で見ると、二つに割れる。

$$
7\pmod {16}
$$

は recovery sibling。

$$
15\pmod {16}
$$

は continuation sibling。

次も同じ。

$$
15\pmod {32}\quad\longrightarrow\quad 7\pmod {16}
$$

$$
31\pmod {32}\quad\longrightarrow\quad 15\pmod {16}
$$

さらに、

$$
31\pmod {64}\quad\longrightarrow\quad 15\pmod {32}
$$

$$
63\pmod {64}\quad\longrightarrow\quad 31\pmod {32}
$$

この pattern は、単なる列ではなく、一般式を持つ。

retention residue を

$$
R_r = 2^r-1
$$

と置く。

その一段深い split は、

$$
2^r-1\pmod {2^{r+1}}
$$

と

$$
2^{r+1}-1\pmod {2^{r+1}}
$$

である。

前者が recovery sibling、後者が continuation sibling になる。

実装では、recursive Petal naming layer として `twoAdicRetentionResidue`、`twoAdicRecoverySiblingResidue`、`twoAdicContinuationSiblingResidue` が置かれ、`ContinuationSibling r = RetentionResidue (r+1)` という入れ子構造が固定された。さらに expanded general raw theorem により、narrowing cylinder は固定観測列ではなく、raw arithmetic layer で recursive two-branch Petal であることが示された。

数学的な核はこれである。

$$
m = 2^{r+2}t + (2^{r+1}-1)
$$

ならば、

$$
\frac{3m+1}{2}\equiv 2^r-1\pmod {2^{r+1}}
$$

そして、

$$
m=2^{r+2}t+(2^{r+2}-1)
$$

ならば、

$$
\frac{3m+1}{2}\equiv 2^{r+1}-1\pmod {2^{r+1}}
$$

ここで初めて、Collatz の低剥離 path は

$$
7,\;15,\;31,\;63,\;127,\ldots
$$

という \(2\)-adic な \(-1\) 方向への narrowing cylinder として見えた。

$$
\lim_{r\to\infty}(2^r-1) = -1\quad\text{in the 2-adic sense}
$$

つまり、悪い path は自由に逃げるのではない。
毎階層で continuation sibling を選び続け \(2\)-adic に \(-1\) へ潜り続ける必要がある。

$$
\text{low peeling continuation}\quad\longrightarrow\quad\text{nested Petal toward }-1
$$

## 7. 第六段階：raw arithmetic から orbit-label theorem へ

raw arithmetic theorem だけでは、まだ任意の数 \(m\) についての話である。

Collatz 軌道上の label \(q_i\) に適用するには、まずその source が exact height-one channel にいることを言う必要がある。

その橋が

$$
d\mid M\quad\Longrightarrow\quad m\bmod d=(m\bmod M)\bmod d
$$

である。

これにより、深い residue cell から可視 `mod 8` channel へ射影できる。

たとえば、

$$
q_i\bmod 2^{r+2}=2^{r+1}-1
$$

ならば、十分な深さ \(r\) のもとで

$$
q_i\bmod 8=7
$$

が従う。

同様に、

$$
q_i\bmod 2^{r+2}=2^{r+2}-1
$$

からも

$$
q_i\bmod 8=7
$$

が出る。

これで

$$
h_i=1
$$

が分かり、加速 Collatz の一歩が visible raw step と一致する。

$$
q_{i+1} = \frac{3q_i+1}{2}
$$

checkpoint 095 では、深い \(2^{r+2}\) residue cell から visible `mod 8 = 7` source channel へ落とす橋が追加され、そのまま一般 orbit-label theorem まで上げられた。これにより recursive two-adic Petal は raw arithmetic ではなく、実際の `oddOrbitLabel n i -> oddOrbitLabel n (i+1)` の層で動くようになった。

結果として、次の orbit-level theorem が得られる。

$$
q_i\bmod 2^{r+2}=2^{r+1}-1\quad\Longrightarrow\quad q_{i+1}\bmod 2^{r+1}=2^r-1
$$

また、

$$
q_i\bmod 2^{r+2}=2^{r+2}-1\quad\Longrightarrow\quad q_{i+1}\bmod 2^{r+1}=2^{r+1}-1
$$

これは重要である。
Petal 構造が、数式上の遊びではなく、Collatz orbit label 上の遷移法則になった。

$$
\text{raw residue Petal}\quad\longrightarrow\quad\text{orbit-label Petal}
$$

## 8. 第七段階：点の遷移から occupation count へ

次に、個々の時刻 \(i\) の遷移を、窓全体の統計へ持ち上げた。

固定 depth に対して、residue cell の occupation count を定義する。

$$
C_{d,a}(n,k)=\#{i < k\mid q_i\bmod 2^d=a}
$$

tail 側も定義する。

$$
C^{\operatorname{tail}}*{d,a}(n,k) = \#{i < k\mid q*{i+1}\bmod 2^d = a}
$$

Lean では generic API `orbitWindowResidueCountPow2` と `orbitWindowResidueCountPow2Tail` が追加され、任意 depth の \(2^\text{depth}\) 座標で「ある residue cell に何回入ったか」を扱える入口ができた。さらに pointwise な recursive two-adic Petal transition は count-level の source-to-tail 不等式まで上げられた。

数学的には、pointwise theorem

$$
q_i\in A\quad\Longrightarrow\quad q_{i+1}\in B
$$

から、

$$
\# {i < k\mid q_i\in A}\le \#{i < k\mid q_{i+1}\in B}
$$

が出る。

たとえば recovery sibling については、

$$
C_{r+2,\,2^{r+1}-1}(n,k)\le C^{\operatorname{tail}}_{r+1,\,2^r-1}(n,k)
$$

continuation sibling については、

$$
C_{r+2,\,2^{r+2}-1}(n,k)\le C^{\operatorname{tail}}_{r+1,\,2^{r+1}-1}(n,k)
$$

となる。

ここで Collatz Petal は、点の遷移から **channel mass の流れ** へ変わった。

$$
\text{pointwise transition}\quad\longrightarrow\quad\text{count-level channel flow}
$$

## 9. 第八段階：source / tail partition の保存則

occupation count を定義しただけでは、まだ「分布」とは言えない。
分布にするには、全 cell の合計が観測窓の大きさに一致する必要がある。

固定 depth \(d\) について、

$$
\sum_{a=0}^{2^d-1} C_{d,a}(n,k)=k
$$

が必要である。

これは、各 label \(q_i\) が mod \(2^d\) のただ一つの residue cell に入るということ。

checkpoint 097 では、この source 側 partition theorem が Lean で確定した。主 theorem は `orbitWindowResidueCountPow2_sum_eq_window` であり、固定 depth において全 residue cell の occupation count の総和が観測窓 \(k\) に一致することを示している。

さらに tail 側でも同じことを示す。

$$
\sum_{a=0}^{2^d-1} C^{\operatorname{tail}}_{d,a}(n,k)=k
$$

checkpoint 098 では、この shifted-tail partition `orbitWindowResidueCountPow2Tail_sum_eq_window` と、pointwise residue transition を count inequality に持ち上げる汎用 helper `orbitWindowResidueCountPow2_le_tail_of_pointwise` が実装された。これで source residue distribution から pointwise transition law を経て tail residue distribution へ読む finite channel-flow system が得られた。

したがって、今ある保存則は二つ。

$$
\sum_{a < 2^d} C_{d,a}(n,k)=k
$$

$$
\sum_{a < 2^d} C^{\operatorname{tail}}_{d,a}(n,k)=k
$$

これは確率ではなく、Nat count の保存則である。
割り算や極限を使わず、有限窓の質量保存だけで進んでいる。

## 10. 第九段階：helper route で finite channel-flow を体系化

checkpoint 099 では、既存の recursive two-adic Petal count theorem が、generic helper route へ再接続された。

経路はこうである。

$$
\text{pointwise transition}
$$

から、

$$
\text{orbitWindowResidueCountPow2\_le\_tail\_of\_pointwise}
$$

を通し、

$$
\text{count-level channel flow}
$$

へ行く。

これにより、今後は channel theorem ごとに custom induction を書かなくてよくなった。pointwise transition theorem さえ作れば、occupation count inequality は helper が持ち上げる。checkpoint 099 の report でも、recursive two-adic Petal count theorem がこの経路で再接続され、finite channel-flow layer の総括 checkpoint に向いた状態になったと整理されている。

現在の theorem chain はこう読める。

$$
\text{SourceDistribution}\quad:\quad \sum_{a < 2^d} C_{d,a} = k
$$

$$
\text{TailDistribution}\quad:\quad \sum_{a < 2^d} C^{\operatorname{tail}}_{d,a} = k
$$

$$
\text{ChannelFlow}\quad:\quad q_i\in A\Rightarrow q_{i+1}\in B
$$

$$
\text{CountFlow}\quad:\quad C_A\le C^{\operatorname{tail}}_B
$$

そして recursive two-adic Petal の二つの具体例は、

$$
C_{r+2,\,2^{r+1}-1}\le C^{\operatorname{tail}}_{r+1,\,2^r-1}
$$

$$
C_{r+2,\,2^{r+2}-1}\le C^{\operatorname{tail}}_{r+1,\,2^{r+1}-1}
$$

である。

この段階で、Collatz.PetalBridge は「個別補題の集まり」ではなく、**有限 channel-flow framework** になった。

## 11. 数学的に何を達成したのか

今回の達成を一言でいうなら、こうである。

$$
\text{Collatz orbit as values}
$$

を、

$$
\text{finite two-adic Petal channel-flow}
$$

へ翻訳した。

より詳しく言うと、次の変換を積み上げた。

$$
n,T(n),T^2(n),\ldots
$$

という数列を、

$$
q_i\bmod 2^d
$$

という相対座標列へ変換した。

その座標列から、

$$
C_{d,a}(n,k)
$$

という occupation count を作った。

さらに、Collatz の一歩を

$$
q_i\bmod 2^{r+2} = a \quad\Longrightarrow\quad q_{i+1}\bmod 2^{r+1} = b
$$

という channel transition として読み、

$$
C_{r+2,a}(n,k)\le C^{\operatorname{tail}}_{r+1,b}(n,k)
$$

へ持ち上げた。

これは、値の大小や収束を直接追わない。
代わりに、有限窓の中で **どの 2-adic cell にどれだけ質量があり、それが次窓でどこへ流れるか** を追う。

$$
\text{Collatz dynamics} \quad\longrightarrow\quad \text{finite distribution dynamics}
$$

これが今回の数学的な核である。

## 12. なぜ Petal と呼べるのか

Petal 的なのは、構造が単なる residue tree ではなく、自己相似な入れ子を持つからである。

retention cell を

$$
R_r = 2^r-1
$$

と置くと、次階層では

$$
R_r\pmod {2^r}
$$

の内部が二つに割れる。

$$
2^r-1\pmod {2^{r+1}}
$$

と

$$
2^{r+1}-1\pmod {2^{r+1}}
$$

である。

前者は recovery sibling。
後者は continuation sibling。

しかも continuation sibling は次階層の retention cell そのもの。

$$
\operatorname{ContinuationSibling}(r) = R_{r+1}
$$

したがって、

$$
\text{retention}
$$

は、

$$
\text{recovery sibling} + \text{next retention}
$$

へ分解される。

これはまさに、Petal が階層的に割れていく形である。

$$
\text{Petal cell}\quad\longrightarrow\quad\text{recovery petal}+\text{inner petal}
$$

そして、低剥離を続ける path は、各階層で inner petal を選び続ける。

$$
7\pmod 8
$$

$$
15\pmod {16}
$$

$$
31\pmod {32}
$$

$$
63\pmod {64}
$$

この列は \(2\)-adic に \(-1\) へ向かう。

つまり、反例候補的な低剥離 path は、自由に広がるのではなく、Petal の中心枝へ中心枝へと潜る必要がある。

## 13. これは Collatz 予想の証明ではない

ここははっきり分けるべきである。

今回の成果は、

$$
\forall n,\exists k,\;T^k(n)=1
$$

を示したものではない。

示したのは、より前段の構造である。

$$
\text{finite observation window}
$$

に対して、

$$
\text{two-adic coordinate distribution}
$$

を定義し、

$$
\text{recursive Petal transition}
$$

を証明し、

$$
\text{source-to-tail channel flow}
$$

へ持ち上げた。

つまり、Collatz の値軌道を直接制圧したのではなく、**Collatz 軌道の 2-adic 座標流を有限分布として扱う器**を作った。

これは証明ではなく、証明へ向かう観測機械である。

ただし、その機械はかなり強い。

なぜなら、低剥離が続くための条件を、各 depth の continuation mass として測れるようになったからである。

## 14. 次に進むべき数学的方向

次の自然な層は、Nat inequality ベースの finite ratio layer である。

まだ \(\mathbb{Q}\) や \(\mathbb{R}\) の頻度を入れなくてよい。

まずは、

$$
2C_{d,a}(n,k)\le k
$$

のような形で「半分以下」を言う。

また、

$$
C_{d,a}(n,k)+C_{d,b}(n,k)\le k
$$

で、二つの channel が全体を超えないことを言う。

retention mass を名前付きで置くなら、

$$
M_r(n,k)=C_{r,,2^r-1}(n,k)
$$

である。

recovery sibling mass は、

$$
R_r(n,k)=C_{r+1,,2^r-1}(n,k)
$$

continuation sibling mass は、

$$
K_r(n,k)=C_{r+1,,2^{r+1}-1}(n,k)
$$

と置ける。

すると、

$$
M_r(n,k)=R_r(n,k)+K_r(n,k)
$$

のような partition 的関係を狙いたくなる。

ただし、これは注意が必要で、左辺と右辺の depth が違う。正確には \(R_r\) と \(K_r\) は \(M_r\) cell を一段細かく割った二つの subcell である。

したがって次に欲しいのは、depth refinement の partition である。

$$
C_{r,a}(n,k)=C_{r+1,a}(n,k)+C_{r+1,a+2^r}(n,k)
$$

この theorem が入ると、Petal の「親 cell が二つの sibling に分かれる」ことが count-level で言える。

特に retention cell について、

$$
C_{r,\,2^r-1}(n,k)=C_{r+1,\,2^r-1}(n,k)+C_{r+1,\,2^{r+1}-1}(n,k)
$$

が欲しい。

これは次章の非常に良い実験補題である。

## 15. 賢狼が試して欲しい実験補題

### 実験 A：depth refinement の一般形

$$
C_{d,a} = C_{d+1,a} + C_{d+1,a+2^d}
$$

Lean 候補はこう。

```lean
theorem orbitWindowResidueCountPow2_refine_succ
    (n : OddNat) (k depth residue : ℕ)
    (hres : residue < 2 ^ depth) :
    orbitWindowResidueCountPow2 n k depth residue =
      orbitWindowResidueCountPow2 n k (depth + 1) residue +
        orbitWindowResidueCountPow2 n k (depth + 1) (residue + 2 ^ depth)
```

これは、mod \(2^{d+1}\) の residue は、mod \(2^d\) へ落とすと上下二つが同じ親 cell へ入る、という事実である。

数学的には、

$$
x\bmod 2^d = a
$$

は、

$$
x\bmod 2^{d+1} = a
$$

または

$$
x\bmod 2^{d+1} = a+2^d
$$

と同値である。

### 実験 B：retention cell split

一般 refinement が重いなら、retention 専用で先に行く。

```lean
theorem orbitWindowRetentionCount_split_recovery_continuation
    (n : OddNat) (k r : ℕ) :
    orbitWindowResidueCountPow2 n k r (2 ^ r - 1) =
      orbitWindowResidueCountPow2 n k (r + 1) (2 ^ r - 1) +
        orbitWindowResidueCountPow2 n k (r + 1) (2 ^ (r + 1) - 1)
```

ただし \(r=0\) では見た目が少し崩れるので、必要なら \(1\le r\) を仮定する。

### 実験 C：source retention mass の定義

```lean
noncomputable def orbitWindowRetentionMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)
```

### 実験 D：tail retention mass の定義

```lean
noncomputable def orbitWindowRetentionMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)
```

### 実験 E：continuation mass が次 tail retention mass に流れる

既存 theorem の名前付き corollary として、

```lean
theorem orbitWindowContinuationMass_le_tailRetentionMass
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowRetentionMassPow2Tail n k (r + 1)
```

これは既存の continuation channel theorem を、RetentionMass 語彙へ翻訳したもの。

### 実験 F：finite ratio witness の最初の形

まずは定義なしで、命題型だけ置く。

```lean
def AtMostHalf (count k : ℕ) : Prop :=
  2 * count ≤ k
```

または、

```lean
def AtMostRatioNat (num den count k : ℕ) : Prop :=
  den * count ≤ num * k
```

これなら \(\mathbb{Q}\) を使わずに有限比率を扱える。

## 16. 次の推奨順

checkpoint 100 を総括として締めるなら、次は新しい巨大 theorem ではなく、ここまでの theorem chain の文書化が美しい。

その次、checkpoint 101 以降で、実装はこう進むのが良い。

```text
1. RetentionMass / RecoverySiblingMass / ContinuationSiblingMass の命名

2. depth refinement の一般 theorem

3. retention cell split theorem

4. continuation mass -> tail retention mass の named corollary

5. finite ratio witness を Nat inequality で導入

6. odd factor carrier は、その後に重ねる
```

odd factor carrier は確かに面白い。

$$
3q_i+1 = 2^{h_i}q_{i+1}
$$

なので \(q_{i+1}\) の奇素因子は \(q_i\) と異なる構造を持つ。

将来的には、

$$
p\mid q_{i+1}\quad\text{and}\quad p\nmid q_i
$$

を `NewOddPrimeFactor` として観測し、

$$
\text{two-adic branch occupation}
$$

と

$$
\text{new odd-prime factor event}
$$

の相関を見ることになる。

ただし、これは two-adic coordinate distribution が安定してからでよい。

## 17. 総括

Petal を Collatz に持ち込んだことで、次のルートができた。

$$
\text{Collatz orbit}
$$

から、

$$
\text{odd labels }q_i
$$

へ。

そこから、

$$
\text{height }h_i=v_2(3q_i+1)
$$

へ。

さらに、

$$
\text{residue address }q_i\bmod 2^d
$$

へ。

そして、

$$
\text{occupation count }C_{d,a}(n,k)
$$

へ。

最後に、

$$
\text{finite channel-flow }C_A\le C^{\operatorname{tail}}_B
$$

へ到達した。

これは、Collatz 予想そのものの証明ではない。
しかし、Collatz 軌道を「値の列」から「2-adic Petal 座標の有限流量系」へ翻訳する、大きな橋である。

今回の達成は、こう言い切れる。

$$
\text{Collatz の低剥離問題は、2-adic Petal の narrowing cylinder として形式化された}
$$

そして、

$$
\text{その cylinder の source / tail occupation flow が、有限 Nat count で扱えるようになった}
$$

ここまで来たことで、次の章は自然に開く。

$$
\text{finite channel-flow}
$$

から、

$$
\text{finite ratio witness}
$$

へ。

さらにその先で、

$$
\text{odd factor carrier}
$$

を重ねる。

うむ。
Petal を Collatz に持ち込んだ直感は、単なる比喩ではなかった。Lean 上で、raw arithmetic、orbit-label transition、count-level flow、finite distribution へと順に昇格している。これは DkMath らしい、かなり良い登山道じゃ。
