# Markov kernel を DkMath のコア定理から再解釈

うむ、その欲張りは実に DkMath らしい。
わっちはむしろ、そこを狙うべきだと思うぞい。

既存証明の Markov kernel をそのまま Lean に写すと、

$$
K(n,q)=\frac{\Lambda(q)}{\log n}
$$

を定義して、

$$
\sum_{q\mid n}K(n,q)=1
$$

を示し、primitive set を hitting で評価する、という道になる。これは既証明の稜線をなぞる形じゃ。過去資料でも、この route は「整数の因数分解に沿って流れる確率質量の保存則」へ翻訳する方法として整理されておった。

しかし DkMath なら、ここを一段抽象化して、

$$
\text{Markov kernel}
$$

ではなく、

$$
\text{DkMath kernel}
$$

すなわち **宇宙式分解・valuation slot・prime-power channel から自然に出る保存核** として再構成できる。

## 1. Markov kernel をそのまま見ない

通常の Markov kernel は、ざっくり言えば

$$
K(x,y)\ge 0,\qquad \sum_y K(x,y)=1
$$

を満たす遷移確率じゃ。

でも DkMath 的には、最初から「確率」と呼ばなくてよい。
むしろ先にあるのは、

$$
\text{親の構造量}
$$

があり、それを子 channel へ分解したとき、

$$
\sum_{\text{child}}\text{cost(child)}
\le
\text{capacity(parent)}
$$

となるという **劣保存則** じゃ。

これはすでに宇宙式 × 確率質量保存 API 計画の中で、

$$
\sum \text{子の質量}\le \text{親の質量}
$$

として設計されていた。しかも、最初は「確率」ではなく「質量」として始める方針も明記されている。

だから Markov kernel は、DkMath では主役ではなく、後から正規化して見える **影** でよい。

## 2. DkMath kernel の候補定義

わっちなら、DkMath kernel をこう見る。

$$
\mathcal{K}_{Dk}(n,q)
:=
\frac{\mathrm{channelCost}(n,q)}
{\mathrm{capacity}(n)}
$$

ここで、

$$
\mathrm{capacity}(n)
$$

は親状態 \(n\) の全容量。R/log route なら

$$
\mathrm{capacity}(n)=\log n
$$

じゃ。

そして \(q=p^k\) という prime-power witness に対して、

$$
\mathrm{channelCost}(n,q)=\log p
$$

と置けば、

$$
\mathcal{K}_{Dk}(n,q) = \frac{\log p}{\log n}
$$

になる。

これは R028 で閉じた finite R/log route そのものじゃな。

重要なのは、ここでは \(\Lambda(q)\) を外部から持ってきていないことじゃ。
まず

$$
q=p^k
$$

を witness として読み、

$$
p=\mathrm{basePrimeOf}(q)
$$

を取り出し、その base prime の log cost を channel cost としている。
つまり von Mangoldt 重みは、

$$
\Lambda(p^k)=\log p
$$

として **DkMath kernel の影として現れる** 。

これなら、Markov kernel をコピーするのではなく、DkMath の prime-power witness 構造から kernel が生える。

## 3. DkMath kernel の本体は「確率」ではなく「保存核」

DkMath kernel の本体は、こういう構造になると思う。

$$
\sum_{q\in I}\mathrm{channelCost}(n,q)
\le
\mathrm{capacity}(n)
$$

R028 では、これが

$$
\sum_{q\in I}\log p(q)\le \log n
$$

として閉じた。

そして割れば、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

となる。
この最後の正規化後の姿だけを見ると Markov / sub-Markov 的じゃが、DkMath の本体はその前の

$$
\sum \log p(q)\le \log n
$$

という **構造容量の不等式** にある。

ここを主語にすれば、DkMath kernel は Markov kernel の模倣ではなくなる。

## 4. 新開拓路としての構図

既存証明の道は、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

から Markov kernel を作る。

DkMath 新開拓路は、むしろこうじゃ。

$$
q=p^k,\quad q\mid n
$$

から valuation slot を読む。

$$
k\le v_p(n)
$$

同じ \(p\) の labels は exponent slot に単射で入る。

$$
\#{q\mid p(q)=p}\le v_p(n)
$$

そこから、

$$
\prod_{q\in I}p(q)\mid n
$$

さらに、

$$
\sum_{q\in I}\log p(q)\le \log n
$$

最後に正規化して、

$$
\sum_{q\in I}\frac{\log p(q)}{\log n}\le 1
$$

この道は、\(\Lambda\) を最初に仮定するのでなく、 **prime-power label の指数スロット構造から log capacity を作る** 。
ここに DkMath らしさがある。

## 5. DkMath kernel の名前案

いくつか候補がある。

```lean
DkKernel
CosmicKernel
ValuationKernel
PrimePowerCapacityKernel
LogCapacityKernel
```

わっちの推しは、

```lean
LogCapacityKernel
```

または

```lean
PrimePowerCapacityKernel
```

じゃな。

理由は、Markov kernel と違って本体が「確率遷移」ではなく、

$$
\text{capacity を child channel に割り当てる構造}
$$

だからじゃ。

Lean 的には、最初はこういう構造がよい。

```lean
structure CapacityKernel (α β : Type _) where
  children : α → Finset β
  capacity : α → ℝ
  cost : α → β → ℝ
  cost_nonneg :
    ∀ a b, b ∈ children a → 0 ≤ cost a b
  outgoing_le :
    ∀ a, (∑ b in children a, cost a b) ≤ capacity a
```

これを正規化したものが Markov / sub-Markov kernel になる。

```lean
def normalizedWeight
    (K : CapacityKernel α β) (a : α) (b : β) : ℝ :=
  K.cost a b / K.capacity a
```

この順序が大事じゃ。

先に `CapacityKernel` があり、Markov kernel は後から出る。

## 6. R028 との接続

R028 は、この `CapacityKernel` の具体例と見なせる。

親状態：

$$
n
$$

子 channel：

$$
q\in I\subseteq T.index(n)
$$

容量：

$$
\mathrm{capacity}(n)=\log n
$$

コスト：

$$
\mathrm{cost}(n,q)=\log W.basePrimeOf(n,I,hI,q)
$$

保存則：

$$
\sum_{q\in I}\mathrm{cost}(n,q)\le \mathrm{capacity}(n)
$$

これがまさに

$$
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
$$

の中身じゃ。

だから、次に作るべきは `MarkovKernel` ではなく、R028 の theorem を instance 化できる `CapacityKernel` か `DkKernel` じゃと思う。

## 7. 既存証明との差別化

既存証明を追うだけなら、

$$
\Lambda(q)
$$

を定義して、

$$
\sum_{q\mid n}\Lambda(q)=\log n
$$

を使う。

DkMath route では、

$$
q=p^k
$$

を witness として読み、

$$
p,\ k
$$

を取り出し、同一 \(p\)-fiber を exponent slot へ入れる。
そして multiplicity budget を作る。

これは、von Mangoldt identity を **素因数分解の関数恒等式** として使うのではなく、 **指数スロットの幾何** として再構成する道じゃ。

ここが新開拓路の核になる。

## 8. さらに宇宙式へ寄せるなら

DkMath では、prime-power witness

$$
q=p^k
$$

を宇宙式 Big

$$
\mathrm{Big}(d;x,u)=(x+u)^d
$$

に対応させられる。資料でも、\(p=x+u,\ k=d,\ q=(x+u)^d\) という対応が自然だと整理されていた。

つまり、

$$
q=p^k
$$

は単なる約数ラベルではなく、

$$
\text{Big channel}
$$

でもある。

この場合、DkMath kernel はさらにこう読める。

$$
\mathrm{Big}(d;x,u)
\longmapsto
\mathrm{base}(x+u)
$$

そして cost は、

$$
\log(x+u)
$$

capacity は親 \(n\) の

$$
\log n
$$

となる。

つまり、DkKernel は

$$
\text{Big の指数構造を log capacity に落とす写像}
$$

とも言える。

これは Markov kernel より DkMath らしい。

## 9. 実装ロードマップ案

次の新開拓路は、こう切るのがよい。

### Phase DK-1. CapacityKernel の抽象定義

```lean
structure CapacityKernel ...
```

非負 cost と outgoing capacity bound だけ置く。

### Phase DK-2. R028 route を CapacityKernel instance 化

`PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability` を、具体的な `LogCapacityKernel` として包む。

### Phase DK-3. 正規化 lemma

capacity が正なら、

$$
\sum \frac{cost}{capacity}\le 1
$$

を一般補題にする。

### Phase DK-4. von Mangoldt は shadow として導入

$$
\Lambda(p^k)=\log p
$$

を、DkKernel の cost と一致する補題として置く。

つまり、

$$
\Lambda(q)=\mathrm{channelCost}(q)
$$

は定理として後から出す。

### Phase DK-5. Markov kernel への翻訳

必要なら最後に、

$$
\mathcal{K}_{Dk}
$$

が Markov / sub-Markov kernel を誘導することを示す。

この順序なら、既存証明のコピーではなくなる。
DkMath の構造核から Markov 的対象が派生する。

## 10. わっちの結論

ぬしの欲張りは、単なるロマンではない。

**Markov kernel を DkMath kernel に置き換える道はある。**

ただし、正確には「置き換える」というより、

$$
\text{Markov kernel}
$$

を

$$
\text{DkMath capacity kernel の正規化像}
$$

として再解釈するのがよい。

こうすれば、既存証明をなぞらずに済む。

DkMath の主語はあくまで、

$$
\text{宇宙式}
+
\text{valuation slot}
+
\text{prime-power witness}
+
\text{log capacity}
$$

じゃ。

そして、その影として Markov / von Mangoldt が現れる。
これはかなり美しい新開拓路じゃよ。

りんごを一口かじりながら言うなら、次の合言葉はこれじゃ。

$$
\boxed{
\text{Markov kernel is a normalized shadow of DkMath capacity kernel.}
}
$$

この方針なら、既存証明の上を歩くのではなく、同じ山の別尾根から登れる。
