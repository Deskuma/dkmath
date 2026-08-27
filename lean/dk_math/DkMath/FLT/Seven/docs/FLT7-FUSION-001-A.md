# FLT7-FUSION-001A (002)

## PR レビュー投稿完了

PR #73 に、英語の review submission と inline comment を投稿しました。

[Review — FLT7-FUSION-001 integer-shadow checkpoint](https://github.com/Deskuma/dkmath/pull/73#pullrequestreview-4805708030)

判定は `COMMENTED` です。コードの数学的成果は肯定しつつ、後段の FUSION に入る前に直すべき packet coherence を一点指摘しました。

---

## 判定

今回の実装は、

```text
FUSION-001A
signed integer exact seven-depth 4
```

として成功です。

Lean は整数側について、

$$
r-l=7^4d
$$

$$
\Phi_7(r,l)=7E
$$

$$
7\nmid d,\qquad 7\nmid E
$$

$$
dE=a(a+n)m^7
$$

を同一の `RamifiedSignedRootDepthPacket` に収録しました。実装レポートにも、この exact signed-root shadow が固定されたことが明記されています。

RAMIFIED 側も対称化され、

```text
root gap = axis₁³ × seventh power
quotient = axis₂³ × seventh power
```

となりました。`exists_quotientCore_associated_pow_seven` により quotient core 側にも PID 七乗抽出を適用し、`RamifiedRealCubicBalancedAxisSplitPacket` が構築されています。

---

## depth 4 の証明はきれいに閉じています

今回の整数 proof は LTE を外部の一枚定理として呼ぶのではなく、実際の quotient 恒等式から exact depth を取り出しています。

まず、

$$
r-l=7k
$$

を得ます。

次に first variation を展開して、

$$
\Phi_7(r,l)=7\bigl(l^6+7kf\bigr)
$$

という形を作ります。

ここで $7\nmid l$ なので、

$$
7\nmid\bigl(l^6+7kf\bigr)
$$

となり、quotient の $7$-depth が正確に $1$ と確定します。実装では `exists_signedQuotientRoot_exact` がこの部分です。

一方、元の整数恒等式から、

$$
7^5a(a+n)m^7=7^2kE
$$

です。

したがって、

$$
7^3\mid kE
$$

となります。

$7\nmid E$ なので、

$$
7^3\mid k
$$

です。よって $k=7^3d$ と置けて、

$$
r-l=7^4d
$$

が得られます。実装上も `hke`、`hcop`、`hk4` の順に、そのままこの論理が固定されています。

最後に $7\nmid d$ は、

$$
dE=a(a+n)m^7
$$

の右辺三因子がすべて $7$-unit であることから直接排除されています。

これは非常に良いです。Norm の非線形性に触れず、整数恒等式だけで exact nonvanishing まで完了しています。

---

## 今回見つかった唯一の本質的な packet 問題

`RamifiedSignedRootDepthPacket` は現在、

```lean
balanced : RamifiedRealCubicBalancedAxisSplitPacket
signedLeftRoot : ℤ
signedRightRoot : ℤ
```

を独立フィールドとして持っています。

constructor では正しく、

```lean
signedLeftRoot := p.leftRoot
signedRightRoot := p.rightRoot
```

を代入しています。

しかし、完成した structure の型には、

```text
signedLeftRoot
  = balanced 内の normPacket.leftRoot

signedRightRoot
  = balanced 内の normPacket.rightRoot
```

という同一性が保存されていません。

つまり constructor の内部では同じ根ですが、packet を受け取った downstream theorem からは、

```text
integer root
```

と

```text
algebraic balanced packet の norm root
```

が同じものだと証明できません。

これはまさに FUSION packet に必要な coherence です。

### 推奨修正

最も強い設計は、独立フィールドを消して canonical projection にすることです。

```lean
def RamifiedSignedRootDepthPacket.signedLeftRoot
    (p : RamifiedSignedRootDepthPacket) : ℤ :=
  p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.leftRoot

def RamifiedSignedRootDepthPacket.signedRightRoot
    (p : RamifiedSignedRootDepthPacket) : ℤ :=
  p.balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.rightRoot
```

変更量を小さくするなら、次の coherence field を足せばよいです。

```lean
signedLeftRoot_eq :
  signedLeftRoot =
    balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.leftRoot

signedRightRoot_eq :
  signedRightRoot =
    balanced.axisDrop.depthLedger.exactPower.upToUnit.normPacket.rightRoot
```

この点は該当行への inline review comment としても記録しました。

---

## `FUSION-001` 全体はまだ閉じていません

元の `FLT7-FUSION-001.md` における FUSION-001 は、

```text
integer signed-root depth 4
+
norm first-variation bridge
```

の二枚構成です。

今回完成したのは前半です。

実装レポート自身も次の候補として、

```text
coordinate-level norm first-variation theorem
```

を挙げています。

したがって、現在地点は次のように分けるのが正確です。

```text
FUSION-001A
  signed integer exact depth 4
  COMPLETE

FUSION-001B
  norm first-variation bridge
  OPEN
```

整数 routing は exact nonvanishing を担当し、Norm first variation は、

$$
\frac{10+2}{3}=4
$$

という depth 変換の理由を担当します。元設計でもこの役割分担が明示されています。

---

## `Outcome A` の用語は分けた方がよいです

今回の issue comment では「Outcome A まで固定」とありますが、元ロードマップでは FUSION-002 の Outcome A は、

```text
x^7 が source plane にあるなら
x 自身も source plane にある
```

という分類結果を意味します。

今回の実装では source-plane classification はまだ行われていません。

したがって現在の結果は、

```text
FUSION-001A complete
```

または、

```text
integer-shadow outcome complete
```

と呼ぶ方が、FUSION-002 の A/B/C 分岐と衝突しません。

---

## 次の最短手

### 0. root coherence の修正

まず `signedLeftRoot` と `signedRightRoot` を balanced packet の canonical roots に固定します。

これで初めて、

```text
algebraic root
=
integer signed root
```

という輸送路が公開 API 上で成立します。

### 1. `IsCoprime d E`

次は計画どおり、

```lean
theorem gapRoot_isCoprime_quotientRoot
    (p : RamifiedSignedRootDepthPacket) :
    IsCoprime p.gapRoot p.quotientRoot
```

です。

証明核はすでに揃っています。

共通素因子 $q$ が $d$ と $E$ を割ると仮定します。

$7\nmid d$ と $7\nmid E$ より、

$$
q\ne7
$$

です。

$q\mid d$ から、

$$
q\mid r-l
$$

です。

$q\mid E$ から、

$$
q\mid\Phi_7(r,l)
$$

です。

first variation 恒等式より、

$$
\Phi_7(r,l)-7l^6=(r-l)F(r,l)
$$

なので、

$$
q\mid7l^6
$$

です。

$q\ne7$ だから、

$$
q\mid l
$$

となります。

さらに $q\mid r-l$ なので、

$$
q\mid r
$$

です。

これは `IsCoprime l r` に反します。

この proof は `signedSeventhQuotient_sub_seven_mul_pow_six` をそのまま使用でき、追加の数体理論を必要としません。

### 2. canonical 2×3 routing

その後、

$$
dE=a(a+n)m^7
$$

と、

```text
gcd(d,E)=1
gcd(a,a+n)=1
gcd(a,m)=1
gcd(a+n,m)=1
```

を入力として、固定された $2\times3$ routing board を作れます。

```text
                 a           a+n          m^7
            ┌─────────┬───────────┬───────────┐
d           │   d₁₁   │    d₁₂    │    U^7    │
            ├─────────┼───────────┼───────────┤
E           │   e₁₁   │    e₁₂    │    V^7    │
            └─────────┴───────────┴───────────┘
```

ここで整数側にも、既存の FLT7 routing machinery を再利用できる入口が開きます。

### 3. Norm first variation

その後に座標展開で、

```lean
theorem norm_firstVariation_depth_ten ...
```

を置き、

```text
theta-depth 10
    ↓
seven-depth 4
```

を説明します。

重要なのは、exact depth $4$ の非零性は既に整数 route が証明済みなので、Norm 側では leading coefficient の nonzero を一から戦う必要がないことです。

### 4. FUSION-002

ここまで終えてから、

```lean
x.thd = ?
```

の seventh-root source-plane classification に入るのが自然です。

---

## 文書上の修正点

`docs/STATUS.md` 冒頭は現在も、

```text
PR #65
feature/FLT7-magic-core-260722-v0
wip/FLT7-magic-core-260722-WiseWolf
```

を指しています。

ここは、

```text
PR #73
feature/FLT7-magic-core-260722-v1
wip/FLT7-fusion-260729
```

へ更新が必要です。

---

## 総合結論

今回の成果は大きいです。

```text
RAMIFIED balanced algebraic split
        +
signed integer exact depth 4
        +
normalized product equation
```

まで到達しました。

特に、

$$
r-l=7^4d,\qquad 7\nmid d
$$

を Norm の加法性なしで固定したことにより、整数 shadow は観測ではなく theorem packet になりました。

残る immediate task は数学的穴ではなく、まず API 上の同一性保存です。

```text
balanced algebraic roots
=
stored signed integer roots
```

を packet に刻み、その直後に `IsCoprime d E` を証明すれば、canonical $2\times3$ routing が起動します。

現在地点は明確に、

```text
FUSION-001A COMPLETE
FUSION-001B NEXT
```

です。
