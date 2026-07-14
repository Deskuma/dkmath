# Design Note No.104 checkpoint

## 1/4→1/8→1/16→1/2^n → 1/k, k*1/k=1

うむ。これはかなり重要な段階じゃ。
ぬしが今言っているのは、**角度でも円でもなく、保存核上のシフト操作を反復したときに、有限周期構造が細分化されていく** という観測じゃな。

これは良い。かなり良い。

## 1. いま見えている構造

最初の四状態一巡では、状態幅は \(1/4\)。
その状態の端点から中心へ移る shift は半分なので、\(1/8\)。

これを初期操作として見ると、

$$
\frac{1}{4}
\quad\mapsto\quad
\frac{1}{8}
\quad\mapsto\quad
\frac{1}{16}
\quad\mapsto\quad
\frac{1}{32}
\quad\mapsto\quad \cdots
$$

となる。

ここで大事なのは、これはまだ角度分割ではないことじゃ。
これは **保存核上の正規化周期を、shift midpoint 操作で細分化している** だけ。

```text
四状態一巡:
  1/4 単位で戻る

端点から中心への shift:
  1/8 が見える

さらに中心を端点として読む:
  1/16 が見える

再帰:
  1/2^n が見える
```

この読みはかなり自然じゃ。

## 2. 一般形はこうなる

\(1/2^n\) の単位が見えているなら、対応する return count は \(2^n\)。

$$
\text{step size}=\frac{1}{2^n}
$$

ならば、

$$
2^n\cdot\frac{1}{2^n}=1
$$

なので、\(2^n\) 回で正規化周期 \(1\) に戻る。

DkMath 的には、

```text
unit phase:
  1 / 2^n

return count:
  2^n

cycle law:
  repeat 2^n times and return
```

じゃな。

これは円ではない。
ただし、円と同じように「一巡する有限周期」が細かくなる。

## 3. 連続化の読み

この再帰を無限に続ければ、dyadic mesh が埋まっていく。

$$
\left{\frac{k}{2^n}\mid 0\le k\le 2^n\right}
$$

が、\(n\) を増やすごとに細かくなる。

これを極限で見ると、正規化周期 \([0,1]\) の中が dyadic に埋まる。

ただし、ここでもまだ円とは言わない。

```text
言えること:
  正規化周期上の dyadic refinement がある
  finite return law がある
  mesh が細かくなる
  連続パラメータ候補が生まれる

まだ言わないこと:
  円である
  円弧である
  半径 r の円周である
  角度 theta である
```

この guardrail はかなり大切じゃ。

## 4. 1/k 分割への一般化

さらに \(1/k\) 分割へ一般化すると、非常に良い。

$$
\text{step size}=\frac{1}{k}
$$

ならば、

$$
k\cdot\frac{1}{k}=1
$$

なので、\(k\) 回で戻る。

つまり、

```text
k 分割:
  unit phase = 1/k

return law:
  k steps return to 1 full cycle
```

これは「円弧」と言いたくなるが、まだ言わない方がよい。
まずは **正規化周期の k 分割観測** で十分じゃ。

Euclidean bridge を付けた後にだけ、

```text
Euclidean reading:
  k 等分の円周角
```

と読める。

ここでも順序は、

```text
保存核
  -> 正規化周期
  -> k 分割
  -> k 回で戻る
  -> Euclidean 解釈
```

じゃ。

## 5. 形状を問わないのは正しい

ぬしの「形状はまだ問わない」は正しい。

ここで証明したいのは、曲線の形ではなく、周期パラメータの構造じゃ。

```text
今問うもの:
  分割
  shift
  midpoint
  return count
  refinement
  cyclic parameter

まだ問わないもの:
  円形状
  曲率
  弧長
  半径
  Euclidean metric
```

つまり、まずは位相とパラメータの骨格を作る。

形状は、その骨格を保存核で正規化していった先に現れるものじゃ。

## 6. 半径は保存核で固定されている

ここも重要じゃ。

半径を別途意識しなくてよい、という直感はかなり正しい。

DkMath 側では、半径に相当するものは \(q2\) 保存核で固定される。

$$
q2(z)=\text{constant}
$$

が先にある。

だから、連続化で必要なのは「半径をどう設定するか」ではなく、

```text
保存核 q2 の同じ level 上で、
どのように phase parameter を細かく動かすか
```

じゃ。

つまり、半径は外から持ち込むものではなく、保存核 level としてすでに固定されている。

```text
radius-like data:
  q2 level

phase-like data:
  normalized cyclic parameter

shape reading:
  later Euclidean interpretation
```

この分離は非常によい。

## 7. Lean での証明ターゲット

この考えを Lean に載せるなら、最初はものすごく軽くてよい。

まず、正規化周期の \(k\) 分割。

```lean
def normalizedCycleStep (k : ℕ) : ℝ :=
  1 / (k : ℝ)
```

ただし \(k=0\) は避ける必要があるので、 theorem には `0 < k` を入れる。

```lean
theorem normalizedCycleStep_mul_returnCount
    {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * normalizedCycleStep k = 1 := by
  unfold normalizedCycleStep
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)]
```

次に dyadic 版。

```lean
def dyadicCycleStep (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ n
```

そして、

```lean
theorem dyadicCycleStep_returnCount (n : ℕ) :
    ((2 : ℕ) ^ n : ℝ) * dyadicCycleStep n = 1 := by
  unfold dyadicCycleStep
  field_simp [pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)]
```

この二つだけでも、かなり意味がある。

## 8. shift midpoint の証明

次に、端点から中心への shift。

\(k\) 分割の state width は \(1/k\)。
端点から中心への shift はその半分。

$$
\text{center shift}=\frac{1}{2k}
$$

dyadic なら、\(k=2^n\) なので、

$$
\text{center shift}=\frac{1}{2^{n+1}}
$$

四状態から始めるなら \(k=4\)。

$$
\text{center shift}=\frac{1}{8}
$$

Lean では、

```lean
def normalizedCenterShift (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ))
```

または、

```lean
def normalizedCellEndpoint (k i : ℕ) : ℝ :=
  (i : ℝ) / (k : ℝ)

def normalizedCellCenter (k i : ℕ) : ℝ :=
  ((i : ℝ) + 1 / 2) / (k : ℝ)
```

この方が構造的には良い。

すると、

```lean
theorem normalizedCellCenter_eq_endpoint_add_half_step
    {k : ℕ} (hk : 0 < k) (i : ℕ) :
    normalizedCellCenter k i =
      normalizedCellEndpoint k i + normalizedCycleStep k / 2
```

が欲しい。

これが「端点から中心への shift」の一般 theorem じゃ。

## 9. 極点を挟んだ中央が端点

ぬしの発想を一般化すると、各 endpoint は隣接する二つの center の中点でもある。

分割幅を \(1/k\) とすると、center は endpoint から \(1/(2k)\) だけずれる。

だから endpoint \(i/k\) は、

$$
\frac{i}{k}
===========

\frac{\left(\frac{i}{k}-\frac{1}{2k}\right)
+\left(\frac{i}{k}+\frac{1}{2k}\right)}{2}
$$

の中点。

これは良い theorem になる。

```lean
theorem endpoint_eq_midpoint_between_neighbor_centers
    {k : ℕ} (hk : 0 < k) (i : ℕ) :
    normalizedCellEndpoint k i =
      ((normalizedCellEndpoint k i - normalizedCycleStep k / 2)
        + (normalizedCellEndpoint k i + normalizedCycleStep k / 2)) / 2
```

これはかなり基本だが、意味が深い。

「端点が中心だった」の第一歩じゃ。

## 10. このルートの到達地図

ぬしの言う構造を整理すると、こうなる。

```text
4-state cycle:
  step = 1/4

endpoint-to-center shift:
  shift = 1/8

recursive shift:
  1/4 -> 1/8 -> 1/16 -> ...

dyadic refinement:
  step = 1/2^n
  return count = 2^n

general refinement:
  step = 1/k
  return count = k

shape:
  not yet specified

q2:
  conserved level, radius-like data fixed
```

これはかなりよい骨格じゃ。

## 11. 次に Codex に見るべきこと

Codex から設計書が上がってきたら、確認ポイントはこれじゃ。

```text
角度を使っていないか
円弧を使っていないか
回転を使っていないか
半径を外から導入していないか
1/8 を 45° と読んでいないか
まず 4-state cycle から 1/8 を出しているか
dyadic refinement を 1/2^n として分離しているか
general k refinement を 1/k として分離しているか
return count k を証明対象にしているか
q2 保存核を radius-like fixed level として扱っているか
```

この方針なら安全じゃ。

## 12. 結論

ぬしの構想はかなり筋が良い。

まず、

$$
\frac{1}{4}\to\frac{1}{8}\to\frac{1}{16}\to\frac{1}{32}\to\cdots
$$

を shift refinement として見る。

次に、

$$
\frac{1}{2^n}
\quad\text{returns after}\quad
2^n\ \text{steps}
$$

を証明する。

さらに、

$$
\frac{1}{k}
\quad\text{returns after}\quad
k\ \text{steps}
$$

へ一般化する。

そして、形状はまだ問わない。
半径も問わない。
なぜなら \(q2\) 保存核がすでに level を固定しているから。

これは、連続化へ進む前の **pre-geometric cyclic parameter theory** と呼べる段階じゃな。
円を作るのではなく、円のように読める周期構造が先に生まれている。
