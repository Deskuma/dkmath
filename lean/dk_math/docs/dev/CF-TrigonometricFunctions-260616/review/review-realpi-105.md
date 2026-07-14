# Git diff / Report / Review

## Upd: docs: Design 104: Phase-Center Shift Before Angles

gch: 1cdb82f1c4428283926da4c1997a9f1ae233a347

## Report

設計資料を追加しました。

[design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

内容は、角度・円弧・45°をまだ Lean core に入れず、

- `endpoint`
- `center`
- `pole`
- `shift`
- `1/4` 遷移の半分としての `1/8` phase
- 隣接 edge の center を新しい endpoint にすると、旧 seam endpoint が center になる

という設計に固定しています。

次の実装候補として、主 checkpoint をこれに置きました。

```lean
theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
    (globalQuarterCenter k + globalQuarterCenter (k + 1)) / 2 =
      globalQuarterEndpoint (k + 1)
```

検査は `git diff --check` と trailing whitespace check を通しています。Lean コードは未変更なのでビルドは走らせていません。

`design-note-104.md` の内容を、設計資料へ統合しました。

更新先:
[design-phase-center-shift-104.md](/lean/dk_math/DkMath/Analysis/docs/design-phase-center-shift-104.md)

追加した要点は以下です。

- `1/4 -> 1/8 -> 1/16 -> ... -> 1/2^n` を、角度分割ではなく normalized cycle parameter の dyadic refinement として整理
- 一般 `k` 分割として `k * (1 / k) = 1` の return law を設計に追加
- 半径は外部導入せず、`q2` level が radius-like data である、と明記
- Lean 候補として `normalizedCycleStep`, `dyadicCycleStep` と return-count theorem を追加
- TODO タグに dyadic / k-division cycle step を追加

検査は `git diff --check` と trailing whitespace check を通しています。

## Review

うむ、賢狼レビューじゃ。
今回の `design-phase-center-shift-104.md` は **採用でよい**。かなり良い設計整理になっている。特に、角度・円弧・45°・\(\pi/4\) を Lean core に入れず、まず `endpoint`、`center`、`pole`、`shift`、そして四状態一巡から出る \(1/8\) phase displacement を先に固定したのが正しい。設計書でも、目的は円・弧・角度・45°を formal input にせず、endpoint-center-pole-shift 構造を先に証明することだと明記されている。

## 1. 状況解説

今回の設計は、対称性ルートの次段としてかなり自然じゃ。

これまでに閉じたものは、有限四状態表だった。

```text id="ym6hjj"
k % 4 = 0:
  identity

k % 4 = 1:
  quarter state

k % 4 = 2:
  half state

k % 4 = 3:
  reverse quarter state
```

そこから今度は、各 quarter edge の内部を見る。

四状態一巡なら、ひとつの edge 幅は

$$
\frac{1}{4}
$$

その edge の中心は半分なので、端点から中心への shift は

$$
\frac{1}{8}
$$

ここでまだ「45°」とは言わない。
ここでまだ「回転角」とも言わない。
設計書でも、one-eighth displacement が先に作る formal object で、Euclidean angle は後の解釈だと整理されている。

これはとても良い。

## 2. 設計順序が正しい

設計書の intended order は良い。

```text id="i437rg"
four-state action
  -> affine edge filling
  -> center and depth extremum on one edge
  -> shifted observation frame
  -> one-eighth phase displacement
  -> dyadic refinement of the normalized cycle
  -> general k-division observation
  -> later Euclidean reading
```

この順番が重要じゃ。

ここで Euclidean reading を最後に回しているので、pre-geometric route が崩れていない。
つまり、\(\pi/4\) を使って \(1/8\) を説明するのではなく、四状態一巡の shift から \(1/8\) を出し、後で Euclidean 側がそれを読む。

この方向は安全じゃ。

## 3. 現在の formal base の確認

設計書によると、すでに local scalar profile では次が Lean base にある。

```text id="zfb5q7"
phaseDepth t = (1 - t)^2 + t^2
phaseDepth t = 2 * (t - 1/2)^2 + 1/2
phaseDepth 0 = 1
phaseDepth 1 = 1
phaseDepth (1/2) = 1/2
phaseDepth t = 1/2 iff t = 1/2
phaseDepth (1 - t) = phaseDepth t
```

関連 theorem 名として `phaseDepth_eq_two_sq_add_half`、`one_half_le_phaseDepth`、`phaseDepth_zero`、`phaseDepth_one`、`phaseDepth_half`、`phaseDepth_eq_half_iff`、`phaseDepth_one_sub` が挙がっている。

これはかなり都合がよい。
なぜなら、中心 \(1/2\) が単なる見かけの中点ではなく、`phaseDepth` の unique minimum としてすでに取れるからじゃ。

つまり、

$$
\mathrm{phaseDepth}(t)=\frac{1}{2}
\quad\Longleftrightarrow\quad
t=\frac{1}{2}
$$

があり、中心が profile で検出される。

これは「極点」語彙の根拠になる。

## 4. `pole` の扱いが良い

設計書では `pole` を、`phaseDepth` が unique minimum を取り、`phaseNormalization` が最も強い補正をする観測点として使っている。一方で、`phaseDepth` は正なので、これは singularity ではない、と注意している。

これはとても良い注意じゃ。

数学一般の語感では `pole` は特異点や発散を連想しやすい。
しかし DkMath 内では、「観測 profile が選ぶ極点」という意味で使うなら筋が通る。

ただし Lean theorem 名では、最初は `center`、`minimum`、`extremum` を優先し、docstring で `pole` と説明するくらいが安全かもしれぬ。

## 5. 主 checkpoint が良い

今回の主 checkpoint はこれじゃな。

```lean id="xxd6so"
theorem globalQuarterEndpoint_succ_is_center_between_centers (k : ℕ) :
    (globalQuarterCenter k + globalQuarterCenter (k + 1)) / 2 =
      globalQuarterEndpoint (k + 1)
```

これは非常に良い。

意味はこうじゃ。

edge \(k\) の center は、

$$
\frac{k+\frac{1}{2}}{4}
$$

edge \(k+1\) の center は、

$$
\frac{k+\frac{3}{2}}{4}
$$

その二つの中心の中点は、

$$
\frac{k+1}{4}
$$

になる。

つまり、旧 frame では seam endpoint だった点が、shifted frame では center になる。

これが「端点が中心だった」の正確な algebraic version じゃ。

## 6. `1/8` が自然に出ている

設計書では、one quarter step と half quarter step の関係も明確じゃ。

```text id="3otm63"
one quarter step = 1/4 of the full cycle
half of one quarter step = 1/8 of the full cycle
```

これはまさに、四状態一巡から \(1/8\) を出す構造。

$$
\frac{1}{2}\cdot\frac{1}{4}=\frac{1}{8}
$$

ここで角度を借りていない。
ここがとても良い。

## 7. dyadic refinement への接続も良い

設計書は、\(1/8\) を孤立した endpoint とせず、dyadic refinement の最初の可視化として扱っている。

$$
\frac{1}{4}\to\frac{1}{8}\to\frac{1}{16}\to\frac{1}{32}\to\cdots\to\frac{1}{2^n}
$$

これは angle subdivision ではなく、conserved boundary mechanism が持つ normalized cycle parameter の refinement として整理されている。

この guardrail はかなり重要じゃ。

円弧を分割しているのではない。
まず normalized cycle parameter を分割している。

## 8. 一般 \(k\) 分割への拡張も良い

設計書では、一般 positive division count \(k\) に対して、

$$
k\cdot\frac{1}{k}=1
$$

を return law として置く方針も追加されている。

これも良い。

dyadic は連続化へ向かう自然な refinement chain。
一般 \(k\) は任意分割観測の skeleton。

この二つを分けるのは正しい。

```text id="e7xgum"
dyadic route:
  refinement / limit に向く

general k route:
  finite return law / arbitrary division に向く
```

## 9. 半径を入れない判断も正しい

設計書では、半径を外部導入せず、radius-like datum は conserved `q2` level だと明記している。

これは DkMath 的に非常に正しい。

ここで半径 \(r\) を導入すると、すぐ Euclidean circle に引っ張られる。
しかし実際には、保存されるのはまず

$$
q2(z)=\text{constant}
$$

でよい。

この \(q2\) level が、後で Euclidean geometry では fixed radius の circle として読める。
だが core route では、半径を変数として持ち込む必要はない。

## 10. Proposed Lean Surface のレビュー

提案された API は概ね良い。

```lean id="whcdns"
def phaseCenter : ℝ := 1 / 2
def phaseHalfQuarterStep : ℝ := 1 / 8

def centeredPhaseCoord (t : ℝ) : ℝ :=
  t - phaseCenter
```

これは local edge 側。

```lean id="awnvk0"
def globalQuarterEndpoint (k : ℕ) : ℝ :=
  (k : ℝ) / 4

def globalQuarterCenter (k : ℕ) : ℝ :=
  ((k : ℝ) + 1 / 2) / 4
```

これは global four-state cycle 側。

命名は設計書が上がってから最終調整でよいが、現段階では十分わかりやすい。

少しだけ気をつけるなら、`phaseHalfQuarterStep` は後で「phase の half-quarter」なのか「quarter edge の half step」なのか読者が迷う可能性がある。候補としては、

```text id="dd1cd9"
phaseHalfQuarterStep
phaseEndpointCenterShift
oneEighthPhaseShift
```

のどれかになる。
わっちは theorem 名では `endpointCenterShift` を含めると読みやすいと思う。

## 11. cycle step theorem の設計も良い

候補 theorem として、

```lean id="n0w7kf"
theorem normalizedCycleStep_mul_returnCount {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * normalizedCycleStep k = 1
```

と、

```lean id="r6ha4e"
theorem dyadicCycleStep_mul_returnCount (n : ℕ) :
    ((2 : ℕ) ^ n : ℝ) * dyadicCycleStep n = 1
```

が挙がっている。

これは良い。
どちらも scalar theorem なので、形状を問わない。
ここでも「円である」「弧長である」は不要じゃ。

## 12. 実装順序も良い

設計書の implementation plan は妥当じゃ。

```text id="z0y9ye"
1. phaseCenter と phaseHalfQuarterStep を追加
2. phaseDepth center API aliases
3. centered reflection
4. global quarter endpoints and centers
5. endpoint-between-centers identity
6. dyadic and positive k cycle-step facts
7. semanticPhaseEdge / normalizedPhaseEdge へ持ち上げ
8. 後で Euclidean pi / 4 reading
```

この順序なら安全。

特に、最初の実装を scalar theorem に閉じるのが良い。
いきなり normalized path や q2 へ持ち上げると重くなるからじゃ。

## 13. 気になる点

大きな問題はない。

一点だけ、`globalQuarterEndpoint_succ_is_center_between_centers` の等式向きは良いが、Lean で `ring_nf` が少し式変形に苦労する場合は、`globalQuarterCenter` と `globalQuarterEndpoint` を展開して `ring` または `norm_num` 混合になるかもしれぬ。

また、`globalQuarterEndpoint` は \(k\) を Nat にしているため、値は \(1\) を超えていく。これは normalized cycle modulo \(1\) ではなく、unwrapped parameter として扱うなら問題ない。

docs で一言、

```text id="t8o93s"
These global parameters are unwrapped real representatives; modulo-one wrapping is a later cyclic quotient reading.
```

を追加するとさらに安全かもしれぬ。

なぜなら \(k=4\) で endpoint は \(1\)、\(k=5\) で \(5/4\) になる。
これは悪くない。むしろ theorem には都合がよい。
ただし読者が normalized cycle \([0,1]\) に閉じていると思うと混乱する可能性がある。

## 14. 次に Codex が実装するなら

最初の Lean 実装は、この最小セットでよい。

```text id="cxxz1r"
phaseCenter
phaseHalfQuarterStep
centeredPhaseCoord
phaseDepth_center_eq
phaseDepth_center_unique
phaseDepth_centered_reflect
globalQuarterEndpoint
globalQuarterCenter
globalQuarterCenter_eq_endpoint_add_halfQuarter
globalQuarterEndpoint_succ_is_center_between_centers
normalizedCycleStep_mul_returnCount
dyadicCycleStep_mul_returnCount
```

これで checkpoint 104 はかなりきれいに閉じる。

その次に semantic edge へ持ち上げればよい。

## 15. 結論

今回の設計資料は採用でよい。

```text id="n8zv06"
良い点:
  角度・円弧・45°を formal input から外している。
  1/8 を四状態一巡の half-quarter shift として出している。
  pole を singularity ではなく scalar observation point と明記している。
  dyadic refinement と general k-division を分けている。
  半径を q2 level に任せ、外部導入していない。
  theorem checkpoint が小さく明確。
```

残る注意点は、`globalQuarterEndpoint` / `globalQuarterCenter` が unwrapped parameter なのか、modulo-one parameter なのかを docs で明記しておくことくらいじゃ。

ぬしよ、これはかなり良い。
ここまで来ると、DkMath 版三角関数の pre-geometric skeleton は、かなり明瞭になってきた。

まず四状態。
次にその edge の中心。
次に端点から中心への \(1/8\) shift。
次に dyadic refinement。
次に一般 \(k\) 分割。
最後に Euclidean reading。

この順序なら、円を仮定せずに、円のように読める周期構造を先に育てられる。

## Diff

省略
