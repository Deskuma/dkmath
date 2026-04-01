# FLT-BAFCT-260401-v0 の戦況評価と次の一手

うむ、これは良い戦況じゃ。
**momentum は本物** じゃよ。いま残敵が

$$
\text{sorry} =
\underbrace{\neg p^2 \nmid x'}*{\#1\ \text{descent provenance}}
+
\underbrace{\text{weak packet concrete}}*{\#2a\ \text{構成のみ}}
$$

へ綺麗に分離された、という事実そのものが大きい。しかも `#2b` の `¬ p \nmid t'` 導出は companion lemma 群で完全に消えておるから、もう architecture の混乱ではなく、**本当に残った形式化作業** だけが見えておる。

## 1. 戦況評価

まず敵の性質が違う。

`#1` は **threading 敵** じゃ。
つまり、`RealizationSeed` や descent chain の中にすでにあるはずの

$$
x = qx', \qquad q \ne p, \qquad v_p(x)=1
$$

を、`ArithmeticCoreStrong` の返り値にちゃんと運び出せていない、という問題じゃ。
これは「新しい数学」が要るのではなく、**既存データの運搬路を通す** 戦いじゃ。

`#2a` は **construction 敵** じゃ。
しかも今回の report では、weak packet packaging concrete がまだ無いことが、かなりはっきりしておる。つまりこちらは「局所補題の不足」ではなく、**まだ置かれていない concrete theorem を新設する戦い** じゃ。

## 2. どちらを先に殴るべきか

わっちの判断はこうじゃ。

$$
\boxed{
\text{次は \#2a を先に殴るべし}
}
$$

理由は 3 つある。

### 2.1. 不確実性が大きいのは #2a

`#1` は provenance threading なので、少なくとも「何を示せばよいか」は見えておる。
一方 `#2a` は、そもそも weak packet concrete の concrete provider がまだ存在するのか、あるいは target 入力がまだ弱いのか、その境界が未確定じゃ。
この **最大の不確実性** を先に潰すべきじゃ。

### 2.2. #2a が通れば `PacketPackagingStrong` が実質完成する

今や `PacketPackagingStrong` 本体では、

1. weak concrete で `pkt'`
2. `pkt'.x = x'`
3. `¬ p^2 \nmid x'`
4. companion lemma
5. `¬ p \nmid pkt'.t`

という流れまで組めておる。
つまり #2a が通れば、その戦線は almost closed じゃ。

### 2.3. #2a が失敗したときの教訓が大きい

もし #2a が通らぬなら、それは target 入力がまだ弱いと分かる。
これは architecture の再調整点を明確にする。
一方 #1 を先に潰しても、#2a が曖昧なままでは前進量が読みにくい。

---

## 3. 次の攻略方針

だから次は、`#2a` を **2 段に割って** 攻めるのがよい。

## 3.1. Stage A. `weak packet concrete` の feasibility check

まず新しい theorem を仮置きする。

```lean id="eh6h68"
theorem primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hz'lt
  sorry
```

ここで、いきなり証明を書き切ろうとせず、まず本文の最初の 5 行で

* どの既存 theorem を使って smaller packet の shape data を取るか
* あるいは shape data 自体がまだ足りないのか

を確認する。

この段階の目的は **証明完了ではなく feasibility 判定** じゃ。

## 3.2. Stage B. `weak concrete` をさらに分割

`weak packet concrete` がそのまま重ければ、次の 2 層に割る。

### A. shape data の回収

$$
z' - y' = p^{p-1} (t')^p, \qquad
GN = p (s')^p, \qquad
x' = p(t's')
$$

を smaller counterexample から取り出す層。

### B. packet packaging

上の shape data から `PrimeGe5BranchANormalFormPacket p` を組む層。

この分解で、もし A が既存 theorem から取れるなら、B は constructor 的な作業になる。
逆に A が取れないなら、そこが本当の open kernel じゃ。

## 3.3. Stage C. `PacketPackagingStrong` を完成

`weak concrete` が通ったら、もう強い版は wrapper だけで済む。
ここは勝ちやすい。

---

## 4. #1 はどう扱うか

`#1` は捨てるわけではない。
ただし順番は後じゃ。

`#1` は次の 2 補題に砕くとよい。

### 4.1. 元の正規形から (v_p(x)=1)

$$
x = p(ts), \qquad \neg p \mid t, \qquad \neg p \mid s
\Longrightarrow
\neg p^2 \nmid x
$$

### 4.2. descent で (v_p) 保存

$$
x = qx', \qquad q \ne p, \qquad \neg p^2 \nmid x
\Longrightarrow
\neg p^2 \nmid x'
$$

これで `ArithmeticCoreStrong_of_weak_and_descent` の `sorry` はかなり軽くなるはずじゃ。
だが、これは **weak concrete の feasibility が確認されてから** でよい。

---

## 5. つまり次の一手は何か

一言で言えば、こうじゃ。

$$
\boxed{
\text{次は \#2a の weak concrete 新設を先に攻める。}
}
$$

さらに具体的には、

1. `primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete` を立てる
2. その中で **shape data が既存から取れるか** を確認する
3. 取れるなら packet constructor へ流す
4. 取れぬなら target をさらに 1 段分解する
5. そのあとで #1 の threading へ戻る

これが最も損の少ない策じゃ。

---

## 6. わっちの読み

今の戦況は、

$$
\text{\#2a を攻める} \Rightarrow
\begin{cases}
\text{通れば PacketPackagingStrong 完了}\\
\text{通らねば本当の open kernel が確定}
\end{cases}
$$

となる。
どちらに転んでも得るものが大きい。
だから、策士としては **先に #2a** じゃよ。🍎

必要なら次に、その `primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete` の **攻略用 Lean skeleton** を起こすぞい。

---

よし、起こすぞい。
今の戦況整理どおり、残敵は

$$
\text{sorry} = \underbrace{\neg p^2 \nmid x'}*{\#1\ \text{descent provenance}} + \underbrace{\text{weak packet concrete}}*{\#2a\ \text{構成のみ}}
$$

で、`#2b = \neg p \nmid t'` 側は companion lemma で既に消えておる。だから次は `weak packet concrete` を **独立 theorem として探索・固定** するのが正道じゃ。

以下、`primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete` を中心にした **攻略用 Lean skeleton 全文** を置く。
これは「すぐ証明完了」ではなく、**どこで shape data が足りぬのかを露出させる probe 用 skeleton** じゃ。

```lean id="s1fpm7"
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/-!
## Weak packet concrete: exploration layer

目的:
- `PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget`
  の concrete provider を 1 本立てる。
- ここでは strongness (`¬ p ∣ pkt'.t`) は要求しない。
- まず `PrimeGe5BranchANormalFormPacket p` を実際にどう構成するかを可視化する。

設計方針:
1. smaller counterexample `(x', y', z')` から必要な shape data を集める
2. その shape data から normal form packet を組む
3. 返り値は `pkt'.z < z ∧ pkt'.x = x'`
-/

/--
packet 構成に必要な最小 shape data を bundling する作業用 structure。

`weak concrete` が重い場合は、
まずこの structure を concrete に作る theorem を先に立てる。
-/
structure PrimeGe5BranchAPrimitivePacketShapeData (p x' y' z' : ℕ) where
  hp_dvd_gap : p ∣ (z' - y')
  hgap       : z' - y' = p ^ (p - 1) * t ^ p
  hsGN       : GN p (z' - y') y' = p * s ^ p
  hsx        : x' = p * (t * s)
  t : ℕ
  s : ℕ

/--
ShapeData から packet を組む target。

もし既存 concrete packet constructor が無いなら、
この target を先に埋めるとよい。
-/
abbrev PrimeGe5BranchAPrimitivePacketOfShapeDataTarget : Prop :=
  ∀ {p x' y' z' : ℕ},
    PrimeGe5CounterexamplePack p x' y' z' →
    PrimeGe5BranchAPrimitivePacketShapeData p x' y' z' →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.x = x' ∧ pkt'.y = y' ∧ pkt'.z = z'

/--
smaller counterexample から ShapeData を取り出す target。

もし `weak concrete` が直接重いなら、
まずこの target を concrete にする。
-/
abbrev PrimeGe5BranchAPrimitivePacketShapeDataOfSmallerCounterexampleTarget : Prop :=
  ∀ {p x' y' z' : ℕ},
    PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') →
    ∃ data : PrimeGe5BranchAPrimitivePacketShapeData p x' y' z',
      True

/--
ShapeData を使って weak concrete を得る橋。

これは no-sorry で通るべき部分。
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete_of_shapeData_and_packet
    (hShape :
      PrimeGe5BranchAPrimitivePacketShapeDataOfSmallerCounterexampleTarget)
    (hPacket :
      PrimeGe5BranchAPrimitivePacketOfShapeDataTarget) :
    PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hz'lt
  rcases hShape hpack' hp_dvd_gap' with ⟨data, _⟩
  rcases hPacket hpack' data with ⟨pkt', hx_eq, hy_eq, hz_eq⟩
  refine ⟨pkt', ?_, hx_eq⟩
  simpa [hz_eq] using hz'lt

/--
直接版の weak concrete provider。

最初はここをすぐ埋めようとせず、
下の 2 つの open kernel
- ShapeData 抽出
- packet constructor
へ分けて攻略するとよい。
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget := by
  -- 第1段階では、下の 2 subtargets を concrete にする方針で進める。
  apply
    primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete_of_shapeData_and_packet
  · exact primeGe5BranchAPrimitivePacketShapeDataOfSmallerCounterexample
  · exact primeGe5BranchAPrimitivePacketOfShapeData

/--
Open kernel A:
smaller counterexample から shape data を取り出す concrete provider。

ここで探すもの:
- `hgap : z' - y' = p^(p-1) * t^p`
- `hsGN : GN p (z' - y') y' = p * s^p`
- `hsx  : x' = p * (t*s)`

もし既存 theorem がそのまま無ければ、
この theorem をさらに 2 本へ割る:
- gap/GN shape 回収
- x' = p*(t*s) 回収
-/
theorem primeGe5BranchAPrimitivePacketShapeDataOfSmallerCounterexample
    : PrimeGe5BranchAPrimitivePacketShapeDataOfSmallerCounterexampleTarget := by
  intro p x' y' z' hpack' hp_dvd_gap'
  /-
  TODO 探索メモ:
  1. existing weak restore / smallerCounterexample route を grep
  2. `z' - y' = p^(p-1) * t^p` を返す theorem を拾う
  3. `GN ... = p * s^p` を返す theorem を拾う
  4. `x' = p*(t*s)` を返す theorem を拾う
  5. 最後に `⟨{...}, trivial⟩` で返す
  -/
  sorry

/--
Open kernel B:
ShapeData から packet を組む concrete provider。

ここは「構成」であって、strongness はまだ要求しない。
返り値は `pkt'.x = x' ∧ pkt'.y = y' ∧ pkt'.z = z'` としておくと、
後段で `hx_eq ▸ hx'_not_sq` に流しやすい。
-/
theorem primeGe5BranchAPrimitivePacketOfShapeData
    : PrimeGe5BranchAPrimitivePacketOfShapeDataTarget := by
  intro p x' y' z' hpack' data
  /-
  TODO 探索メモ:
  1. `PrimeGe5BranchANormalFormPacket` の constructor / field 順を確認
  2. 必須 field:
     - pack
     - hp_dvd_gap
     - hgap
     - hsGN
     - hsx
     - t
     - s
  3. `data` の中身をそのまま流し込めるか確認
  4. 返り値の equality は `rfl` または `simp`
  -/
  sorry

end DkMath.FLT
```

## 使い方

この skeleton の狙いは、`weak concrete` をさらに

$$
\text{ShapeData 抽出} + \text{packet constructor}
$$

へ割ることじゃ。
こうすると、いまの敵 `#2a` が

* `#2a-1`: shape data をどこから取るか
* `#2a-2`: packet をどう組むか

へ分かれる。
これは探索にも Codex にも人手にも優しい。

## 攻略順

次はこう動くとよい。

### 1. `PrimeGe5BranchANormalFormPacket` の constructor を確認

`fields` の順と、`hsx` の正確な shape を見る。

### 2. `smaller counterexample` から `hgap`, `hsGN`, `hsx` を取る theorem を grep

この段階では theorem 名の特定だけでよい。

### 3. `primeGe5BranchAPrimitivePacketOfShapeData` を先に通す

もし constructor が明瞭なら、こちらは先に no-sorry にできる可能性が高い。

### 4. 最後に `ShapeDataOfSmallerCounterexample` を攻める

ここが実質的な探索本丸じゃ。

## わっちの見立て

この skeleton にすると、戦況はさらにこう整理される。

$$
\text{残敵} =
\underbrace{\neg p^2 \nmid x'}*{\#1}
+
\underbrace{\text{ShapeData 抽出}}*{\#2a-1}
+
\underbrace{\text{packet constructor}}_{\#2a-2}
$$

このうち `#2a-2` は軽い可能性が高い。
だから、次の 1 勝は **packet constructor 側** から取れるかもしれぬ。
それで momentum をさらに増やすのが良いの。

必要なら次に、
**`rg` / `grep` でどの theorem 名を探すかの具体的探索プロンプト集**
まで起こすぞい。
