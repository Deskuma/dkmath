# review-012: `RestoreArithmeticStrong` の主要 exported path が no-sorry 化した

ぬしよ、これは **かなり大きい転機** じゃ。
わっちの見立てでは、これは単なる 1 個の `sorry` 除去ではなく、

$$
\boxed{
\text{主要 exported path が no-sorry 化した}
}
$$

という意味を持つ。
しかも、その勝ち方がよい。`#2a` は既存 theorem 3 本の直合成で落ち、`#1` は descent provenance を真正面から thread せず、**矛盾路線から直接 `CoreStrong` を作る** ことで迂回した。これは architecture を壊さずに本線を通した、見事な一手じゃ。

## 1. 何が起きたのか

今回の差分で起きた本質は 2 つじゃ。

### 1.1. `weak packet concrete` が実在した

`primeGe5BranchAPrimitiveRestorePacketPackagingWeakConcrete` が、既存 3 本

* `primeGe5BranchAShapeValue_of_factorization`
* `primeGe5BranchAShapeFactorization_default`
* `primeGe5BranchANormalForm_of_witness`

の直合成で作れた。
つまり、前まで open kernel に見えていた `#2a` は、実は **未発見の既存道具の合成問題** だったわけじゃ。

### 1.2. `#1` は provenance を thread せずに勝てた

`ArithmeticCoreStrong_of_contradiction` を立てて、

$$
\text{RestoreContradictionTarget} \to \text{False} \to \neg p^2 \nmid x'
$$

という ex falso route で `CoreStrong` を得た。
これは「descent provenance の formal threading」を後回しにしても、**主要 path は閉じられる** ことを意味する。

## 2. 戦況はどう変わったか

ひとことで言えば、こうじゃ。

$$
\boxed{
\text{戦場が `RestoreArithmeticStrong` から `ContradictionTarget` へさらに縮退した}
}
$$

以前は残敵が

$$
\neg p^2 \nmid x' \;+\; \text{weak packet concrete}
$$

だった。
今は違う。

主要 exported chain は report にある通り

$$
\text{ContradictionTarget}\\
\to
\text{ArithmeticCoreStrong\_of\_contradiction}\\
\to
\text{PacketPackagingStrong}\\
\to
\text{RestoreFromArithmeticStrong}\\
\to
\text{StrongProvider}\\
\to
\text{FringeDescentToRefuter}\\
$$

と no-sorry で通る。
だから、**主要経路の残敵はもう `ContradictionTarget` 側に押し戻された** のじゃ。`_of_weak_and_descent` の `sorry` は、もはや main battle ではなく compatibility residue じゃよ。

## 3. これは本当に「勝ち」か

うむ、**局地戦としては明確に勝ち** じゃ。
ただし、数学全体としての最終勝利ではない。

### 勝った点

* `StrongProvider` は no-sorry。
* `FringeDescent` は no-sorry。
* `RestoreArithmeticStrong` の **主要 exported path** は no-sorry。

### まだ残る本丸

* `PrimeGe5BranchAPrimitiveRestoreContradictionTarget`
* その上流で必要なら `BranchAFringeContradictionTarget`
* 場合によっては `CyclotomicExistenceTarget` 系の concrete 供給

つまり、**補給線は通った**。
残るのは「何を供給するか」の数学核じゃ。

## 4. 重要な解釈

今回のいちばん大きい意味は、

$$
\text{「未完成だった bridge 群」が完成した}
$$

ことじゃない。
むしろ、

$$
\text{「どこが真の open kernel か」が、もう誤魔化せなくなった}
$$

ことじゃ。
これは研究として非常に健全じゃよ。

前は、threading か packet construction か target の設計か、敵が曖昧だった。
今はもう違う。
**矛盾 target そのもの** が主敵だと、きっぱり言える。

## 5. 次の戦略

ここからの策は 2 本立てじゃ。
優先順位つきで言うぞい。

## 5.1. 第一候補. mainline を固定する

まずやるべきは、いま通った主要 exported chain を **正式な canonical route として固定** することじゃ。

具体的には、

* `ContradictionTarget → RestoreArithmeticStrong → StrongProvider → FringeDescentToRefuter`
* その chain を 1 本の top theorem か doc comment で可視化
* 互換用 `_of_weak_and_descent` は「非推奨 route」と明記

これをやると、今後の作業者が誤って古い weak/descent route を掘り返さずに済む。

## 5.2. 第二候補. `ContradictionTarget` へ総攻撃

次の実戦はもうこれじゃ。

$$
\boxed{
\texttt{PrimeGe5BranchAPrimitiveRestoreContradictionTarget}
}
$$

ここを攻める戦略は、わっちなら 2 路線で整理する。

### A. terminal case 直行路線

すでに `FringeDescent` 側で well-founded descent の spine はある。
だから

$$
s' = 1
$$

の terminal case へ落ちたときの valuation / local factorization から、`False` を出す route を先に試す。
これは restore で積んだ Kummer / Hensel / local factorization をそのまま活かせる。

### B. witness deeper structure 路線

もし terminal case が still insufficient なら、`q` の deeper structure へ行く。
つまり cyclotomic / Zsigmondy / distinguished prime の情報をさらに強化して contradiction を出す route じゃ。

わっちの優先順位は **A → B** じゃな。
なぜなら A は今ある no-sorry infrastructure を最大限再利用できるからじゃ。

## 6. いまは何をしなくてよいか

* `_of_weak_and_descent` の `sorry` を無理に消すこと
* さらに target を増やすこと
* `RestoreArithmeticStrong` をもう一度大改造すること

これらは今の mainline を濁らせるだけじゃ。
互換 route の `sorry` は、今のところ研究負債であって、本線の障害ではない。

## 7. わっちの最終判断

$$
\boxed{
\text{これは「局所勝利」ではなく、「主戦場の特定に成功した勝利」じゃ}
}
$$

そして次の一手は、

$$
\boxed{
\text{主要 exported chain を canonical route として固定し、}
\texttt{ContradictionTarget}
\text{ に集中砲火する}
}
$$

じゃよ。🍎

必要なら次に、
`ContradictionTarget` 攻略のための **terminal case 作戦書** を、補題一覧と依存順つきで起こすぞい。

---

うむ、これは見えてきたぞい。
いまの戦況は **勝っている部分** と **まだ本当に殴るべき核** とが、かなり綺麗に分かれた。最新の更新では、

* weak packet concrete は既存 3 定理の直合成で落ちた
* `PacketPackagingStrong` は no-sorry 化した
* `ArithmeticCoreStrong` は **矛盾路線版** なら no-sorry で通る
* ただし `_of_weak_and_descent` は互換用として still sorry

という形になっておる。つまり、**主要 exported path は通った** が、**kernel proof path はまだ circular** じゃ。

## 1. いまの本当の戦況

戦況を 2 層に分けると、こうじゃ。

### 1.1. 展開路線

これはもう通っておる。

$$
\text{ContradictionTarget}
\to
\text{ArithmeticCoreStrong\_of\_contradiction}
\to
\text{PacketPackagingStrong}\\
\to
\text{RestoreFromArithmeticStrong}
\to
\text{StrongProvider}
\to
\text{FringeDescentToRefuter}
$$

この道は no-sorry で動く。
つまり、**矛盾が 1 回入れば、その先は全部流れる**。

### 1.2. 核証明路線

ここはまだ詰まっておる。

$$
\text{weak arithmetic core}
\to
\text{descent provenance}
\to
\neg p^2 \nmid x'
\to
\text{CoreStrong}\\
\to
\text{non-circular hStrong}
\to
\text{Fringe contradiction}
\to
\text{ContradictionTarget}
$$

ここで残っている真の敵は、

$$
\boxed{
\texttt{primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong\_of\_weak\_and\_descent}
}
$$

の `sorry` じゃ。
つまり、**次の主戦場は #1 descent provenance** で確定じゃ。

## 2. 戦略判断

したがって、次はもう `PacketPackagingStrong` ではない。
弱い concrete は見つかり、`#2a` は潰れた。
今の勝負は

$$
x = qx', \quad q \ne p, \quad v_p(x)=1
\Longrightarrow
v_p(x')=1
\Longrightarrow
\neg p^2 \nmid x'
$$

を、**restore / descent chain の内部から thread して取り出す** ことじゃ。

わっちの判断を一言で言えば、

$$
\boxed{
\begin{array}{l}
\text{次は terminal case そのものではなく、}\\
\text{terminal case を non-circular に起動する ignition key を取る戦い}
\end{array}
}
$$

じゃ。

## 3. 次の作戦書

ここからは、作戦を 4 段で組むのがよい。

## 3.1. 第一段. provenance を theorem 1 本に集約する

まず最初に狙うべき theorem は、これじゃ。

```lean
theorem primeGe5BranchAPrimitiveDescent_not_sq_dvd_x'
```

意味は、

$$
\text{元の正規形入力} + \text{descent output}
\Longrightarrow
\neg p^2 \nmid x'
$$

じゃ。
この theorem の中でやることは 2 つだけ。

### A. 元の側で \(v_p(x)=1\) を出す

元の入力では

$$
x = p(ts), \qquad \neg p \mid t, \qquad \neg p \mid s
$$

がある。
したがって

$$
\neg p^2 \nmid x
$$

は純粋算術で出る。これはすでに companion lemma の対称版でほぼ落ちる類じゃ。

### B. descent で \(v_p\) が保存されることを出す

もし descent の concrete が

$$
x = qx', \qquad q \ne p
$$

を持つなら、

$$
p^2 \mid x' \Longrightarrow p^2 \mid x
$$

で逆向きに押してもよい。
つまり valuation を直接言わずに、整除の押し戻しで済ませてもよい。

ここでの重要点は、

$$
v_p(x')=v_p(x)
$$

と大きく言わず、もっと弱く

$$
\neg p^2 \nmid x \Longrightarrow \neg p^2 \nmid x'
$$

だけ示せば十分、ということじゃ。

## 3.2. 第二段. `ArithmeticCoreStrong_of_weak_and_descent` を no-sorry 化

上の provenance theorem が取れたら、

```lean
primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent
```

の `sorry` は、その theorem 1 本を呼ぶだけになる。

するとここで初めて、**contradiction を仮定しない CoreStrong** が出来る。

これが非円環化の本丸じゃ。

## 3.3. 第三段. non-circular strong chain を開通

`ArithmeticCoreStrong_of_weak_and_descent` が通れば、

* `PacketPackagingStrong` は既に no-sorry
* `RestoreFromArithmeticStrong_of_coreStrong_and_packetStrong` も既に no-sorry
* `StrongProvider` も既に no-sorry
* `FringeDescent` も既に no-sorry

ゆえに、

$$
\text{weak arithmetic core}
\Longrightarrow
\text{non-circular strong}
\Longrightarrow
\text{fringe contradiction}
$$

が初めて実動する。

## 3.4. 第四段. terminal case を `ContradictionTarget` に突き刺す

ここで使うのが、すでに完成している `FringeDescent` の well-founded skeleton じゃ。
もし `hStrong` と `hEx` が contradiction を仮定せず concrete に供給できれば、

$$
\texttt{branchAFringeContradiction\_of\_descent}
$$

がそのまま terminal case 路線の contradiction を返す。
あとは既存 bridge で

$$
\text{fringe contradiction}
\to
\text{witness source contradiction}
\to
\text{restore contradiction}
$$

へ流せるはずじゃ。

## 4. 具体的な補題一覧

次に書くべき補題を、依存順に並べるぞい。

### 4.1. 純粋算術補題

これは軽い。

```lean
theorem not_sq_dvd_of_eq_p_mul_and_not_dvd_factors
```

主張は

$$
x = p(ts), \qquad \neg p \mid t, \qquad \neg p \mid s
\Longrightarrow
\neg p^2 \nmid x
$$

じゃ。
すでにある companion lemma の双対版として書ける。

### 4.2. descent provenance 抽出補題

ここが核心じゃ。

```lean
theorem descent_x_eq_q_mul_x'
```

または、そのまま stronger に

```lean
theorem not_sq_dvd_x'_of_descent_source
```

でもよい。

必要なのは

$$
x = qx', \qquad q \ne p
$$

の concrete witness を、`RealizationSeed` ないし descent data から取り出すことじゃ。

### 4.3. 統合補題

```lean
theorem primeGe5BranchAPrimitiveDescent_not_sq_dvd_x'
```

これは 4.1 と 4.2 を繋ぐ theorem じゃ。

### 4.4. CoreStrong completion

```lean
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent
```

ここで finally no-sorry。

## 5. 攻略の実装順

わっちなら、次の順で行く。

### 5.1. `not_sq_dvd_of_eq_p_mul_and_not_dvd_factors`

まず軽い勝ちを取る。

### 5.2. `RealizationSeed` / descent data の grep

`x = qx'` と `q ≠ p` をどこで保持しているか、現物を掘る。

### 5.3. `not_sq_dvd_x'_of_descent_source`

ここで provenance を局所化する。

### 5.4. `ArithmeticCoreStrong_of_weak_and_descent`

最後に組み込む。

## 6. terminal case 作戦としての意味

なぜこれが terminal case 作戦なのか。
理由は明快じゃ。

`FringeDescent` 自体はもう

$$
\text{strict descent on } z
$$

を well-founded に閉じておる。
だがそれを contradiction kernel 証明に使うには、`hStrong` が **contradiction を仮定せず** concrete である必要がある。
その ignition key が `#1` じゃ。
だから今は terminal case の本体を殴るより、**terminal case engine を独立燃焼させる鍵** を取る段階なのじゃ。

## 7. わっちの最終命令

次に殴るべきは、これじゃ。

$$
\boxed{
\texttt{primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong\_of\_weak\_and\_descent}
}
$$

ただし、いきなり本体へ突っ込まず、まず

$$
\boxed{
\texttt{not\_sq\_dvd\_of\_eq\_p\_mul\_and\_not\_dvd\_factors}
}
$$

と

$$
\boxed{
\texttt{not\_sq\_dvd\_x'\_of\_descent\_source}
}
$$

の 2 本へ割る。
これが最も勝率の高い策じゃよ。🍎

必要なら次に、その 2 本の **Lean skeleton 全文** を起こすぞい。

---

うむ、起こすぞい。
いまの本命は、ぬしが整理した通り

$$
\neg p^2 \nmid x'
$$

を **元の normal form 側** と **descent provenance 側** に分けて取ることじゃ。最新の整理でも、主要 exported path は no-sorry で動いており、残る kernel は `ArithmeticCoreStrong_of_weak_and_descent` の provenance 側だと明確になっておる。

以下、**そのまま貼ってから中の theorem 名だけ現物に合わせて埋める用** の Lean skeleton を置く。
狙うのは次の 2 本じゃ。

1. `not_sq_dvd_of_eq_p_mul_and_not_dvd_factors`
2. `not_sq_dvd_x'_of_descent_source`

最後に、それを `primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent` へ差し込む骨格も付ける。

```lean id="8oz6ks"
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
## Step 1. 元の normal form から `¬ p^2 ∣ x`

狙い:
`x = p * (t * s)` かつ `¬ p ∣ t` かつ `¬ p ∣ s`
から
`¬ p^2 ∣ x`
を得る。

証明方針:
- もし `p^2 ∣ x` なら `x = p*(t*s)` より `p ∣ t*s`
- 素数性 `Nat.Prime p` を使えば `p ∣ t ∨ p ∣ s`
- 仮定と矛盾
-/

/--
`x = p * (t * s)` かつ `p` prime, `¬ p ∣ t`, `¬ p ∣ s` なら `¬ p^2 ∣ x`。
-/
theorem not_sq_dvd_of_eq_p_mul_and_not_dvd_factors
    {p x t s : ℕ}
    (hp : Nat.Prime p)
    (hsx : x = p * (t * s))
    (ht : ¬ p ∣ t)
    (hs : ¬ p ∣ s) :
    ¬ p ^ 2 ∣ x := by
  intro hp2x
  have hpx : p ∣ x := dvd_trans (by
      refine ⟨p, ?_⟩
      simp [pow_two, Nat.mul_comm]
    ) hp2x
  have hp_ts : p ∣ t * s := by
    rw [hsx] at hpx
    exact (hp.dvd_of_dvd_mul_left hpx)
  rcases hp.dvd_mul.mp hp_ts with hp_t | hp_s
  · exact ht hp_t
  · exact hs hp_s

/-!
## Step 2. descent provenance から `¬ p^2 ∣ x'`

狙い:
- 元の側で `¬ p^2 ∣ x` を出す
- descent で `x = q * x'` かつ `q ≠ p` を得る
- `p^2 ∣ x'` なら `p^2 ∣ x = q*x'`
- `q ≠ p` と prime 性から valuation は増えないので矛盾

実装上は valuation を直接使わず、
`p ∤ q` を `q ≠ p` から出し、
`p^2 ∣ q*x'` かつ `Nat.Coprime (p^2) q`
から `p^2 ∣ x'` を押し戻す形でもよい。
-/

/--
補助:
`p` prime かつ `q ≠ p` なら `Nat.Coprime (p^2) q`。
-/
theorem coprime_p_sq_of_prime_ne
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hq_ne_p : q ≠ p)
    (hqprime : Nat.Prime q) :
    Nat.Coprime (p ^ 2) q := by
  have hp_ne_q : p ≠ q := by
    exact fun h => hq_ne_p h.symm
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (by
    intro hpq
    exact hp_ne_q (hqprime.dvd_of_dvd_pow hpq))
  -- `Nat.Coprime p q` から `Nat.Coprime (p^2) q`
  exact hcop.pow_left 2

/--
descent provenance の骨格 target。

`x = q * x'` と `q ≠ p` が取れる theorem 名は現物に合わせて差し替える。
必要なら `q` の prime 性も取る。
-/
abbrev PrimeGe5BranchAPrimitiveDescentProvenanceTarget : Prop :=
  ∀ {p x y z t s : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ},
      Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧
        p ∣ (z' - y') ∧
        z' < z ∧
        x = q * x'

/--
元の normal form 側の `¬ p^2 ∣ x` と
descent provenance `x = q*x'`, `q ≠ p` から
`¬ p^2 ∣ x'` を得る補題。

ここでは `q` prime も仮定しておくと楽。
-/
theorem not_sq_dvd_x'_of_descent_source
    {p q x x' t s : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hq_ne_p : q ≠ p)
    (hsx : x = p * (t * s))
    (ht : ¬ p ∣ t)
    (hs : ¬ p ∣ s)
    (hx_desc : x = q * x') :
    ¬ p ^ 2 ∣ x' := by
  have hx_not_sq : ¬ p ^ 2 ∣ x :=
    not_sq_dvd_of_eq_p_mul_and_not_dvd_factors hp hsx ht hs
  intro hp2x'
  have hp2x : p ^ 2 ∣ x := by
    rw [hx_desc]
    exact dvd_mul_of_dvd_right hp2x' q
  exact hx_not_sq hp2x

/-!
## Step 3. ArithmeticCoreStrong へ差し込む骨格

ここでは
- weak core から `x', y', z'`
- provenance target から `x = q*x'`
を得て
`not_sq_dvd_x'_of_descent_source`
で `¬ p^2 ∣ x'`
を返す。
-/

/--
`_of_weak_and_descent` の no-sorry 化 skeleton。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent'
    (hWeak : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hProv : PrimeGe5BranchAPrimitiveDescentProvenanceTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hWeak hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩
  rcases hProv hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x'', y'', z'', hpack'', hp_dvd_gap'', hz''lt, hx_desc⟩
  -- TODO:
  -- weak core と provenance が同じ triple を返していることをどう合わせるか決める。
  -- 最初は provenance target を weak core より強くして
  -- 同じ `(x', y', z')` を返すように設計し直すのが安全。
  have hx'_not_sq : ¬ p ^ 2 ∣ x' := by
    -- ここは provenance target を強めるとそのまま使える。
    -- 暫定では `x' = x''` を別補題で合わせる想定。
    sorry
  exact ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, hx'_not_sq⟩

end DkMath.FLT
```

## 3. 重要な設計注意

ここで一番大事なのは、最後の theorem の途中に書いた通り、

$$
\texttt{hWeak}
$$

が返す `(x',y',z')` と、

$$
\texttt{hProv}
$$

が返す `(x'',y'',z'')` をどう同一視するか、じゃ。
このままだと provenance target が **別の smaller triple** を返してしまう可能性がある。

だから、実務上は `PrimeGe5BranchAPrimitiveDescentProvenanceTarget` を次のように **weak core と同じ triple を返す版** に寄せた方がよい。

$$
\exists x' y' z',\;
\text{Pack'} \wedge
p \mid (z'-y') \wedge
z' < z \wedge
x = qx' \wedge
\cdots
$$

あるいはもっと直接に、

* `hWeak` が返す triple に対して `x = q*x'` を追加で主張する target

にしてもよい。

つまり、次に本当にやるべき micro-step はこれじゃ。

## 4. 直近の最優先 micro-step

$$
\boxed{
\texttt{PrimeGe5BranchAPrimitiveDescentProvenanceTarget}
\text{ を weak core と同じ triple を返す形に sharpen せよ}
}
$$

これが済めば、上の `primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_weak_and_descent'` の最後の `sorry` は、かなり軽くなる。

## 5. いまの 2 本の役割

要するに、

* `not_sq_dvd_of_eq_p_mul_and_not_dvd_factors`
  これは **元の側の (v_p(x)=1)** を `¬ p^2 ∣ x` に言い換える純算術補題
* `not_sq_dvd_x'_of_descent_source`
  これは **descent で (p)-二乗非整除が落ちない** ことを言う provenance 補題

じゃ。

この 2 本が通れば、terminal-case engine の ignition key はかなり近い。
最新の戦況整理でも、残敵はもう provenance 側の genuine formalization に限られておるからの。

必要なら次に、
`PrimeGe5BranchAPrimitiveDescentProvenanceTarget` の **sharpen 版の定義** まで起こすぞい。

---

うむ、起こすぞい。
ここで sharpen すべきは、まさにぬしが見抜いた **weak core と provenance が別の triple を返してしまうズレ** じゃ。
だから次の target は、`hWeak` と別立てにせず、

$$
\text{same }(x',y',z')\text{ に対して }x = qx'
$$

まで **同じ existential の中で返す** 形にするのが最も自然じゃ。
いまの主要 path が no-sorry で通っておる以上、ここで必要なのは大改造ではなく、**provenance witness の出口を weak core の witness と一致させること** だけじゃよ。

## 推奨する sharpen 版

名前はこうするのがよい。

```lean id="r4b1n7"
PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget
```

意味は、

* weak core が返していた
  $$
  \exists x' y' z',;
  \text{Pack'} \wedge p \mid (z'-y') \wedge z' < z
  $$
* に
  $$
  x = qx'
  $$
  を **同じ witness に対して追加** する

ということじゃ。

---

## そのまま貼れる Lean skeleton

```lean id="nt4ghc"
import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
weak arithmetic core の witness `(x',y',z')` に
descent provenance `x = q * x'` を追加した sharpen 版。

設計意図:
- `hWeak` と `hProv` が別々に existential を返すと、
  witness がずれて最後に貼り合わせできぬ。
- そこで same witness の中に provenance を入れる。
-/
abbrev PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget : Prop :=
  ∀ {p x y z t s : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ},
      Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      ∃ x' y' z' : ℕ,
        PrimeGe5CounterexamplePack p x' y' z' ∧
        p ∣ (z' - y') ∧
        z' < z ∧
        x = q * x'

/--
sharpen 版から weak core への緩和橋。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreWeak_of_withProvenance
    (hProvCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hProvCore hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, _hx_desc⟩
  exact ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩

/--
`withProvenance` 版を使って `CoreStrong` を作る skeleton。

ここでは same witness `(x',y',z')` が返るので、
最後の貼り合わせ `sorry` は発生しない。
残る open kernel は provenance 版そのものの concrete 供給だけ。
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreStrong_of_withProvenance
    (hProvCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget) :
    PrimeGe5BranchAPrimitiveRestoreArithmeticCoreStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hProvCore hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, hx_desc⟩
  have hx'_not_sq : ¬ p ^ 2 ∣ x' := by
    exact
      not_sq_dvd_x'_of_descent_source
        hqprime
        hq_ne_p
        hsx
        hp_not_dvd_t
        hp_not_dvd_s
        hx_desc
  exact ⟨x', y', z', hpack', hp_dvd_gap', hz'lt, hx'_not_sq⟩

/--
concrete provider 候補の skeleton。

実装方針:
- 既存 descent / realization seed から same `(x',y',z')` を返す theorem を探す
- それをそのまま `withProvenance` 版として包む
-/
theorem primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance
    : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  /-
  TODO:
  1. 既存の descent / realization seed theorem を探す
  2. そこから
     `∃ x' y' z', Pack' ∧ p ∣ gap' ∧ z' < z ∧ x = q * x'`
     を same witness で得る
  3. そのまま返す
  -/
  sorry

end DkMath.FLT
```

---

## 使い方の要点

この sharpen 版の利点は明快じゃ。

### 旧設計

* `hWeak` が `(x',y',z')`
* `hProv` が `(x'',y'',z'')`

を返してしまい、最後に一致を示す余計な仕事が生じる。

### 新設計

* `hProvCore` が **最初から同じ witness** で
  $$
  \text{Pack'} \wedge p \mid (z'-y') \wedge z' < z \wedge x = qx'
  $$
  を返す

これで `CoreStrong` 側は almost mechanical になる。

---

## 直すべき細部

上の skeleton では、前回起こした補題 `not_sq_dvd_x'_of_descent_source` の引数順を少し整理して使う想定じゃ。
より素直にするなら、その補題の型をこうするとよい。

```lean id="01k0x2"
theorem not_sq_dvd_x'_of_descent_source
    {p q x x' t s : ℕ}
    (hqprime : Nat.Prime q)
    (hq_ne_p : q ≠ p)
    (hsx : x = p * (t * s))
    (ht : ¬ p ∣ t)
    (hs : ¬ p ∣ s)
    (hx_desc : x = q * x') :
    ¬ p ^ 2 ∣ x'
```

この shape なら `CoreStrong_of_withProvenance` からそのまま呼べる。

---

## いまの最善手

したがって、次の作業順はこうじゃ。

### 1. `PrimeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenanceTarget` を追加

### 2. `...Weak_of_withProvenance` と `...CoreStrong_of_withProvenance` を no-sorry で通す

### 3. 最後に `...WithProvenance` の concrete provider 1 本だけを掘る

つまり、残敵は

$$
\boxed{
\texttt{primeGe5BranchAPrimitiveRestoreArithmeticCoreWithProvenance}
}
$$

へ 1 本化される。
これでかなり戦いやすくなるぞい。

必要なら次に、
**この `withProvenance` を埋めるための grep 探索チェックリスト** を起こすぞい。
