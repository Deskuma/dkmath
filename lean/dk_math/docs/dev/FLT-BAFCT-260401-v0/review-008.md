# review-008: `RestoreArithmeticStrong.lean` の `sorry` の埋め方について

うむ、切り方はよい。
ただし、次は **history に書いた 3 段全部を新設する必要はない**。
最新 snapshot を見ると、`TriominoCosmicBranchARestore.lean` にはすでに

* `PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget`
* `PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget`
* `primeGe5BranchAPrimitiveRestoreArithmeticCore_of_residueRoot_and_descentAssembly`
* `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_restoreSubtargets`
* `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_smallerCounterexample_and_packet`

という **分解済みの canonical bridge** がある。だから、`RestoreArithmeticStrong` で新しく掘るべきは 3 本ではなく、実質 **1 本だけ** じゃ。

## 結論

次はこう攻めるのが最短じゃ。

$$
\boxed{
\text{ArithmeticCore は weak のまま再利用し、}
\text{PacketPackaging だけ strong 化する}
}
$$

つまり、新しく作るべき target は

```text id="64s624"
PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget
```

これ 1 本でよい可能性が高い。

---

## 1. なぜそれでよいか

`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` の weak 版は、既に

$$
\text{smaller counterexample existence}
\quad+\quad
\text{packet packaging}
$$

の 2 段に切れておる。
しかも `TriominoCosmicBranchARestore.lean` では、

* `PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget`
  は **そのまま**
  `PrimeGe5BranchAPrimitiveSmallerCounterexampleFromArithmeticTarget`
  の alias じゃ。
* `PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget`
  は **そのまま**
  `PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget`
  の alias じゃ。
* その 2 本を合成する theorem も、すでに no-sorry で置いてある。

だから strong 化の本質は、

$$
\exists pkt',\; pkt'.z < z
$$

を

$$
\exists pkt',\; pkt'.z < z \land \neg p \mid pkt'.t
$$

へ強める **後半 packaging 段** に集中させればよい。

言い換えると、

* smaller counterexample を作る arithmetic core はそのまま使う
* packet に包む瞬間に strongness を要求する

これが最小改造じゃ。

---

## 2. まず作るべき定義

新ファイル `TriominoCosmicBranchARestoreArithmeticStrong.lean` では、まずこれを置く。

```lean
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget : Prop :=
  ∀ {p z x' y' z' : ℕ}, PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') →
    z' < z →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ ¬ p ∣ pkt'.t
```

これが新しい家主じゃ。

---

## 3. 次に置くべき橋

そのうえで、main theorem は skeleton の `sorry` をいきなり埋めるのではなく、まず **橋 theorem** を先に置く。

```lean
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackStrong : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hArithCore hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩
  exact hPackStrong hpack' hp_dvd_gap' hz'lt
```

これは、いまの既存 weak theorem

```text id="8v71hs"
primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_smallerCounterexample_and_packet
```

の strong 平行版じゃ。
ここは no-sorry で通るはずじゃよ。

---

## 4. だから main skeleton はこう変える

いまの

```lean id="km70q3"
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  sorry
```

は、まだ大きすぎる。
これをいきなり埋めるのではなく、まずは **入力つき wrapper** に差し替える。

### 先に置くべき版

```lean
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_subtargets
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackStrong : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  exact
    primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong
      hArithCore hPackStrong
```

### その後の exported theorem

最後に、もし concrete default が揃ったら

```lean
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  -- ここで concrete hArithCore, hPackStrong を供給
  ...
```

とすればよい。

---

## 5. 次の本丸はどこか

この設計にすると、本当の主戦場は 1 箇所に圧縮される。

$$
\boxed{
\texttt{PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget}
}
$$

じゃ。

つまり、次に実装で本当に殴るべきは

* smaller counterexample を packet に包むとき
* なぜ `¬ p ∣ pkt'.t` が保たれるのか

ここだけになる。

Arithmetic core 側を strong 化しようとすると、また target が増えて霧が出る。
今はそれを避けるべきじゃ。

---

## 6. 実務手順

わっちなら、次はこの順で書く。

## 6.1. `RestoreArithmeticStrong.lean` に新 target を追加

`PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget`

## 6.2. strong 平行版 wrapper を no-sorry で実装

`primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong`

## 6.3. main skeleton を「subtargets 受け取り版」に置き換える

`..._of_subtargets`

## 6.4. 最後に concrete `hPackStrong` を別 theorem として掘る

ここが本丸。

---

## 7. ひとことで言えば

$$
\boxed{
\text{次は target を増やすのではなく、strongness を後半 packaging 段へ押し込め}
}
$$

じゃ。

ぬしの今の skeleton は悪くない。
ただし、main theorem を直接埋めに行くとまた重くなる。
先に **weak arithmetic core + strong packet packaging** の 2 段へ割れ。
それがいちばん賢い攻め方じゃよ。

必要なら次に、そのまま貼れる形で
`TriominoCosmicBranchARestoreArithmeticStrong.lean` の **書き換え後 Lean skeleton 全文** を出すぞい。

---

よし、最新の戦況整理に合わせて、**ArithmeticCore は weak を再利用し、PacketPackaging だけ strong 化する** 形の全文 skeleton を置くぞい。
これなら主戦場が `PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget` に 1 本化され、`RestoreArithmeticStrong` 全体の骨格は no-sorry で組める。

以下、そのまま貼ってから、既存 weak theorem 名だけ現物に合わせて微調整する想定の全文じゃ。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchAPrimitiveStrongProvider

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
`PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget` の強化版。

weak 版は
`∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z`
を返すのみだが、strong 版ではさらに
`¬ p ∣ pkt'.t`
を保持した packet を返す。

ここが RestoreArithmeticStrong の本命・主戦場じゃ。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget : Prop :=
  ∀ {p z x' y' z' : ℕ},
    PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') →
    z' < z →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
Arithmetic core は weak のまま再利用し、
packet packaging だけ strong 化して
`RestoreFromArithmeticStrongTarget` を得る橋。

設計意図:
- smaller counterexample existence は既存 weak core をそのまま使う
- `¬ p ∣ pkt'.t` を要求する強さは packet 化の瞬間に押し込める
- これにより strong 化の責務を 1 箇所へ集中できる
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackStrong : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  rcases hArithCore hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩
  exact hPackStrong hpack' hp_dvd_gap' hz'lt

/--
上の橋の別名版。
`restore subtargets` という見出しで後から検索しやすくするために置く。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_restoreSubtargets
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackStrong : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  exact
    primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong
      hArithCore hPackStrong

/--
`RestorePacketPackagingStrongTarget` の concrete provider 候補。

ここだけを open kernel として残す。
狙いは、既存 weak packet packaging route が作る `pkt'` について、
構成由来の性質から `¬ p ∣ pkt'.t` を追加で回収すること。
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingStrong
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hz'lt
  /-
  想定ルート:
  1. 既存 weak theorem
     `PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget`
     もしくはその default/provider から
     `∃ pkt', pkt'.z < z`
     を得る。
  2. その `pkt'` が concrete にどう構成されたかを追い、
     `pkt'.t` が元の primitive side 条件を保つことを示す。
  3. `¬ p ∣ pkt'.t` を追加して返す。
  -/
  sorry

/--
最終 exported theorem。

ArithmeticCore の concrete provider は既存 weak theorem をそのまま使い、
packet packaging のみ strong provider を挿す。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong
    : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  apply primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_restoreSubtargets
  ·
    /-
    現物の既存 theorem 名に合わせてここを差し替えること。
    候補:
    `primeGe5BranchAPrimitiveRestoreArithmeticCore_of_residueRoot_and_descentAssembly`
    -/
    exact primeGe5BranchAPrimitiveRestoreArithmeticCore_of_residueRoot_and_descentAssembly
  ·
    exact primeGe5BranchAPrimitiveRestorePacketPackagingStrong

end DkMath.FLT
```

## 次に埋める `sorry` の考え方

この skeleton のよいところは、`sorry` が **1 箇所** に圧縮されることじゃ。

$$
\boxed{
\texttt{primeGe5BranchAPrimitiveRestorePacketPackagingStrong}
}
$$

ここだけを殴ればよい。

中でやることは 3 段じゃ。

1. 既存 weak packet packaging theorem から `pkt'` を取る
2. その `pkt'` の **構成由来** を追う
3. `¬ p ∣ pkt'.t` を示して `⟨pkt', hlt, hpt'⟩` を返す

大事なのは、ここでも packet の静的 field から直接 `¬ p ∣ pkt'.t` を捻り出そうとせぬことじゃ。
前に詰まったのは、まさにそこだったからの。`StrongProvider` 側でも、局所証明ではなく **入口を 1 段上げる** ことで no-sorry 化に成功したのじゃ。

必要なら次に、この `primeGe5BranchAPrimitiveRestorePacketPackagingStrong` の中だけを対象にして、

* 既存 weak theorem をどう `rcases` するか
* `¬ p ∣ pkt'.t` をどの concrete construction から拾うか
* そこで追加すべき中間補題名の候補

まで、さらに 1 段細かい skeleton に砕いて出すぞい。
