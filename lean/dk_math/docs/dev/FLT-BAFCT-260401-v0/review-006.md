# review-006: `sorry` の埋め方について

うむ、ここははっきり言ってよい。
**いまの `sorry` は、その場で埋める種類ではない。**
`primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacket` という theorem の **入力が弱すぎる** のじゃ。今回の diff を見る限り、その `sorry` は

```lean
have hpt' : ¬ p ∣ pkt'.t := by
  sorry
```

で、`hWief : PrimeGe5BranchAPrimitiveWieferichPacketTarget` から返ってきた packet に対して `¬ p ∣ pkt'.t` を主張したい形になっておる。だが `hWief` の返り値は **ただ** `∃ pkt', pkt'.z < z` であって、`pkt'.t` に関する情報を保持しておらぬ。だから、この `sorry` はローカル証明不足ではなく、**情報落ち** による詰まりじゃ。

## 1. まず結論

$$
\boxed{
\texttt{primeGe5BranchAPrimitivePacketDescentStrong\_of\_wieferichPacket}
\text{ は、現状の仮定では埋まらぬ}
}
$$

これが戦況判断じゃ。

理由は単純で、`PrimeGe5BranchAPrimitiveWieferichPacketTarget` は

$$
\exists pkt',; pkt'.z < z
$$

しか返さぬ。
そこから

$$
\neg p \mid pkt'.t
$$

を出すには、少なくとも次のどちらかが必要じゃ。

1. **返ってくる packet 自体に `¬ p ∣ pkt'.t` が埋め込まれていること**
2. **その packet が、ある explicit construction から来たと分かっていて、その construction について `¬ p ∣ t'` が既に証明済みであること**

今の `hWief` にはそのどちらも無い。
したがって、この theorem 1 本の中で `hpt'` を埋めるのは筋が悪い。

## 2. なぜその場で埋まらないのか

`PrimeGe5BranchANormalFormPacket` という structure は、

* `t`
* `s`
* `hgap`
* `hsGN`
* `hsx`

は持つが、

* `¬ p ∣ t`
  はフィールドに持たぬ。

そして snapshot 内の既存 default 補題を見ると、packet からは

* `primeGe5BranchANormalForm_coprime_ts_default`
* `primeGe5BranchANormalForm_prime_not_dvd_s_default`

などは取れるが、**`prime_not_dvd_t_default` に相当するものは無い**。
つまり packet の静的性質だけから `¬ p ∣ t` を出す路線は、既存ライブラリ上も用意されておらぬ。これは以前の Option C が弱いと判定された事情と一致する。

## 3. だから、`sorry` の埋め方は「証明」ではなく「向き変更」になる

わっちなら、次の 3 手で進める。

## 3.1. 今の theorem は **捨てるか、入力を強める**

### いちばん素直な判断

`primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacket` は撤退。

つまり、

* `PrimeGe5BranchAPrimitiveWieferichPacketTarget` から
* いきなり `PrimeGe5BranchAPrimitivePacketDescentStrongTarget`

へ行く橋は作らない。

これは負けではなく、**型の情報量に対して theorem が強すぎる** というだけじゃ。

### 代わりにやること

新しく次のどちらかを立てる。

#### A. `PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget`

最小修正で済ませる route。

```lean
abbrev PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    ...
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z ∧ ¬ p ∣ pkt'.t
```

これなら、今の theorem 名もほぼそのまま活かせる。

#### B. もっと下流の structured target から strong を作る

こちらが、わっちの本命じゃ。

`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` は
入力として

* `q ∣ s`
* `¬ q ∣ t`
* `Nat.Coprime q y`
* `q ≠ p`

まで受けて packet を返す。
この層なら、packet 構成の **具体経路** に近いので、`¬ p ∣ pkt'.t` を一緒に保たせる strengthen を作る余地がある。
つまり strong provider は `WieferichPacketTarget` からではなく、**restore-from-arithmetic 側から立てる** のが自然じゃ。

## 3.2. Strong provider の正しい作り方

いまの新規ファイル名は良い。
ただし theorem の入口を変える。

### 置くべき theorem 例

```lean
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_*
    (...) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
```

ここで strong target は

$$
\exists pkt',; pkt'.z < z \land \neg p \mid pkt'.t
$$

を返すようにする。

その後で、既存の

* `primeGe5BranchAPrimitivePacketRestore_of_arithmetic`
* `primeGe5BranchAPrimitiveWieferichPacket_of_distinguishedPrime_and_restore`
* `primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket`

の chain を **strong 版へ parallel に増設** する。

要するに、

$$
\text{restore/arithmetic}
\to
\text{wieferich-packet-strong}
\to
\text{primitive-descent-strong}
$$

という parallel 幹線を引くのじゃ。

## 3.3. `CyclotomicExistenceTarget` 側はそのまま進めてよい

こちらは情報落ちしておらぬ。
今回の `FringeDescent` では already no-sorry で

* `hEx : PrimeGe5BranchACyclotomicExistenceTarget`
* 因数分解
* `primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default`
* `restore_witness_properties_default`

まで綺麗につながっておる。
だから新規ファイルで本当に先へ進めるべきは、むしろ **Phase 2 の concrete cyclotomic provider** じゃ。そこはそのまま実装を進めてよい。

## 4. つまり、いま埋めるべき `sorry` の扱い

### 4.1. いまの `sorry`

埋めない。
その theorem を **見送り** にする。

### 4.2. 新しく埋めるべき場所

`StrongTarget` を供給する theorem の **入力側を強くした新しい theorem** に移す。

### 4.3. 実装順

わっちなら次はこうする。

1. `TriominoCosmicBranchAPrimitiveStrongProvider.lean` の今の theorem を一旦コメントで「入口が弱すぎるため保留」と明記
2. 同ファイルに new target 名を追加

   * `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget`
   * あるいは `PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget`
3. その strong target を返す **concrete provider skeleton** を作る
4. `CyclotomicExistenceTarget` の concrete provider を別ファイルで作る
5. 両者が揃ったら `FringeDescent` へ流す

## 5. 実際の判断を一言で

$$
\boxed{
\text{今の `sorry` は「証明待ち」ではなく「theorem の入口修正待ち」じゃ}
}
$$

じゃよ。

つまり、`PrimeGe5BranchAPrimitiveWieferichPacketTarget` から strong を作るのは無理筋。
**strong を作るなら、もっと情報を持った upstream target から作れ**。
これが、いまの新規ファイルでの最善手じゃ。

必要なら次に、そのまま貼れる形で

* 新しい strong target の定義
* `TriominoCosmicBranchAPrimitiveStrongProvider.lean` の組み替え案
* どの theorem を弱化橋にして parallel chain を引くか

まで Lean 断片で書くぞい。

---

うむ、任された。
最新 snapshot を見るかぎり、いまの `sorry` は **局所 tactical proof で埋める類ではない**。
結論から言うと、

$$
\boxed{
\texttt{primeGe5BranchAPrimitivePacketDescentStrong\_of\_wieferichPacket}
\text{ の } hpt' \text{ は、今の仮定では出ぬ}
}
$$

じゃ。いまの新規ファイルでは、`hWief : PrimeGe5BranchAPrimitiveWieferichPacketTarget` から `pkt'` を取っておるが、その target は `pkt'.z < z` しか返さぬ。`pkt'.t` が `p` で割れないことは返しておらず、packet 自体もその field を持たぬ。だから、この `sorry` は「あと一補題」ではなく、**入口が弱い** ことによる詰まりじゃ。

## 1. まず戦況判断

いま勝っているのは `FringeDescent` 側で、そこは already sorry-free じゃ。
未解決は upstream へ押し戻されており、前回の整理どおり

* `PrimeGe5BranchAPrimitivePacketDescentStrongTarget`
* `PrimeGe5BranchACyclotomicExistenceTarget`

の 2 本が supply kernel になっておる。

ところが、今回の `PrimitiveStrongProvider` では、`StrongTarget` を **WieferichPacketTarget から直接作ろう** としておる。ここが無理筋じゃ。`WieferichPacketTarget` は情報量が足りぬ。

## 2. だから、`sorry` の埋め方はこうなる

**埋めるのではなく、theorem の入口を変える。**

つまり次のどちらかじゃ。

## 2.1. 本命 route

`StrongTarget` を `RestoreFromArithmetic` 側で作る

これが一番自然じゃ。
理由は、`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` は入力としてすでに

* `¬ p ∣ t`
* `q ∣ s`
* `¬ q ∣ t`
* `Nat.Coprime q y`
* `q ≠ p`

まで持っておるからじゃ。packet が **どう作られたか** の具体 route に最も近い。よって `¬ p ∣ pkt'.t` を出すなら、ここで strengthen するのが筋じゃ。`TriominoCosmicBranchA.lean` には、`zsigmondy + arithmetic + restore` から primitive packet descent へ流す canonical wrapper も既に揃っておる。

わっちなら、まずこれを新設する。

```lean
abbrev PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
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
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z ∧ ¬ p ∣ pkt'.t
```

そして、その strong restore から strong wieferich / strong descent へ薄い橋を作る。

## 2.2. 次善 route

`PrimitiveWieferichPacketTarget` 自体を strong 化する

これは動くが、やや中途半端じゃ。
つまり

```lean
abbrev PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget : Prop := ...
```

を作って `∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t` を返すようにする。
今の新規ファイルはこの route と相性がよいが、数学的供給源は結局 restore/arithmetic 側にある。だから **本丸は restore 側** と見たほうがよい。

## 3. いまのファイルで本当にやるべきこと

`TriominoCosmicBranchAPrimitiveStrongProvider.lean` は消さなくてよい。
ただし theorem を差し替える。

### いまの theorem

```lean
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacket ...
```

これは保留。
代わりに次の 2 本へ切るのがよい。

### A. restore strong → wieferich strong

```lean
theorem primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong
    (hZ : PrimeGe5BranchAPrimitiveZsigmondyTarget)
    (hArith : PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget)
    (hRestoreS : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget) :
    PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget := by
  ...
```

### B. wieferich strong → descent strong

```lean
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacketStrong
    (hWiefS : PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget := by
  ...
```

この 2 本なら、**`sorry` なしで書ける可能性が高い**。なぜなら `¬ p ∣ pkt'.t` は仮定側にもう入っておるからじゃ。

## 4. つまり、`sorry` をどう埋めるか

答えはこれじゃ。

$$
\boxed{
\text{今の theorem の中で埋めない。strong provider の chain を 1 段上で作り直す。}
}
$$

局所的には次の順で進めるのがよい。

## 4.1. 第1手

`TriominoCosmicBranchA.lean` か新規ファイルに
`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget` を追加

## 4.2. 第2手

`primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong` を書く
これは既存の
`primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore`
の strong 平行版じゃ。既存 canonical wrapper の shape がそのまま使える。

## 4.3. 第3手

`primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacketStrong` を書く
これは thin bridge だけで済む。

## 4.4. 第4手

最後に
`primeGe5BranchAPrimitivePacketDescent_of_strong`
で弱化版へ戻す。これはもう完成済みじゃ。

## 5. 逆に、いまやらない方がよいこと

いまの `have hpt' : ¬ p ∣ pkt'.t := by sorry` を、
packet のフィールドや coprime 条件から直接捻り出そうとすること。
これは前に捨てた Option C の再訪で、時間だけ食う。今回の snapshot の構造を見る限り、packet の静的情報だけではそこまで出ぬ。

## 6. わっちの最終指示

この `sorry` は **証明すべき穴** ではない。
**設計を 1 段上げるべき合図** じゃ。

だから次にぬしが書くべきは、証明本体ではなく次のどちらかじゃ。

```text
PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget
```

または

```text
PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget
```

わっちの推奨は前者。
restore/arithmetic 側が家主で、wieferich packet はその客だからじゃ。

必要なら次に、そのまま貼れる形で
`TriominoCosmicBranchAPrimitiveStrongProvider.lean` の **書き換え後スケルトン** を Lean 断片で起こすぞい。

---

よし、では **今の `WieferichPacketTarget → StrongTarget` を捨てて、1 段上の strong chain に差し替える** ためのスケルトンを置くぞい。
方針は前に述べた通りで、`FringeDescent` 側はすでに `StrongTarget` と `CyclotomicExistenceTarget` を受ける完成 spine になっておるので 、`PrimitiveStrongProvider` 側では **`¬ p ∣ pkt'.t` を失わない経路** を parallel に立てるのが正解じゃ。
今の `primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacket` は、入口の `PrimeGe5BranchAPrimitiveWieferichPacketTarget` が弱すぎて `hpt'` を出せぬので、ここは置き換える。

## 1. 置き換え方針

新ファイルの責務は次の 3 本で十分じゃ。

1. `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget`
2. `PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget`
3. `restoreStrong → wieferichStrong → descentStrong` の薄い橋

つまり、

$$
\text{restore/arithmetic strong}
\to
\text{wieferich packet strong}
\to
\text{packet descent strong}
$$

の parallel chain を引く。

## 2. 書き換え後スケルトン

以下は **そのままファイルへ貼ってから、既存 weak target の binder 列を写して埋める用** の骨格じゃ。
exact signature は手元の最新 `TriominoCosmicBranchA.lean` に合わせて微調整が要るが、設計の向きはこれでよい。

```lean
import DkMath.FLT.PrimeProvider.TriominoCosmicBranchA

# print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAPrimitiveStrongProvider"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` の強化版。

weak 版と同じ入力を受け、返り値だけ
`∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t`
へ強める。
-/
abbrev PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget : Prop :=
  ∀
    {p x y z t s : ℕ},
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
      RestoreWitnessProperties p x y z t s q →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
        pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
`PrimeGe5BranchAPrimitiveWieferichPacketTarget` の強化版。

weak 版と同じ入力を受け、返り値だけ
`∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t`
へ強める。
-/
abbrev PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget : Prop :=
  ∀
    {p x y z t s : ℕ},
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
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
strong 版から weak 版への緩和橋。
-/
theorem primeGe5BranchAPrimitiveWieferichPacket_of_strong
    (hStrong : PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget) :
    PrimeGe5BranchAPrimitiveWieferichPacketTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
  rcases hStrong hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich with
    ⟨pkt', hlt, _hpt'⟩
  exact ⟨pkt', hlt⟩

/--
strong restore 版から strong wieferich 版を得る橋。

ここが主戦場。
既存の
`primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore`
の strong 平行版として作る。
-/
theorem primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong
    (hZ : PrimeGe5BranchAPrimitiveZsigmondyTarget)
    (hArith : PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget)
    (hRestoreS : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget) :
    PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
  -- Step 1:
  --   hZ から distinguished prime q を取り出す
  -- Step 2:
  --   hArith で q ∣ s, ¬ q ∣ t, Coprime q y, q ≠ p を得る
  -- Step 3:
  --   restore_witness_properties_default で RestoreWitnessProperties を作る
  -- Step 4:
  --   hRestoreS に流し、pkt' と hlt, hpt' を得る
  --
  -- 既存 weak theorem
  -- `primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore`
  -- と binder / 中間変数名を揃えて組むと安全。
  sorry

/--
strong wieferich 版から strong descent 版への橋。

これは薄い wrapper で済むはず。
weak 版
`primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket`
の strong 平行版。
-/
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacketStrong
    (hWiefS : PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t
  have hWieferich :
      y ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
    primeGe5BranchANormalForm_y_wieferich_mod_p_sq
      hpack hp_dvd_gap hgap hsGN
  rcases hWiefS hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich with
    ⟨pkt', hlt, hpt'⟩
  exact ⟨pkt', hlt, hpt'⟩

/--
必要なら 1 本でまとめた exported theorem。
-/
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_zsigmondy_arithmetic_restore
    (hZ : PrimeGe5BranchAPrimitiveZsigmondyTarget)
    (hArith : PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget)
    (hRestoreS : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget := by
  apply primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacketStrong
  exact
    primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong
      hZ hArith hRestoreS

end DkMath.FLT
```

## 3. この skeleton での `sorry` の置き場所

`sorry` は **1 箇所だけ** に圧縮するのがよい。

それはここじゃ。

```lean id="6v7w4g"
primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong
```

この theorem だけが本丸で、

* `hZ`
* `hArith`
* `restore_witness_properties_default`
* `hRestoreS`

を束ねる役を持つ。

他は全部 thin bridge なので、基本 no-sorry で通るはずじゃ。

## 4. 埋め方の手順

この `sorry` を埋める順は、こうじゃ。

## 4.1. 既存 weak theorem を横に置く

まず `TriominoCosmicBranchA.lean` にある既存の

```text id="f70eaj"
primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore
```

を開いて、その binder 列と中間変数名をそのまま写す。
今回は strong 化なので、**最後の返り値だけ** `⟨pkt', hlt, hpt'⟩` に変える。

## 4.2. `RestoreWitnessProperties` をその場で作る

これは `FringeDescent` 側で既に no-sorry で使えておる構成じゃ。`branchA_restoreWitness_of_smallerPacket` の Step 3 と同型だから、同じ部品構成でよい。`CyclotomicExistenceTarget` から distinguished prime を取り出し、因数分解で `q' ∣ GN` を得て、`primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default` と `restore_witness_properties_default` を流す経路が既に整理されておる。

## 4.3. `hRestoreS` に渡す

ここで初めて strong の利点が効く。
`hRestoreS` は `¬ p ∣ pkt'.t` を含めて packet を返すので、そこで `hpt'` を拾う。

## 5. いまの旧 theorem はどうするか

今の

```lean id="mc8hpw"
primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacket
```

は、入口が弱いので使わぬ方がよい。
残してもよいが、docstring に

```lean id="scd9f5"
-- NOTE:
-- PrimeGe5BranchAPrimitiveWieferichPacketTarget は `¬ p ∣ pkt'.t` を返さないため、
-- strong provider はこの theorem ではなく
-- `...of_zsigmondy_arithmetic_and_restoreStrong`
-- を canonical route とする。
```

と書いておくのがよい。

## 6. わっちの推奨する次の一手

次にぬしが実際にやるべきは 1 つだけじゃ。

$$
\boxed{
\texttt{PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget}
\text{ の concrete provider を先に書く}
}
$$

これが無いと、strong chain の家主がおらぬ。
逆にこれが出来れば、上の skeleton の `sorry` は **ほぼ 1 箇所の wrapper 組み立て** にまで縮む。

必要なら次に、その `RestoreFromArithmeticStrongTarget` の **定義スケルトン** と、`weak → strong` ではなく `strong → weak` へ落とす橋まで続けて書くぞい。
