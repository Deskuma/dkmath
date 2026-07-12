# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow

gch: 57890fc245ea74457b25e7d6d0d8049b265615d7

## Report

その通りでした。前回は cp-298 の局所指示だけで止めてしまっていました。末尾には「成功後は自律的に進み、完成か真正な障害まで続行」と明記されています。

今回はそこまで進め直しました。

- [UpperWindow.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/UpperWindow.lean)
- [FloatWindow.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean)
- [DyadicFloat.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean)
- [Core.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean)
- [WidthBalance.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/WidthBalance.lean)
- [OrbitBalance.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OrbitBalance.lean)
- [PatternLedger.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PatternLedger.lean)

下位側も cp-300 相当まで閉じています。

```text
positive centers ≤ (hi - lo) / 2 + 1
positive centers ≤ nonpositive positions + 1
```

どちらも sortedness、diagnosis、canonical family、coverage 仮定なしです。

上位側では次の事実が Lean で確定しました。

```text
stateUpperCarry n = 1 or 2

bitWidth (3*n+1)
  = bitWidth n + stateUpperCarry n

bitWidth n + stateUpperCarry n
  = s(n) + bitWidth (T n)

bitWidth n < bitWidth (T n)
  ↔ stateUpperCarry n = 2 ∧ s(n) = 1
```

累積形も通っています。

```text
sumS(n,k) + bitWidth(iterateT k n)
  = bitWidth(n) + k + carryTwoCount(n,k)
```

さらに、

```text
width growth
  -> n mod 8 = 3 or n mod 8 = 7
```

まで既存 residue theorem と接続しました。したがって `1 mod 8` と `5 mod 8` は width growth を起こせません。

全新規ファイルに `sorry` / `axiom` はありません。`FloatWindow` と公開 `DkMath.Collatz.PetalBridge` までビルド済みです。詳細は [report-petal-298.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-298.md) に同期しました。

まだ全体は閉じていません。現在の行き止まりではなく、次の独立した山は Mersenne 境界、`3 mod 8` の遅延返済、`carry 2 ∧ 7 mod 8` reservoir の定量化です。

## Review

## 結論

**採用。しかも cp-298 の成功というより、下位 pressure と上位 Float を結ぶ新幹線の開通じゃ。**

Codex は最低目標だった direct two-spacing を通した後、そのまま

- cp-299 相当の center Finset packing
- cp-300 相当の nonpositive successor injection
- UpperWindow
- exact dyadic Float
- 一歩 width balance
- 軌道全体の telescoping ledger
- $\bmod 8$ pattern bridge

まで自律的に進んだ。

これは、Codex を第二の頭脳として先へ走らせる方式が正しかったことを、実装成果で証明しておる。添付 report では公開 `PetalBridge` までの build、全新規ファイルの no-`sorry` / no-`axiom` が報告され、差分上でも新規 `sorry` / `axiom` は見当たらない。

ただし、次の山について Codex の認識を一か所だけ補正する必要がある。

> `3 mod 8` の遅延返済そのものは新しい山ではない。既存 `TailGrammar` / `DriftBudget` に既にかなり強く実装されている。

新しい山は、

> **上位の carry-two debt と、下位の delayed peeling payment を同じ会計へ入れ、支払先の重複を pressure として処理すること**

じゃ。

---

## 1. 下位側――direct local Big は完全に成功

追加された最小核は、

```lean
sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt
```

じゃ。

二つの local-island witness $W,W'$ が、

$$
W.val<W'.val
$$

を満たすなら、

$$
W.val+2\le W'.val
$$

が成立する。

証明は非常に美しい。

左 witness の中心直後では margin が非正であり、

$$
\operatorname{Margin}(r+W.val+1)\le0
$$

右 witness の中心では margin が正である。

$$
0<\operatorname{Margin}(r+W'.val)
$$

もし $W'.val=W.val+1$ なら、同じ座標が正かつ非正となる。

したがって中心は隣接できない。

### 評価

これは旧 route より明確に強い。

不要になったものは、

- list sortedness
- list adjacency
- diagnosis
- recovered state
- canonical packing state
- coverage
- unresolved pair correction

じゃ。

つまり two-spacing は外部の pair carrier が与える性質ではなく、

> **`SourcePressureLocalIsland` 自身の内部性質**

だった。

cp-297 で旧 canonical route が空であると判明し、cp-298 で本当の Core が local-island predicate 内から掘り出された。見事な反転じゃよ。

---

## 2. center Finset packing も正しい

次に、

```lean
sourcePressurePositiveWitnessCentersInWindow
```

として、witness を絶対中心座標

$$
W\longmapsto r+W.val
$$

へ写している。

この写像の単射性も正しい。

$$
r+W.val=r+W'.val\Longrightarrow W.val=W'.val\Longrightarrow W=W'
$$

したがって cardinality が保存される。

```lean
sourcePressurePositiveWitnessCentersInWindow_card_eq
```

さらに center image の two-spacing を証明し、既存の

```lean
finset_card_le_half_window_add_one_of_twoSeparated
```

へ直接流している。

結果は、

$$
\#\text{PositiveWitnesses}\le\frac{hi-lo}{2}+1
$$

じゃ。

旧 route の $+2$ から $+1$ へ鋭くなり、unresolved correction も消えた。

### 重要な境界

この theorem は **与えられた list `L` 内の explicit witness family** を数えている。

つまり、

```text
L に含まれる positive local-island witnesses
```

の local Big じゃ。

全ての可能な local island が `L` に列挙されている、という completeness は別命題である。この境界は現在の theorem 名とコメントで十分守られておる。

---

## 3. nonpositive position 上界もよい

各 center $m$ に、

$$
m\longmapsto m+1
$$

を対応させる。

center の直後は非正だから、$m<hi$ なら窓内の nonpositive position へ入る。

右端 $m=hi$ だけは $hi+1$ へ外れるため、boundary は高々一点。

したがって、

$$
\#\text{PositiveWitnesses}\le\#\text{NonposPositions}+1
$$

が得られた。

この $+1$ は曖昧な補正ではなく、

> **右端 `hi` に center が存在する可能性**

そのものじゃ。

そして、

```lean
sourcePressurePositiveWitnesses_localBig_direct
```

で二つの上界がまとめられた。

$$
\#\text{PositiveWitnesses}\le\frac{hi-lo}{2}+1
$$

$$
\#\text{PositiveWitnesses}\le\#\text{NonposPositions}+1
$$

この下位側実装は、わっちから見ても手直し不要の完成品じゃ。

---

## 4. 上位側――`stateUpperCarry` の定義は当たり

現在の bit width を、

$$
w(n):=\operatorname{bitWidth}(n)
$$

とする。

上位 carry は、

$$
c(n):=\left\lfloor\frac{3n+1}{2^{w(n)}}\right\rfloor
$$

として定義された。

正の $n$ では、

$$
2^{w(n)-1}\le n<2^{w(n)}
$$

なので、

$$
1\le c(n)\le2
$$

となる。

Lean では、

```lean
stateUpperCarry_one_or_two
```

として、

$$
c(n)=1\lor c(n)=2
$$

が確定した。

これは上位ビット側の観測単位として非常に良い。

`carry = 1` は raw $3n+1$ が一枚だけ上の width へ出る状態。

`carry = 2` は二枚上まで届く状態じゃ。

---

## 5. raw width theorem は正確で強い

追加された、

```lean
bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry
```

は、

$$
w(3n+1)=w(n)+c(n)
$$

を述べる。

通常の「$3n+1$ は最大 $+2$ bit」という上界ではない。

> **実際に $+1$ か $+2$ かを、own-width quotient が正確に決定する**

という等式じゃ。

例を挙げれば、

$$
n=5,\quad w(n)=3,\quad 3n+1=16,\quad c(n)=2,\quad w(16)=5
$$

ゆえに、

$$
5=3+2
$$

となる。

これは Float 観測の核心として申し分ない。

---

## 6. 最大成果――上下 bit の完全保存会計

下位 height を、

$$
h(n):=s(n)=v_2(3n+1)
$$

加速写像を、

$$
T(n):=\frac{3n+1}{2^{h(n)}}
$$

とする。

Codex はまず、

```lean
threeNPlusOne_eq_pow_height_mul_T
```

として、

$$
3n+1=2^{h(n)}T(n)
$$

を再公開した。

さらに、

```lean
bitWidth_pow_two_mul
```

から、

$$
w(3n+1)=h(n)+w(T(n))
$$

を証明した。

raw width theorem と合流すると、

$$
w(n)+c(n)=h(n)+w(T(n))
$$

が得られる。

Lean 名は、

```lean
bitWidth_add_upperCarry_eq_height_add_bitWidth_T
```

じゃ。

これは今回の最重要定理である。

### DkMath 的意味

```text
現在の width
+
上位から発生した carry debt
=
下位で支払った peeling
+
次状態に残った width
```

じゃ。

上位と下位が、どちらも **binary position 一単位**で完全に同じ会計帳へ載った。

これまで下位側の $v_2$ と上位側の bit-width は別々の観測だった。

今回初めて、

> **上位の生成と下位の剥離が同じ整数単位で保存される**

ことが Lean で固定された。

これは挟み撃ち構想の背骨そのものじゃよ。

---

## 7. width growth の完全分類

一歩の balance と、

$$
c(n)\in{1,2}
$$

$$
1\le h(n)
$$

から、

```lean
bitWidth_growth_iff_carryTwo_and_heightOne
```

が証明された。

$$
w(n)<w(T(n))\Longleftrightarrow c(n)=2\land h(n)=1
$$

この theorem は非常に強い。

width が増えるには、

1. 上位側で最大 carry $2$
2. 下位側で最小 payment $1$

が同時に必要になる。

逆に $h(n)\ge2$ なら、

$$
w(T(n))\le w(n)
$$

である。

従来の「平均 drift」ではなく、一歩ごとの完全分類じゃ。

---

## 8. 軌道全体の telescope も成功

Codex は、

```lean
sumUpperCarry
orbitWindowUpperCarryCountEqTwo
```

を導入した。

各 carry は $1$ または $2$ なので、

$$
\operatorname{sumUpperCarry}(n,k)=k+\operatorname{carryTwoCount}(n,k)
$$

となる。

一歩 balance を telescope すると、

$$
\operatorname{sumS}(n,k)+w(T^k(n))=w(n)+\operatorname{sumUpperCarry}(n,k)
$$

したがって、

$$
\operatorname{sumS}(n,k)+w(T^k(n))=w(n)+k+\operatorname{carryTwoCount}(n,k)
$$

が得られた。

これは言い換えると、

$$
w(T^k(n))+\bigl(\operatorname{sumS}(n,k)-k\bigr)=w(n)+\operatorname{carryTwoCount}(n,k)
$$

じゃ。

左の $\operatorname{sumS}-k$ は baseline $1$ を超えた **追加 peeling payment**。

右の carry-two count は baseline carry $1$ を超えた **追加 upper debt**。

したがって、

> **最終 width + 累積追加支払 = 初期 width + 累積追加借金**

という完全会計になった。

これは今後、専用の `extraPeeling` API として名前を付ける価値がある。

---

## 9. $\bmod 8$ 接続も正しい

growth なら $h(n)=1$。

既存 residue theorem により、

$$
h(n)=1\Longleftrightarrow n\bmod8\in{3,7}
$$

なので、

$$
w(n)<w(T(n))\Longrightarrow n\bmod8=3\lor n\bmod8=7
$$

となる。

したがって、

$$
n\bmod8=1
$$

または、

$$
n\bmod8=5
$$

では width growth は起きない。

`PatternLedger` でこの接続が固定されたのも正しい。

これで上位から逃げる軌道は、

```text
carry 2
+
height 1
+
residue 3 or 7 mod 8
```

まで絞られた。

---

## 10. `DyadicFloatObservation` の設計評価

ここは **採用だが、次へ使う前に意味を分けるべき箇所** じゃ。

現在の構造は、

```lean
structure DyadicFloatObservation where
  value : ℕ
  width : ℕ
  upperBits : ℕ
  lowerBits : ℕ
  upper : ℕ
  lower : ℕ
  gap : ℕ
  carry : ℕ
  height : ℕ
```

となっている。

### 良い点

- exact arithmetic である
- IEEE Float ではないことが明確
- upper / lower / gap / carry / height を一つに束ねた
  -デバッグ・表示・標本記録には便利

### 注意点 1――`value` が入っている

観測構造自身に元の完全値 `value` が入っている。

したがって、将来、

```text
同じ DyadicFloatObservation を持つ候補 state の個数
```

を数えると、`value` が同じことまで要求され、最初から一意になってしまう。

追い込み漁の「情報を一部だけ観測し、候補集合を絞る」用途には、別の型が必要じゃ。

推奨分離はこうなる。

```lean
structure DyadicFloatSignature where
  width : ℕ
  upperBits : ℕ
  lowerBits : ℕ
  upper : ℕ
  lower : ℕ
  carry : ℕ
  height : ℕ
```

これは観測可能な情報だけ。

そして、

```lean
structure DyadicFloatWitness where
  value : ℕ
  signature : DyadicFloatSignature
  sound : signature = dyadicFloatSignature ... value
```

のように、完全値を持つ証拠側を分ける。

これは差し戻し理由ではない。

だが candidate cardinality を本格実装する前に分けるべきじゃ。

### 注意点 2――structure 自体には整合条件がない

任意の `DyadicFloatObservation` を直接 constructor で作れば、

```text
width = 3
upper = 999
carry = 17
```

のような不整合値も作れる。

現在の theorem は全て、

```lean
dyadicFloatObservation q r n
```

という canonical constructor に対して述べているので問題はない。

今後、任意の observation を theorem 引数にするなら、

- proof field を持たせる
- validity predicate を定義する
- canonical image だけを扱う

のどれかが必要じゃ。

---

## 11. `middleGapCapacity` はまだ「候補数定理」ではない

現在は、

$$
g:=w(n)-q-r
$$

$$
\operatorname{middleGapCapacity}:=2^g
$$

と定義され、

$$
w(n)\le q+r\Longrightarrow g=0
$$

$$
g=0\Longrightarrow2^g=1
$$

まで証明された。

これは正しい。

ただし、まだ証明されたのは、

> **未観測 middle word の形式的な bit-pattern 容量**

じゃ。

まだ証明されていないのは、

```text
指定された width
指定された upper prefix
指定された lower suffix
を同時に満たす自然数候補の Finset.card
```

である。

とくに $q>w(n)$ の場合、

$$
w(n)-q=0
$$

へ Nat subtraction が潰れるため、

```lean
upperPrefix q n = n
```

となる。

また $q+r>w$ の overlap 時には、upper と lower の共通 bit が整合しているかを確認する必要がある。

したがって本当の候補数 theorem には、

- fixed width
- window bounds
- upper/lower compatibility
- overlap consistency

が必要になる。

Codex の report が「raw candidate capacity」と書いているのは正確じゃ。

---

## 12. `FloatStepLedger` も canonical record として読む

```lean
structure FloatStepLedger where
  widthBefore : ℕ
  upperCarry : ℕ
  height : ℕ
  widthAfter : ℕ
  residue8 : Fin 8
```

も、任意の値に balance を強制する型ではない。

ただし、

```lean
floatStepLedger n
```

に対して、

```lean
floatStepLedger_balance
```

が成立するので、現在の用途では十分じゃ。

将来有限 automaton の node として使うなら、

```lean
structure ValidFloatStepLedger extends FloatStepLedger where
  balance :
    widthBefore + upperCarry = height + widthAfter
  carry_range :
    upperCarry = 1 ∨ upperCarry = 2
  ...
```

のような valid state が必要になる。

---

## 13. Codex report の「次の山」を補正

Codex は次の山として、

```text
3 mod 8 delayed-payment accounting
```

を挙げている。

しかし snapshot を再調査すると、既に `TailGrammar` / `DriftBudget` に次がある。

```lean
orbitWindowNextHeight_two_le_of_mod_eight_eq_three

tailMod8Three_le_nextTailHeightCountGe_two

orbitWindowResidueCountMod8EqThree_delayed_drift

orbitWindowResidueCountMod8EqThree_delayed_drift_strong

tailExactHeightOneReservoir_budget_with_remainder
```

つまり、

```text
3 mod 8
  -> 次段 height >= 2
```

と、その count-level drift budget は既に実装済みじゃ。

`7 mod 8` 側も、

```lean
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven

tailMod8Seven_le_nextTailHeightCountEq_one

tailRemainderLevel1_step_grammar
```

さらに $\bmod 16,\bmod 32,\ldots$ の delayed-reservoir tower まで存在する。

したがって、次に必要なのは delayed payment の再証明ではない。

> **Float growth count を既存 delayed reservoir grammar へ接続する bridge**

じゃ。

---

## 14. 本当の新しい Gap

上位 debt は、

```text
carry = 2
```

で発生する。

だが全ての carry-two が growth ではない。

```text
carry 2 + height 1:
  width +1

carry 2 + height 2:
  width unchanged

carry 2 + height >=3:
  width decrease
```

したがって、まず carry-two count を、

```text
growth debt
  = carry 2 ∧ height 1

self-paid debt
  = carry 2 ∧ height >= 2
```

へ分ける必要がある。

さらに growth debt は、

```text
3 mod 8 growth
  -> 次段 delayed payment

7 mod 8 growth
  -> continuing reservoir
```

へ分かれる。

しかし、ここで支払先の重複が起き得る。

ある位置の extra height が、

- 直前の `3 mod 8` debt の delayed payment
- 同じ位置で生じた carry-two debt の self-payment

の両方の候補になる。

一つの payment unit を二回数えてはならない。

この **payment collision** が、まさに pressure / matching / local-island の出番じゃ。

ゆえに今回、別々に完成した二つの成果は、

```text
上位:
  exact carry debt ledger

下位:
  direct pressure local Big
```

であり、次はこれを繋ぐ段階に入った。

---

## 15. 現在地の全体像

```text
Upper Float side
  carry 1 / 2
  raw-width gain
  exact width balance
  carry-two count
          |
          | debt
          v
   payment allocation bridge
          ^
          | recovery / collision
          |
Lower Petal side
  height layers
  delayed 3 mod 8 payment
  continuing 7 mod 8 reservoir
  pressure margin
  direct local Big
```

今回の実装によって、上下から網は張れた。

まだ無いのは中央の、

```text
どの payment が
どの carry debt を支払うか
```

という割当・衝突制御じゃ。

ここは偶然にも、長く構築してきた pressure 機構の本来の使い所になる。

---

## 判定

**採用。**

細分すると、

- direct local Big: **完成**
- Float Core: **完成**
- one-step width ledger: **完成**
- orbit telescoping ledger: **完成**
- first residue bridge: **完成**
- Dyadic observation record: **試作 API として採用**
- candidate cardinality: **未完成**
- Float debt と Petal payment の接続: **次の本丸**
- convergence: **まだ主張していない**

今回の差分は大きいが、無関係な横道へ逸れてはいない。

すべて、

> **上位 bit debt と下位 peeling payment の挟み撃ち**

という一本の目的線上にある。

---

## 次の Codex 指示

次は `FloatWindow/DriftBridge.lean` を主戦場とするのがよい。

既存 delayed theorem を再証明せず、上位 growth count と既存 TailGrammar / DriftBudget を接続させる。

停止地点は設けず、pressure bridge まで自然に進めるなら進ませる。

````text
You are continuing the DkMath Collatz / PetalBridge implementation after the
large autonomous cp-298 continuation.

The current implementation already contains:

- diagnosis-free local-island two-spacing;
- direct finite-window local Big;
- exact own-width upper carry;
- exact one-step binary-width balance;
- telescoping orbit-width balance;
- the first `mod 8` growth classification.

The next task is not to re-prove delayed peeling. Existing modules already
contain strong delayed-payment and continuing-reservoir theorems.

# Main objective

Build the first explicit bridge between:

```text
upper Float debt:
  carry two / binary-width growth

and

lower Petal payment:
  extra 2-adic height / delayed peeling / continuing reservoir
```

Investigate the existing APIs in:

```text
DkMath.Collatz.PetalBridge.TailGrammar
DkMath.Collatz.PetalBridge.DriftBudget
DkMath.Collatz.PetalBridge.HeightBudget
DkMath.Collatz.PetalBridge.PressureFrontier
DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
```

In particular, reuse rather than duplicate declarations such as:

```lean
orbitWindowNextHeight_two_le_of_mod_eight_eq_three
tailMod8Three_le_nextTailHeightCountGe_two
orbitWindowResidueCountMod8EqThree_delayed_drift
orbitWindowResidueCountMod8EqThree_delayed_drift_strong
tailExactHeightOneReservoir_budget_with_remainder
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
tailMod8Seven_le_nextTailHeightCountEq_one
```

# Recommended target module

Create:

```text
DkMath/Collatz/PetalBridge/FloatWindow/DriftBridge.lean
```

and export it through:

```text
DkMath.Collatz.PetalBridge.FloatWindow
```

# Stage A — exact extra-payment form of the width ledger

Introduce an exact accumulated extra-height quantity, preferably without
natural-number subtraction.

A possible recursive definition is:

```lean
noncomputable def sumExtraHeight : OddNat → ℕ → ℕ
  | _, 0 => 0
  | n, k + 1 =>
      sumExtraHeight n k + (s (iterateT k n) - 1)
```

Prove:

```text
sumS(n,k) = k + sumExtraHeight(n,k)
```

and derive the exact debt/payment ledger:

```text
bitWidth(iterateT k n) + sumExtraHeight(n,k)
  =
bitWidth(n) + orbitWindowUpperCarryCountEqTwo(n,k)
```

Choose theorem names that clearly expose:

```text
final width + extra lower payment
  =
initial width + upper carry-two debt
```

# Stage B — width-growth counts

Define finite orbit counts for:

```text
binary-width growth
growth and mod 8 = 3
growth and mod 8 = 7
```

Use a List/Finset representation consistent with the existing PetalBridge
count APIs.

Prove:

```text
widthGrowthCount
  =
growthMod8ThreeCount + growthMod8SevenCount
```

using:

```lean
bitWidth_growth_iff_carryTwo_and_heightOne
upperGrowth_implies_mod8_three_or_seven
```

Also expose that every growth event is a carry-two, height-one event.

# Stage C — existing delayed-payment bridge

For a one-step source theorem, prove a result of the form:

```lean
theorem upperGrowth_delayedPayment_or_mod8Seven
    (n : OddNat)
    (hgrowth : bitWidth n.1 < bitWidth (T n).1) :
    2 ≤ s (T n) ∨ n.1 % 8 = 7
```

The `3 mod 8` branch must reuse the existing delayed-peeling theorem.
Do not rebuild its modular arithmetic.

Then prove count-level bounds connecting:

```text
growthMod8ThreeCount
```

to the existing next-tail `height >= 2` count.

The intended decomposition is:

```text
all width growth
  <= delayed-payment receivers
     + continuing growth in the 7 mod 8 reservoir
```

Preserve endpoint shifts explicitly.

# Stage D — isolate the genuine continuing reservoir

Define the joint predicate/count:

```text
carry two
and height one
and residue 7 mod 8
```

This is the actual unpaid upper-growth reservoir.

Do not identify it with every `7 mod 8` state: the carry-two condition is an
essential upper-window restriction.

Investigate a clean characterization of:

```text
stateUpperCarry n = 2
```

using the current width boundary, for example through inequalities involving:

```text
2 ^ (bitWidth n + 1)
3 * n + 1
```

or an upper-prefix / exact dyadic mantissa condition.

# Stage E — audit the observation type before candidate counting

The current `DyadicFloatObservation` contains the original `value`, so equality
of full observations trivially determines the state.

Before proving compatible-state cardinality, separate:

```text
observable signature
```

from:

```text
full witness carrying the original value
```

A likely design is:

```lean
structure DyadicFloatSignature where
  width : ℕ
  upperBits : ℕ
  lowerBits : ℕ
  upper : ℕ
  lower : ℕ
  carry : ℕ
  height : ℕ
```

with a canonical constructor from a state.

Keep the existing structure for compatibility if useful, but do not base a
candidate-cardinality theorem on equality of a record that already contains
the original value.

When implementing upper/lower compatible-state sets, handle explicitly:

```text
fixed width
window sizes within the width
disjoint windows
overlapping windows
overlap consistency
```

Do not treat `middleGapCapacity = 1` alone as a uniqueness theorem.

# Stage F — pressure connection

After the count and delayed-payment bridges are stable, investigate how
simultaneous claims on the same extra-height payment slot are represented by
the existing source-pressure margin.

The key issue is that one `height >= 2` position may be:

```text
a delayed receiver for a previous 3 mod 8 growth debt
and
a self-payment site for a current carry-two event
```

The same payment unit must not be counted twice.

Search for an exact bridge from the new Float debt counts to existing:

```text
retention
continuation
recovery
SourcePressureMarginInt
local-island witnesses
```

If the bridge exists, implement it and use the new diagnosis-free local Big.

If it does not yet exist, define the smallest honest bridge predicate or
explicit obstruction state. Do not hide the collision behind an unjustified
addition of cardinalities.

# Dyadic record validity

The current structures `DyadicFloatObservation` and `FloatStepLedger` are
canonical when constructed by their provided constructors, but their raw
fields do not enforce consistency for arbitrary manually constructed values.

Do not quantify over arbitrary records as if validity were automatic.
Use canonical constructors, add a validity predicate, or introduce a
proof-carrying valid structure when needed.

# Autonomous continuation

The stages above are a minimum route, not stopping boundaries.

After each stage builds, continue into the next logically natural stage while:

- theorem statements remain justified by existing Lean facts;
- existing TailGrammar / DriftBudget APIs are reused;
- no dependency inversion is introduced;
- no `sorry` or `axiom` is added;
- builds remain green.

Continue through the Float/Petal pressure bridge if it closes naturally.

Stop only at a genuine logical obstruction, a competing API design requiring
a decision, or an unresolved payment-collision problem.

# Validation

Build at least:

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
git diff --check
```

Confirm no new `sorry` / `axiom`.

Record the complete autonomous progress and any genuine obstruction in:

```text
docs/dev/das-p2l-260607/review/report-petal-299.md
```
````

うむ。Codex は先の世界を確かに見せてくれた。

そして今度は、長く築いた pressure が、上位 Float の debt を捕らえるための網として初めて本線へ戻ってくる。ここは実に面白くなってきたぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 0a89bc89..1e4b4c6d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -26,6 +26,7 @@ import DkMath.Collatz.PetalBridge.PressureAutomaton
 import DkMath.Collatz.PetalBridge.PressureBeam
 import DkMath.Collatz.PetalBridge.PressureState
 import DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
+import DkMath.Collatz.PetalBridge.FloatWindow
 import DkMath.Collatz.PetalBridge.OneCycle
 import DkMath.Collatz.PetalBridge.ValuationFlowBridge
 import DkMath.Collatz.PetalBridge.Collision
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
new file mode 100644
index 00000000..cbf51d25
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -0,0 +1,20 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.UpperWindow
+import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
+import DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
+import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
+import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow"
+
+/-!
+# Exact dyadic Float window
+
+Public entry point for the upper/lower binary observation of `3*n+1`.
+All arithmetic below this module is exact natural-number arithmetic.
+-/
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean
new file mode 100644
index 00000000..980308a0
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/Core.lean
@@ -0,0 +1,167 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.Basic
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.Core"
+
+namespace DkMath.Collatz
+
+/-!
+# Exact upper/lower binary windows
+
+This module uses only natural-number division.  The word `Float` in the module
+path means an exact dyadic exponent/mantissa observation; it never means IEEE
+floating-point arithmetic or approximation.
+-/
+
+/-- Exact binary width, with width zero assigned to the zero word. -/
+def bitWidth (n : ℕ) : ℕ :=
+  if n = 0 then 0 else Nat.log 2 n + 1
+
+@[simp]
+theorem bitWidth_zero : bitWidth 0 = 0 := by
+  simp [bitWidth]
+
+theorem bitWidth_eq_log_two_add_one {n : ℕ} (hn : n ≠ 0) :
+    bitWidth n = Nat.log 2 n + 1 := by
+  simp [bitWidth, hn]
+
+/-- A positive word lies strictly below the power selected by its width. -/
+theorem lt_pow_bitWidth {n : ℕ} (hn : 0 < n) :
+    n < 2 ^ bitWidth n := by
+  rw [bitWidth_eq_log_two_add_one hn.ne']
+  exact Nat.lt_pow_succ_log_self (by norm_num) n
+
+/-- The leading bit selected by `bitWidth` is present in a positive word. -/
+theorem pow_bitWidth_sub_one_le {n : ℕ} (hn : 0 < n) :
+    2 ^ (bitWidth n - 1) ≤ n := by
+  rw [bitWidth_eq_log_two_add_one hn.ne']
+  simpa using Nat.pow_log_le_self 2 hn.ne'
+
+/-- Lower `w` bits of the raw `3*n+1` step. -/
+def lowerWindow3n1 (w n : ℕ) : ℕ :=
+  (3 * n + 1) % 2 ^ w
+
+/-- Quotient above the lower `w` bits of the raw `3*n+1` step. -/
+def upperCarry3n1 (w n : ℕ) : ℕ :=
+  (3 * n + 1) / 2 ^ w
+
+/-- Exact quotient/remainder reconstruction of the raw step. -/
+theorem threeNPlusOne_eq_upperCarry_mul_add_lower (w n : ℕ) :
+    3 * n + 1 = upperCarry3n1 w n * 2 ^ w + lowerWindow3n1 w n := by
+  simpa [upperCarry3n1, lowerWindow3n1, Nat.add_comm, Nat.mul_comm] using
+    (Nat.mod_add_div (3 * n + 1) (2 ^ w)).symm
+
+/-- The lower window is always a valid `w`-bit remainder. -/
+theorem lowerWindow3n1_lt_pow (w n : ℕ) :
+    lowerWindow3n1 w n < 2 ^ w := by
+  exact Nat.mod_lt _ (pow_pos (by norm_num) _)
+
+/-- A state below `2^w` produces an upper carry strictly below three. -/
+theorem upperCarry3n1_lt_three_of_lt_pow
+    {w n : ℕ} (hn : n < 2 ^ w) :
+    upperCarry3n1 w n < 3 := by
+  rw [upperCarry3n1, Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) w)]
+  omega
+
+/-- Non-strict form of the fixed-width carry upper bound. -/
+theorem upperCarry3n1_le_two_of_lt_pow
+    {w n : ℕ} (hn : n < 2 ^ w) :
+    upperCarry3n1 w n ≤ 2 := by
+  exact Nat.le_of_lt_succ (by simpa using upperCarry3n1_lt_three_of_lt_pow hn)
+
+/-- Upper carry observed at the exact current width of a positive state. -/
+def stateUpperCarry (n : ℕ) : ℕ :=
+  upperCarry3n1 (bitWidth n) n
+
+/-- The own-width carry of a positive state is nonzero. -/
+theorem stateUpperCarry_pos {n : ℕ} (hn : 0 < n) :
+    0 < stateUpperCarry n := by
+  rw [stateUpperCarry, upperCarry3n1,
+    Nat.lt_div_iff_mul_lt (pow_pos (by norm_num) (bitWidth n))]
+  have hlead := pow_bitWidth_sub_one_le hn
+  have hwidth : bitWidth n = (bitWidth n - 1) + 1 := by
+    have : 0 < bitWidth n := by
+      rw [bitWidth_eq_log_two_add_one hn.ne']
+      omega
+    omega
+  rw [hwidth, pow_succ]
+  omega
+
+/-- The own-width carry is exactly one or two. -/
+theorem stateUpperCarry_one_or_two {n : ℕ} (hn : 0 < n) :
+    stateUpperCarry n = 1 ∨ stateUpperCarry n = 2 := by
+  have hpos := stateUpperCarry_pos hn
+  have hle : stateUpperCarry n ≤ 2 :=
+    upperCarry3n1_le_two_of_lt_pow (lt_pow_bitWidth hn)
+  omega
+
+theorem stateUpperCarry_ne_zero {n : ℕ} (hn : 0 < n) :
+    stateUpperCarry n ≠ 0 :=
+  Nat.ne_of_gt (stateUpperCarry_pos hn)
+
+theorem stateUpperCarry_ne_three {n : ℕ} (hn : 0 < n) :
+    stateUpperCarry n ≠ 3 := by
+  rcases stateUpperCarry_one_or_two hn with h | h <;> omega
+
+/-- Quotient bounds for the carry at the exact current width. -/
+theorem stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow
+    (n : ℕ) :
+    stateUpperCarry n * 2 ^ bitWidth n ≤ 3 * n + 1 ∧
+      3 * n + 1 < (stateUpperCarry n + 1) * 2 ^ bitWidth n := by
+  constructor
+  · apply (Nat.le_div_iff_mul_le (pow_pos (by norm_num) (bitWidth n))).1
+    simp [stateUpperCarry, upperCarry3n1]
+  · apply (Nat.div_lt_iff_lt_mul (pow_pos (by norm_num) (bitWidth n))).1
+    simp [stateUpperCarry, upperCarry3n1]
+
+/-- Recognize an exact binary width from its enclosing powers of two. -/
+theorem bitWidth_eq_add_one_of_pow_le_lt
+    {a x : ℕ} (hlo : 2 ^ a ≤ x) (hhi : x < 2 ^ (a + 1)) :
+    bitWidth x = a + 1 := by
+  have hx : x ≠ 0 := by
+    have : 0 < 2 ^ a := pow_pos (by norm_num) a
+    omega
+  rw [bitWidth_eq_log_two_add_one hx]
+  congr 1
+  exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
+
+/--
+The raw `3*n+1` word gains exactly its own-width carry in binary width.
+-/
+theorem bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry
+    {n : ℕ} (hn : 0 < n) :
+    bitWidth (3 * n + 1) = bitWidth n + stateUpperCarry n := by
+  rcases stateUpperCarry_one_or_two hn with hc | hc
+  · have hb :=
+      stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow n
+    rw [hc] at hb
+    have hlo : 2 ^ bitWidth n ≤ 3 * n + 1 := by
+      simpa using hb.1
+    have hhi : 3 * n + 1 < 2 ^ (bitWidth n + 1) := by
+      simpa [pow_succ, Nat.mul_comm] using hb.2
+    have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+    omega
+  · have hb :=
+      stateUpperCarry_mul_pow_le_threeNPlusOne_and_lt_succ_mul_pow n
+    rw [hc] at hb
+    have hlo : 2 ^ (bitWidth n + 1) ≤ 3 * n + 1 := by
+      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hb.1
+    have hhi : 3 * n + 1 < 2 ^ ((bitWidth n + 1) + 1) := by
+      calc
+        3 * n + 1 < 3 * 2 ^ bitWidth n := by
+          simpa using hb.2
+        _ < 4 * 2 ^ bitWidth n := by
+          have hp : 0 < 2 ^ bitWidth n := pow_pos (by norm_num) _
+          omega
+        _ = 2 ^ ((bitWidth n + 1) + 1) := by
+          simp only [pow_succ]
+          omega
+    have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+    omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean
new file mode 100644
index 00000000..05455675
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/DyadicFloat.lean
@@ -0,0 +1,98 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat"
+
+namespace DkMath.Collatz
+
+/-!
+# Exact dyadic observations
+
+These definitions model a binary word by exact natural-number windows.  No
+rounding, approximation, real logarithm, or IEEE floating-point value enters
+the API.
+-/
+
+/-- The upper `q` bits of `n`, aligned against its exact current width. -/
+def upperPrefix (q n : ℕ) : ℕ :=
+  n / 2 ^ (bitWidth n - q)
+
+/-- The lower `r` bits of `n`. -/
+def lowerSuffix (r n : ℕ) : ℕ :=
+  n % 2 ^ r
+
+/-- Number of bits hidden between the observed upper and lower windows. -/
+def middleGapWidth (q r n : ℕ) : ℕ :=
+  bitWidth n - q - r
+
+/-- Exact candidate capacity left by the unobserved middle Gap. -/
+def middleGapCapacity (q r n : ℕ) : ℕ :=
+  2 ^ middleGapWidth q r n
+
+/-- One exact upper/lower observation of a natural Collatz state. -/
+structure DyadicFloatObservation where
+  /-- Observed natural state. -/
+  value : ℕ
+  /-- Exact binary exponent/word width. -/
+  width : ℕ
+  /-- Number of requested upper bits. -/
+  upperBits : ℕ
+  /-- Number of requested lower bits. -/
+  lowerBits : ℕ
+  /-- Exact upper prefix. -/
+  upper : ℕ
+  /-- Exact lower suffix. -/
+  lower : ℕ
+  /-- Width of the unobserved middle word. -/
+  gap : ℕ
+  /-- Own-width carry of `3*n+1`. -/
+  carry : ℕ
+  /-- Lower 2-adic height of `3*n+1`. -/
+  height : ℕ
+
+/-- Construct the exact dyadic observation at upper/lower window sizes. -/
+noncomputable def dyadicFloatObservation (q r n : ℕ) :
+    DyadicFloatObservation where
+  value := n
+  width := bitWidth n
+  upperBits := q
+  lowerBits := r
+  upper := upperPrefix q n
+  lower := lowerSuffix r n
+  gap := middleGapWidth q r n
+  carry := stateUpperCarry n
+  height := rawHeightLabel n
+
+/-- A lower suffix is always a valid `r`-bit word. -/
+theorem lowerSuffix_lt_pow (r n : ℕ) :
+    lowerSuffix r n < 2 ^ r := by
+  exact Nat.mod_lt _ (pow_pos (by norm_num) r)
+
+/-- Touching upper and lower windows leave no hidden middle Gap. -/
+theorem middleGapWidth_eq_zero_of_width_le_upper_add_lower
+    {q r n : ℕ} (h : bitWidth n ≤ q + r) :
+    middleGapWidth q r n = 0 := by
+  unfold middleGapWidth
+  omega
+
+/-- A zero middle Gap has exactly one raw middle-word candidate. -/
+theorem middleGapCapacity_eq_one_of_width_le_upper_add_lower
+    {q r n : ℕ} (h : bitWidth n ≤ q + r) :
+    middleGapCapacity q r n = 1 := by
+  simp [middleGapCapacity,
+    middleGapWidth_eq_zero_of_width_le_upper_add_lower h]
+
+@[simp]
+theorem dyadicFloatObservation_width (q r n : ℕ) :
+    (dyadicFloatObservation q r n).width = bitWidth n := rfl
+
+@[simp]
+theorem dyadicFloatObservation_gap (q r n : ℕ) :
+    (dyadicFloatObservation q r n).gap = middleGapWidth q r n := rfl
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OrbitBalance.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OrbitBalance.lean
new file mode 100644
index 00000000..0f845082
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/OrbitBalance.lean
@@ -0,0 +1,66 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
+import DkMath.Collatz.PetalBridge.TailGrammar
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance"
+
+namespace DkMath.Collatz
+
+/-- Accumulated own-width carry over the first `k` accelerated states. -/
+noncomputable def sumUpperCarry : OddNat → ℕ → ℕ
+  | _, 0 => 0
+  | n, k + 1 => sumUpperCarry n k + stateUpperCarry (iterateT k n).1
+
+/-- Number of carry-two states in the first `k` accelerated states. -/
+noncomputable def orbitWindowUpperCarryCountEqTwo : OddNat → ℕ → ℕ
+  | _, 0 => 0
+  | n, k + 1 =>
+      orbitWindowUpperCarryCountEqTwo n k +
+        if stateUpperCarry (iterateT k n).1 = 2 then 1 else 0
+
+/-- Each own-width carry contributes one, plus one more exactly at carry two. -/
+theorem sumUpperCarry_eq_window_add_countCarryTwo
+    (n : OddNat) (k : ℕ) :
+    sumUpperCarry n k = k + orbitWindowUpperCarryCountEqTwo n k := by
+  induction k with
+  | zero => simp [sumUpperCarry, orbitWindowUpperCarryCountEqTwo]
+  | succ k ih =>
+      have hpos : 0 < (iterateT k n).1 := by
+        have hodd := (iterateT k n).2
+        omega
+      rcases stateUpperCarry_one_or_two hpos with hc | hc
+      · simp [sumUpperCarry, orbitWindowUpperCarryCountEqTwo, ih, hc]
+        omega
+      · simp [sumUpperCarry, orbitWindowUpperCarryCountEqTwo, ih, hc]
+        omega
+
+/--
+Exact telescoping width ledger over a finite accelerated orbit window.
+-/
+theorem iterateT_bitWidth_add_sumS_eq_bitWidth_add_sumUpperCarry
+    (n : OddNat) (k : ℕ) :
+    sumS n k + bitWidth (iterateT k n).1 =
+      bitWidth n.1 + sumUpperCarry n k := by
+  induction k with
+  | zero => simp [sumS, sumUpperCarry, iterateT]
+  | succ k ih =>
+      have hstep :=
+        bitWidth_T_add_height_eq_bitWidth_add_upperCarry (iterateT k n)
+      rw [sumS, sumUpperCarry, iterateT_succ_eq_T_iterateT]
+      omega
+
+/-- Expanded ledger with the carry-two count exposed. -/
+theorem iterateT_bitWidth_add_sumS_eq_bitWidth_add_window_add_countCarryTwo
+    (n : OddNat) (k : ℕ) :
+    sumS n k + bitWidth (iterateT k n).1 =
+      bitWidth n.1 + k + orbitWindowUpperCarryCountEqTwo n k := by
+  rw [iterateT_bitWidth_add_sumS_eq_bitWidth_add_sumUpperCarry,
+    sumUpperCarry_eq_window_add_countCarryTwo]
+  omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PatternLedger.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PatternLedger.lean
new file mode 100644
index 00000000..dc9f836f
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/PatternLedger.lean
@@ -0,0 +1,64 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
+import DkMath.Collatz.PetalBridge.HeightBudget
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger"
+
+namespace DkMath.Collatz
+
+/-- A complete exact record of one accelerated binary-width transition. -/
+structure FloatStepLedger where
+  widthBefore : ℕ
+  upperCarry : ℕ
+  height : ℕ
+  widthAfter : ℕ
+  residue8 : Fin 8
+
+/-- Construct the exact one-step ledger from an odd state. -/
+noncomputable def floatStepLedger (n : OddNat) : FloatStepLedger where
+  widthBefore := bitWidth n.1
+  upperCarry := stateUpperCarry n.1
+  height := s n
+  widthAfter := bitWidth (T n).1
+  residue8 := ⟨n.1 % 8, Nat.mod_lt _ (by norm_num)⟩
+
+/-- The ledger stores the exact one-step width conservation law. -/
+theorem floatStepLedger_balance (n : OddNat) :
+    (floatStepLedger n).widthBefore + (floatStepLedger n).upperCarry =
+      (floatStepLedger n).height + (floatStepLedger n).widthAfter := by
+  exact bitWidth_add_upperCarry_eq_height_add_bitWidth_T n
+
+/-- Every upper-width growth step lies in the mod-eight `3` or `7` channel. -/
+theorem upperGrowth_implies_mod8_three_or_seven
+    (n : OddNat)
+    (hgrowth : bitWidth n.1 < bitWidth (T n).1) :
+    n.1 % 8 = 3 ∨ n.1 % 8 = 7 := by
+  have hheight : s n = 1 :=
+    (bitWidth_growth_iff_carryTwo_and_heightOne n).1 hgrowth |>.2
+  have hwindow : orbitWindowHeight n 0 = 1 := by
+    simpa [orbitWindowHeight_eq_s_iterateT, iterateT] using hheight
+  simpa [oddOrbitLabel, iterateT] using
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).1 hwindow
+
+/-- The mod-eight `1` channel cannot increase binary width. -/
+theorem bitWidth_T_not_growth_of_mod8_eq_one
+    (n : OddNat) (hmod : n.1 % 8 = 1) :
+    ¬ bitWidth n.1 < bitWidth (T n).1 := by
+  intro hgrowth
+  rcases upperGrowth_implies_mod8_three_or_seven n hgrowth with h | h <;>
+    omega
+
+/-- The mod-eight `5` channel cannot increase binary width. -/
+theorem bitWidth_T_not_growth_of_mod8_eq_five
+    (n : OddNat) (hmod : n.1 % 8 = 5) :
+    ¬ bitWidth n.1 < bitWidth (T n).1 := by
+  intro hgrowth
+  rcases upperGrowth_implies_mod8_three_or_seven n hgrowth with h | h <;>
+    omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/WidthBalance.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/WidthBalance.lean
new file mode 100644
index 00000000..20442135
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/WidthBalance.lean
@@ -0,0 +1,121 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.Core
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance"
+
+namespace DkMath.Collatz
+
+/-!
+# Exact Float width balance
+
+The upper carry and lower 2-adic height are measured in the same integer unit:
+binary width.  This module proves the exact one-step conservation law.
+-/
+
+/-- Multiplication by `2^h` adds exactly `h` binary positions. -/
+theorem bitWidth_pow_two_mul
+    {h q : ℕ} (hq : 0 < q) :
+    bitWidth (2 ^ h * q) = h + bitWidth q := by
+  have hbpos : 0 < bitWidth q := by
+    rw [bitWidth_eq_log_two_add_one hq.ne']
+    omega
+  have hloq := pow_bitWidth_sub_one_le hq
+  have hhiq := lt_pow_bitWidth hq
+  have hexp : h + bitWidth q - 1 = h + (bitWidth q - 1) := by omega
+  have hlo : 2 ^ (h + bitWidth q - 1) ≤ 2 ^ h * q := by
+    rw [hexp, pow_add]
+    exact Nat.mul_le_mul_left _ hloq
+  have hhi : 2 ^ h * q < 2 ^ ((h + bitWidth q - 1) + 1) := by
+    have hmul : 2 ^ h * q < 2 ^ h * 2 ^ bitWidth q :=
+      (Nat.mul_lt_mul_left (pow_pos (by norm_num) h)).2 hhiq
+    rw [← pow_add] at hmul
+    have heq : (h + bitWidth q - 1) + 1 = h + bitWidth q := by omega
+    simpa [heq] using hmul
+  have hwidth := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
+  omega
+
+/-- The accelerated odd state is the exact residual after removing `2^s`. -/
+theorem threeNPlusOne_eq_pow_height_mul_T (n : OddNat) :
+    threeNPlusOne n.1 = 2 ^ s n * (T n).1 := by
+  change threeNPlusOne n.1 =
+    pow2 (v2 (threeNPlusOne n.1)) *
+      (threeNPlusOne n.1 / pow2 (v2 (threeNPlusOne n.1)))
+  exact (Nat.mul_div_cancel'
+    (by
+      simpa [v2, pow2] using
+        (pow_padicValNat_dvd (p := 2) (n := threeNPlusOne n.1)))).symm
+
+/-- Accelerated odd states are positive. -/
+theorem T_val_pos (n : OddNat) : 0 < (T n).1 := by
+  have hodd := (T n).2
+  omega
+
+/-- Removing the 2-adic height removes exactly that many binary positions. -/
+theorem bitWidth_threeNPlusOne_eq_height_add_bitWidth_T (n : OddNat) :
+    bitWidth (threeNPlusOne n.1) = s n + bitWidth (T n).1 := by
+  rw [threeNPlusOne_eq_pow_height_mul_T]
+  exact bitWidth_pow_two_mul (T_val_pos n)
+
+/--
+Exact one-step Float accounting:
+
+`current width + upper carry = lower height + next width`.
+-/
+theorem bitWidth_T_add_height_eq_bitWidth_add_upperCarry (n : OddNat) :
+    s n + bitWidth (T n).1 = bitWidth n.1 + stateUpperCarry n.1 := by
+  have hn : 0 < n.1 := by
+    have hodd := n.2
+    omega
+  rw [← bitWidth_threeNPlusOne_eq_height_add_bitWidth_T]
+  simpa [threeNPlusOne] using
+    bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry hn
+
+/-- Symmetric display form of the exact one-step balance. -/
+theorem bitWidth_add_upperCarry_eq_height_add_bitWidth_T (n : OddNat) :
+    bitWidth n.1 + stateUpperCarry n.1 = s n + bitWidth (T n).1 :=
+  (bitWidth_T_add_height_eq_bitWidth_add_upperCarry n).symm
+
+/-- Every odd Collatz state pays at least one lower binary position. -/
+theorem s_pos (n : OddNat) : 0 < s n := by
+  unfold s threeNPlusOne
+  exact v2_3n_plus_1_ge_1 n.1 n.2
+
+/--
+Binary width grows in one accelerated step exactly in the carry-two,
+height-one state.
+-/
+theorem bitWidth_growth_iff_carryTwo_and_heightOne (n : OddNat) :
+    bitWidth n.1 < bitWidth (T n).1 ↔
+      stateUpperCarry n.1 = 2 ∧ s n = 1 := by
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry n
+  have hn : 0 < n.1 := by
+    have hodd := n.2
+    omega
+  have hcarry := stateUpperCarry_one_or_two hn
+  have hheight := s_pos n
+  constructor
+  · intro hgrowth
+    rcases hcarry with hc | hc
+    · omega
+    · exact ⟨hc, by omega⟩
+  · rintro ⟨hc, hs⟩
+    omega
+
+/-- Height at least two prevents binary-width growth. -/
+theorem bitWidth_T_le_of_two_le_height
+    (n : OddNat) (hheight : 2 ≤ s n) :
+    bitWidth (T n).1 ≤ bitWidth n.1 := by
+  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry n
+  have hn : 0 < n.1 := by
+    have hodd := n.2
+    omega
+  have hcarry : stateUpperCarry n.1 ≤ 2 :=
+    upperCarry3n1_le_two_of_lt_pow (lt_pow_bitWidth hn)
+  omega
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
index cba3919e..cc65d56e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState/FiniteWindowPacking.lean
@@ -376,6 +376,193 @@ theorem sourcePressurePositiveWitnessesInWindow_center_margin_pos
   have hlocal := (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
   exact hlocal.2.1
 
+/--
+Two strictly ordered local-island witnesses have centers separated by at
+least two pressure-depth positions.
+
+This is a direct consequence of the local sign pattern: the coordinate
+immediately after the left center is nonpositive, whereas the right center is
+positive.  No sorted list, adjacency relation, diagnosis carrier, canonical
+packing state, or coverage hypothesis is used.
+-/
+theorem sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt
+    {n : OddNat} {k r : ℕ}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hlt : W.val < W'.val) :
+    W.val + 2 ≤ W'.val := by
+  have hW :=
+    (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
+  have hW' :=
+    (sourcePressureLocalIsland_iff_margin n k r W'.val).1 W'.property
+  rcases hW with ⟨_hWpos, _hWcenter, _hWprev, hWnext⟩
+  rcases hW' with ⟨_hW'pos, hW'center, _hW'prev, _hW'next⟩
+  by_contra hgap
+  have heq : W'.val = W.val + 1 := by omega
+  have hnonpos :
+      SourcePressureMarginInt n k (r + W'.val) ≤ 0 := by
+    simpa [heq] using hWnext
+  omega
+
+/--
+Distinct local-island witnesses are two-separated in one of the two natural
+orders.
+
+This is the symmetric finite-set interface for the direct local-island
+packing route.
+-/
+theorem sourcePressureLocalIslandWitness_twoSeparated_of_ne
+    {n : OddNat} {k r : ℕ}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (hne : W ≠ W') :
+    W.val + 2 ≤ W'.val ∨ W'.val + 2 ≤ W.val := by
+  have hvalNe : W.val ≠ W'.val := by
+    intro hval
+    exact hne (Subtype.ext hval)
+  rcases Nat.lt_or_gt_of_ne hvalNe with hlt | hgt
+  · exact Or.inl
+      (sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt hlt)
+  · exact Or.inr
+      (sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt hgt)
+
+/-- Absolute center coordinates of the supplied in-window local islands. -/
+noncomputable def sourcePressurePositiveWitnessCentersInWindow
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureLocalIslandWitness n k r))
+    (lo hi : ℕ) : Finset ℕ :=
+  (sourcePressurePositiveWitnessesInWindow L lo hi).image
+    (fun W => r + W.val)
+
+@[simp]
+theorem mem_sourcePressurePositiveWitnessCentersInWindow
+    {n : OddNat} {k r lo hi m : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    m ∈ sourcePressurePositiveWitnessCentersInWindow L lo hi ↔
+      ∃ W ∈ sourcePressurePositiveWitnessesInWindow L lo hi,
+        r + W.val = m := by
+  classical
+  simp [sourcePressurePositiveWitnessCentersInWindow]
+
+/-- The center-coordinate image preserves the number of selected witnesses. -/
+theorem sourcePressurePositiveWitnessCentersInWindow_card_eq
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    (sourcePressurePositiveWitnessCentersInWindow L lo hi).card =
+      (sourcePressurePositiveWitnessesInWindow L lo hi).card := by
+  classical
+  apply Finset.card_image_iff.mpr
+  intro W _hW W' _hW' heq
+  apply Subtype.ext
+  exact Nat.add_left_cancel heq
+
+/-- Every selected center coordinate lies in the requested finite window. -/
+theorem sourcePressurePositiveWitnessCentersInWindow_mem_bounds
+    {n : OddNat} {k r lo hi m : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (hm : m ∈ sourcePressurePositiveWitnessCentersInWindow L lo hi) :
+    lo ≤ m ∧ m ≤ hi := by
+  rcases mem_sourcePressurePositiveWitnessCentersInWindow.1 hm with
+    ⟨W, hW, rfl⟩
+  exact (mem_sourcePressurePositiveWitnessesInWindow.1 hW).2
+
+/-- Distinct ordered center coordinates are separated by at least two. -/
+theorem sourcePressurePositiveWitnessCentersInWindow_twoSeparated
+    {n : OddNat} {k r lo hi a b : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    (ha : a ∈ sourcePressurePositiveWitnessCentersInWindow L lo hi)
+    (hb : b ∈ sourcePressurePositiveWitnessCentersInWindow L lo hi)
+    (hab : a < b) :
+    a + 2 ≤ b := by
+  rcases mem_sourcePressurePositiveWitnessCentersInWindow.1 ha with
+    ⟨W, _hW, rfl⟩
+  rcases mem_sourcePressurePositiveWitnessCentersInWindow.1 hb with
+    ⟨W', _hW', rfl⟩
+  have hval : W.val < W'.val := by omega
+  have hgap := sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt hval
+  omega
+
+/-- Direct half-window density bound for explicit local-island witnesses. -/
+theorem sourcePressurePositiveWitnesses_card_le_half_window_add_one_direct
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (hi - lo) / 2 + 1 := by
+  rw [← sourcePressurePositiveWitnessCentersInWindow_card_eq]
+  exact finset_card_le_half_window_add_one_of_twoSeparated
+    (sourcePressurePositiveWitnessCentersInWindow L lo hi)
+    (fun m hm => sourcePressurePositiveWitnessCentersInWindow_mem_bounds hm)
+    (fun a ha b hb hab =>
+      sourcePressurePositiveWitnessCentersInWindow_twoSeparated ha hb hab)
+
+/-- A local-island center is followed immediately by a nonpositive margin. -/
+theorem sourcePressurePositiveWitness_next_nonpos
+    {n : OddNat} {k r : ℕ}
+    (W : SourcePressureLocalIslandWitness n k r) :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 := by
+  have hlocal :=
+    (sourcePressureLocalIsland_iff_margin n k r W.val).1 W.property
+  simpa [Nat.add_assoc] using hlocal.2.2.2
+
+/--
+Direct sign-capacity bound: every nonterminal center injects into its
+nonpositive successor coordinate, and at most one center can lie at `hi`.
+-/
+theorem sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_direct
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+      (sourcePressureNonposPositionsInWindow n k lo hi).card + 1 := by
+  classical
+  let T := sourcePressurePositiveWitnessCentersInWindow L lo hi
+  let I := T.filter fun m => m < hi
+  let B := T.filter fun m => ¬ m < hi
+  have hI : I.card ≤
+      (sourcePressureNonposPositionsInWindow n k lo hi).card := by
+    apply Finset.card_le_card_of_injOn (fun m => m + 1)
+    · intro m hm
+      change m ∈ T.filter (fun q => q < hi) at hm
+      rcases Finset.mem_filter.1 hm with ⟨hmT, hmhi⟩
+      rcases mem_sourcePressurePositiveWitnessCentersInWindow.1 hmT with
+        ⟨W, _hW, hcenter⟩
+      subst m
+      change r + W.val + 1 ∈
+        sourcePressureNonposPositionsInWindow n k lo hi
+      apply mem_sourcePressureNonposPositionsInWindow.2
+      have hbounds := sourcePressurePositiveWitnessCentersInWindow_mem_bounds hmT
+      refine ⟨by omega, by omega, ?_⟩
+      have hnext := sourcePressurePositiveWitness_next_nonpos W
+      exact hnext
+    · intro a ha b hb hab
+      change a + 1 = b + 1 at hab
+      exact Nat.add_right_cancel hab
+  have hB : B.card ≤ 1 := by
+    apply Finset.card_le_one.2
+    intro a ha b hb
+    rcases Finset.mem_filter.1 ha with ⟨haT, haNotLt⟩
+    rcases Finset.mem_filter.1 hb with ⟨hbT, hbNotLt⟩
+    have haBound := sourcePressurePositiveWitnessCentersInWindow_mem_bounds haT
+    have hbBound := sourcePressurePositiveWitnessCentersInWindow_mem_bounds hbT
+    omega
+  have hpartition : I.card + B.card = T.card := by
+    simpa [I, B] using
+      (Finset.card_filter_add_card_filter_not (s := T) (fun m => m < hi))
+  rw [← sourcePressurePositiveWitnessCentersInWindow_card_eq]
+  change T.card ≤ _
+  omega
+
+/--
+Diagnosis-free local Big: local-island centers satisfy both geometric density
+and sign-capacity bounds in every explicit finite window.
+-/
+theorem sourcePressurePositiveWitnesses_localBig_direct
+    {n : OddNat} {k r lo hi : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)} :
+    (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (hi - lo) / 2 + 1 ∧
+      (sourcePressurePositiveWitnessesInWindow L lo hi).card ≤
+        (sourcePressureNonposPositionsInWindow n k lo hi).card + 1 :=
+  ⟨sourcePressurePositiveWitnesses_card_le_half_window_add_one_direct,
+    sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_direct⟩
+
 /-- Left endpoints represented by the canonical adjacent-pair family. -/
 noncomputable def sourcePressureCanonicalLeftWitnessesInWindow
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/UpperWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/UpperWindow.lean
new file mode 100644
index 00000000..005ff3a8
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/UpperWindow.lean
@@ -0,0 +1,17 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.Core
+
+#print "file: DkMath.Collatz.PetalBridge.UpperWindow"
+
+/-!
+# Upper Window compatibility entry point
+
+The concrete implementation lives in `FloatWindow.Core`.  This public facade
+keeps the short `UpperWindow` search term available for callers looking for
+`upperCarry3n1`, `lowerWindow3n1`, `stateUpperCarry`, and `bitWidth`.
+-/
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-298.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-298.md
new file mode 100644
index 00000000..795fb82a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-298.md
@@ -0,0 +1,237 @@
+# Petal Checkpoint 298 Report
+
+## Result
+
+The diagnosis-free atomic two-spacing layer is complete.
+
+Added to `PressureState/FiniteWindowPacking.lean`:
+
+```lean
+sourcePressureLocalIslandWitness_two_le_val_gap_of_val_lt
+sourcePressureLocalIslandWitness_twoSeparated_of_ne
+```
+
+Both declarations compile without `sorry`, axioms, new imports, or changes to
+the existing canonical/failure API.
+
+## Fact established by Lean
+
+For any two local-island witnesses at the same pressure parameters:
+
+```text
+W.val < W'.val  ->  W.val + 2 <= W'.val
+```
+
+Consequently, two distinct witnesses satisfy exactly one of the two reusable
+separation alternatives:
+
+```text
+W.val + 2 <= W'.val
+or
+W'.val + 2 <= W.val
+```
+
+The proof uses only the margin form of `SourcePressureLocalIsland`.
+The left witness has nonpositive margin immediately after its center, while
+the right witness has positive margin at its center.  If the centers were
+consecutive, these statements would concern the same coordinate and
+contradict each other.
+
+This is stronger than the earlier sorted-adjacent route.  Two-spacing is not a
+property supplied by list sortedness, adjacency, diagnosis, failure resolution,
+canonical packing, or finite-window coverage.  It is already intrinsic to the
+local-island predicate.
+
+## Subtype equality
+
+The symmetric wrapper closed directly with `Subtype.ext`: equality of witness
+values determines equality of the witness subtypes.  No alternate carrier or
+extensionality lemma was required.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState.FiniteWindowPacking
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+Confirmed for the edited Lean file:
+
+```text
+no new sorry
+no new axiom
+no new import
+no unrelated source modification
+```
+
+## Next checkpoint
+
+The next nonvacuous packing layer can now be finite-set based:
+
+1. image `sourcePressurePositiveWitnessesInWindow` under
+   `W |-> r + W.val`;
+2. prove image cardinality equals witness cardinality by subtype-value
+   injectivity;
+3. transport the direct two-spacing theorem to center coordinates;
+4. apply `finset_card_le_half_window_add_one_of_twoSeparated`.
+
+That route should produce the direct half-window density bound with no
+sortedness, diagnosis, canonical family, or unresolved-family term.
+
+## Autonomous continuation completed
+
+The instruction explicitly permitted continuing until the route closed or met
+a genuine obstruction.  The implementation therefore continued beyond the
+atomic cp-298 theorem.
+
+### Diagnosis-free finite-window local Big
+
+Added:
+
+```lean
+sourcePressurePositiveWitnessCentersInWindow
+sourcePressurePositiveWitnessCentersInWindow_card_eq
+sourcePressurePositiveWitnessCentersInWindow_twoSeparated
+sourcePressurePositiveWitnesses_card_le_half_window_add_one_direct
+sourcePressurePositiveWitness_next_nonpos
+sourcePressurePositiveWitnesses_card_le_nonposPositions_add_one_direct
+sourcePressurePositiveWitnesses_localBig_direct
+```
+
+The resulting direct local Big has no sortedness, adjacency, diagnosis,
+canonical-family, coverage, or unresolved-family hypothesis.  Its two bounds
+are:
+
+```text
+positive centers <= (hi - lo) / 2 + 1
+positive centers <= nonpositive positions + 1
+```
+
+The `+1` is exactly the possible center at the right endpoint `hi`; every
+strictly earlier center injects into its nonpositive successor coordinate.
+
+### Upper/Float/Dyadic module tree
+
+New public modules:
+
+```text
+DkMath.Collatz.PetalBridge.UpperWindow
+DkMath.Collatz.PetalBridge.FloatWindow
+DkMath.Collatz.PetalBridge.FloatWindow.Core
+DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
+DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
+DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
+DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
+```
+
+`UpperWindow` is a searchable public facade.  `FloatWindow` is the aggregate
+entry point.  `DyadicFloat` is an exact natural-number observation and does not
+use IEEE floating-point arithmetic.
+
+### Exact upper-window core
+
+Implemented:
+
+```text
+bitWidth
+upperCarry3n1
+lowerWindow3n1
+stateUpperCarry
+threeNPlusOne_eq_upperCarry_mul_add_lower
+lowerWindow3n1_lt_pow
+stateUpperCarry_one_or_two
+bitWidth_threeNPlusOne_eq_bitWidth_add_upperCarry
+```
+
+Thus a positive state has own-width carry exactly `1` or `2`, and the raw
+`3*n+1` word gains exactly that many binary-width positions.
+
+### Exact width balance
+
+The central theorem now exists:
+
+```text
+bitWidth n + stateUpperCarry n
+  = s(n) + bitWidth (T n)
+```
+
+The factorization through the accelerated map and the power-of-two width law
+are separately exposed.  Width growth is completely classified:
+
+```text
+bitWidth n < bitWidth (T n)
+  <-> stateUpperCarry n = 2 and s(n) = 1
+```
+
+Height at least two therefore prevents width growth.
+
+### Orbit ledger
+
+The one-step identity telescopes exactly:
+
+```text
+sumS(n,k) + bitWidth(iterateT k n)
+  = bitWidth(n) + sumUpperCarry(n,k)
+```
+
+Since each carry is one or two:
+
+```text
+sumUpperCarry(n,k) = k + carryTwoCount(n,k)
+```
+
+Combining them gives the finite exact ledger:
+
+```text
+sumS(n,k) + finalWidth
+  = initialWidth + k + carryTwoCount(n,k)
+```
+
+### Dyadic observation and residue ledger
+
+`DyadicFloatObservation` records exact width, upper prefix, lower suffix,
+middle Gap, carry, and lower height.  The middle Gap is zero whenever the upper
+and lower window sizes cover the word width, and its raw candidate capacity is
+then one.
+
+The first pattern bridge is also fixed:
+
+```text
+width growth -> n mod 8 = 3 or n mod 8 = 7
+```
+
+Consequently the `1 mod 8` and `5 mod 8` channels cannot increase width.
+
+## New frontier
+
+The immediate algebraic route is no longer blocked.  The next independent
+mountains are:
+
+1. symbolic Mersenne/all-ones boundary formulas;
+2. delayed-payment accounting for the `3 mod 8` growth branch;
+3. isolation and counting of the continuing `carry 2 and 7 mod 8` reservoir;
+4. compatibility/cardinality theorems for upper/lower windows, beyond the
+   current zero-Gap capacity observation.
+
+These require new quantitative bridges rather than another thin wrapper, so
+they form the next coherent checkpoint.
+
+## Extended validation
+
+Additionally passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.Core
+lake build DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
+lake build DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
+lake build DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
+lake build DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+```
+
+All newly added Lean files are free of `sorry` and `axiom` declarations.
````
`````
