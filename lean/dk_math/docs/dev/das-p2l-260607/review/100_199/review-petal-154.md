# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureAccounting

gch: 0326573fdb6478b11ba8ad2528791b348a2d4df1

## Report

cp153 を実装しました。今回は指示通り main root の [PressureAccounting.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean) のみ更新しています。

追加した主な層:

- `SourcePressureIntervalPulseAddress` list から accounted interval list への変換
- list 長さ保存
- pulse-address list の `sum ≤ -length` と非空なら負
- pulse-address list の sorted / failure dichotomy
- 直接 before 述語 `SourcePressureIntervalPulseAddressBefore`
- pair-level iff 補題
- sorted pulse-address list から family への lift と budget wrapper

重要な注意として、コードコメントにも `not before` は overlap 証拠ではなく「sorted-before failure」に過ぎない、と明記しました。

レポートも追加済みです: [report-petal-153.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-153.md)

確認:

- `lake build DkMath.Collatz.PetalBridge.PressureAccounting` 通過
- `lake build DkMath.Collatz.PetalBridge` 通過
- `PressureAccounting.lean` の `sorry` 検索ヒットなし
- `git diff --check` 通過

既存の `ZsigmondyCyclotomicResearch` の `sorry` warning は今回範囲外です。

## Review

## 結論

うむ、Checkpoint 153 は **採用** じゃ 👍️
今回は指示通り、`PressureAccounting.lean` の main root のみに集中できておる。

今回の中心は、

```text id="vsvdta"
SourcePressureIntervalPulseAddress
  -> SourcePressureAccountedInterval
  -> explicit list
  -> sorted / failure split
  -> sorted family
  -> negative budget
```

の導線をつないだことじゃな。

特に、単発の

```lean id="x94mlm"
sourcePressureAccountedInterval_of_intervalPulseAddress
```

を、list / sorted / failure / family / budget へ持ち上げたのが大きい。レポートでも、`OneCycle`、`ValuationFlowBridge`、ABC には触れず、`PressureAccounting` のみ更新したと明記されておる。これは main root 復帰として正しい。

## 実装内容の解説

## 1. address list から accounted list への変換

追加された定義はこれじゃ。

```lean id="kkwwfz"
def sourcePressureAccountedIntervalList_of_intervalPulseAddressList
```

中身は素直に、

```lean id="cj7e8n"
L.map sourcePressureAccountedInterval_of_intervalPulseAddress
```

これで、実体である `SourcePressureIntervalPulseAddress` のリストを、会計可能な `SourcePressureAccountedInterval` のリストへ変換できるようになった。

長さ保存補題も入っている。

```lean id="n9fkbf"
sourcePressureAccountedIntervalList_of_intervalPulseAddressList_length
```

これは後続の `≤ -length` 系の定理でかなり効く。

## 2. pulse-address list budget が通った

今回の主砲はこれじゃ。

```lean id="ecmm30"
sourcePressureIntervalPulseAddressList_sum_le_neg_length
```

意味はこう。

```text id="yazkfx"
明示的に与えた interval-pulse address が m 個あるなら、
それらを accounted interval に変換した net drop 合計は高々 -m。
```

つまり、

$$
\sum_{A\in L}\mathrm{NetDrop}(A)\le -|L|
$$

が、`SourcePressureIntervalPulseAddress` の明示リストで直接言えるようになった。

これはかなり重要じゃ。
前回までは `SourcePressureAccountedInterval` を直接渡す必要があった。今回からは、実際の frontier / pulse 側の住所オブジェクトをそのまま使える。

## 3. sorted / failure layer も address 側へ上がった

追加された二つ。

```lean id="hiek3h"
def SourcePressureIntervalPulseAddressListSortedBefore
def SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
```

これは accounted list 側の sorted / failure を、address list 側へ転送している。

さらに、

```lean id="x6h3zz"
sourcePressureIntervalPulseAddressList_sorted_or_failure
```

により、任意の明示 address list は、

```text id="5wc9n2"
sorted として扱える
または
sorted-before failure を持つ
```

のどちらかへ分岐できる。

これは PetalBridge らしい。
成功ルートだけでなく、失敗ルートも first-class にしている。

## 4. `not before != overlap` の注意が良い

今回、コードコメントにも

```text id="6fbg35"
not before != overlap
```

が明記されているのは非常によい。

これは重要じゃ。

`A before B` が失敗したからといって、すぐに \(A\) と \(B\) が重なっているとは限らない。
単に順序が逆かもしれない。

したがって failure は、

```text id="0g4n78"
sorted-before failure
```

であって、

```text id="yex7c5"
overlap evidence
```

ではない。

ここを明示したのは、後の大域議論で誤爆しないために大事じゃ。

## 5. direct before predicate も良い

追加された、

```lean id="ccyxah"
def SourcePressureIntervalPulseAddressBefore
```

は、

```lean id="rz2ij7"
A.start + A.len ≤ B.start
```

という直接形じゃ。

さらに、

```lean id="x65eiu"
sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
```

で、accounted interval 側の before と一致することも固定した。

これは良い橋じゃ。
今後は address の世界で順序を語りつつ、必要なら accounted interval 側の予算 API に落とせる。

## 6. sorted address list から family へ

追加された、

```lean id="teec05"
sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
```

も良い。

これで、

```text id="7um5c1"
sorted interval-pulse address list
  -> accounted interval family
```

が直接作れる。

さらに、

```lean id="f5fs65"
sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
```

まであるので、sorted address list を family にして、そのまま budget が読める。

## 注意点

## 1. まだ producer ではない

今回で address list を処理する API はできた。
ただし、まだ次は言っていない。

```text id="q5tfbz"
どこからその address list が生成されるか
その list が全 pulse を覆うか
その list が maximal か
orbit window と完全対応するか
```

ここは未到達じゃ。

今あるのは、

```text id="54ldl6"
明示的に与えられた SourcePressureIntervalPulseAddress の list
```

を処理する API じゃ。

## 2. budget は union accounting ではない

今回の `sum ≤ -length` は、あくまで明示リスト上の cost 合計じゃ。

まだ、

```text id="fpvylh"
区間の合併上の pressure accounting
```

ではない。

これは今後も明記するべきじゃ。

## 数学的な意味

今回で、本線はかなりつながった。

```text id="82f1g8"
interval pulse address
  -> accounted interval
  -> explicit address list
  -> sorted/failure dichotomy
  -> sorted accounted family
  -> negative budget
```

これはかなり大きい。
いままでは `PressureFrontier` 側の住所オブジェクトと、`PressureAccounting` 側の会計オブジェクトが少し離れていた。今回、その橋が list レベルまで伸びた。

ここまで来ると、次の main root は明確じゃ。

```text id="twj2vb"
producer 側、つまり orbit-window / frontier 側から
explicit SourcePressureIntervalPulseAddress list をどう得るか
```

ここへ進む。

## 次の指示方針

次は **main root 専念**。
`OneCycle`、`ValuationFlowBridge`、ABC は触らない。
`PressureAccounting` と、必要なら `PressureFrontier` との薄い接続だけを見る。

特に次は、

```text id="x8apcy"
explicit address list を受け取るだけ
```

から、

```text id="amwds5"
frontier / orbit-window producer が出す address list を受け取る
```

へ進むのがよい。

ただし、まだ coverage は言わない。
producer が出した list に対して、sorted/failure split を返すだけに留める。

## 次の Codex 依頼

```text id="5n1rf0"
Checkpoint 154: Main root only — connect pulse-address list accounting to frontier producers.

Scope:
Focus only on the main root.

Allowed files:
- DkMath/Collatz/PetalBridge/PressureAccounting.lean
- DkMath/Collatz/PetalBridge/PressureFrontier.lean
- optionally a new thin file:
  DkMath/Collatz/PetalBridge/PressureAddressFamily.lean

Do not modify:
- OneCycle.lean
- ValuationFlowBridge.lean
- ABC files
- NumberTheory files

unless a build/import issue forces a tiny fix.

Context:
Checkpoint 153 lifted explicit `SourcePressureIntervalPulseAddress` lists into
the `PressureAccounting` sorted/failure/budget API.

Existing main-root API includes:

- sourcePressureAccountedInterval_of_intervalPulseAddress
- sourcePressureAccountedIntervalList_of_intervalPulseAddressList
- sourcePressureIntervalPulseAddressList_sum_le_neg_length
- sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty
- SourcePressureIntervalPulseAddressBefore
- sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
- SourcePressureIntervalPulseAddressListSortedBefore
- SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
- sourcePressureIntervalPulseAddressList_sorted_or_failure
- sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
- sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
- sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty

Global rules:
- Do not claim maximality.
- Do not claim uniqueness of pressure families.
- Do not claim coverage.
- Do not claim prefix behavior.
- Do not claim union accounting.
- Do not claim Collatz convergence.
- Keep all statements about explicitly supplied or explicitly produced interval-pulse addresses.
- Failure means sorted-before failure, not overlap, unless extra hypotheses prove overlap.

Main goal:
Create a thin address-family layer for explicit `SourcePressureIntervalPulseAddress`
lists and connect it to the sorted/failure/budget API.

Part A: define an explicit pulse-address family carrier.

Add a structure:

  structure SourcePressureIntervalPulseAddressFamily
      (n : OddNat) (k r : Nat) where
    items : List (SourcePressureIntervalPulseAddress n k r)

This carrier should not contain coverage, maximality, or disjointness fields.
It is just an explicit list wrapper.

Part B: sorted/failure predicates for the family.

Define:

  def SourcePressureIntervalPulseAddressFamilySortedBefore
      (F : SourcePressureIntervalPulseAddressFamily n k r) : Prop :=
    SourcePressureIntervalPulseAddressListSortedBefore F.items

  def SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure
      (F : SourcePressureIntervalPulseAddressFamily n k r) : Prop :=
    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure F.items

Prove:

  theorem sourcePressureIntervalPulseAddressFamily_sorted_or_failure
      (F : SourcePressureIntervalPulseAddressFamily n k r) :
      SourcePressureIntervalPulseAddressFamilySortedBefore F ∨
        SourcePressureIntervalPulseAddressFamilyHasSortedBeforeFailure F

Part C: family to accounted-family lift.

Define:

  def sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily
      (F : SourcePressureIntervalPulseAddressFamily n k r)
      (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
      SourcePressureAccountedIntervalFamily n k r :=
    sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
      F.items hsorted

Prove budget wrappers:

  theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_le_neg_length
      (F : SourcePressureIntervalPulseAddressFamily n k r)
      (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F) :
      (((sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily F hsorted).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
          -((F.items.length : Nat) : Int)

  theorem sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily_sum_neg_of_nonempty
      (F : SourcePressureIntervalPulseAddressFamily n k r)
      (hsorted : SourcePressureIntervalPulseAddressFamilySortedBefore F)
      (hF : F.items ≠ []) :
      (((sourcePressureAccountedIntervalFamily_of_sortedPulseAddressFamily F hsorted).items).map
        (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0

Part D: constructors.

Add thin constructors:

  def sourcePressureIntervalPulseAddressFamily_nil
      (n : OddNat) (k r : Nat) :
      SourcePressureIntervalPulseAddressFamily n k r

  def sourcePressureIntervalPulseAddressFamily_singleton
      (A : SourcePressureIntervalPulseAddress n k r) :
      SourcePressureIntervalPulseAddressFamily n k r

  def sourcePressureIntervalPulseAddressFamily_cons
      (A : SourcePressureIntervalPulseAddress n k r)
      (F : SourcePressureIntervalPulseAddressFamily n k r) :
      SourcePressureIntervalPulseAddressFamily n k r

Also add length simp wrappers if useful.

Part E: producer bridge skeleton.

Search existing `PressureFrontier.lean` for objects that already produce or
package interval-pulse addresses.  Do not invent coverage.

If there is already a structure or theorem that contains one
`SourcePressureIntervalPulseAddress`, add only a thin constructor:

  def sourcePressureIntervalPulseAddressFamily_singleton_of_address
      (A : SourcePressureIntervalPulseAddress n k r) :
      SourcePressureIntervalPulseAddressFamily n k r

If there is already a list-producing object, add a wrapper from that object to
`SourcePressureIntervalPulseAddressFamily`.

If no producer exists yet, do not fabricate one.  Instead add a comment section
or report note saying:

  "No canonical frontier producer of address lists was found in this checkpoint."

Part F: failure is not overlap.

Add comments near the family failure predicate:

  "Family sorted-before failure is an order obstruction only. It does not imply
   interval overlap; reversed order is also a failure."

Do not prove overlap theorems unless additional hypotheses make the statement
true.

Part G: report.

Create:

  docs/dev/das-p2l-260607/review/report-petal-154.md

Include:
- whether a new file was created or PressureAccounting was extended directly,
- exact name of the pulse-address family carrier,
- constructors added,
- sorted/failure family predicates added,
- sorted-or-failure theorem added,
- accounted-family lift added,
- budget wrappers added,
- whether any existing frontier producer was found,
- if no producer was found, state that explicitly,
- explicit note that this checkpoint does not introduce maximality, uniqueness,
  coverage, prefix behavior, union accounting, or Collatz convergence.

Verification:

  lake build DkMath.Collatz.PetalBridge.PressureAccounting
  lake build DkMath.Collatz.PetalBridge.PressureFrontier
  lake build DkMath.Collatz.PetalBridge

If a new file is created:

  lake build DkMath.Collatz.PetalBridge.PressureAddressFamily

Run:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureFrontier.lean

If a new file is created:

  rg -n "\\bsorry\\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAddressFamily.lean

Also run:

  git diff --check
```

## 総評

良い進展じゃ。
今回で、main root はかなり実体に近づいた。

```text id="3294i7"
address witness
  -> accounted interval
  -> address list
  -> sorted/failure
  -> family
  -> budget
```

ここまで来た。

次は、これをさらに `SourcePressureIntervalPulseAddressFamily` として包み、frontier producer へ接続する段階じゃ。
ただし、まだ coverage は言わない。
「明示されたものを、正しく会計する」だけに徹する。これが main root の安全な登山道じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
index 5b9f2ee7..fe8c7806 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
@@ -388,6 +388,27 @@ def sourcePressureAccountedInterval_of_intervalPulseAddress
       simpa [SourcePressureIntervalNetDrop] using
         sourcePressureIntervalPulseAddress_margin_after_eq_start_add_sum_netDrop A }
 
+/--
+Map an explicit list of interval-pulse addresses to accounted intervals.
+
+This is only a carrier conversion.  It preserves the supplied list order and
+does not assert that the addresses are maximal, unique, disjoint, covering, or
+prefix-shaped.
+-/
+def sourcePressureAccountedIntervalList_of_intervalPulseAddressList
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r)) :
+    List (SourcePressureAccountedInterval n k r) :=
+  L.map sourcePressureAccountedInterval_of_intervalPulseAddress
+
+@[simp]
+theorem sourcePressureAccountedIntervalList_of_intervalPulseAddressList_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r)) :
+    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).length =
+      L.length := by
+  simp [sourcePressureAccountedIntervalList_of_intervalPulseAddressList]
+
 /--
 Finite-list pressure budget over explicitly provided accounted intervals.
 
@@ -409,6 +430,43 @@ theorem sourcePressureAccountedInterval_list_sum_le_neg_length
       simp at ih ⊢
       omega
 
+/--
+Finite-list pressure budget over explicitly supplied interval-pulse addresses.
+
+This theorem is deliberately just a list-cost statement.  It does not require
+the supplied addresses to be sorted or disjoint, and it does not state union
+accounting for their covered depths.
+-/
+theorem sourcePressureIntervalPulseAddressList_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r)) :
+    ((sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((L.length : ℕ) : ℤ) := by
+  simpa [sourcePressureAccountedIntervalList_of_intervalPulseAddressList] using
+    sourcePressureAccountedInterval_list_sum_le_neg_length
+      (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
+
+/--
+Any nonempty explicit interval-pulse-address list has negative total listed
+net drop after conversion to accounted intervals.
+
+This is only a cost statement for the supplied witnesses; it is not union
+accounting over their geometric support.
+-/
+theorem sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureIntervalPulseAddress n k r)}
+    (hL : L ≠ []) :
+    ((sourcePressureAccountedIntervalList_of_intervalPulseAddressList L).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  have hbudget := sourcePressureIntervalPulseAddressList_sum_le_neg_length L
+  have hlen : 0 < L.length := by
+    cases L with
+    | nil => contradiction
+    | cons _ _ => simp
+  omega
+
 /--
 Any nonempty explicit list of accounted intervals has negative total net drop.
 
@@ -675,6 +733,27 @@ def SourcePressureAccountedIntervalBefore
     (A B : SourcePressureAccountedInterval n k r) : Prop :=
   NatIntervalBefore A.start A.len B.start B.len
 
+/--
+Ordered non-overlap for two interval-pulse addresses.
+
+This is the direct pulse-address version of `SourcePressureAccountedIntervalBefore`.
+Its negation is only a sorted-before failure.  It is not, by itself, overlap
+evidence: the addresses may simply be in the reverse order.
+-/
+def SourcePressureIntervalPulseAddressBefore
+    {n : OddNat} {k r : ℕ}
+    (A B : SourcePressureIntervalPulseAddress n k r) : Prop :=
+  A.start + A.len ≤ B.start
+
+theorem sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r} :
+    SourcePressureIntervalPulseAddressBefore A B ↔
+      SourcePressureAccountedIntervalBefore
+        (sourcePressureAccountedInterval_of_intervalPulseAddress A)
+        (sourcePressureAccountedInterval_of_intervalPulseAddress B) := by
+  rfl
+
 /-- Transitive-like composition for ordered accounted intervals. -/
 theorem SourcePressureAccountedIntervalBefore.trans_like
     {n : OddNat} {k r : ℕ}
@@ -1009,6 +1088,137 @@ theorem sourcePressureAccountedIntervalList_sorted_or_failure
             · exact Or.inr (Or.inr htail)
           · exact Or.inr (Or.inl hAB)
 
+/--
+Adjacent sortedness for an explicit interval-pulse-address list.
+
+The predicate is defined by converting addresses to accounted intervals and
+reusing the accounted-list sortedness.  It is still only a statement about the
+explicit list supplied by the caller.
+-/
+def SourcePressureIntervalPulseAddressListSortedBefore
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r)) : Prop :=
+  SourcePressureAccountedIntervalListSortedBefore
+    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
+
+/--
+Adjacent sorted-before failure for an explicit interval-pulse-address list.
+
+This is not overlap evidence.  It only records that the converted accounted
+list is not adjacent-sorted at some neighboring pair.
+-/
+def SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r)) : Prop :=
+  SourcePressureAccountedIntervalListHasSortedBeforeFailure
+    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
+
+/--
+Every explicit interval-pulse-address list is either adjacent-sorted after
+conversion or carries an adjacent sorted-before failure.
+
+This is a list-internal dichotomy only; it is not a coverage or convergence
+statement.
+-/
+theorem sourcePressureIntervalPulseAddressList_sorted_or_failure
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r)) :
+    SourcePressureIntervalPulseAddressListSortedBefore L ∨
+      SourcePressureIntervalPulseAddressListHasSortedBeforeFailure L :=
+  sourcePressureAccountedIntervalList_sorted_or_failure
+    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
+
+/-- A two-address list is sorted exactly when the first address is before the second. -/
+theorem sourcePressureIntervalPulseAddressListSortedBefore_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r} :
+    SourcePressureIntervalPulseAddressListSortedBefore [A, B] ↔
+      SourcePressureIntervalPulseAddressBefore A B := by
+  change
+    SourcePressureAccountedIntervalListSortedBefore
+      [sourcePressureAccountedInterval_of_intervalPulseAddress A,
+        sourcePressureAccountedInterval_of_intervalPulseAddress B] ↔
+      SourcePressureIntervalPulseAddressBefore A B
+  rw [sourcePressureAccountedIntervalListSortedBefore_pair_iff]
+  exact sourcePressureIntervalPulseAddressBefore_iff_accountedBefore.symm
+
+/--
+A two-address list has a sorted-before failure exactly when the first address
+is not before the second.
+
+Again, this does not imply overlap.  It only detects failure of this chosen
+left-to-right order.
+-/
+theorem sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff
+    {n : OddNat} {k r : ℕ}
+    {A B : SourcePressureIntervalPulseAddress n k r} :
+    SourcePressureIntervalPulseAddressListHasSortedBeforeFailure [A, B] ↔
+      ¬ SourcePressureIntervalPulseAddressBefore A B := by
+  change
+    SourcePressureAccountedIntervalListHasSortedBeforeFailure
+      [sourcePressureAccountedInterval_of_intervalPulseAddress A,
+        sourcePressureAccountedInterval_of_intervalPulseAddress B] ↔
+      ¬ SourcePressureIntervalPulseAddressBefore A B
+  rw [sourcePressureAccountedIntervalListHasSortedBeforeFailure_pair_iff]
+  exact not_congr sourcePressureIntervalPulseAddressBefore_iff_accountedBefore.symm
+
+/--
+Build an accounted family from an adjacent-sorted interval-pulse-address list.
+
+The family is still the conversion of an explicitly supplied list.  The sorted
+hypothesis is only used to obtain pairwise disjointness of the converted
+intervals.
+-/
+def sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r))
+    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
+    SourcePressureAccountedIntervalFamily n k r :=
+  sourcePressureAccountedIntervalFamily_of_sortedBefore
+    (sourcePressureAccountedIntervalList_of_intervalPulseAddressList L)
+    hsorted
+
+@[simp]
+theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r))
+    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
+    (sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
+      L hsorted).items.length = L.length := by
+  simp [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList,
+    sourcePressureAccountedIntervalFamily_of_sortedBefore,
+    sourcePressureAccountedIntervalList_of_intervalPulseAddressList]
+
+/--
+Budget wrapper for a sorted interval-pulse-address family.
+
+The sorted hypothesis packages the family.  The inequality itself is still the
+explicit-list budget over the converted address witnesses.
+-/
+theorem
+    sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
+    {n : OddNat} {k r : ℕ}
+    (L : List (SourcePressureIntervalPulseAddress n k r))
+    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
+      L hsorted).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum ≤
+        -((L.length : ℕ) : ℤ) := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList]
+    using sourcePressureIntervalPulseAddressList_sum_le_neg_length L
+
+theorem
+    sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureIntervalPulseAddress n k r)}
+    (hsorted : SourcePressureIntervalPulseAddressListSortedBefore L)
+    (hL : L ≠ []) :
+    (((sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
+      L hsorted).items).map
+      (fun A => SourcePressureIntervalNetDrop n k r A.start A.len)).sum < 0 := by
+  simpa [sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList]
+    using sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty hL
+
 /-- Singleton sorted-family budget wrapper. -/
 theorem sourcePressureAccountedIntervalFamily_sorted_singleton_sum_le_neg_one
     {n : OddNat} {k r : ℕ}
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-153.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-153.md
new file mode 100644
index 00000000..0bfadcfb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-153.md
@@ -0,0 +1,186 @@
+# report-petal-153
+
+Checkpoint: 153
+
+Subject: main root only; lift explicit interval-pulse-address lists into the
+`PressureAccounting` family and obstruction API.
+
+## Summary
+
+This checkpoint stayed in:
+
+```text
+DkMath.Collatz.PetalBridge.PressureAccounting
+```
+
+No `OneCycle`, `ValuationFlowBridge`, or ABC files were modified.
+
+The core move was to lift the existing single-address bridge:
+
+```lean
+sourcePressureAccountedInterval_of_intervalPulseAddress
+```
+
+from one `SourcePressureIntervalPulseAddress` to explicit lists, sorted-list
+predicates, sorted families, budget wrappers, and pair-level failure facts.
+
+All claims remain about explicitly supplied interval-pulse addresses.  Nothing
+new claims maximality, uniqueness, coverage, prefix behavior, union accounting,
+or Collatz convergence.
+
+## Added List Conversion
+
+Chosen name:
+
+```lean
+def sourcePressureAccountedIntervalList_of_intervalPulseAddressList
+```
+
+It is the direct map:
+
+```lean
+L.map sourcePressureAccountedInterval_of_intervalPulseAddress
+```
+
+Length wrapper added:
+
+```lean
+theorem sourcePressureAccountedIntervalList_of_intervalPulseAddressList_length
+```
+
+## Added Pulse-Address List Budget
+
+Implemented:
+
+```lean
+theorem sourcePressureIntervalPulseAddressList_sum_le_neg_length
+```
+
+This proves that the converted list of explicit address witnesses contributes
+at most `-L.length` to the summed interval net drop.
+
+Also added the nonempty corollary:
+
+```lean
+theorem sourcePressureIntervalPulseAddressList_sum_neg_of_nonempty
+```
+
+This is an extra convenience theorem inferred after the main budget theorem
+passed.
+
+## Added Pulse-Address Sorted / Failure Layer
+
+Implemented:
+
+```lean
+def SourcePressureIntervalPulseAddressListSortedBefore
+def SourcePressureIntervalPulseAddressListHasSortedBeforeFailure
+theorem sourcePressureIntervalPulseAddressList_sorted_or_failure
+```
+
+These are defined through the accounted-list conversion, so they inherit the
+existing sorted/failure dichotomy.
+
+Important comment preserved in code:
+
+```text
+not before != overlap
+```
+
+A sorted-before failure only says that the chosen left-to-right adjacent order
+failed.  The interval may be reversed rather than overlapping.
+
+## Added Direct Pulse-Address Before Predicate
+
+Optional part F was implemented.
+
+Added:
+
+```lean
+def SourcePressureIntervalPulseAddressBefore
+theorem sourcePressureIntervalPulseAddressBefore_iff_accountedBefore
+```
+
+This gives the direct address-level predicate:
+
+```lean
+A.start + A.len <= B.start
+```
+
+and proves that it agrees with the accounted-interval predicate after
+conversion.
+
+## Added Pair-Level Pulse Facts
+
+As an extra small API layer, added:
+
+```lean
+theorem sourcePressureIntervalPulseAddressListSortedBefore_pair_iff
+theorem sourcePressureIntervalPulseAddressListHasSortedBeforeFailure_pair_iff
+```
+
+These make two-address examples easy to read:
+
+```text
+[A, B] sorted  <-> A before B
+[A, B] failure <-> not A before B
+```
+
+Again, the failure theorem is not an overlap theorem.
+
+## Added Sorted Family Lift
+
+Implemented:
+
+```lean
+def sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList
+```
+
+and wrappers:
+
+```lean
+theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_le_neg_length
+theorem sourcePressureAccountedIntervalFamily_of_sortedIntervalPulseAddressList_sum_neg_of_nonempty
+```
+
+The sorted hypothesis is used to package the converted list as a pairwise
+disjoint family.  The budget theorem remains the explicit-list budget.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureAccounting
+lake build DkMath.Collatz.PetalBridge
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge/PressureAccounting.lean
+```
+
+The `rg` check returned no matches.
+
+The build still reports the existing unrelated warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch uses sorry
+```
+
+This is outside checkpoint 153.
+
+## Next Inference
+
+The next natural main-root step is to connect this pulse-address list layer to
+the nearest orbit-window or frontier producer:
+
+```text
+producer of explicit SourcePressureIntervalPulseAddress list
+  -> sorted/failure split
+  -> if sorted: accounted family and budget
+  -> if failure: obstruction evidence kept first-class
+```
+
+The key design rule should remain:
+
+```text
+failure is order failure first, overlap only with extra hypotheses.
+```
````
`````
