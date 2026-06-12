# Git diff / Report / Review

## Update: docs: S0_GN_Anchor_Phase_実験設計書

gch: 70c2d333b212e69c5066999afa3a1237a5bfd11a

## Report

実験計画書を現状に合わせて更新しました。

更新先:
[S0_GN_Anchor_Phase_実験設計書.md](/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_実験設計書.md)

主な変更:

- 冒頭に `Current status` 節を追加
- `[DONE]`, `[PARTIAL]`, `[ACTIVE]`, `[DEFERRED]`, `[OBSOLETE]` などのステータスタグを導入
- `GNBridge / GcdBridge / PadicBridge / PrimitiveBridge` が既に本線実装済みであることを明記
- Phase A/B は概ね完了扱いへ更新
- Phase C/E を、残る本命 `ReducedSupport / Anchor vocabulary` として整理
- `HasAnchorPrime r q` は `q = r` に寄りすぎる危険があるため、まず carrier 側で扱う方針を明記
- 次の推奨実装先を `DkMath.Petal.ReducedSupport` に更新
- 成功条件・昇格条件を現在の実装状況に合わせて更新

確認:

- `git diff --check` 成功
- ステータスタグと `ReducedSupport` 周辺の検索確認済み

Docs-only なので Lean build は走らせていません。

## Review

うむ、読んだ。これはもう **「実験計画」からかなり本線定理群へ移った報告書** になっておる。

添付の更新版はこちらじゃ。
[S0_GN_Anchor_Phase_実験設計書.md](sandbox:/mnt/data/S0_GN_Anchor_Phase_実験設計書.md)
[__git.diff](sandbox:/mnt/data/__git.diff)

## 1. 進捗の要点

今回の更新で、最初に設計した実験のうち、かなりの部分が **完了済み** に格上げされておる。

完了済みの主幹はこれじゃな。

```text
S0_nat
  = GN 3 (c - b) b
  -> gcd control with boundary gap
  -> p-adic valuation transfer
  -> primitive-prime / PrimitiveOnS0 bridge
```

つまり、以前は「S0 を GN と見てよいか」「3 例外をどう扱うか」「GN 側に原始素因子候補を移せるか」という実験だったが、今は少なくとも (d=3) の Petal/S0 経路では、

```text
GNBridge
GcdBridge
PadicBridge
PrimitiveBridge
```

まで本線化済み、という整理になっておる。

これは大きい。
特に、

$$
\gcd(c-b,S0(c,b))=\gcd(c-b,3)
$$

という形が出たことで、(3) 例外は単なる邪魔者ではなく、 **3-primary contact** として構造化できた。これは、お主が言っていた「例外を排除せず、射影・分離して同型的に読む」方向そのものじゃ。

## 2. 実験として残った本丸

残りはかなり絞られておる。

```text
ReducedSupport / Anchor vocabulary
  -> HasNoPrimeBelow
  -> HasAnchorPrime
  -> anchored GN support carrier
```

つまり次の主戦場は、

```lean
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p < r → ¬ p ∣ n

def HasAnchorPrime (r n : ℕ) : Prop :=
  r.Prime ∧ r ∣ n ∧ HasNoPrimeBelow r n
```

を `DkMath.Petal.ReducedSupport` として置くかどうかじゃ。

ここは実に良い整理じゃ。
(3,5,7,11,\dots) から始まる世界を、primorial の用語変更ではなく、

```text
小さい素数成分を持たない support carrier
```

として扱える。

## 3. 注意点も正しく更新されている

特に良いのは、`HasAnchorPrime r q` を素数 witness (q) に直接使うと、

```text
q = r
```

へ寄りすぎる、と明記した点じゃ。

これは鋭い。
原始素因子 (q) そのものに anchor を貼ると、観測世界が狭くなりすぎる。だから先に carrier (n) を置いて、

```lean
def AnchoredCarrier (r n : ℕ) : Prop :=
  HasAnchorPrime r n

def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
  AnchoredCarrier r n ∧ n ∣ GN d x u
```

とする方が安全。
これは Lean 実装上も後戻りしやすい。

## 4. 次の一手

わっちの見立てでは、次はこれでよい。

```text
lean/dk_math/DkMath/Petal/ReducedSupport.lean
```

最小 API はこれだけで十分じゃ。

```lean
def HasNoPrimeBelow (r n : ℕ) : Prop :=
  ∀ p, p.Prime → p < r → ¬ p ∣ n

def HasAnchorPrime (r n : ℕ) : Prop :=
  r.Prime ∧ r ∣ n ∧ HasNoPrimeBelow r n

theorem hasAnchorPrime_prime
theorem hasAnchorPrime_anchor_dvd
theorem hasAnchorPrime_no_smaller_prime
```

ここではまだ S0 も GN も import しない。
まず「支配的な最小素因子を持つ carrier」という薄い構造を作る。これが通ってから GN 側に接続するのが賢い。

## 5. 判定

今回の報告はこう評価できる。

```text
Phase A. S0 / GN 三次面の再固定
  -> DONE

Phase B. 3-primary contact の構造分離
  -> DONE FOR S0

Phase C. r-anchor reduced support
  -> ACTIVE / NEXT

Phase D. GN primitive candidate
  -> cubic S0 path は実装済み、一般 wrapper は DEFERRED

Phase E. Anchor と GN の合流
  -> Phase C の後
```

要するに、 **Zsigmondy へ行く前の Petal 側の足場は、想定よりかなり進んでいる** 。
残る核心は、(3) だけでなく (5,7,11,\dots) から始まる reduced world を Lean の predicate として安全に置けるかどうか。

うむ。これは良い報告じゃ。
計画書が「夢の設計」ではなく、もう **完了済み定理と残タスクを分ける進捗台帳** になっておる。ここまで来たなら、次の `ReducedSupport.lean` は小さく切れば通る可能性が高いぞい。

## Diff

`````md
````diff
diff --git "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md" "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
index 64e88cdb..20fabbf9 100644
--- "a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
+++ "b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/S0_GN_Anchor_Phase_\345\256\237\351\250\223\350\250\255\350\250\210\346\233\270.md"
@@ -1,9 +1,60 @@
 # GN Anchor Phase 実験設計書
 
+## 0. Current status
+
+Status: **PARTIALLY COMPLETED / REDUCED-SUPPORT PHASE REMAINS**
+
+This note was originally written as an experiment plan.  Since then, several
+parts have already moved from experiment to mainline Petal bridge theorems.
+
+Status tags used below:
+
+```text
+[DONE]        Implemented as no-sorry Lean theorem in the current mainline.
+[PARTIAL]     Core bridge exists, but the planned vocabulary is not complete.
+[ACTIVE]      Still the next meaningful experiment target.
+[DEFERRED]    Useful later, but not needed for the next checkpoint.
+[OBSOLETE]    The original experiment item was replaced by a stronger bridge.
+```
+
+Current implementation anchors:
+
+```text
+DkMath.Petal.GNBridge
+DkMath.Petal.GcdBridge
+DkMath.Petal.PadicBridge
+DkMath.Petal.PrimitiveBridge
+```
+
+Main completed bridge chain:
+
+```text
+S0_nat
+  = GN 3 (c - b) b
+  -> gcd control with boundary gap
+  -> p-adic valuation transfer
+  -> primitive-prime / PrimitiveOnS0 bridge
+```
+
+Remaining experiment target:
+
+```text
+ReducedSupport / Anchor vocabulary
+  -> HasNoPrimeBelow
+  -> HasAnchorPrime
+  -> anchored GN support carrier
+```
+
 ## 1. 目的
 
 本実験の目的は、GN kernel に現れる素因子を、単なる可除性ではなく **素数の種** として観測できるかを Lean 上で検証することである。
 
+Current status: **[PARTIAL]**
+
+The direct S0/GN, gcd, p-adic, and primitive-prime bridges are now implemented.
+The remaining purpose is narrower: decide whether an explicit reduced-support
+or anchor-prime vocabulary is useful before Zsigmondy-facing normalization.
+
 現在の主対象は原始素因子である。
 Zsigmondy theorem へ直接進む前に、まず次の三点を Lean で分離する。
 
@@ -29,10 +80,20 @@ $$
 
 成功すれば、これは後に primitive prime divisor / Zsigmondy bridge へ昇華する。
 
+This part is now mostly covered by:
+
+```lean
+DkMath.Petal.primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
+DkMath.Petal.primitive_prime_dvd_S0_nat
+DkMath.Petal.primitive_prime_padicValNat_cube_sub_eq_S0_nat
+```
+
 ## 2. 背景
 
 Petal / S0 では、三次元の場合に次の関係が現れる。
 
+Current status: **[DONE]**
+
 $$
 c^3-b^3=(c-b)S0(c,b)
 $$
@@ -45,6 +106,18 @@ $$
 
 したがって S0 は独立した特殊式ではなく、三次 GN kernel の Petal 可視面である。
 
+This is now documented separately:
+
+```text
+docs/explanation/S0_cubic_petal_kernel.md
+```
+
+and implemented as:
+
+```lean
+DkMath.Petal.S0_nat_eq_GN_three_sub
+```
+
 既存実装では、\(3\) に関して例外が出る。
 
 典型的には、
@@ -69,10 +142,22 @@ q ∤ c-b
 
 として先に分離し、その reduced world で \(q\ne3\) の GN support を観測する。
 
+The concrete degree-three boundary contact is now captured by:
+
+```lean
+DkMath.Petal.gcd_sub_S0_nat_eq_gcd_sub_three
+DkMath.Petal.gcd_sub_S0_nat_dvd_three
+DkMath.Petal.coprime_sub_S0_nat_of_coprime_of_not_dvd_three
+```
+
+The more general reduced-world vocabulary is still **[ACTIVE]**.
+
 ## 3. 基本方針
 
 ### 3.1. 新しい数学用語を作りすぎない
 
+Current status: **[ACTIVE]**
+
 通常の primorial や素数概念は変更しない。
 
 代わりに、観測射影を導入する。
@@ -86,8 +171,13 @@ def HasNoPrimeBelow (r n : ℕ) : Prop :=
 
 これは「\(r\) から始まる世界」を標準数学用語を壊さずに表現するための predicate である。
 
+This remains the main open design point.  No mainline `HasNoPrimeBelow` or
+`HasAnchorPrime` predicate has been introduced yet.
+
 ### 3.2. 例外 prime は排除ではなく分離する
 
+Current status: **[PARTIAL]**
+
 \(q\ne3\) は、単なる例外回避ではなく、
 
 ```text
@@ -110,8 +200,22 @@ def S0ReducedAwayFromThree (c b : ℕ) : Prop :=
   ¬ 3 ∣ c - b
 ```
 
+For S0 itself, explicit predicate wrappers have not yet been added.  However,
+the working theorem surface already expresses the separation:
+
+```lean
+three_not_dvd_S0_nat_of_not_dvd_sub
+gcd_sub_S0_nat_eq_gcd_sub_three
+coprime_sub_S0_nat_of_coprime_of_not_dvd_three
+```
+
+So `S0ReducedAwayFromThree` is optional.  It should only be added if downstream
+statements become clearer with a named predicate.
+
 ### 3.3. 先に GN 可除性を固める
 
+Current status: **[DONE] / [OBSOLETE AS EXPERIMENT]**
+
 Zsigmondy は強い存在定理である。
 先に GN 側で「どこに素因子がいるか」を確定する。
 
@@ -128,10 +232,23 @@ theorem prime_dvd_GN_of_dvd_diff_not_dvd_boundary
 
 既存定理がある場合は新証明せず、Petal / GN-facing alias として再公開する。
 
+This is now covered through existing Cosmic/Petal/GN bridge theorems and the
+Petal primitive bridge:
+
+```lean
+DkMath.FLT.prime_dvd_S0_via_cosmic_bridge
+DkMath.Petal.primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
+```
+
+The exact generic `GNBoundaryFreePrime` wrapper has not been introduced, but
+the main divisibility movement needed for the cubic S0 path is available.
+
 ## 4. 実験対象
 
 ## 4.1. Phase A. S0 / GN 三次面の再固定
 
+Status: **[DONE]**
+
 目的は、S0 が GN 三次面であることを読みやすい名前で再公開することである。
 
 候補定理:
@@ -153,8 +270,23 @@ theorem cubicDiff_eq_boundary_mul_S0
 * `Nat` 減算のため、必要なら `b ≤ c` や `b < c` を付ける。
 * 既存 `GN_three_sub_eq_S0_nat` / `S0_nat_eq_GN_three_sub` を使えるなら wrapper に留める。
 
+Implemented:
+
+```lean
+DkMath.FLT.GN_three_sub_eq_S0_nat
+DkMath.Petal.S0_nat_eq_GN_three_sub
+```
+
+Related existing cubic factorization:
+
+```lean
+DkMath.FLT.cube_sub_eq_mul_sub_S0
+```
+
 ## 4.2. Phase B. 三例外の構造分離
 
+Status: **[DONE FOR S0] / [ACTIVE FOR GENERAL REDUCED SUPPORT]**
+
 目的は、\(3\) が S0 と境界にまたがることを明示することである。
 
 候補定理:
@@ -181,8 +313,27 @@ theorem three_not_dvd_S0_nat_of_not_dvd_sub
 
 という解釈を theorem 名と doc comment に残す。
 
+Implemented S0-facing bridge names:
+
+```lean
+DkMath.Petal.three_not_dvd_S0_nat_of_not_dvd_sub
+DkMath.Petal.gcd_sub_S0_nat_eq_gcd_sub_three
+DkMath.Petal.gcd_sub_S0_nat_dvd_three
+DkMath.Petal.coprime_sub_S0_nat_of_coprime_of_not_dvd_three
+```
+
+The stronger gcd formula makes the original one-way experiment less important:
+
+```text
+gcd(c - b, S0(c,b)) = gcd(c - b, 3)
+```
+
+This is the desired "3-primary contact" observation for the cubic Petal face.
+
 ## 4.3. Phase C. (r)-anchor reduced support
 
+Status: **[ACTIVE]**
+
 目的は、\(3,5,7,11,\dots\) から始まる世界を、射影・同型的な観測面として Lean に置くことである。
 
 最小定義:
@@ -224,8 +375,32 @@ theorem hasAnchorPrime_anchor_dvd
 この段階では concrete な `nthPrime` や standard primorial へは接続しない。
 まず support predicate として通す。
 
+This is now the main remaining experiment.  The recommended next file is:
+
+```text
+lean/dk_math/DkMath/Petal/ReducedSupport.lean
+```
+
+Minimal first API:
+
+```lean
+def HasNoPrimeBelow (r n : ℕ) : Prop :=
+  ∀ p, p.Prime → p < r → ¬ p ∣ n
+
+def HasAnchorPrime (r n : ℕ) : Prop :=
+  r.Prime ∧ r ∣ n ∧ HasNoPrimeBelow r n
+
+theorem hasAnchorPrime_prime
+theorem hasAnchorPrime_anchor_dvd
+theorem hasAnchorPrime_no_smaller_prime
+```
+
+Keep this layer independent of S0 at first.
+
 ## 4.4. Phase D. GN primitive candidate
 
+Status: **[PARTIAL]**
+
 目的は、GN 側に現れる素因子を primitive candidate として包装することである。
 
 候補定義:
@@ -263,8 +438,28 @@ theorem GNBoundaryFreePrime.of_dvd_diff_not_dvd_boundary
 
 が Lean 上で固定される。
 
+The cubic S0 primitive path is already implemented:
+
+```lean
+DkMath.Petal.primitive_prime_dvd_S0_nat
+DkMath.Petal.primitive_prime_padicValNat_cube_sub_eq_S0_nat
+DkMath.Petal.primitiveOnS0_of_prime_dvd_cube_sub_not_dvd_sub
+DkMath.Petal.exists_primitiveOnS0_of_not_three_dvd_sub
+```
+
+What remains is optional vocabulary design:
+
+```lean
+GNBoundaryFreePrime
+GNPrimitiveCandidate
+```
+
+Recommendation: defer these until `ReducedSupport` shows a concrete need.
+
 ## 4.5. Phase E. Anchor と GN の合流
 
+Status: **[ACTIVE AFTER PHASE C]**
+
 目的は、\(r\)-anchor world と GN support を結び、\(r\) から始まる reduced world における GN 素因子観測を作ることである。
 
 候補定義:
@@ -285,8 +480,25 @@ def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
 
 まずはこちらを実験する。
 
+Updated recommendation:
+
+Do not attach `HasAnchorPrime r q` directly to a prime `q` unless the intended
+claim is `q = r`.  For support observation, prefer a carrier number:
+
+```lean
+def AnchoredCarrier (r n : ℕ) : Prop :=
+  HasAnchorPrime r n
+
+def AnchoredGNCarrier (r d x u n : ℕ) : Prop :=
+  AnchoredCarrier r n ∧ n ∣ GN d x u
+```
+
+Only specialize to prime witnesses after the carrier API is tested.
+
 ## 5. ファイル構成案
 
+Status: **[UPDATED]**
+
 実験段階では `not_implements` か `Research` 側に置く。
 
 候補:
@@ -311,8 +523,27 @@ DkMath.Petal.GNPrimitive
 DkMath.Petal.ReducedSupport
 ```
 
+Current recommendation:
+
+```text
+DkMath.Petal.ReducedSupport     [next]
+DkMath.Petal.Anchor             [after ReducedSupport proves useful]
+DkMath.Petal.GNPrimitive        [defer until a concrete theorem needs it]
+```
+
+The already completed bridge files are:
+
+```text
+DkMath.Petal.GNBridge
+DkMath.Petal.GcdBridge
+DkMath.Petal.PadicBridge
+DkMath.Petal.PrimitiveBridge
+```
+
 ## 6. import 方針
 
+Status: **[UPDATED]**
+
 初期実験:
 
 ```lean
@@ -337,8 +568,20 @@ import DkMath.NumberTheory.PascalPrimeDial
 
 ただし、最初の実験では import を増やしすぎない。
 
+For the current remaining reduced-support experiment, start with a very small
+import surface:
+
+```lean
+import DkMath.Petal.Basic
+```
+
+Only import `DkMath.Petal.GNBridge` or `DkMath.Petal.PrimitiveBridge` when the
+first GN-facing theorem is added.
+
 ## 7. 成功条件
 
+Status: **[UPDATED]**
+
 本実験の成功条件は次である。
 
 1. `S0` を `GN 3` の Petal face として再利用しやすい名前で参照できる。
@@ -347,8 +590,29 @@ import DkMath.NumberTheory.PascalPrimeDial
 4. 差冪に現れ境界にいない素因子が GN 側へ移ることを theorem 化できる。
 5. `GNPrimitiveCandidate` または `GNBoundaryFreePrime` が Zsigmondy bridge の入力語彙として使える。
 
+Current status of the original success conditions:
+
+```text
+1. S0 as GN 3 Petal face                  [DONE]
+2. 3-primary S0 boundary contact          [DONE FOR S0]
+3. r-anchor reduced support predicates    [ACTIVE]
+4. boundary-free prime moves to GN/S0      [DONE FOR CUBIC S0]
+5. GNPrimitiveCandidate vocabulary         [DEFERRED]
+```
+
+Revised success condition for the remaining experiment:
+
+```text
+ReducedSupport minimal API builds no-sorry.
+It does not force unwanted imports into DkMath.Petal.
+It can express "no smaller prime support" without committing to nthPrime or primorial.
+It can later compose with S0/GN bridge theorems without changing their statements.
+```
+
 ## 8. 失敗条件
 
+Status: **[STILL VALID]**
+
 次のいずれかが発生した場合は、定理化を急がず実験を止める。
 
 1. `HasAnchorPrime` が強すぎて、一般 \(r\)-world を表現できない。
@@ -357,8 +621,15 @@ import DkMath.NumberTheory.PascalPrimeDial
 4. 既存 GN / gcd theorem の wrapper で済む範囲を超え、新規 gcd 理論が必要になる。
 5. Zsigmondy へ渡す前に anchor predicate が本線 import を汚染する。
 
+Additional current failure condition:
+
+6. `HasAnchorPrime r n` is mostly used with `n = q` for a prime witness and
+   collapses to `q = r`, making the predicate too narrow for support carriers.
+
 ## 9. 昇格条件
 
+Status: **[UPDATED]**
+
 次が満たされたら、実験ファイルから本線へ昇格する。
 
 ```text
@@ -376,6 +647,32 @@ three_not_dvd_S0_nat_of_not_dvd_sub
 GNBoundaryFreePrime.of_dvd_diff_not_dvd_boundary
 ```
 
+The old list mixes already-completed bridge targets with still-open vocabulary.
+The updated minimal build target should be:
+
+```text
+lake build DkMath.Petal.ReducedSupport
+```
+
+with no-sorry API:
+
+```lean
+HasNoPrimeBelow
+HasAnchorPrime
+hasAnchorPrime_prime
+hasAnchorPrime_anchor_dvd
+hasAnchorPrime_no_smaller_prime
+```
+
+Optional second checkpoint:
+
+```lean
+AnchoredCarrier
+AnchoredGNCarrier
+anchoredGNCarrier_anchor
+anchoredGNCarrier_dvd_GN
+```
+
 昇格先は次のいずれかとする。
 
 ```text
@@ -384,8 +681,18 @@ DkMath.Petal.GNPrimitive
 DkMath.Petal.Anchor
 ```
 
+Current preferred promotion order:
+
+```text
+1. DkMath.Petal.ReducedSupport
+2. DkMath.Petal.Anchor
+3. DkMath.Petal.GNPrimitive, only if needed
+```
+
 ## 10. 将来展望
 
+Status: **[UNCHANGED]**
+
 この実験が成功した場合、次の定理群へ進む。
 
 ```text
````
`````
