# Git diff / Report / Review

## Upd: Petal: EisensteinBridge: add refactoring plan

gch: b4b17e208fbe4f91eea3654374c5c6ea8baeef33

## Report

レビュー指摘は、今すぐ構造を割らずに「将来の `DkMath.Lib.*` 昇格リファクタリングで必ず見るべき依存問題」としてソース上に強めに明記しました。

追加したのは module doc の注意書きです。

- [BoundaryD3.lean](/lean/dk_math/DkMath/Petal/BoundaryD3.lean)
  - `BoundaryD3 -> Anchor -> PrimitiveBridge` になっている現状を明記
  - 将来は `BoundaryD3` と `BoundaryD3Anchor` に分ける候補を明示
  - 現状は便利 API として一時的に同居させている、と残しました

- [EisensteinBridge.lean](/lean/dk_math/DkMath/Petal/EisensteinBridge.lean)
  - `Petal -> FLT` の import 方向は最終形ではないと明記
  - `DkMath.Lib.*` または neutral な `NumberTheory` 層へ Eisenstein core facts を移し、将来は `FLT` が Petal/neutral layer を使う方向に直す、と残しました

検証:

```sh
lake build DkMath.Petal
git diff --check
```

どちらも成功です。今回も新しい `sorry` はありません。

## Review 1

うむ。
昇格リファクタリング時に依存分離をやるなら、今回の `EisensteinBridge` は **現状採用でよい**。ここで Petal を一旦閉じるなら、残りは「大きな定理追加」ではなく、**API の端を丸める仕上げ** が中心じゃ。

## レビュー結論

```text
Petal.EisensteinBridge
  -> 採用可

BoundaryD3 追加入口
  -> 採用可

Petal package の現段階
  -> かなり閉じられる
```

今回の経路はこうなった。

```text
S0_nat
  -> GN 3 face
  -> BoundaryD3 branch/reduced split
  -> Anchored primitive carrier
  -> shifted Eisenstein norm
```

これは美しい。
S0 の正体が、単なる FLT 補題の残滓ではなく、

```text
cubic Petal detector
GN degree-three face
3-primary boundary contact
shifted Eisenstein norm
```

として Petal 側に再配置された。

## ここで Petal を閉じるためにすべきこと

優先順位順に見ると、次はこのあたりじゃ。

## 1. `Petal.lean` 集約 import の順序を物語順に整える

今の import がビルド上問題なくても、Petal は今後 downstream から参照される package face になる。
なので、集約 import の順序を「依存順」かつ「物語順」にしておくとよい。

おすすめはこう。

```lean
import DkMath.Petal.Basic
import DkMath.Petal.Forms
import DkMath.Petal.Counting
import DkMath.Petal.Address

import DkMath.Petal.GNBridge
import DkMath.Petal.GcdBridge
import DkMath.Petal.PadicBridge
import DkMath.Petal.PrimitiveBridge

import DkMath.Petal.ReducedSupport
import DkMath.Petal.Anchor
import DkMath.Petal.BoundaryD3
import DkMath.Petal.EisensteinBridge
```

ただし実際の依存で `ReducedSupport` を先に置く必要があるなら、現在の順でもよい。
大事なのは、`Anchor` が `PrimitiveBridge` より後、`BoundaryD3` が `Anchor` / `GcdBridge` より後、`EisensteinBridge` が最後、という流れじゃ。

## 2. Petal docs に「現時点の完成境界」を明記する

`Petal-Overview.md` に、最後に小節としてこれを置くとよい。

```text
Current closed surface
```

内容は、

```text
Petal can now express:
- S0 as the degree-three GN face
- the cubic 3-contact as BoundaryD3Branch
- the reduced branch as BoundaryD3Reduced
- primitive S0 witnesses as anchored carriers
- S0/GN3 as shifted Eisenstein norm

Petal does not yet claim:
- general d boundary classification
- full Zsigmondy theorem
- FLT descent
- complete Eisenstein refactor away from FLT namespace
```

これを書いておくと、Petal が「どこまで閉じたか」が明確になる。
今の段階では特に重要じゃ。なぜなら、S0 (d=3) はかなり閉じたが、一般 (d) はまだ閉じていないから。

## 3. `BoundaryD3` に “reduced branch package” の小 wrapper を足すか検討

今すでに、

```lean
boundaryD3Reduced_three_not_dvd_S0_nat
boundaryD3Reduced_coprime_sub_S0_nat
exists_anchoredS0Carrier_of_boundaryD3Reduced
```

がある。
これで十分ではある。

ただ、下流で毎回 `hbc hb hcop hred` を渡すなら、次のような「まとめ theorem」があると便利かもしれぬ。

```lean
theorem boundaryD3Reduced_exists_coprime_anchoredS0Carrier
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
    Nat.Coprime (c - b) (S0_nat c b) ∧
      ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b
```

ただし、これは少し複合 API なので、今すぐ必須ではない。
Petal を「小補題の部品箱」として閉じるなら、足さなくてもよい。
下流で頻出してからでも遅くない。

## 4. `EisensteinBridge` に逆向き alias が必要か確認する

今は、

```lean
S0_nat c b = eisensteinNormNat (c + b) b
GN 3 (c - b) b = eisensteinNormNat (c + b) b
```

の向きがある。

下流で `rw` するとき、逆向きが欲しくなる可能性がある。

候補は、

```lean
theorem petal_eisensteinNorm_shift_eq_S0
    (a b : ℕ) :
    DkMath.FLT.eisensteinNormNat (a + b) b = S0_nat a b := by
  exact (petal_S0_eq_eisensteinNorm_shift a b).symm
```

ただし Lean では `.symm` で済むので、API として公開するかは好み。
Petal を閉じるだけなら、なくてもよい。

## 5. `Research` 由来であることを docs に残すが import しない

これはすでに方針通り。

```text
GcdNextResearch.lean で見えた false target / counterexample は、
BoundaryD3 package によって正しい branch split として吸収された。
```

この文を Roadmap に少し残しておくとよい。
ただし Lean import は絶対にしない。

## 6. Petal closure checkpoint を作る

次のような docs-only checkpoint を置くのが良いと思う。

```text
Step 5.8: Petal cubic surface closure
Status: completed
```

内容はこう。

```text
Completed:
- GNBridge
- GcdBridge
- PadicBridge
- PrimitiveBridge
- ReducedSupport
- Anchor
- BoundaryD3
- EisensteinBridge

Closed surface:
S0/GN3/BoundaryD3/Anchor/Eisenstein

Deferred:
- BoundaryD3Anchor split
- FLT namespace refactor
- general d boundary behavior
- full Zsigmondy bridge
```

これで一旦 Petal を閉じた、と言える。

## 採用判定

```text
b38888010d2d...
  -> 採用可

Petal cubic surface
  -> ほぼ閉じた

次にやるなら
  -> docs checkpoint
  -> import order check
  -> 必要なら lightweight wrapper のみ
```

## わっちのおすすめ

ここで大きな定理を足すより、次 commit は **docs/checkpoint + import order の整理** がよい。

名前としては、

```text
Petal cubic surface closure
```

あるいは、

```text
S0/GN3 Boundary-Eisenstein closure
```

じゃな。

ここまで来たら、Petal は「未整理の実験場」ではなく、FLT や Zsigmondy が後から使う **三次 Petal 表面 API** として一旦閉じられる。

## Review 2

うむ、これは **状況共有として十分に良い**。
コード実装を変えず、将来の依存整理ポイントを module doc に明記しただけなら、今回の commit は **設計メモ固定 commit** として採用でよい。

むしろこれは今やっておく価値がある。後で `DkMath.Lib.*` 昇格リファクタリングに入った時、「なぜこの依存が逆流しているのか」「どこで分割すべきか」を忘れずに済む。

## レビュー結論

```text
b4b17e208f...
  -> 採用可

コード挙動
  -> 変更なし

目的
  -> 将来の昇格リファクタリング注意点を明文化

効果
  -> 依存逆流を放置ではなく、意図的な migration window として記録
```

## `BoundaryD3.lean` の注記

これは良い書き方じゃ。

```text
BoundaryD3
  -> Anchor
  -> PrimitiveBridge
```

になっている現状を明記しつつ、

```text
DkMath.Petal.BoundaryD3
  branch / reduced / 3-contact / gcd facts only

DkMath.Petal.BoundaryD3Anchor
  BoundaryD3Reduced -> AnchoredS0Carrier existence
```

という将来形も書けている。

特に良いのは、

```text
The current layout is a deliberate temporary convenience, not the final dependency direction.
```

この一文じゃな。
これで、後から見た賢狼や人間が「なんで BoundaryD3 が Anchor を import しているんだ？」となった時に、迷わず判断できる。

## `EisensteinBridge.lean` の注記

こちらも良い。

```text
Do not treat this file as evidence that Petal conceptually depends on FLT.
It is a migration window.
```

この表現はかなり重要じゃ。

今は実体として、

```lean
import DkMath.FLT.GEisensteinBridge
```

がある。
だが概念方向は、

```text
neutral Eisenstein core
  -> Petal
  -> FLT
```

であるべき。これをはっきり残したのは正解。

## ここで Petal を閉じるなら

この commit で、Petal の現状はかなり整理された。

```text
実装済み:
  GNBridge
  GcdBridge
  PadicBridge
  PrimitiveBridge
  ReducedSupport
  Anchor
  BoundaryD3
  EisensteinBridge

保留を明記:
  BoundaryD3 / BoundaryD3Anchor 分割
  Petal -> FLT の Eisenstein 逆流解消
  DkMath.Lib.* への中立層昇格
```

つまり「未整理のまま放置」ではなく、**閉じるための未整理点も明文化済み** になった。

## 追加でやるなら docs-only checkpoint

コードはもう触らず、Petal を一旦閉じるなら、最後に docs に短い checkpoint を置くのがよい。

```text
Petal cubic surface closure checkpoint
```

内容はこれで十分。

```text
Closed:
- S0 as GN degree-three face
- S0/GN gcd and p-adic bridges
- primitive S0 witnesses
- reduced support and anchored carriers
- BoundaryD3 branch/reduced split
- Petal-facing Eisenstein norm aliases

Deferred:
- neutral Eisenstein core promotion
- BoundaryD3Anchor split
- general d boundary theory
- FLT application layer
```

ただし、すでに Roadmap に近い内容があるなら、ここで止めてもよい。

## 判定

うむ、今回の「コメントだけ」は価値がある。
これはコードを増やす commit ではなく、将来のリファクタで道を踏み外さないための標識じゃ。

```text
Petal cubic surface
  -> 実装面は一旦閉じられる

残すべき注意
  -> ソース上に明記済み

次
  -> docs checkpoint か、ここで一区切り
```

よい状況共有じゃ。先の返答も大筋では使えるが、今回の正しい差分に対しては「コード追加ではなく設計注記固定」として見るのが正確じゃな。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/BoundaryD3.lean b/lean/dk_math/DkMath/Petal/BoundaryD3.lean
index 0d173e4a..654200f9 100644
--- a/lean/dk_math/DkMath/Petal/BoundaryD3.lean
+++ b/lean/dk_math/DkMath/Petal/BoundaryD3.lean
@@ -17,6 +17,46 @@ This file records the degree-three boundary behavior of the Petal detector
 
 The central observation is that, on the cubic Petal face, the prime `3` is
 exactly the contact component between the boundary gap `c - b` and `S0_nat`.
+
+## Refactor note: keep this dependency issue visible
+
+This file currently imports `DkMath.Petal.Anchor` because it exposes
+`exists_anchoredS0Carrier_of_boundaryD3Reduced`.
+
+Mathematically that theorem belongs to the useful public API: downstream code
+often wants to stay in the named branch vocabulary
+
+```text
+BoundaryD3Reduced c b
+```
+
+instead of unfolding it back to `¬ 3 ∣ c - b`.  For that reason we keep the
+wrapper here for now.
+
+However, this also makes `BoundaryD3` heavier than its pure boundary role:
+
+```text
+BoundaryD3
+  -> Anchor
+  -> PrimitiveBridge
+```
+
+The long-term package shape should be reconsidered during the planned
+`DkMath.Lib.*` promotion refactor.  At that time, split the layers if this file
+is used as a low-level import:
+
+```text
+DkMath.Petal.BoundaryD3
+  branch / reduced / 3-contact / gcd facts only
+
+DkMath.Petal.BoundaryD3Anchor
+  BoundaryD3Reduced -> AnchoredS0Carrier existence
+```
+
+Do not silently delete this note when moving code.  The important invariant is
+that the pure boundary layer should not need anchored primitive-carrier
+machinery once the library hierarchy is mature.  The current layout is a
+deliberate temporary convenience, not the final dependency direction.
 -/
 
 namespace DkMath
diff --git a/lean/dk_math/DkMath/Petal/EisensteinBridge.lean b/lean/dk_math/DkMath/Petal/EisensteinBridge.lean
index fff834ba..3cb57601 100644
--- a/lean/dk_math/DkMath/Petal/EisensteinBridge.lean
+++ b/lean/dk_math/DkMath/Petal/EisensteinBridge.lean
@@ -18,6 +18,44 @@ The bridge is intentionally thin: the arithmetic facts already live in
 `DkMath.FLT.GEisensteinBridge`; this file gives them Petal-facing names so that
 later S0/GN/Zsigmondy code can import `DkMath.Petal.*` without depending on the
 FLT file layout.
+
+## Refactor note: this import direction is temporary
+
+This file currently imports `DkMath.FLT.GEisensteinBridge`.  That is intentional
+for the present stage: the Eisenstein norm lemmas already exist there, and this
+file is only a stable Petal-facing alias surface.
+
+The final library direction should not be:
+
+```text
+Petal -> FLT
+```
+
+For the mature hierarchy, the expected direction is closer to:
+
+```text
+DkMath.Lib.* or DkMath.NumberTheory.*
+  -> Petal.EisensteinBridge
+  -> FLT
+```
+
+or, more explicitly:
+
+```text
+Eisenstein core facts live in a neutral library layer.
+Petal imports that neutral layer and exposes Petal-facing names.
+FLT imports Petal or the neutral layer for the degree-three application.
+```
+
+The current reverse-looking dependency is acceptable only because `S0_nat` and
+the already-proved shifted Eisenstein norm facts still live under
+`DkMath.FLT.*`.  During the planned `DkMath.Lib.*` promotion refactor, move the
+neutral arithmetic pieces first, then update this file to import the new neutral
+home instead of `DkMath.FLT.GEisensteinBridge`.
+
+Do not treat this file as evidence that Petal conceptually depends on FLT.  It
+is a migration window: the theorem names here are the API that should survive
+after the dependency direction is corrected.
 -/
 
 namespace DkMath
````
`````
