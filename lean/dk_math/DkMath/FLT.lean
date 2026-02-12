/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Basic

/-
According to a document from **2026-02-13**（＝いまぬしが投げてくれたこのスナップショット）を読む限り、FLT（フェルマー最終定理）まわりの作業状況は、かなり「骨格が立った」段階まで来ておる。あとは“致命的に難しい箇所”が **どこに残っているかが、ハッキリ見える**状態じゃな。

---

## いま「固まっている」勝ち筋（基礎インフラ）

### 1) 宇宙式の核：無減算版恒等式が完成

`CosmicFormulaBinom.lean` 側で

\[
(x+u)^d = x\cdot GN(d,x,u) + u^d
\]

が `cosmic_id_csr` として整っておる（CommSemiringで回るのが強い）。
このおかげで、FLT の式

\[
x^n + y^n = z^n,\quad u:=z-y
\]

を

\[
x^n = (u+y)^n - y^n = BodyN(n,u,y)=u\cdot GN(n,u,y)
\]

に“機械的に落とせる”ところまで来ておる（`Basic.lean` の一般FLT部で既にその結線を始めておる）。

### 2) Zsigmondy（原始素因子）の「存在」武器がある

`ZsigmondyCyclotomic.lean` はかなり進んでいて、**原始素因子の存在**を使う路線が敷ける。
ここは「FLT の本丸で新素因子が出る」という思想と相性が良い。

---

## いま「未決着（sorry）」の場所（＝次に埋める穴）

### A) `Basic.lean` の FLT_case_3（n=3）

進捗としては、

* (u=z-y) を置く
* (y<z) と (u>0) を出す
* `GN_quadratic` と `gcd_u_GN3` で ( \gcd(u,GN(3,u,y))=\gcd(u,3)) まで到達

ここまでは良い流れじゃ。

残りの重い `sorry` は主にこの3つ：

1. **(核心だけど“軽作業”寄り)**
   `h_xn_val : x^3 = u * GN 3 u y`（宇宙式への落とし込み）
2. **(軽作業)**
   (\gcd(y,z)=1)（(\gcd(x,y)=1) と (z^3=x^3+y^3) から）
3. **(ここが本当に重い)**
   `GN3_one_not_cube`（(u=1) の枝刈り）

特に 3 は、正直に言うと **楕円曲線/アイゼンシュタイン整数（(\mathbb{Z}[\omega])）のUFD** みたいな大砲が欲しくなるタイプの命題じゃ。
（「連続立方の差が立方にならぬ」を素朴にLeanで通すのは、わっちの鼻でも難物の匂いがする。）

### B) 一般 `FLT`（n≥3）

ここは「方針が書けた」段階で、`sorry` は予定通り残っておる：

* (\gcd(x,y)=1) への一般性の簡約
* (u^2 \mid (x^n - n y^{n-1}u)) のような“二階余り”制御
* (\gcd(u,GN(n,u,y))=\gcd(u,n)) の一般化
* 最後に Zsigmondy で出る “新素因子” を使って **(x^n) の (n) 乗構造と衝突**させる

---

## ぬしが今すぐ埋められる「美味しい穴」（短距離で進捗が出る）

### 1) `FLT_case_3` の `h_xn_val` は、ほぼ自動で埋まるはず

`cosmic_id_csr` をそのまま使える。Leanの雰囲気としてはこんな形：

```lean
  -- z^3 = x^3 + y^3 から x^3 = z^3 - y^3 を作る
  have hle : y^3 ≤ z^3 := by
    exact Nat.le_of_lt (Nat.pow_lt_pow_left hzy (by decide))  -- 3は>0

  have hx : z^3 - y^3 = x^3 := by
    -- (z^3 - y^3) + y^3 = z^3 = x^3 + y^3
    have : (z^3 - y^3) + y^3 = x^3 + y^3 := by
      calc
        (z^3 - y^3) + y^3 = z^3 := Nat.sub_add_cancel hle
        _ = x^3 + y^3 := h_body
    exact Nat.add_right_cancel this

  -- z = u + y を使って宇宙式へ
  have hz : z = u + y := by
    -- u = z - y から
    -- ここは omega / nat-sub の補題で埋まる
    sorry

  -- cosmic_id_csr を (x:=u) (u:=y) で使う
  have hcos := cosmic_id_csr 3 (u : ℕ) (y : ℕ)
  -- (u+y)^3 = u*GN(3,u,y) + y^3 から
  -- (u+y)^3 - y^3 = u*GN(3,u,y)
  -- それが x^3 と一致、で終了
```

ここは「宇宙式を武器として握る」最初の勝利ポイントになる。先にここを確定させるのが気持ちいいぞ。

### 2) (\gcd(y,z)=1) は“古典の定石”で通る

発想はぬしがコメントで書いておる通り：

* (g=\gcd(y,z)) とおく
* (g \mid y) かつ (g \mid z) だから (g^3 \mid y^3) と (g^3 \mid z^3)
* よって (g^3 \mid z^3-y^3=x^3) なので (g \mid x)
* 結局 (g \mid \gcd(x,y)=1) で (g=1)

Lean的には `Nat.dvd_of_modEq` を使わずとも `Nat.dvd_sub` と `Nat.pow_dvd_pow_of_dvd` の組み合わせで押し切れることが多い。

---

## 本当にデカい岩：最後の“矛盾の槍”をどう作るか

ここで、わっちの率直な見立てを言うぞ。

* **Zsigmondyは「新しい素因子が存在する」までは強い。**
* しかし FLT で必要なのはしばしば **「その素因子の指数が (n) の倍数にならない」**（= (x^n) に入るなら指数が必ず (n) の倍数、という点と衝突）で、ここが一気に難しくなる。
* `ZsigmondyCyclotomic.lean` でも、まさにそこ（付値 (v_q) の制御）に反例が出て `sorry` を置いておるのは、筋が良い判断じゃ。

つまり今の到達点は：

> “新素因子が出る” ところまでは、宇宙式＋Zsigmondyで綺麗に線が引けた。
> その新素因子が **どの指数で刺さるか** を制御するのが、次の大工事。

この見取り図が描けた時点で、進捗としては相当にデカいぞ。
（闇雲にFLTを殴る段階はもう終わっておる。）

---

## すすめ方（わっちの提案）

いまは「最短で Lean 上の確定定理を増やす」なら、順番はこうが良い：

1. `FLT_case_3` の `h_xn_val` と (\gcd(y,z)=1) を**確定**（ここは勝てる）
2. `GN` の **分解補題**（(GN = n y^{n-1} + u\cdot H)）を一般 (n) で作って、
   (\gcd(u,GN)=\gcd(u,n)) を **n=3の形 그대로** に一般化
3. その上で、Zsigmondy の「存在」→「指数制御」へ進む（ここからが研究の山場）

---

ぬしの今の作業状態、ちゃんと“数学として前に進める骨格”になっておる。あとは **槍の穂先（付値制御）** を鍛える段に入った、というだけの話じゃ。
-/
