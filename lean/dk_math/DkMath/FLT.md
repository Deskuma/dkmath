# FLT - Fermat's Last Theorem

## 進捗状況

According to a document from **2026-02-13**
（＝いまぬしが投げてくれたこのスナップショット）
を読む限り、FLT（フェルマー最終定理）まわりの作業状況は、
かなり「骨格が立った」段階まで来ておる。

あとは“致命的に難しい箇所”が **どこに残っているかが、ハッキリ見える** 状態じゃな。

---

## いま「固まっている」勝ち筋（基礎インフラ）

### 1. 宇宙式の核：無減算版恒等式が完成

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
x^n = (u+y)^n - y^n = \mathrm{BodyN}(n,u,y)=u\cdot G_\N(n,u,y)
\]

に“機械的に落とせる”ところまで来ておる（`Basic.lean` の一般FLT部で既にその結線を始めておる）。

### 2. Zsigmondy（原始素因子）の「存在」武器がある

`ZsigmondyCyclotomic.lean` はかなり進んでいて、**原始素因子の存在**を使う路線が敷ける。
ここは「FLT の本丸で新素因子が出る」という思想と相性が良い。

---

## いま「未決着（sorry）」の場所（＝次に埋める穴）

### A. `Basic.lean` の FLT_case_3（n=3）

進捗としては、

* \(u=z-y\) を置く
* \(y < z\) と \(u > 0\) を出す
* `GN_quadratic` と `gcd_u_GN3` で \( \gcd(u,GN(3,u,y))=\gcd(u,3)\) まで到達

ここまでは良い流れじゃ。

残りの重い `sorry` は主にこの3つ：

1. **(核心だけど“軽作業”寄り)**
   `h_xn_val : x ^ 3 = u * GN 3 u y`（宇宙式への落とし込み）
2. **(軽作業)**
   \(\gcd(y,z)=1\)（\(\gcd(x,y)=1\) と \(z^3=x^3+y^3\) から）
3. **(ここが本当に重い)**
   `GN3_one_not_cube`（\(u=1\) の枝刈り）

特に 3 は、正直に言うと **楕円曲線/アイゼンシュタイン整数（\(\mathbb{Z}[\omega]\)）のUFD** みたいな大砲が欲しくなるタイプの命題じゃ。
（「連続立方の差が立方にならぬ」を素朴にLeanで通すのは、わっちの鼻でも難物の匂いがする。）

### B. 一般 `FLT`（n≥3）

ここは「方針が書けた」段階で、`sorry` は予定通り残っておる：

* \(\gcd(x,y)=1\) への一般性の簡約
* \(u^2 \mid (x^n - n y^{n-1}u)\) のような“二階余り”制御
* \(\gcd(u,GN(n,u,y))=\gcd(u,n)\) の一般化
* 最後に Zsigmondy で出る “新素因子” を使って **\(x^n\) の \(n\) 乗構造と衝突** させる

---

## ぬしが今すぐ埋められる「美味しい穴」（短距離で進捗が出る）

### 1. `FLT_case_3` の `h_xn_val` は、ほぼ自動で埋まるはず（済み✅️）

`cosmic_id_csr` をそのまま使える。Leanの雰囲気としてはこんな形：

提案コード:

```lean
  -- z^3 = x^3 + y^3 から x^3 = z^3 - y^3 を作る
  have hle : y^3 ≤ z^3 := by
    exact Nat.le_of_lt (Nat.pow_lt_pow_left hzy (by decide))  -- 3は > 0

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

実装コード: 2026/02/13 20:09 checked ✅️

```lean
/-- 補題: $d=3$ の場合、$GN$ は二次形式である -/
lemma GN_quadratic (u y : ℕ) : GN 3 u y = u ^ 2 + 3 * u * y + 3 * y ^ 2 := by
  unfold GN
  simp [Finset.sum_range_succ]
  ring
```

```lean
  -- 2. x^3 = u * GN 3 u y
  have h_xn_val : x ^ 3 = u * GN 3 u y := by
    rw [GN_quadratic]
    have hz : z = u + y := (Nat.sub_add_cancel hzy.le).symm
    zify at hz h_body ⊢
    rw [hz] at h_body
    rw [← add_left_cancel_iff (a := (y : ℤ) ^ 3)]
    rw [add_comm, ← h_body]
    ring
```

ここは「宇宙式を武器として握る」最初の勝利ポイントになる。先にここを確定させるのが気持ちいいぞ。

### 2. \(\gcd(y,z)=1\) は“古典の定石”で通る（済み✅️）

発想はぬしがコメントで書いておる通り：

* \(g=\gcd(y,z)\) とおく
* \(g \mid y\) かつ \(g \mid z\) だから \(g^3 \mid y^3\) と \(g^3 \mid z^3\)
* よって \(g^3 \mid z^3 - y^3 = x^3\) なので \(g \mid x\)
* 結局 \(g \mid \gcd(x,y) = 1\) で \(g=1\)

Lean的には `Nat.dvd_of_modEq` を使わずとも `Nat.dvd_sub` と `Nat.pow_dvd_pow_of_dvd` の組み合わせで押し切れることが多い。

---

## ✅ 修正を適用しました（コンパイル確認済み）

```lean
  -- 一般の y, u については、GN(n, u, y) が新しい素因数（Zsigmondy 原始素因子）を
  -- 持つことを利用して、$x^n$ の $n$ 乗構造と矛盾することを示すのが本筋じゃな。

  have h_gcd_u_y : Nat.gcd u y = 1 := by
    -- g = gcd(y, z) とおく。g | y, g | z ならば g^n | y^n, z^n → g^n | x^n → g | x
    let g := Nat.gcd y z
    have hg_y : g ∣ y := Nat.gcd_dvd_left y z
    have hg_z : g ∣ z := Nat.gcd_dvd_right y z
    have hg_y_pow : g ^ n ∣ y ^ n := pow_dvd_pow_of_dvd hg_y n
    have hg_z_pow : g ^ n ∣ z ^ n := pow_dvd_pow_of_dvd hg_z n
    have hg_x_pow : g ^ n ∣ x ^ n := by
      have : z ^ n - y ^ n = x ^ n := by
        rw [← hxy]
        simp
      rw [← this]
      exact Nat.dvd_sub hg_z_pow hg_y_pow
    have n_ne_zero : n ≠ 0 := by
      intro heq
      have : 3 ≤ 0 := by rwa [heq] at hn
      linarith
    have hg_x : g ∣ x := (Nat.pow_dvd_pow_iff n_ne_zero).mp hg_x_pow
    have hd : g ∣ Nat.gcd x y := Nat.dvd_gcd hg_x hg_y
    -- gcd(x,y) = 1 を仮定しているので g = 1
    have hg_one : g = 1 := by rw [h_coprime] at hd; exact Nat.eq_one_of_dvd_one hd
    -- よって gcd(y,z)=1, さらに u = z - y より gcd(u,y)=1
    have h_gcd_yz : Nat.gcd y z = 1 := by simpa [g] using hg_one
    have h_gcd_u_y : Nat.gcd u y = 1 := by
      have h1 : Nat.gcd z y = 1 := by
        have : Nat.gcd y z = 1 := by simpa [g] using hg_one
        rwa [Nat.gcd_comm] at this
      have h_eq : u.gcd y = z.gcd y := by
        dsimp [u]
        have step := Nat.gcd_sub_self_right hzy.le
        calc
          (z - y).gcd y = y.gcd (z - y) := by rw [Nat.gcd_comm]
          _ = y.gcd z := by rw [step]
          _ = z.gcd y := by rw [Nat.gcd_comm]
      rw [h_eq]
      exact h1
    exact h_gcd_u_y
```

変更点（要点）

* `theorem FLT` に `h_coprime : Nat.gcd x y = 1` を追加（一般証明で必要だったため）。
* 一般版 `FLT` 内の証明を修正：
  * `g := gcd(y,z)` による古典的な議論で、g^n | x^n → g | x を正しく導出して `g = 1` とするように改めた。
  * `Nat.pow_dvd_pow_iff` の前提（n ≠ 0）を明示的に証明して渡すようにした。
  * `gcd(u,y)=1` の導出を定義・順序を整え、Lean の書き方に合わせて安定化。
* 不要／間違った n=3 固有の依存（h_body を 3 に固定して使う等）を除去。
* すべての編集後に `lake build` を実行し、`DkMath.FLT.Basic` のビルドは成功（ただしファイル内に残る未完 `sorry` は警告として残存）。

主なファイル変更

* Basic.lean
  * `theorem FLT` の仮定に `h_coprime` を追加
  * `gcd` 関連の証明ブロックを安全に書き直し

なぜ直したか（短く）

* 元の一般版 `FLT` で h_coprime が無いのにその仮定を使っていた（未定義識別子の原因）。
* n に依存する（3 固有の）推論を一般 n に誤って適用していた。
* Lean 側の補題（例：pow_dvd_pow_iff, gcd_sub_self_right）の前提／形に合わせて補助証明を補った。

次にやれること（提案）

1. （推奨）`theorem FLT` を「任意の解は既約化して議論可能」という形で自動的に原始解へ還元する補題を追加して、外部呼び出し側が `h_coprime` を与えなくても良くする。💡
2. `sorry` の残り箇所（未完の補題）を順次完成して完全証明にする。🔧

ビルド結果（要約）

* lake build 実行 — `DkMath.FLT.Basic` ビルド成功（未完の `sorry` 警告は残存）

---

もしよければ、わっちが次にやること：

1. ぬしが望むなら `theorem FLT` からの「原始化（gcd を取り除く）」を自動化して `h_coprime` を不要にする改修を行うかの？
2. 残っている `sorry` を順に潰して完全化していくかの？

どちらに進めるか、ぬしの意向を教えてくりゃれ。

---

## 本当にデカい岩：最後の“矛盾の槍”をどう作るか

ここで、わっちの率直な見立てを言うぞ。

* **Zsigmondyは「新しい素因子が存在する」までは強い。**
* しかし FLT で必要なのはしばしば **「その素因子の指数が \(n\) の倍数にならない」**（= \(x^n\) に入るなら指数が必ず \(n\) の倍数、という点と衝突）で、ここが一気に難しくなる。
* `ZsigmondyCyclotomic.lean` でも、まさにそこ（付値 \(v_q\) の制御）に反例が出て `sorry` を置いておるのは、筋が良い判断じゃ。

つまり今の到達点は：

> “新素因子が出る” ところまでは、宇宙式＋Zsigmondyで綺麗に線が引けた。
> その新素因子が **どの指数で刺さるか** を制御するのが、次の大工事。

この見取り図が描けた時点で、進捗としては相当にデカいぞ。
（闇雲にFLTを殴る段階はもう終わっておる。）

---

## すすめ方（わっちの提案）

いまは「最短で Lean 上の確定定理を増やす」なら、順番はこうが良い：

1. `FLT_case_3` の `h_xn_val` と \(\gcd(y,z)=1\) を**確定**（ここは勝てる）
2. `GN` の **分解補題**（\(GN = n y^{n-1} + u\cdot H\)）を一般 \(n\) で作って、
   \(\gcd(u,GN)=\gcd(u,n)\) を **n=3の形そのまま** に一般化
3. その上で、Zsigmondy の「存在」→「指数制御」へ進む（ここからが研究の山場）

---

ぬしの今の作業状態、ちゃんと“数学として前に進める骨格”になっておる。あとは **槍の穂先（付値制御）** を鍛える段に入った、というだけの話じゃ。
