# No Square on S0 Work Notes

status: 作業中 - phase-09:

## Index

※以前の作業は以下、アーカイブログへ移しました。

[NoSqOnS0: phase-01](NoSqOnS0-WorkNotes-phase-01.md)
[NoSqOnS0: phase-02](NoSqOnS0-WorkNotes-phase-02.md)
[NoSqOnS0: phase-03](NoSqOnS0-WorkNotes-phase-03.md)
[NoSqOnS0: phase-04](NoSqOnS0-WorkNotes-phase-04.md)
[NoSqOnS0: phase-05](NoSqOnS0-WorkNotes-phase-05.md)
[NoSqOnS0: phase-06](NoSqOnS0-WorkNotes-phase-06.md)
[NoSqOnS0: phase-07](NoSqOnS0-WorkNotes-phase-07.md)
[NoSqOnS0: phase-08](NoSqOnS0-WorkNotes-phase-08.md)

## 課題

- [x] なし

## 状況タスク

phase-09

## 実装方針

評価！レビューしてもらった。

===

うむ！これは **詰め** どころか、かなり “封鎖線” が出来てきたのう。貼ってくれた追加分、構造としてめちゃくちゃ良い。ポイントを短く、しかし鋭く診断するぞえ。

## 1. いま何が達成されたか

### 1.1. 「補集合の判定器」を実装しておる

`by_cases hNoSq : NoSqOnS0 c b` を置いて、

- `hNoSq` が真なら従来ルートで FLT を返す
- `hNoSq` が偽なら、
  `¬NoSq → ∃q (q^2|S0)` を作り、
  それを `q=3` と `q≠3` に割り、
  `q≠3` は `SupportExceptThree + NonLiftable` で潰し、
  結局 `3^2|S0` を引きずり出して、
  `mod3 separated` で `¬ 3|S0` を出して矛盾

この流れが `NoSqOnS0_of_support_nonLiftable_mod3_separated` にまとまっており、**補集合を A 側へ押し戻す** 形に成功しておる。
つまり “別判定器が必要” という話は、少なくともこの入力セットの範囲では **かなり縮んだ**。

## 2. 最高に良いところ（設計として勝ってる）

### 2.1. `not_NoSqOnS0_iff_exists_sq_factor` が核

これがあると「NoSq が壊れる」という情報が、具体的な反例 (q) に落ちる。補集合の地図が描ける。偉い。

### 2.2. “q=3 のみが生き残る” を Lean で定理化した

`three_sq_dvd_of_not_NoSqOnS0_of_support_nonLiftable` がまさにそれ。
これは、後で例外処理や最終合流を書く時の **要石** になる。

### 2.3. 入口の “入力構造体” `NoSqInput`

これ、実務的に強い。仮定を散らさず “束” に閉じ込めたので、後から

- `NoSqInput` を生成する補題
- `NoSqInput` を弱めた `NoSqInputLite`

などの拡張がやりやすくなる。

## 3. ただし、ここに1つ “論理のほつれ” がある（重要）

お主の `NoSqInput` に

```lean
hNoSq : NoSqOnS0 c b
```

が入っておるのに、最後で

```lean
by_cases hNoSq : NoSqOnS0 c b
```

と分岐しておる。

この分岐は **`hIn.hNoSq` がある時点で片側が決まってしまう**。つまり、

- `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqInput` は実質、常に “真側” を通る
- 偽側（補集合処理）は、この `NoSqInput` からは **到達不能**

これは「間違い」ではない。だが、設計目的が

> 「NoSq が成り立たないケースも別ルートで総なめしたい」

なら、入力構造体の設計が少しズレておる。

### 3.1. 解決策（最短・綺麗）

`NoSqInput` を 2 段に分けるのが良い。

- `BaseInput c b`：`hbc` `coprime` `hc_nz` `hb_nz` `hsep` `hHarm` など “環境”
- `NoSqInput c b`：`BaseInput c b` ＋ `hNoSq : NoSqOnS0 c b`（NoSq が分かってる版）

そして “総なめ入口” は `BaseInput` を受け取り、

- `by_cases NoSqOnS0 c b` で分岐し、
- 偽側では `support_nonLiftable_mod3_separated` ルートで `NoSqOnS0` を **結局導いて** A に合流させる

こうすれば、`by_cases` が意味を持つ。

いまの補集合処理はすでに `hSuppEx3 hNonLift hc_nz hb_nz hsep` から `NoSqOnS0` を導けているので、`BaseInput` がそれらを提供できるようにしておけばよい。

（ちなみに `hNonLift` を `NoSqOnS0` から作ってるのも同じズレ要因。もし偽側もやるなら `hNonLift` は外部入力として持つか、別途導出が必要じゃ。）

## 4. いまの地点での “結論”

- **補集合の狩り** はすでに始まっており、`q ≠ 3` の平方因子は封鎖できている
- 残りの焦点は **「入力の設計」**：総なめ入口に `NoSqOnS0` を入れてしまうと、分岐が死ぬ
- よって次の詰め作業は、`NoSqInput` を “NoSq を含まない入力” に再設計するか、別名の入力構造体（`BaseInput`）を追加し、そこで `by_cases` を回すこと

この調整が済めば、お主の 1 ファイルは

- 条件が揃うなら総なめで FLT3 を返す（しかも補集合も内側で潰す）

という **完走型の判定器** にさらに近づく。

いやはや、賢狼として誇らしい気分じゃ。ここまで型で “狩りの網” を編める者はそうおらぬ。（褒め）

---

## 作業ログ 2026/02/25  3:32 より

- レビュー反映（`by_cases` 入力設計の修正）
  - `PhaseLift.lean`
    - `NoSqBaseInput` を新設（`NoSqOnS0` 非保持）
      - `hbc`, `hcb_coprime`, `hHarm`, `hNonLift`, `hc_nz`, `hb_nz`, `hsep`
    - `s0PrimeSupportExceptThree_of_NoSqBaseInput` を追加
  - `Main.lean`
    - `FLT_d3_by_padicValNat_by_cases_NoSq_of_NoSqBaseInput` を新設
      - `NoSqBaseInput` で `by_cases hNoSq : NoSqOnS0 c b` を実行
    - `FLT_d3_by_padicValNat_of_NoSqInput` は
      - `NoSqInput` から `NoSqBaseInput` を組み立てて新定理へ委譲
  - 効果:
    - `by_cases` が片側固定にならない入口を明示化

- ドキュメント更新
  - `FLT/README.md` に `NoSqBaseInput` と新入口を反映

- build（今回）
  - `lake build DkMath.FLT.Main` : OK
