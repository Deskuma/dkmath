# 対応状況

PR: <https://github.com/Deskuma/dkmath/pull/53>

## 対応済み

### discussion_r3085207779

- [r3085207779](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085207779)

はい。今回の指摘 `discussion_r3085207779` については、ローカルで確認して修正まで入れました。

修正内容は、[`ClassGroupBridge.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/ClassGroupBridge.lean) で `IsRegularPrime` が実際に `p` を使う placeholder になるよう細くし、`classGroupPTorsionFree_of_regularPrime` が regular-prime 仮定だけから現在の強い `CyclotomicClassGroupPTorsionFreeTarget` を導かない形に直したことです。あわせて [`RegularPrimeRoute.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/RegularPrimeRoute.lean) と [`Samples.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Samples.lean) も更新して、regular-prime route 側が明示的な class-group 仮定 `hCl` を受け取るように揃えました。

検証は `lake build DkMath.FLT.Kummer.ClassGroupBridge`、`lake build DkMath.FLT.Kummer.RegularPrimeRoute`、`lake build DkMath.FLT.Samples` で通しています。`DkMathTest.FLT.Kummer.RegularPrimeRouteNoSorry` も回しましたが、このターンでは完了ログを取り切れていません。

---

ご指摘どおりでした。`IsRegularPrime` が実際には `p` を使っておらず、しかも `CyclotomicClassGroupPTorsionFreeTarget` 相当の強い内容を regular-prime 仮定だけから流し込んでいたため、placeholder としても API が強すぎる状態になっていました。

この点を修正し、

- `IsRegularPrime (p : ℕ)` を少なくとも `a ^ p = 1 → a = 1` の形で `p` を使う placeholder に変更
- `classGroupPTorsionFree_of_regularPrime` は regular-prime 仮定だけから強い `CyclotomicClassGroupPTorsionFreeTarget` を導かない形に変更
- その結果として、`RegularPrimeRoute` 側は明示的な class-group 仮定 `hCl` を受け取るように整理

しました。

確認として、少なくとも以下はローカルでビルド通過しています。

- `lake build DkMath.FLT.Kummer.ClassGroupBridge`
- `lake build DkMath.FLT.Kummer.RegularPrimeRoute`
- `lake build DkMath.FLT.Samples`

ありがとうございました。

### discussion_r3085207725

- [r3085207725](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085207725)

結論だけ言うと、今は「`classGroupPTorsionFree_of_regularPrime` だけを `p` 一般化する段階」ではないです。
やるなら `target` 側から一段下までまとめて `p` を通す必要があります。

理由は明確で、いまの設計は

- [`IsRegularPrime`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/ClassGroupBridge.lean:96) だけは `p` を使う
- でも [`CyclotomicClassGroupPTorsionFreeTarget`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:4812) はまだ `∀ n`
- さらに [`CyclotomicPTorsionAnnihilationTarget`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/CyclotomicPrincipalization.lean:843) も `∀ n`

という形だからです。
この状態で comment 7725 のように theorem だけ

```lean
{p : ℕ} ... : ...
```

にして `h` をその `p` に適用しても、返り値側がまだ「その `p` の命題」になっていないので、設計としては中途半端です。

なので今の正しい整理は、今回やった通りです。

- `IsRegularPrime p` は少なくとも `p` を使う placeholder にする
- しかし regular-prime 仮定だけから、より強い `CyclotomicClassGroupPTorsionFreeTarget` は導かない
- そのため refined route では [`hCl`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/RegularPrimeRoute.lean:439) を明示で受ける

つまり、comment 7725 の「`p=5` 固定はおかしい」という指摘自体は正しいですが、直し方は「theorem の `p` 一般化」ではなく、「その bridge を薄くして overclaim をやめる」が先、という状況です。

本当に `p` を一般化するなら、次の refactor が要ります。

1. `CyclotomicClassGroupPTorsionFreeTarget` を `(...TargetAt p)` の形にする
2. `CyclotomicPTorsionAnnihilationTarget` も同様に `p` を持たせる
3. `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` など Stage 1b を全部それに合わせる
4. その上で初めて `classGroupPTorsionFree_of_regularPrime` を「その `p` の target」を返す theorem にする

なので、現状への答えは

- `IsRegularPrime` の `p` 一般化: もうやるべき段階
- route/theorem 単体の `p` 一般化: まだ早い
- target family ごとの `p` thread 化: 次の独立 refactor なら可能

です。

---

ご指摘の趣旨は理解しています。もともとの `@h 5 Nat.prime_five ...` は、theorem の見かけに対して `p = 5` を固定しており、`regular prime → class-group assumption` の橋としては不適切でした。

ただ、現時点では theorem 単体だけを `{p : ℕ}` で一般化しても十分ではありません。というのも、上流の `IsRegularPrime` は `p` を持てても、下流の `CyclotomicClassGroupPTorsionFreeTarget` / `CyclotomicPTorsionAnnihilationTarget` 側がまだ「任意の `n` に対する generic statement」という形のままで、`p` を thread する target family にはなっていないためです。この状態で theorem だけ `p`-parameterized にしても、返り値側の意味論が追いついていません。

そのため今回は、`p = 5` 固定の不正確な橋を残すのではなく、regular-prime 仮定だけから現在の強い `CyclotomicClassGroupPTorsionFreeTarget` を導くこと自体をやめ、refined route 側では class-group 仮定を明示入力として受ける形に整理しました。`p` を本当に一般化するなら、次の段階で `CyclotomicClassGroupPTorsionFreeTarget` などを含めて target 全体を `p` 付きに組み替える必要がある、という認識です。

### discussion r3085681656 〜 r3085681790

- [r3085681656](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085681656)
- [r3085681717](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085681717)
- [r3085681737](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085681737)
- [r3085681758](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085681758)
- [r3085681790](https://github.com/Deskuma/dkmath/pull/53#discussion_r3085681790)

## 2026-04-15 作業メモ

### `Basic.lean` の `z' < y` 分岐

- 対象: `lean/dk_math/DkMath/FLT/Kummer/Basic.lean`
- 指摘要旨: `z' < y` 分岐での反証が弱く、`simp at hz'` と `omega` では必要な矛盾が十分に示せていない。

対応:

- `descentExistence_exists_iff_gnReduction_exists` の `z' < y` 分岐を書き換えた。
- `p = 0` の退化ケースを先に切り分けたうえで、
  `y ^ p ≤ z' ^ p` は `hz'` から、
  `z' ^ p < y ^ p` は `Nat.pow_lt_pow_left` から得て、
  `not_le_of_gt` で矛盾を出す形へ変更した。

検証:

- `lake build DkMath.FLT.Kummer.Basic`

### `Core.lean` の no-op 仮定

- 対象: `lean/dk_math/DkMath/FLT/Core.lean`
- 指摘要旨: `let _ := hd` は no-op であり、読み手を混乱させる。

対応:

- `GN_eq_head_of_x_eq_zero` から `let _ := hd` を削除した。
- 未使用仮定として明確にするため、引数名を `hd` から `_hd` に変更した。

検証:

- `lake build DkMath.FLT.Core`

### `ClassGroupBridge.lean` の placeholder 名

- 対象: `lean/dk_math/DkMath/FLT/Kummer/ClassGroupBridge.lean`
- 指摘要旨: `IsRegularPrime` という名前は classical regular prime と読み違えやすく、placeholder 名として強すぎる。

対応:

- `IsRegularPrime` を `IsRegularPrimeReceiver` に改名した。
- 併せて [`RegularPrimeRoute.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/RegularPrimeRoute.lean) と [`Samples.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Samples.lean) の参照先も更新した。

検証:

- `lake build DkMath.FLT.Kummer.ClassGroupBridge`
- `lake build DkMath.FLT.Kummer.RegularPrimeRoute`
- `lake build DkMath.FLT.Samples`

### `ClassGroupBridge.lean` の universe `{0}` 指摘

- 対象: `lean/dk_math/DkMath/FLT/Kummer/ClassGroupBridge.lean`
- 指摘要旨: `universe u` が導入されているのに theorem 側で `.{0}` を hard-code している。

確認結果:

- `ClassGroupBridge` / `RegularPrimeRoute` / `Samples` だけでなく、
  下流の [`CyclotomicPrincipalization.lean`](($PROJECT_ROOT)/lean/dk_math/DkMath/FLT/Kummer/CyclotomicPrincipalization.lean) を含めて `.{u}` 化を試した。
- しかしこの route では theorem 本体が `CyclotomicField p ℚ` を concrete に選んでおり、
  `CyclotomicClassGroupPTorsionFreeTarget.{u}` に上げると
  `@CyclotomicField p ℚ` の箇所で universe mismatch が発生した。
- したがって、現状の設計では `.{0}` は単なる書き忘れではなく、
  concrete specialization に引きずられて残っている固定であることを確認した。

現時点の結論:

- この指摘は「その場で `.{u}` に直せる」種類ではない。
- 返信は、`CyclotomicField p ℚ` を使う route 全体の universe 設計を先に組み替える必要がある、という状況説明にする。
- 作業ツリー上は `.{u}` 化の試行を戻し、build が通る元の設計に復帰済み。

検証:

- `lake build DkMath.FLT.Kummer.CyclotomicPrincipalization DkMath.FLT.Kummer.ClassGroupBridge DkMath.FLT.Kummer.RegularPrimeRoute DkMath.FLT.Samples`

### `CoreBeamGap.lean` の `GN_eq_sum` 修飾

- 対象: `lean/dk_math/DkMath/CosmicFormula/CoreBeamGap.lean`
- 指摘要旨: `Defs.GN` 導入後、`GN_eq_sum` が import / open に依存して曖昧になりうる。

対応:

- `body_eq_core_add_beam` 内の
  `rw [GN_eq_sum]`
  を
  `rw [DkMath.CosmicFormulaBinom.GN_eq_sum]`
  に変更した。

検証:

- `lake build DkMath.CosmicFormula.CoreBeamGap`
