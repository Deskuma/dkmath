# review Phase "B"

## 1. 結論

うむ、Phase BF は **ratio-style toy route の concrete 実走完了** じゃ。

Phase BE で一般定理として、

$$
A(p)\ge 0,\qquad B(n) > 0,\qquad \sum_q A(p(q))\le B(n)
$$

から

$$
\mathrm{weightedHitMass}\le C
$$

へ進む `ratioBaseWeight_hitMass_le_const` ができた。今回 Phase BF では、それを sample に実際に適用し、

$$
A(2)=1,\quad A(p\ne2)=0,\qquad B(n)=1
$$

という具体的な ratio-style toy weight で、

$$
\mathrm{weightedHitMass}\le 1
$$

まで no-sorry で通した。build と no-sorry 検査も成功しておる。

これはかなり良い。
抽象 API が「動くはず」ではなく、 **実際に走る登山道** になった。

## 2. 今回の主役

今回追加された中心はこの流れじゃ。

```lean
sampleTenRatioA
sampleTenRatioB
sampleTenRatioA_nonneg
sampleTenRatioB_pos
sampleTenRatioBudget
sampleTenRatioWeightChannelProvider
sampleTenRatioWeightChannelProvider_channelProviderAt_subProbability
sampleTenRatioBaseWeight_hitMass_le_one
```

数学的には、

$$
A(p)=
\begin{cases}
1 & p=2,\\
0 & p\ne2,
\end{cases}
\qquad
B(n)=1
$$

として、

$$
c(n,p)=\frac{A(p)}{B(n)}=A(p)
$$

を作ったわけじゃ。

sample kernel の状態 \(10\) では labels が

$$
{2,5}
$$

で、witness provider はそれぞれ base prime \(2,5\) を読む。したがって、

$$
A(2)+A(5)=1+0=1\le B(10)=1
$$

となり、budget 条件が閉じる。

状態 \(10\) 以外では index が空なので、総量は \(0\) 。
ゆえに全状態で sub-probability が成り立つ。

## 3. 何が前進したか

前段までの道はこうだった。

$$
\text{ratioBasePrimeWeight}\\
\to
\text{RatioBaseWeightBudget}\\
\to
\text{BaseWeightSubProbability}\\
\to
\text{ratioBaseWeight\_hitMass\_le\_const}
$$

今回、これを concrete sample で通した。

つまり、

$$
\text{具体的な }A,B
$$

$$
\Downarrow
$$

$$
\text{budget}
$$

$$
\Downarrow
$$

$$
\text{PrimePowerChannelProvider}
$$

$$
\Downarrow
$$

$$
\mathrm{weightedHitMass}\le 1
$$

まで到達した。

これは、手定義 toy weight route、witness-provider weight route に続く、第3の concrete route と見てよい。

## 4. 手定義 weight から ratio-style weight への昇格

以前の sample は、直接

$$
w(10,2)=1,\qquad w(10,5)=0
$$

を定義していた。

その後、witness-provider route により、

$$
w(n,q)=c(n,p(q))
$$

として説明できるようになった。

今回さらに、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

という ratio-style に昇格した。

つまり同じ sample weight が、次のように段階的に意味を増してきた。

$$
\text{手定義 weight}
$$

$$
\to
\text{base prime 依存 weight}
$$

$$
\to
\text{ratio-style weight }A(p)/B(n)
$$

これはとても良い登り方じゃ。
いきなり \(\log p/\log n\) へ飛ばず、有理 toy model で構造だけを先に固めておる。

## 5. Lean 的にも良い仕上がり

`sampleTenRatioBudget` で一度 `simp` の unused args 警告が出て、それを整理して警告なしにしたのも良い。

この段階では、証明が通るだけでなく、後で読む proof が荒れていないことが大事じゃ。
特にこのファイルはすでに Phase が長く積み上がっておるので、不要な unfold や unused simp 引数を減らすのは、後続の保守性に効く。

## 6. 現在地

ここまでの ratio-style route はこうじゃ。

| 層                                  | 状態   |
| ---------------------------------- | ---- |
| `ratioBasePrimeWeight`             | 完了   |
| ratio-style 非負性                    | 完了   |
| `RatioBaseWeightBudget`            | 完了   |
| budget → sub-probability           | 完了   |
| ratio-style → hit mass bound alias | 完了   |
| concrete ratio-style sample        | 今回完了 |
| ratio-style route 小まとめ             | 未    |
| 実数/log route 設計                    | 未    |
| \(\Lambda(q)/\log n\) 本格接続           | 未    |

つまり、有理 toy model としての ratio-style route は一段落しておる。

## 7. 次の一手

次は History にもある通り、Phase BG として **ratio-style toy route の小まとめ / 整理** が自然じゃ。

ここまでで定理群がかなり増えたので、いきなり実数 \(\log\) に進むより、まずは導線を再確認した方がよい。

わっちなら Phase BG では、新しい大定理を足すより、次のような alias / section コメント / docstring の整理をする。

```lean
-- ratio-style route:
-- A(p) / B(n)
-- nonneg + positive denominator
-- budget
-- sub-probability
-- hit mass bound
```

さらに、定理名としてはすでに十分だが、もし追加するなら、

```lean
sampleTenRatioBaseWeightChannelProvider_channelProviderAt_subProbability
sampleTenRatioBaseWeight_route_summary
```

のような summary theorem は検討してもよい。

ただ、無理に theorem を増やさず、doc 側で小まとめを書くのも賢い。

## 8. その次の山影

Phase BG の後は、いよいよ二択じゃ。

一つ目は、まだ有理 toy model のまま、別の \(A,B\) 例を増やす道。

二つ目は、doc 側で実数/log route の設計を起こす道。

わっちの推奨は、まず doc 側で設計じゃ。

なぜなら Lean にいきなり

$$
A(p)=\log p,\qquad B(n)=\log n
$$

を入れると、`Real.log`、正値性、単調性、自然数から実数への coercion、除算、有限和、そして将来の漸近評価が絡み、一気に重くなるからじゃ。

今はまず、

$$
A(p)\sim \log p,\qquad B(n)\sim \log n
$$

をどの層で扱うか、設計書に分けた方がよい。

## 9. 総括

Phase BF は、ratio-style toy model の **実走成功** じゃ。

これで、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

という形の weight が、

$$
\text{非負性}
\to
\text{budget}
\to
\text{sub-probability}
\to
\mathrm{weightedHitMass}\le 1
$$

まで sample で通った。

山で言えば、比率表 \(A(p)/B(n)\) を持った登山料モデルが、実際の登山口を通り、予算内に収まり、Big の外へ飛び出さないことが確認された。

ここは良い区切りじゃ。
次は一度、Phase BG として小まとめを張る。そこから先、いよいよ \(\log p/\log n\) の雪稜をどう登るか、設計を描く段階じゃな。
