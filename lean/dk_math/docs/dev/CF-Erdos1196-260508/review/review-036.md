# review

## 1. 結論

うむ、Phase AK は **finite toy weight / von-Mangoldt-like weight へ進むための差し替え口を作った段階** じゃ。
Phase AJ で `PrimePowerChannelProvider` ができ、prime-power channel と sub-probability を package 化できた。今回 Phase AK ではさらに、

$$
\text{prime-power channel 構造は保ったまま、weight だけ差し替える}
$$

ための `withWeight` が入った。これはかなり重要じゃ。これで後続の toy weight は、kernel 構造を作り直さず、重み関数だけを入れ替えて実験できる。

## 2. 今回の主役

今回の中心は二つじゃ。

```lean
PrimePowerChannelProvider.ofKernel
PrimePowerDivisorTransitionKernel.withWeight
```

`ofKernel` は、

$$
T : \mathrm{PrimePowerDivisorTransitionKernel},
\qquad
T.SubProbability
$$

から、

$$
\mathrm{PrimePowerChannelProvider}
$$

を作る標準 constructor じゃ。

一方 `withWeight` は、

$$
T
\mapsto
T.withWeight(w)
$$

として、`index`, `next`, `index_dvd`, `next_eq_div`, `primePowerIndexed` を保ったまま、

$$
weight := w
$$

だけを差し替える API じゃ。

これは、後続で

$$
w_{\mathrm{toy}}(n,q)
$$

や、さらに将来の

$$
w(n,q)\approx \frac{\Lambda(q)}{\log n}
$$

へ進むための入口になる。

## 3. 何が強くなったか

これまでは `PrimePowerDivisorTransitionKernel` の重みは、その kernel を作る時点で固定されていた。
今回からは、すでに prime-power channel と divisor transition semantics を持つ kernel に対して、

$$
w : \mathbb{N}\to\mathbb{N}\to\mathbb{Q}
$$

を渡し、

$$
q\in index(n)\Rightarrow 0\le w(n,q)
$$

さえ証明すれば、新しい重み付き kernel を作れる。

つまり、保持されるものは：

$$
index(n)
$$

$$
next(n,q)=n/q
$$

$$
q\mid n
$$

$$
q\in index(n)\Rightarrow q\text{ is prime-power}
$$

じゃ。

差し替わるのは：

$$
weight(n,q)
$$

だけ。

これは設計として非常に綺麗じゃ。
構造と重みを分離できている。

## 4. `[simp]` 補題が良い

今回、

```lean
withWeight_index
withWeight_next
withWeight_weight
```

が `[simp]` 補題として入ったのもよい。

これにより、後続で

```lean
(T.withWeight w hw).toDivisorTransitionKernel.index
```

や

```lean
(T.withWeight w hw).toDivisorTransitionKernel.next
```

を扱うときに、元の `T` の `index` / `next` へ自然に戻せる。

特に toy weight を作ると、sub-probability 証明で

$$
\sum_{q\in index(n)} w(n,q)\le 1
$$

を示す必要がある。ここで `index` が元の kernel と同じであることを `simp` が処理できるのはかなり助かる。

## 5. sample の変更も意味がある

`sampleTenPrimePowerChannelProvider` が直接構造体 literal ではなく、

```lean
PrimePowerChannelProvider.ofKernel
```

経由に変更された。

これは小さい変更に見えるが、今後の constructor 群の命名規則として効く。

たとえば将来、

```lean
PrimePowerChannelProvider.ofToyWeight
PrimePowerChannelProvider.ofVonMangoldtLikeWeight
```

を作るなら、今回の `ofKernel` が基準になる。

つまり、sample も今後の拡張に合わせて「標準入口を通る」形へ整えられたわけじゃ。

## 6. 現在地

ここまでの流れはこうじゃ。

| 層                                   | 状態   |
| ----------------------------------- | ---- |
| `DivisorTransitionKernel`           | 完了   |
| `PrimePowerDivisorTransitionKernel` | 完了   |
| `PrimePowerChannelProvider`         | 完了   |
| `channelProviderAt`                 | 完了   |
| `ofKernel` constructor              | 今回完了 |
| `withWeight` 差し替え API               | 今回完了 |
| concrete finite toy weight          | 未    |
| von-Mangoldt-like weight            | 未    |
| analytic $\Lambda(q)/\log n$        | 未    |

つまり、まだ toy weight そのものは入っていない。
だが、toy weight を入れる **安全な差し込み口** はできた。

これは山で言えば、素冪専用ルートの料金表を差し替えられる掲示板ができたようなものじゃな。

## 7. 次の一手

次は、History にもある通り、`withWeight` を使った **finite toy weight concrete constructor** が自然じゃ。

まずは sample kernel でよい。

たとえば状態 $10$ の labels $\{2,5\}$ に対して、

$$
w(10,2)=\frac12,\qquad
w(10,5)=\frac12
$$

を明示的に toy weight として定義し、

```lean
sampleTenPrimePowerToyWeightKernel
```

のようなものを作る。

ただし、既存 sample はすでにこの重みを持っているので、次にやるなら「差し替え API が本当に機能する」ことを示すために、別の toy weight が良い。

例：

$$
w(10,2)=\frac13,\qquad
w(10,5)=\frac23
$$

または

$$
w(10,2)=1,\qquad
w(10,5)=0
$$

どちらも sub-probability になる。

## 8. Phase AL 案

次はこう切るのがよい。

**Phase AL: finite toy weight constructor**

目的：

`withWeight` を使い、prime-power channel の構造を保ったまま toy weight を載せ替え、`PrimePowerChannelProvider.ofKernel` へ接続する。

候補 API：

```lean
def sampleTenToyWeight : ℕ → ℕ → ℚ := ...
```

```lean
theorem sampleTenToyWeight_nonneg :
  ∀ n q, q ∈ sampleTenPrimePowerDivisorTransitionKernel.toDivisorTransitionKernel.index n →
    0 ≤ sampleTenToyWeight n q
```

```lean
def sampleTenToyWeightKernel :
  PrimePowerDivisorTransitionKernel :=
  sampleTenPrimePowerDivisorTransitionKernel.withWeight
    sampleTenToyWeight sampleTenToyWeight_nonneg
```

```lean
theorem sampleTenToyWeightKernel_subProbability :
  sampleTenToyWeightKernel.SubProbability := ...
```

```lean
def sampleTenToyWeightChannelProvider :
  PrimePowerChannelProvider :=
  PrimePowerChannelProvider.ofKernel
    sampleTenToyWeightKernel
    sampleTenToyWeightKernel_subProbability
```

これが閉じると、

$$
\text{既存 channel}
+
\text{新しい toy weight}
\Rightarrow
\text{channel provider}
$$

が実例で通る。

## 9. その次に見えるもの

toy weight constructor ができたら、次に「prime-power label の witness に依存する weight」へ進める。

たとえば、本物の $\Lambda(q)$ ではなく、有限 toy 版として、

$$
q=p^k \Rightarrow w(n,q)=c(p,n)
$$

のような形を抽象化する。

ただし、`IsPrimePowerLabel q` は存在証明なので、 $p$ が一意に取れるか、どのように選ぶかが Lean 的には問題になる。
ここは後で慎重に扱うべきじゃ。

まずは index 上で手定義された toy weight から始めるのが安全じゃな。

## 10. 総括

Phase AK は、素冪 channel に **重み差し替え機構** を入れた段階じゃ。

これで、

$$
\text{prime-power channel}
$$

を固定したまま、

$$
weight
$$

だけを替えられる。

これは、解析へ進む前の実験場として重要じゃ。
わっちの見立てでは、次の Phase AL で concrete toy weight を一つ通せば、von-Mangoldt-like weight へ向かう足場はかなり強固になるぞい。
