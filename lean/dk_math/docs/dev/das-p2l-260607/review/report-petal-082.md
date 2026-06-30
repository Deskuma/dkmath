# Git diff / Report / Review

No.082 cp

## Upd: Collatz.PetalBridge

Date: 2026/06/30 06:13 JST

## Report

`DkMath.Collatz.PetalBridge` の height occupation layer を、Collatz 固有の
`height >= 1` 事実へ接続しました。

今回の本線実装:

```lean
orbitWindowHeight_one_le
orbitWindowHeightCountGe_one_eq_window
orbitWindowHeightSeq_sum_ge_window_add_countGe_two
orbitWindowHeightPrefixCountGe_one_eq
orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
```

追加の分布 API:

```lean
orbitWindowHeightCountGe_antitone
```

おまけ実験:

```lean
orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
```

`Collatz-PetalBridge-Status.md` も更新し、二層から三層への進展と、
`DkMath.ABC.LayerCakeBasic` との住み分けを維持したまま local Nat count
layer-cake として進める方針を記録しました。

確認:

```bash
lake build DkMath.Collatz.PetalBridge
```

成功。既存の
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6: declaration uses sorry`
警告のみ再表示。

## Result

今回の中心はこれです。

```lean
theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two
    (n : OddNat) (k : ℕ) :
    k + orbitWindowHeightCountGe n k 2 ≤ sumS n k
```

意味:

```text
全 accelerated odd step で最低 1 個の 2 を剥がす。
height >= 2 の step では、さらに 1 個の 2 を剥がす。
したがって k + CountGe 2 が sumS の下界になる。
```

これは前回の

```text
CountGe 1 + CountGe 2 <= sumS
```

を、Collatz 固有の `CountGe 1 = k` で具体化したものです。

prefix 版も同時に固定しました。

```lean
theorem orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
    r + orbitWindowHeightPrefixCountGe n k r 2 ≤ sumS n r
```

これにより、大きな観測窓 `k` の中で先頭 `r` だけを見る局所 drift 下界が
直接使えます。

## Experiment

三層版も no-sorry で通りました。

```lean
theorem orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGe n k 1 + orbitWindowHeightCountGe n k 2 +
        orbitWindowHeightCountGe n k 3 ≤ sumS n k
```

これは重要です。

二層だけなら偶然の手計算で済む可能性がありますが、三層も同じ帰納形で通るなら、
一般 finite layer-cake の形が見えてきます。

推論:

```text
height = h の 1 点は、
  CountGe 1
  CountGe 2
  ...
  CountGe h
に 1 回ずつ寄与する。
```

したがって自然な次目標は:

```lean
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
    (n : OddNat) (k H : ℕ) :
    (Finset.range H).sum
        (fun t => orbitWindowHeightCountGe n k (t + 1))
      ≤ sumS n k
```

## Additional API

`CountGe` の threshold 単調性を固定しました。

```lean
theorem orbitWindowHeightCountGe_antitone
    (n : OddNat) (k : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    orbitWindowHeightCountGe n k b ≤ orbitWindowHeightCountGe n k a
```

これで分布階層を言えるようになります。

```text
CountGe 3 <= CountGe 2 <= CountGe 1 = k
```

## Review

今回の到達点は、Collatz height occupation が「単なる count」から
「drift lower-bound engine」へ移ったことです。

以前:

```text
height >= threshold の点が c 個ある
  -> c * threshold <= sumS
```

現在:

```text
height layer を足し上げる
  -> CountGe 1 + CountGe 2 + CountGe 3 <= sumS
  -> Collatz では CountGe 1 = k
  -> k + CountGe 2 <= sumS
```

ここから次に必要なのは、`CountGe 2`, `CountGe 3`, ... をどう評価するかです。
これは確率化・Markov kernel へ行く前の、有限観測窓上の occupation 推定問題です。

## Next Inference

次回は一般 finite layer-cake を狙うのが自然です。

第一補助候補:

```lean
private theorem range_threshold_count_le
    (H x : ℕ) :
    ((Finset.range H).filter (fun t => t + 1 ≤ x)).card ≤ x
```

この補題の意味:

```text
threshold 1..H のうち、x 以下のものは高々 x 個。
```

これがあれば、list induction で一般 finite layer-cake を組み立てられる見込みです。

次の実験候補:

```lean
theorem orbitWindowHeightSeq_sum_ge_sum_countGe_range
```

この一般形が通れば、Collatz 側の `sumS` は有限 layer occupation の総予算として
扱えるようになります。
