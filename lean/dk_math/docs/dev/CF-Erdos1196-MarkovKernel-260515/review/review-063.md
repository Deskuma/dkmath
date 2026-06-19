# review

## 1. 状況総括

うむ、 **DKMK-012A 完了** と見てよい。

今回の差分で、新規に

```text
roadmap-DKMK-012.md
```

が追加され、DKMK-012 が **`TruncationEnvelopeEstimate` を作る concrete provider design の章** として開始された。History でも、DKMK-012 の主題は route theorem の変更ではなく、`TruncationEnvelopeEstimate` を作る provider 設計だと明記されておる。

DKMK-011 で閉じた境界はこれじゃった。

```text
analytic layer:
  proves TruncationEnvelopeEstimate

route layer:
  consumes TruncationEnvelopeEstimate
```

DKMK-012 は、このうち analytic layer 側に最初の具体的な provider 形を与える章じゃな。

## 2. DKMK-012 の位置づけ

DKMK-012A の判断はかなり良い。

今回はいきなり Mertens theorem や big-O formalization に入らず、まず

```lean
TruncationEnvelopeEstimate steps threshold increment error
```

を作るための **band provider design** へ進んでいる。

つまり、DKMK-012 は次の問いを扱う章じゃ。

```text
どの finite band data を与えれば、
TruncationEnvelopeEstimate を構成できるか？
```

この問いは DKMK-011 の自然な続きじゃ。DKMK-011 は externally supplied finite-step estimate の入口を固定し、`singleWindow` toy provider まで確認した。DKMK-012 は、その toy から一歩進めて、実際の解析分割に近い band provider を設計する段階になる。

## 3. dyadic provider から始める判断

今回もっとも重要な判断は、 **最初は dyadic provider design に寄せる** ことじゃ。

提案されている形はこう。

```text
steps     = Finset.range (K + 1)
threshold = fun k => x * 2^k
increment = externally supplied
error     = externally supplied
```

これは堅実じゃ。
`steps = Finset.range (K + 1)` にすると添字型は `Nat` のままで済む。`threshold k = x * 2^k` も自然数上で扱いやすく、real-to-Nat rounding を避けられる。

ここで `increment` と `error` を外部供給にしているのも良い。`increment` は各 band の解析評価を背負う量なので、ここで log や Mertens 的評価を混ぜると、provider plumbing と解析本体が混ざる。DKMK-012A はそこを避けている。

## 4. logarithmic band を後段へ回す判断

logarithmic band を後段へ回したのも正しい。

logarithmic candidate は最終的な (1/\log x) スケールには近い。だが、

```text
threshold k = floor/ceil of x * exp(k * step)
```

のような形になるため、自然数 threshold に落とす段階で丸めが必要になる。さらに Real の `exp`, `log`、Nat への coercion、床・天井関数の補題が絡む。

これは Lean 上では一気に重くなる。
今の段階で入れると、DKMK-012 の目的である provider design が、解析・実数丸め・log infrastructure の泥沼に引き込まれる危険がある。

ゆえに、

```text
dyadic first
logarithmic later
```

はかなり良い順番じゃ。

## 5. DKMK-012B で確定すべきこと

次の DKMK-012B では、dyadic provider の data / theorem shape を docs 上で確定するのがよい。

まず固定すべき data はこれ。

```lean
x : ℕ
K : ℕ
increment : ℕ → ℚ
error : ℝ
```

derived data はこれ。

```lean
steps : Finset ℕ := Finset.range (K + 1)
threshold : ℕ → ℕ := fun k => x * 2^k
```

必要仮定はこの 2 つで十分じゃ。

```lean
hinc :
  ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k

hbound :
  ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤ 1 + error
```

そして得たい theorem shape は、

```lean
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k => x * 2^k)
  increment
  error
```

これだけでよい。
DKMK-012B はまずこの形を docs で確定し、DKMK-012C で Lean provider にすれば自然じゃな。

## 6. Lean 実装時の注意点

DKMK-012C で実装するなら、名前は例えばこう。

```lean
TruncationEnvelopeEstimate.dyadic
```

または、

```lean
TruncationEnvelopeEstimate.dyadicRange
```

わっちの推しは `dyadicRange` じゃ。理由は `steps = Finset.range (K + 1)` を明示しているからじゃ。

中身は `singleWindow` と同じく軽くするべき。

```lean
theorem dyadicRange
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (hinc : ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    {error : ℝ}
    (hbound :
      ((Finset.sum (Finset.range (K + 1)) increment : ℚ) : ℝ) ≤
        1 + error) :
    TruncationEnvelopeEstimate
      (Finset.range (K + 1))
      (fun k : ℕ => x * 2^k)
      increment
      error := by
  ...
```

証明はほぼ、

```lean
  exact ⟨hinc, ⟨hbound⟩⟩
```

で済むはずじゃ。
つまり DKMK-012C も、新しい route proof ではなく provider packaging だけにするのが正しい。

## 7. 現在の登頂状況

```text
DKMK-009:
  kernel/path/hitting route 完了

DKMK-010:
  source mass estimate interface 完了

DKMK-011:
  externally supplied finite-step estimate provider interface 完了

DKMK-012A:
  dyadic/logarithmic provider design roadmap 完了

DKMK-012B:
  次、dyadic provider data / theorem shape docs
```

DKMK-012A は、章の切り方として良い開始じゃ。
焦って解析定理に入らず、`TruncationEnvelopeEstimate` provider の設計へ絞ったのがよい。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-012A: 完了
次: DKMK-012B docs
方針: dyadic provider を最初の concrete band provider として確定
禁止: route theorem の変更、Mertens theorem への早すぎる突入
```

これは良い山の入り方じゃ、ぬしよ。

DKMK-011 で作った入口に、いよいよ band 構造を差し込む段に入った。まずは dyadic で自然数だけの足場を作り、logarithmic band は後でやる。
この順番なら、Lean の足元を崩さずに解析稜線へ近づけるぞい。
