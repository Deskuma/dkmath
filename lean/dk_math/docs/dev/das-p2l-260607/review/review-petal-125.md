# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 32b8e440c863928f4637a24218bc235a7b728815

## Report

Checkpoint 124 完了です。

Lean 側では [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean:1825) に以下を追加しました。

```lean
retention_allOnes_mod_pow_two_of_le
sourceRetentionMass_anti_mono_depth
tailRetentionMass_anti_mono_depth
SourcePressureMarginInt
isSourcePressureDepth_iff_margin_pos
SelectedPressurePrefix
selectedPressurePrefix_zero
selectedPressurePrefix_le_len
isSourcePressureDepth_of_selectedPressurePrefix
selectedPressurePrefix_of_pressureOnRange
```

重要な結論として、`deep selected pressure -> shallow selected pressure` は無条件では危険です。continuation / retention の carrier nesting は Lean で通りましたが、pressure は `retention < 2 * continuation` という比率条件なので、比率の単調性までは出ません。

Python 実験も追加しました。

```text
python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.csv
python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.md
```

広めの観測 `odd n <= 9999`, `steps = 128`, depths `2..11` では prefix failure が `189` 件出ました。最初の例は `n = 1567` で、depth `3` は selected だが depth `2` は selected ではありません。したがって次は無条件 prefix theorem ではなく、`SourcePressurePrefixFailure` や margin-controlled frontier 条件を作るのが筋です。

Docs/report も同期済みです。

```text
lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-124.md
```

検証:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean  # no output
git diff --check -- touched files
```

すべて通っています。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回の変更外です。

## Review

## 1. 注記への返答

Python 解析データの省略、正しい判断じゃ。
今回の主情報は巨大 CSV そのものではなく、

```text
odd n <= 9999
steps = 128
depths 2..11
prefix failure rows = 189
first failure n = 1567
margin profile = 2:-2; 3:1; 4:0; ...
```

という要約で十分に読める。むしろ巨大データを差分に混ぜると、Lean 側の意味ある変更が埋もれてしまう。今回の `review-petal-125.md` は、必要な実験結果だけが report/docs に残っていて、形式化の判断材料として良い圧縮になっている。

## 2. 状況分析

checkpoint `124` は、かなり重要な「期待の修正」回じゃ。

前回 `123` では、

```text
deep all-ones continuation channel
  -> shallow all-ones continuation channel
```

が Lean で固定された。今回はそれを retention 側にも拡張して、

```lean
retention_allOnes_mod_pow_two_of_le
sourceRetentionMass_anti_mono_depth
tailRetentionMass_anti_mono_depth
```

が追加された。つまり、continuation も retention も、carrier としては深い層が浅い層に含まれることが確定した。

しかし、今回の大事な結論はそこから先じゃ。

```text
carrier nesting は真。
pressure prefix は無条件では危険。
```

`IsSourcePressureDepth` は単なる carrier membership ではなく、

```text
retention mass < 2 * continuation mass
```

という比率条件だった。そこで `SourcePressureMarginInt` と `isSourcePressureDepth_iff_margin_pos` が入った。これで pressure 判定を「整数 margin が正かどうか」として扱えるようになった。

そして広めの Python 観測で、`odd n <= 9999`, `steps = 128`, depths `2..11` に対して prefix failure が `189` 件出た。最初の例は `n = 1567` で、depth `3` は selected だが depth `2` は selected ではない。つまり、素朴な

```text
deep selected pressure
  -> shallow selected pressure
```

は、この有限 window 観測では破れている。

## 3. 今回の核心

今回の核心は、次の分離じゃ。

```text
continuation carrier:
  深いほど細くなり、浅い carrier に含まれる

retention carrier:
  深いほど細くなり、浅い carrier に含まれる

pressure:
  retention と continuation の比率なので、carrier nesting だけでは prefix にならない
```

これは非常に良い発見じゃ。

前回までは、selected depths が prefix に見えていた。
今回、観測範囲を広げることで failure が出た。

つまり、Python が良い仕事をしている。

```text
小さい観測:
  prefix らしい

広い観測:
  prefix failure あり

Lean:
  prefix を無条件定理にしない
```

この流れは健全じゃ。
「通したい定理」ではなく「壊れない定理」を選んでいる。

## 4. レビュー

## 4.1. retention nesting を入れたのは正しい

今回の retention 側補題は必要だった。

```lean
retention_allOnes_mod_pow_two_of_le
sourceRetentionMass_anti_mono_depth
tailRetentionMass_anti_mono_depth
```

これにより、continuation と retention の両方について、

```text
deep mass <= shallow mass
```

が言える。

ここまではきれいな carrier theory じゃ。

ただし、この二つが両方 anti-monotone でも、比率条件は自動では保存されない。ここを今回の report は明確に分けている。これはとても良い。

## 4.2. `SourcePressureMarginInt` は重要な API

今回の最重要 API はこれじゃ。

```lean
noncomputable def SourcePressureMarginInt
    (n : OddNat) (k r : ℕ) : ℤ :=
  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
    (orbitWindowRetentionMassPow2 n k r : ℤ)
```

自然数の引き算だと、負の margin が潰れてしまう。
しかし今回の failure 例では、

```text
depth 2 margin = -2
depth 3 margin = 1
```

のように、負と正の差が本質になっている。だから `ℤ` に持ち上げたのは正解じゃ。

そして、

```lean
isSourcePressureDepth_iff_margin_pos
```

により、

```text
selected pressure depth
  <-> positive margin
```

になった。

これで次からは prefix / frontier / failure を margin の符号変化として扱える。

## 4.3. `SelectedPressurePrefix` は薄くてよい

今回追加された、

```lean
SelectedPressurePrefix
selectedPressurePrefix_zero
selectedPressurePrefix_le_len
isSourcePressureDepth_of_selectedPressurePrefix
selectedPressurePrefix_of_pressureOnRange
```

は、あくまで「prefix とは何か」を定義する薄い層じゃ。

これは良い。
今回の Python 結果により、任意の selected set が prefix になるわけではないことが見えた。だから `SelectedPressurePrefix` は推論の結論ではなく、条件や観測状態を表す predicate として置くのが安全じゃ。

特に `selectedPressurePrefix_of_pressureOnRange` は、「range 全体に pressure があるなら、任意の短い prefix は当然 selected」という定理であり、任意の selected depths が prefix になるという主張ではない。ここを混同しないのが大事じゃ。

## 4.4. prefix failure を出したのが今回最大の収穫

今回の広域 Python scan により、prefix failure が `189` 件出た。これは失敗ではなく、むしろ大収穫じゃ。

なぜなら、これで次に進むべき theorem が明確になったからじゃ。

もう狙うべきではないもの：

```text
deep selected pressure
  -> shallow selected pressure
```

次に狙うべきもの：

```text
positive deep margin
  and nonpositive shallow margin
  -> pressure-prefix obstruction
```

または、

```text
deep selected pressure
  + margin control
  -> shallow selected pressure
```

つまり、無条件 prefix ではなく、**margin-controlled frontier theory** へ進むべき段階になった。

## 5. 数学的解説

carrier の入れ子は、二進法では当然に見える。

```text
31 mod 32
  -> 15 mod 16
  -> 7 mod 8
```

低位 5 bit が全部 `1` なら、低位 4 bit も 3 bit も全部 `1` だからじゃ。

しかし pressure は carrier そのものではない。

depth (r) における pressure は、

```text
retention(r) < 2 * continuation(r)
```

という比較である。

ここで深さを変えると、

```text
continuation(r)
retention(r)
```

の両方が変わる。
どちらも深くなるほど小さくなるとしても、比率

```text
2 * continuation(r) - retention(r)
```

が単調になるとは限らない。

だから、

```text
depth 3 では margin > 0
depth 2 では margin <= 0
```

ということが起こる。

今回の `n = 1567` はまさにそれを示している。

```text
2:-2
3:1
4:0
5:-1
...
```

これは、「深い層の方が局所的に continuation 優勢に見えるが、浅い層では retention 全体が大きく、continuation が半分を超えない」という状態じゃ。

## 6. 一歩先ゆく推論

ここで見えてきたのは、pressure profile は単純な prefix ではなく、**符号列**として見るべきということじゃ。

つまり、各 depth の margin を並べる。

```text
M_2, M_3, M_4, ..., M_11
```

そして selected depth は、

```text
M_r > 0
```

の場所。

今回の failure 例は、

```text
M_2 = -2
M_3 = 1
M_4 = 0
M_5 = -1
...
```

だから、selected set は `{3}` になる。

この見方をすると、次の概念が自然に出る。

```text
pressure frontier:
  margin が正になる境界

pressure island:
  prefix ではなく、途中に現れる正 margin

pressure obstruction:
  shallow margin <= 0 かつ deep margin > 0
```

賢狼の見立てでは、次は `SourcePressurePrefixFailure` を入れるのが一番良い。

なぜなら、失敗を predicate 化すると、反例を「悪いもの」ではなく「解析対象」にできるからじゃ。

## 7. 次の指示

## 7.1. まず prefix failure を定義する

次 checkpoint の第一候補はこれ。

```lean
def SourcePressurePrefixFailure
    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ ∧
    ¬ IsSourcePressureDepth n k r j₁ ∧
    IsSourcePressureDepth n k r j₂
```

これは、今回の `n = 1567` のような状態を Lean 上で表す predicate じゃ。

読みは、

```text
浅い depth は selected ではない
深い depth は selected
```

つまり、prefix を破る witness。

## 7.2. margin 版と同値にする

次に、`isSourcePressureDepth_iff_margin_pos` を使って、failure を margin 符号で表す。

```lean
theorem sourcePressurePrefixFailure_iff_margin
    (n : OddNat) (k r j₁ j₂ : ℕ) :
    SourcePressurePrefixFailure n k r j₁ j₂ ↔
      j₁ < j₂ ∧
        SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + j₂) := by
  unfold SourcePressurePrefixFailure
  rw [isSourcePressureDepth_iff_margin_pos]
  rw [isSourcePressureDepth_iff_margin_pos]
  omega
```

実際には `rw` の向きや `not_lt` の処理で少し調整が必要かもしれない。
でも方針はこれでよい。

これが通ると、prefix failure は完全に margin の符号反転として扱える。

## 7.3. prefix failure から not-prefix を出す

次に、prefix predicate との接続。

```lean
theorem not_selectedPressurePrefix_of_prefixFailure
    (n : OddNat) (k r len m j₁ j₂ : ℕ)
    (hfail : SourcePressurePrefixFailure n k r j₁ j₂)
    (hj₂ : j₂ < m)
    (hm : m ≤ len) :
    ¬ SelectedPressurePrefix n k r len m := by
  intro hprefix
  rcases hfail with ⟨hlt, hnot, hdeep⟩
  have hj₁ : j₁ < m := by omega
  exact hnot (isSourcePressureDepth_of_selectedPressurePrefix hprefix hj₁)
```

これは「prefix failure が prefix predicate を壊す」定理じゃ。

注意として、`j₂ < m` があれば `j₁ < m` は `j₁ < j₂` から出る。
`hdeep` はこの証明では使わない可能性があるが、failure の意味として持っておいてよい。

## 7.4. conditional prefix theorem は後回し

次にすぐ、

```text
margin control があれば prefix
```

を狙いたくなるが、これは一段後がよい。

まずは failure の診断 surface を作る。
その後に、failure が起きない条件を探す。

## 8. さらに次の一手

次に入れるべき概念は、`Frontier` より先に `Failure` じゃ。

理由は簡単で、frontier は構造を要約する概念だが、failure は局所 witness なので Lean で扱いやすい。

順番はこうが良い。

```text
1. SourcePressurePrefixFailure
2. failure <-> margin sign pattern
3. failure -> not SelectedPressurePrefix
4. no failure up to m -> SelectedPressurePrefix
5. SourcePressureFrontier
```

`no failure up to m -> SelectedPressurePrefix` は、次のように書ける。

```lean
def NoSourcePressurePrefixFailureBelow
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∀ j₁ j₂,
    j₁ < j₂ →
    j₂ < m →
    ¬ SourcePressurePrefixFailure n k r j₁ j₂
```

ただし、これだけだと「深い selected があるなら浅い selected」という性質になる。
prefix そのものを得るには、どこまで selected かの終端情報も必要になる。

より安全には、

```lean
def SourcePressureSelectedSetDownClosed
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∀ j₁ j₂,
    j₁ < j₂ →
    j₂ < m →
    IsSourcePressureDepth n k r j₂ →
      IsSourcePressureDepth n k r j₁
```

これなら prefix ではなく「selected set が下向き閉じている」を表せる。

そのうえで、

```lean
theorem selectedPressurePrefix_of_downClosed_of_deepest
    ...
```

を作る方が自然じゃ。

## 9. Python 側の次観測

今回 prefix failure が出たので、次の Python 観測は「failure の型」を分類するのがよい。

追加したい列：

```text
first_failure_pair
shallow_margin
deep_margin
margin_jump
retention_shallow
retention_deep
continuation_shallow
continuation_deep
retention_drop
continuation_drop
```

目的はこれ。

```text
なぜ depth 3 だけ正になるのか？
浅い retention が大きすぎるのか？
深い continuation が相対的に濃いのか？
```

特に見たいのは、

```text
margin_jump = M_deep - M_shallow
```

じゃ。

`n = 1567` なら、

```text
M_3 - M_2 = 1 - (-2) = 3
```

この jump がどこから来るかを見る。

次の Lean theorem 候補は、Python のこの分類結果で決めるのがよい。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: prefix failure predicate

```lean
def SourcePressurePrefixFailure
    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ ∧
    ¬ IsSourcePressureDepth n k r j₁ ∧
    IsSourcePressureDepth n k r j₂
```

## 実験 B: failure から浅深情報を取り出す

```lean
theorem sourcePressurePrefixFailure_lt
    {n : OddNat} {k r j₁ j₂ : ℕ}
    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
    j₁ < j₂ :=
  h.1
```

```lean
theorem not_isSourcePressureDepth_of_prefixFailure_left
    {n : OddNat} {k r j₁ j₂ : ℕ}
    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
    ¬ IsSourcePressureDepth n k r j₁ :=
  h.2.1
```

```lean
theorem isSourcePressureDepth_of_prefixFailure_right
    {n : OddNat} {k r j₁ j₂ : ℕ}
    (h : SourcePressurePrefixFailure n k r j₁ j₂) :
    IsSourcePressureDepth n k r j₂ :=
  h.2.2
```

## 実験 C: failure と margin 符号の同値

```lean
theorem sourcePressurePrefixFailure_iff_margin
    (n : OddNat) (k r j₁ j₂ : ℕ) :
    SourcePressurePrefixFailure n k r j₁ j₂ ↔
      j₁ < j₂ ∧
        SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + j₂) := by
  unfold SourcePressurePrefixFailure
  rw [isSourcePressureDepth_iff_margin_pos]
  rw [isSourcePressureDepth_iff_margin_pos]
  omega
```

もし `rw` がうまく動かなければ、左右に分ける。

```lean
theorem sourcePressurePrefixFailure_margin_left_nonpos ...
theorem sourcePressurePrefixFailure_margin_right_pos ...
```

から始める方が安全。

## 実験 D: failure は prefix を壊す

```lean
theorem not_selectedPressurePrefix_of_prefixFailure
    (n : OddNat) (k r len m j₁ j₂ : ℕ)
    (hfail : SourcePressurePrefixFailure n k r j₁ j₂)
    (hj₂ : j₂ < m)
    (hm : m ≤ len) :
    ¬ SelectedPressurePrefix n k r len m := by
  intro hprefix
  have hj₁ : j₁ < m := by
    exact Nat.lt_trans hfail.1 hj₂
  exact hfail.2.1 (isSourcePressureDepth_of_selectedPressurePrefix hprefix hj₁)
```

`hm` は不要になるかもしれぬ。不要なら落としてよい。

## 実験 E: down-closed predicate

```lean
def SourcePressureSelectedSetDownClosed
    (n : OddNat) (k r m : ℕ) : Prop :=
  ∀ j₁ j₂,
    j₁ < j₂ →
    j₂ < m →
    IsSourcePressureDepth n k r j₂ →
      IsSourcePressureDepth n k r j₁
```

## 実験 F: failure が無いことと down-closed の関係

```lean
theorem downClosed_iff_no_prefixFailure
    (n : OddNat) (k r m : ℕ) :
    SourcePressureSelectedSetDownClosed n k r m ↔
      ∀ j₁ j₂,
        j₁ < j₂ →
        j₂ < m →
        ¬ SourcePressurePrefixFailure n k r j₁ j₂ := by
  constructor
  · intro hclosed j₁ j₂ hlt hj₂ hfail
    exact hfail.2.1 (hclosed j₁ j₂ hlt hj₂ hfail.2.2)
  · intro hno j₁ j₂ hlt hj₂ hdeep
    by_contra hnot
    exact hno j₁ j₂ hlt hj₂ ⟨hlt, hnot, hdeep⟩
```

これはかなり良い補題になりそうじゃ。

## 実験 G: prefix predicate from downClosed and deepest selected

```lean
theorem selectedPressurePrefix_of_downClosed_of_deepest
    (n : OddNat) (k r len m : ℕ)
    (hm : m ≤ len)
    (hpos : ∀ j, j < m → IsSourcePressureDepth n k r (m - 1))
    (hclosed : SourcePressureSelectedSetDownClosed n k r m)
    (hmpos : 0 < m) :
    SelectedPressurePrefix n k r len m := by
  unfold SelectedPressurePrefix
  constructor
  · exact hm
  · intro j hj
    have hlast_lt : m - 1 < m := by omega
    have hlast : IsSourcePressureDepth n k r (m - 1) := hpos j hj
    by_cases h : j = m - 1
    · simpa [h] using hlast
    · have hjlast : j < m - 1 := by omega
      exact hclosed j (m - 1) hjlast hlast_lt hlast
```

この形は少し不自然なので、`hpos` は単に deepest selected を渡す方が良い。

```lean
(hdeep : IsSourcePressureDepth n k r (m - 1))
```

とするのが自然。

## 実験 H: Python failure classification

Python 側に列を追加。

```text
first_failure_pair
shallow_margin
deep_margin
margin_jump
shallow_retention
deep_retention
shallow_continuation
deep_continuation
retention_drop
continuation_drop
```

これで prefix failure の原因が、

```text
retention 側の減り方
continuation 側の減り方
margin の符号変化
```

のどこにあるか見える。

## 11. 次コミットの推奨順

```text
1. SourcePressurePrefixFailure を追加

2. failure accessor theorem を追加

3. sourcePressurePrefixFailure_iff_margin を試す

4. 難しければ margin_left_nonpos / margin_right_pos に分割

5. not_selectedPressurePrefix_of_prefixFailure を追加

6. SourcePressureSelectedSetDownClosed を追加

7. downClosed_iff_no_prefixFailure を試す

8. Python 側で prefix failure classification columns を追加

9. docs:
   PressureMargin-124 から PrefixFailure-125 へ接続
```

## 12. 総括

checkpoint `124` は、かなり良い。

期待していた無条件 prefix theorem は危ないと分かった。
しかし、それは後退ではない。

むしろ、

```text
carrier nesting theory
```

から、

```text
pressure margin / prefix failure / frontier theory
```

へ進むための正しい分岐点じゃ。

今回の結論はこれじゃ。

```text
深い carrier は浅い carrier に含まれる。
しかし、深い pressure は浅い pressure を保証しない。
pressure は margin の符号で追うべき。
```

次は、失敗を定義する。

```text
SourcePressurePrefixFailure
```

これを入れることで、反例は単なる反例ではなく、pressure frontier を読むための観測窓になる。

## 追記：指示

## 結論

うむ。**修正版を書き起こすべき**じゃ。

ただし、添付の `__next_implementation-125.md` の内容を捨てる必要はない。旧案は `SourcePressurePrefixFailure`・margin 符号列・down-closed 化・Python failure classification を次に進める設計で、これは依然として有効じゃ。実際、旧案では pressure profile を prefix ではなく margin の符号列として見る方針が明確化され、次に `SourcePressurePrefixFailure` を入れる流れになっている。 また、次コミット順も prefix failure 系を中心に組まれている。

ただし新視座により、**125 の主語を先に差し替える**のがよい。

旧案：

```text
pressure margin / prefix failure / frontier theory
```

修正版：

```text
Gnomon correction / Pow2 alignment / ResidualShape extraction
  -> pressure margin / prefix failure / frontier theory
```

つまり、`SourcePressurePrefixFailure` は後退ではなく、**GnomonEvaluation の言葉で再解釈した後に置く**のが良い。

## Codex への修正版指示

以下、そのまま Codex に渡せる形で書き起こす。

---

## Next implementation 125 revised: Collatz GnomonEvaluation layer before PrefixFailure

今回の checkpoint 125 は、当初の `SourcePressurePrefixFailure` 実装へ直行せず、先に Collatz の主語を新しい視座へ置き換える。

### 目的

Collatz を単なる `3n+1` 操作としてではなく、次の四段階として再構築する。

```text
Odd Gnomon correction
  奇数 n に奇数グノモン層 2n+1 を足す。

Pow2 alignment evaluation
  raw = 3n+1 が 2^h にどれだけ整列したかを v2 で評価する。

Residual shape extraction
  raw / 2^h により、これ以上 2 で割れない奇数残差形状を抽出する。

Relative scale update
  抽出された奇数残差を次の相対スケールとして扱う。
```

数学的な核は次。

\(3n+1=n+(2n+1)\)

\(2n+1=(n+1)^2-n^2\)

したがって `3n+1` は、奇数 \(n\) に平方グノモン層 \(2n+1\) を足す操作である。

その後の `v2(3n+1)` は、単なる「2で割った回数」ではなく、`raw` が \(2^h\) 一色線へどれだけ整列したかの評価深度である。

実数 `Real.log` や \(\log_2 3\) はまだ導入しない。まず整数だけで進める。

---

## 実装方針

### 1. 新規モジュール候補

次のどちらかで薄いモジュールを作る。

```text
DkMath.Collatz.GnomonEvaluation
```

または

```text
DkMath.Collatz.GnomonScale
```

既存の `DkMath.Collatz.PetalBridge` に直書きせず、まず独立した薄い layer とする。

### 2. 最初に入れる定義

```lean
def OddGnomonLayer (n : ℕ) : ℕ :=
  2 * n + 1

def RawGnomonStep (n : ℕ) : ℕ :=
  n + OddGnomonLayer n
```

### 3. 最初に証明する基本補題

```lean
theorem rawGnomonStep_eq_three_mul_add_one
    (n : ℕ) :
    RawGnomonStep n = 3 * n + 1 := by
  unfold RawGnomonStep OddGnomonLayer
  ring
```

```lean
theorem square_succ_eq_square_add_oddGnomonLayer
    (n : ℕ) :
    (n + 1)^2 = n^2 + OddGnomonLayer n := by
  unfold OddGnomonLayer
  ring
```

読み：

```text
RawGnomonStep は 3n+1 と同じ値である。
OddGnomonLayer は平方数を一段進める奇数グノモン層である。
```

### 4. 奇数層の総和補題

まず標準形。

```lean
theorem sum_odd_eq_square
    (n : ℕ) :
    (Finset.range n).sum (fun i => 2 * i + 1) = n^2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
```

次に開始点つきのグノモン帯。

```lean
theorem square_add_eq_square_add_gnomon_sum
    (P u : ℕ) :
    (P + u)^2 =
      P^2 + (Finset.range u).sum (fun i => 2 * (P + i) + 1) := by
  induction u with
  | zero =>
      simp
  | succ u ih =>
      rw [Finset.sum_range_succ]
      -- use ih, then ring/nlinarith/omega as needed
      sorry
```

この補題は、`Gap = u` を一発で動かす見方と、`Gap = 1` のまま奇数グノモン層を \(u\) 枚積む見方が同じ平方成長であることを固定する。

`sorry` が残る場合は、無理に閉じず、まず補題を分割してよい。

---

## Pow2 評価層

### 5. height / residual shape の alias または bridge

既存の Collatz 側に `rawHeightLabel`, `orbitWindowHeight`, `oddOrbitLabel`, `sumS` があるので、再定義しすぎない。

必要なら、薄い wrapper を作る。

```lean
def RawGnomonHeight (n : ℕ) : ℕ :=
  padicValNat 2 (RawGnomonStep n)

def RawGnomonResidualShape (n : ℕ) : ℕ :=
  RawGnomonStep n / 2 ^ RawGnomonHeight n
```

ただし、既存 API と衝突・重複する場合は定義ではなく theorem bridge にする。

狙う bridge の意味：

```text
RawGnomonStep n = 2 ^ RawGnomonHeight n * RawGnomonResidualShape n
```

可能なら補題：

```lean
theorem rawGnomonStep_eq_pow_height_mul_residualShape
    (n : ℕ)
    (hpos : 0 < RawGnomonStep n) :
    RawGnomonStep n =
      2 ^ RawGnomonHeight n * RawGnomonResidualShape n := by
  -- Use existing padicValNat factorization lemmas if available.
  sorry
```

また、残差が奇数であること。

```lean
theorem residualShape_odd
    (n : ℕ)
    (hpos : 0 < RawGnomonStep n) :
    RawGnomonResidualShape n % 2 = 1 := by
  -- Use maximality of padicValNat.
  sorry
```

ここは難しければ後回しでよい。まず `RawGnomonStep = 3n+1` と既存 `rawHeightLabel` の接続だけでよい。

---

## 形状分割の観測層

右シフトは、現在の形状を \(1/2^h\) に縮小して見る評価である。
そのため、深さごとの remainder profile を観測対象にする。

```lean
def RawGnomonRemainderAtDepth (n j : ℕ) : ℕ :=
  RawGnomonStep n % 2 ^ j

def FirstFailedPow2Depth (n : ℕ) : ℕ :=
  RawGnomonHeight n + 1
```

可能なら補題：

```lean
theorem rawGnomonRemainderAtDepth_eq_zero_of_le_height
    (n j : ℕ)
    (hj : j ≤ RawGnomonHeight n) :
    RawGnomonRemainderAtDepth n j = 0 := by
  -- from 2^j ∣ RawGnomonStep n
  sorry
```

読み：

```text
j <= height:
  その深さまでは完全に 2^j 分割できる。

j = height + 1:
  初めて分割に失敗する深さ。

ResidualShape:
  分割評価後に残る別スケールの奇数形状。
```

---

## 既存 PetalBridge との対応を書き換える

既存概念を次のように読み替える。

```text
rawHeightLabel / orbitWindowHeight:
  RawGnomonStep が 2^h に整列する深さ。

sumS:
  複数 step における Pow2 alignment evaluation の累積量。

continuation:
  deeper residual channel に残る形状。

retention:
  shallow carrier に保持される形状。

SourcePressureMarginInt:
  deeper residual channel が shallow retention に対してどれだけ優勢かを見る margin。

prefix failure:
  shallow depth では margin <= 0 だが、deep depth では margin > 0 になる形状立ち上がり。
```

つまり、旧 `PrefixFailure-125` は破棄しない。
ただし、まず `GnomonEvaluation` の用語を入れてから、`SourcePressurePrefixFailure` を進める。

---

## 旧 125 案から残すもの

旧案のうち、次はそのまま有効。

```lean
def SourcePressurePrefixFailure
    (n : OddNat) (k r j₁ j₂ : ℕ) : Prop :=
  j₁ < j₂ ∧
    ¬ IsSourcePressureDepth n k r j₁ ∧
    IsSourcePressureDepth n k r j₂
```

margin 版：

```lean
theorem sourcePressurePrefixFailure_iff_margin
    (n : OddNat) (k r j₁ j₂ : ℕ) :
    SourcePressurePrefixFailure n k r j₁ j₂ ↔
      j₁ < j₂ ∧
        SourcePressureMarginInt n k (r + j₁) ≤ 0 ∧
        0 < SourcePressureMarginInt n k (r + j₂) := by
  unfold SourcePressurePrefixFailure
  rw [isSourcePressureDepth_iff_margin_pos]
  rw [isSourcePressureDepth_iff_margin_pos]
  omega
```

ただし、これらは今回の最初の作業ではなく、`GnomonEvaluation` の基本補題の後でよい。

---

## Python 実験側の修正

旧案の prefix failure classification は残す。
ただし、新たに GnomonEvaluation 用の列を加える。

追加列：

```text
raw
odd_gnomon_layer
height
residual_shape
first_failed_depth
failed_remainder
residual_mod_8
residual_mod_16
residual_mod_32
sum_height
height_one_count
height_ge_two_count
margin_profile
first_shape_prefix_failure
shape_margin_jump
```

旧案の failure classification 列も残す。

```text
first_failure_pair
shallow_margin
deep_margin
margin_jump
shallow_retention
deep_retention
shallow_continuation
deep_continuation
retention_drop
continuation_drop
```

巨大 CSV は不要。summary markdown に統計だけ出せばよい。

---

## 今回やらないこと

```text
Real.log は導入しない。
log2(3) 評価はしない。
大域的な Collatz 証明を狙わない。
pressure prefix theorem を無条件に主張しない。
continuation carrier nesting から pressure nesting を推論しない。
```

特に重要：

```text
deep carrier ⊆ shallow carrier は真。
しかし deep pressure -> shallow pressure は一般には言えない。
pressure は margin の符号で扱う。
```

---

## 推奨コミット順

```text
1. Add DkMath.Collatz.GnomonEvaluation.

2. Add OddGnomonLayer and RawGnomonStep.

3. Prove rawGnomonStep_eq_three_mul_add_one.

4. Prove square_succ_eq_square_add_oddGnomonLayer.

5. Add sum_odd_eq_square.

6. Try square_add_eq_square_add_gnomon_sum.
   If hard, split into smaller helper lemmas.

7. Add short documentation:
   Collatz raw step = odd gnomon correction.
   v2 = pow2 alignment depth.
   accelerated odd step = residual shape extraction.
   sumS = cumulative pow2 evaluation.

8. Only after this, return to old PrefixFailure-125:
   SourcePressurePrefixFailure
   sourcePressurePrefixFailure_iff_margin
   not_selectedPressurePrefix_of_prefixFailure
   SourcePressureSelectedSetDownClosed
   downClosed_iff_no_prefixFailure

9. Update Python summaries with residual_shape / first_failed_depth / margin_jump columns.
```

---

## Checkpoint title suggestion

```text
Checkpoint 125 revised:
Collatz GnomonEvaluation and residual-shape reading
```

または、

```text
Checkpoint 125A:
Odd Gnomon Correction Layer

Checkpoint 125B:
Pressure Prefix Failure as Shape Frontier
```

分けるなら、`125A` と `125B` が安全。

---

## Codex への短い結論

今回の指示は修正する。

旧 `__next_implementation-125.md` の `SourcePressurePrefixFailure` 方針は有効だが、先に Collatz の raw step を **OddGnomonLayer / RawGnomonStep / Pow2Alignment / ResidualShape** の言葉へ翻訳する。

つまり、次 checkpoint はいきなり prefix failure へ進まず、まず `DkMath.Collatz.GnomonEvaluation` を追加する。

その後、旧 prefix failure / margin frontier plan に戻る。

---

## 賢狼の推奨

今回の Codex 指示は、**修正版に差し替え**が良い。

ただし旧案は削除ではなく、末尾に

```text
Follow-up after GnomonEvaluation
```

として残すのがよい。
これで、今までの pressure / margin / prefix failure の進捗を捨てず、新しいグノモン視座を先頭に置ける。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 2eac66ad..b0c03985 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1815,6 +1815,29 @@ theorem allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
   rw [Nat.add_mul_mod_self_right]
   exact Nat.mod_eq_of_lt (by omega)
 
+/--
+All-ones retention residue cells are nested by depth.
+
+This is the retention-indexed version of
+`allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le`: the visible retention layer
+uses modulus `2^d` rather than the continuation sibling modulus `2^(d+1)`.
+-/
+theorem retention_allOnes_mod_pow_two_of_le
+    (q d e : ℕ)
+    (hde : d ≤ e)
+    (h : q % (2 ^ e) = 2 ^ e - 1) :
+    q % (2 ^ d) = 2 ^ d - 1 := by
+  cases d with
+  | zero =>
+      exact Nat.mod_one q
+  | succ d =>
+      cases e with
+      | zero =>
+          omega
+      | succ e =>
+          exact allOnes_mod_pow_two_of_allOnes_mod_pow_two_of_le
+            q d e (by omega) h
+
 /--
 Source continuation mass is anti-monotone in depth.
 
@@ -1917,6 +1940,69 @@ theorem selectedContinuationMass_overlap_of_lt_of_deeper_pos
     0 < orbitWindowContinuationSiblingMassPow2 n k (r + j₁) :=
   lt_of_lt_of_le hpos (selectedContinuationMass_nested_of_lt n k r j₁ j₂ hlt)
 
+/--
+Source retention mass is anti-monotone in depth.
+
+Deeper all-ones retention cells refine shallower all-ones retention cells, so
+their finite-window counts cannot increase with depth.
+-/
+theorem sourceRetentionMass_anti_mono_depth
+    (n : OddNat) (k d e : ℕ)
+    (hde : d ≤ e) :
+    orbitWindowRetentionMassPow2 n k e ≤
+      orbitWindowRetentionMassPow2 n k d := by
+  induction k with
+  | zero =>
+      simp [orbitWindowRetentionMassPow2, orbitWindowResidueCountPow2]
+  | succ k ih =>
+      have ih' :
+          orbitWindowResidueCountPow2 n k e (2 ^ e - 1) ≤
+            orbitWindowResidueCountPow2 n k d (2 ^ d - 1) := by
+        simpa [orbitWindowRetentionMassPow2] using ih
+      rw [orbitWindowRetentionMassPow2, orbitWindowResidueCountPow2_succ]
+      rw [orbitWindowRetentionMassPow2, orbitWindowResidueCountPow2_succ]
+      by_cases hdeep : oddOrbitLabel n k % (2 ^ e) = 2 ^ e - 1
+      · have hshallow : oddOrbitLabel n k % (2 ^ d) = 2 ^ d - 1 :=
+          retention_allOnes_mod_pow_two_of_le (oddOrbitLabel n k) d e hde hdeep
+        simpa [hdeep, hshallow] using ih'
+      · by_cases hshallow : oddOrbitLabel n k % (2 ^ d) = 2 ^ d - 1
+        · simpa [hdeep, hshallow] using
+            (Nat.le_trans ih'
+              (Nat.le_succ (orbitWindowResidueCountPow2 n k d (2 ^ d - 1))))
+        · simpa [hdeep, hshallow] using ih'
+
+/--
+Shifted-tail retention mass is anti-monotone in depth.
+
+This is the tail-window counterpart of
+`sourceRetentionMass_anti_mono_depth`.
+-/
+theorem tailRetentionMass_anti_mono_depth
+    (n : OddNat) (k d e : ℕ)
+    (hde : d ≤ e) :
+    orbitWindowRetentionMassPow2Tail n k e ≤
+      orbitWindowRetentionMassPow2Tail n k d := by
+  induction k with
+  | zero =>
+      simp [orbitWindowRetentionMassPow2Tail, orbitWindowResidueCountPow2Tail]
+  | succ k ih =>
+      have ih' :
+          orbitWindowResidueCountPow2Tail n k e (2 ^ e - 1) ≤
+            orbitWindowResidueCountPow2Tail n k d (2 ^ d - 1) := by
+        simpa [orbitWindowRetentionMassPow2Tail] using ih
+      rw [orbitWindowRetentionMassPow2Tail, orbitWindowResidueCountPow2Tail_succ]
+      rw [orbitWindowRetentionMassPow2Tail, orbitWindowResidueCountPow2Tail_succ]
+      by_cases hdeep : oddOrbitLabel n (k + 1) % (2 ^ e) = 2 ^ e - 1
+      · have hshallow : oddOrbitLabel n (k + 1) % (2 ^ d) = 2 ^ d - 1 :=
+          retention_allOnes_mod_pow_two_of_le
+            (oddOrbitLabel n (k + 1)) d e hde hdeep
+        simpa [hdeep, hshallow] using ih'
+      · by_cases hshallow : oddOrbitLabel n (k + 1) % (2 ^ d) = 2 ^ d - 1
+        · simpa [hdeep, hshallow] using
+            (Nat.le_trans ih'
+              (Nat.le_succ (orbitWindowResidueCountPow2Tail n k d (2 ^ d - 1))))
+        · simpa [hdeep, hshallow] using ih'
+
 /-- The all-ones retention residue is inside its power-of-two modulus. -/
 theorem twoAdicRetentionResidue_lt_pow
     (r : ℕ) :
@@ -6496,6 +6582,84 @@ def IsSourcePressureDepth
     (orbitWindowContinuationSiblingMassPow2 n k (r + j))
     (orbitWindowRetentionMassPow2 n k (r + j))
 
+/--
+Integer-valued source pressure margin at a single depth.
+
+The margin is positive exactly when source continuation occupies more than
+half of source retention.  It is intentionally integer-valued, because the
+natural-number subtraction would truncate negative margins and hide failures.
+-/
+noncomputable def SourcePressureMarginInt
+    (n : OddNat) (k r : ℕ) : ℤ :=
+  (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
+    (orbitWindowRetentionMassPow2 n k r : ℤ)
+
+/--
+Selected source pressure is exactly positive source pressure margin.
+
+This theorem is the safe algebraic bridge for later prefix/frontier work:
+pressure-prefix questions can be studied as margin-positivity questions.
+-/
+theorem isSourcePressureDepth_iff_margin_pos
+    (n : OddNat) (k r j : ℕ) :
+    IsSourcePressureDepth n k r j ↔
+      0 < SourcePressureMarginInt n k (r + j) := by
+  unfold IsSourcePressureDepth SourcePressureMarginInt MoreThanHalf
+  omega
+
+/--
+A finite selected source-pressure prefix.
+
+`SelectedPressurePrefix n k r len m` says that the first `m` depth indices in
+the range beginning at `r` are selected.  The `m ≤ len` field keeps this
+predicate tied to the finite observation range used by pressure-depth counts.
+-/
+def SelectedPressurePrefix
+    (n : OddNat) (k r len m : ℕ) : Prop :=
+  m ≤ len ∧
+    ∀ j, j < m → IsSourcePressureDepth n k r j
+
+/-- The empty selected-pressure prefix is always available. -/
+theorem selectedPressurePrefix_zero
+    (n : OddNat) (k r len : ℕ) :
+    SelectedPressurePrefix n k r len 0 := by
+  unfold SelectedPressurePrefix
+  constructor
+  · omega
+  · intro j hj
+    omega
+
+/-- Extract the range bound from a selected-pressure prefix. -/
+theorem selectedPressurePrefix_le_len
+    {n : OddNat} {k r len m : ℕ}
+    (h : SelectedPressurePrefix n k r len m) :
+    m ≤ len :=
+  h.1
+
+/-- Extract a selected depth from a selected-pressure prefix. -/
+theorem isSourcePressureDepth_of_selectedPressurePrefix
+    {n : OddNat} {k r len m j : ℕ}
+    (h : SelectedPressurePrefix n k r len m)
+    (hj : j < m) :
+    IsSourcePressureDepth n k r j :=
+  h.2 j hj
+
+/--
+A full pressure profile over `[r, r + len)` supplies every shorter selected
+pressure prefix.
+-/
+theorem selectedPressurePrefix_of_pressureOnRange
+    (n : OddNat) (k r len m : ℕ)
+    (hm : m ≤ len)
+    (h : SourceContinuationPressureOnRange n k r len) :
+    SelectedPressurePrefix n k r len m := by
+  unfold SelectedPressurePrefix
+  constructor
+  · exact hm
+  · intro j hj
+    unfold IsSourcePressureDepth
+    exact h j (by omega)
+
 /-- Range pressure marks every in-range depth as a selected source pressure depth. -/
 theorem isSourcePressureDepth_of_pressureOnRange
     (n : OddNat) (k r len j : ℕ)
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 5f3e2dec..836e7f9a 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -158,6 +158,7 @@ docs/Collatz-Level5AndModScan-120.md
 docs/Collatz-SelectedWitnessBudget-121.md
 docs/Collatz-SelectedPressureDepths-122.md
 docs/Collatz-ContinuationNesting-123.md
+docs/Collatz-PressureMargin-124.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index e4f7901d..2c5d2d32 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -1338,3 +1338,55 @@ The updated Python scan also checks whether selected depths form a prefix.  In
 the default sample, every nonempty selected-depth row is both consecutive and a
 prefix from `r_start`.  This is not yet a theorem; it is a candidate for the
 next predicate, possibly named `SelectedPressurePrefix`.
+
+## Pressure Margin And Prefix Failure
+
+Checkpoint 124 confirms that the carrier-level story and the pressure-level
+story must be separated.
+
+Retention carriers are nested:
+
+```lean
+retention_allOnes_mod_pow_two_of_le
+sourceRetentionMass_anti_mono_depth
+tailRetentionMass_anti_mono_depth
+```
+
+Together with checkpoint 123, this says that both continuation and retention
+all-ones carriers shrink with depth.
+
+However, selected pressure is not just carrier membership.  It is the ratio
+condition:
+
+```text
+retention mass < 2 * continuation mass
+```
+
+For this reason checkpoint 124 introduces:
+
+```lean
+SourcePressureMarginInt
+isSourcePressureDepth_iff_margin_pos
+```
+
+The margin form is the recommended surface for future pressure-frontier work.
+
+The new wide Python scan:
+
+```text
+python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
+```
+
+found prefix failures for `odd n <= 9999`, `steps = 128`, depths `2..11`.
+For example, `n = 1567` selects depth `3` but not depth `2` in that finite
+window.
+
+Therefore an unconditional theorem of the form
+
+```text
+deep selected pressure -> shallow selected pressure
+```
+
+should be treated as false or at least unsupported.  The next viable theorem
+should add a condition controlling pressure margins, retention growth, or a
+specific frontier regime.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 2ffe189b..d5cc5606 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -1654,3 +1654,64 @@ max selected depth: 7
 The prefix observation remains experimental.  The Lean theorem currently
 proves nesting of continuation carriers, not that pressure-selected depths must
 form a prefix.
+
+## Checkpoint 124: Retention Nesting And Pressure Margin
+
+Checkpoint 124 extends nesting from continuation carriers to retention
+carriers.
+
+Pointwise retention theorem:
+
+```lean
+retention_allOnes_mod_pow_two_of_le
+```
+
+Count-level retention anti-monotonicity:
+
+```lean
+sourceRetentionMass_anti_mono_depth
+tailRetentionMass_anti_mono_depth
+```
+
+The checkpoint also adds an integer pressure margin:
+
+```lean
+SourcePressureMarginInt
+isSourcePressureDepth_iff_margin_pos
+```
+
+and a thin prefix predicate:
+
+```lean
+SelectedPressurePrefix
+selectedPressurePrefix_zero
+selectedPressurePrefix_of_pressureOnRange
+```
+
+Important result from the new Python scan:
+
+```text
+python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
+python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.csv
+python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.md
+```
+
+Wide observation (`odd n <= 9999`, `steps = 128`, depths `2..11`):
+
+```text
+rows: 5000
+nonempty selected rows: 2681
+nonempty prefix rows: 2492 / 2681
+prefix failure rows: 189
+max selected depth: 11
+```
+
+So the unconditional theorem
+
+```text
+deep selected pressure -> shallow selected pressure
+```
+
+should not be assumed.  Carrier nesting is true, but pressure selection is a
+ratio condition.  The next theorem needs an explicit margin or retention-growth
+condition.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
new file mode 100644
index 00000000..722a71a2
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureMargin-124.md
@@ -0,0 +1,173 @@
+# Collatz Pressure Margin - Checkpoint 124
+
+Checkpoint 124 investigates whether selected pressure depths form a prefix.
+
+The tempting conjecture was:
+
+```text
+deep selected pressure
+  -> shallow selected pressure
+```
+
+Checkpoint 124 does not prove this.  Instead, it separates what is now proved
+from what fails experimentally.
+
+## Retention Nesting
+
+Checkpoint 123 proved nesting for continuation carriers.  Checkpoint 124 adds
+the retention counterpart.
+
+Pointwise theorem:
+
+```lean
+retention_allOnes_mod_pow_two_of_le
+```
+
+Source count theorem:
+
+```lean
+sourceRetentionMass_anti_mono_depth
+```
+
+Tail count theorem:
+
+```lean
+tailRetentionMass_anti_mono_depth
+```
+
+Together these say:
+
+```text
+deeper all-ones retention mass <= shallower all-ones retention mass
+```
+
+This is a carrier inclusion theorem, not a pressure theorem.
+
+## Pressure Margin
+
+Pressure is a ratio condition:
+
+```text
+retention mass < 2 * continuation mass
+```
+
+To avoid truncated natural subtraction, checkpoint 124 introduces the
+integer-valued margin:
+
+```lean
+SourcePressureMarginInt
+```
+
+with bridge theorem:
+
+```lean
+isSourcePressureDepth_iff_margin_pos
+```
+
+Meaning:
+
+```text
+IsSourcePressureDepth n k r j
+  <-> 0 < SourcePressureMarginInt n k (r+j)
+```
+
+This is the correct API for future pressure-prefix and pressure-frontier
+experiments.
+
+## Prefix Predicate
+
+Checkpoint 124 also adds a thin predicate:
+
+```lean
+SelectedPressurePrefix
+```
+
+Basic API:
+
+```lean
+selectedPressurePrefix_zero
+selectedPressurePrefix_le_len
+isSourcePressureDepth_of_selectedPressurePrefix
+selectedPressurePrefix_of_pressureOnRange
+```
+
+This is intentionally light.  It records what a prefix means, but it does not
+claim that arbitrary selected depths automatically form a prefix.
+
+## Python Prefix Scan
+
+New experiment:
+
+```text
+python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
+python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.csv
+python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.md
+```
+
+Default scan:
+
+```text
+odd n <= 9999
+steps = 128
+r_start = 2
+depth_len = 10
+depths 2..11
+```
+
+Observed:
+
+```text
+rows: 5000
+nonempty selected rows: 2681
+nonempty prefix rows: 2492 / 2681
+prefix failure rows: 189
+max selected count: 10
+max selected depth: 11
+max frontier depth: 12
+```
+
+Example failure:
+
+```text
+n = 1567
+selected depths: 3
+missing depth: 2
+margins: 2:-2; 3:1; 4:0; 5:-1; ...
+```
+
+This shows that the checkpoint 123 prefix observation was window-limited.
+
+## Interpretation
+
+The proved theorem is:
+
+```text
+carrier nesting
+```
+
+The disproved or unsupported theorem is:
+
+```text
+unconditional pressure prefix
+```
+
+The reason is that pressure is a comparison between two nested quantities.
+Both continuation and retention masses shrink with depth, but their ratio need
+not be monotone.
+
+The next useful theorem should therefore be conditional:
+
+```text
+deep positive pressure margin
+  + margin/retention control between shallow and deep layers
+  -> shallow selected pressure
+```
+
+or it should explicitly formalize the obstruction:
+
+```text
+deeper pressure can be positive while shallower pressure margin is nonpositive
+```
+
+Checkpoint 124 therefore redirects the path from an unconditional prefix theorem
+to margin-controlled pressure-frontier theory.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-124.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-124.md
new file mode 100644
index 00000000..5f619ac4
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-124.md
@@ -0,0 +1,178 @@
+# Report Petal 124
+
+## Goal
+
+Checkpoint 124 asked whether a deeper selected source pressure depth forces
+shallower selected source pressure.
+
+The planned path was:
+
+```text
+1. prove retention nesting
+2. express pressure by an integer margin
+3. test the pressure-prefix theorem carefully
+```
+
+## Lean Result
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Retention pointwise theorem:
+
+```lean
+retention_allOnes_mod_pow_two_of_le
+```
+
+Retention count anti-monotonicity:
+
+```lean
+sourceRetentionMass_anti_mono_depth
+tailRetentionMass_anti_mono_depth
+```
+
+Pressure margin API:
+
+```lean
+SourcePressureMarginInt
+isSourcePressureDepth_iff_margin_pos
+```
+
+Prefix API:
+
+```lean
+SelectedPressurePrefix
+selectedPressurePrefix_zero
+selectedPressurePrefix_le_len
+isSourcePressureDepth_of_selectedPressurePrefix
+selectedPressurePrefix_of_pressureOnRange
+```
+
+The Lean result deliberately does not claim unconditional pressure-prefix
+monotonicity.
+
+## Experiment
+
+Added:
+
+```text
+python/Collatz/PetalBridge/selected_pressure_prefix_scan.py
+```
+
+Generated:
+
+```text
+python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.csv
+python/Collatz/PetalBridge/results/selected_pressure_prefix_scan.md
+```
+
+Scan:
+
+```text
+odd n <= 9999
+steps = 128
+r_start = 2
+depth_len = 10
+```
+
+Result:
+
+```text
+rows: 5000
+nonempty selected rows: 2681
+nonempty prefix rows: 2492 / 2681
+prefix failure rows: 189
+max selected count: 10
+max selected depth: 11
+max frontier depth: 12
+```
+
+First observed failure:
+
+```text
+n = 1567
+selected depths: 3
+missing selected depth: 2
+margin profile:
+2:-2; 3:1; 4:0; 5:-1; 6:0; 7:0; 8:0; 9:0; 10:0; 11:0
+```
+
+This means:
+
+```text
+IsSourcePressureDepth at depth 3 is true
+IsSourcePressureDepth at depth 2 is false
+```
+
+in that finite observation window.
+
+## Interpretation
+
+Checkpoint 123 proved continuation carrier nesting.
+
+Checkpoint 124 proves retention carrier nesting.
+
+But pressure is a ratio:
+
+```text
+retention < 2 * continuation
+```
+
+So carrier nesting alone does not imply selected-pressure prefix behavior.
+The wider Python scan shows concrete finite-window failures of the naive prefix
+hypothesis.
+
+## Next Implementation Candidate
+
+The next checkpoint should avoid the unconditional theorem:
+
+```text
+deep selected pressure -> shallow selected pressure
+```
+
+Better targets:
+
+```lean
+def SourcePressureFrontier ...
+def SourcePressureMarginDropControlled ...
+```
+
+or obstruction-facing theorems:
+
+```text
+positive deep margin and nonpositive shallow margin
+  -> pressure-prefix obstruction
+```
+
+The immediate Lean-friendly next step is probably a thin obstruction predicate:
+
+```lean
+def SourcePressurePrefixFailure
+    (n : OddNat) (k r j1 j2 : ℕ) : Prop :=
+  j1 < j2 ∧
+    ¬ IsSourcePressureDepth n k r j1 ∧
+    IsSourcePressureDepth n k r j2
+```
+
+Then connect it to margins:
+
+```text
+SourcePressurePrefixFailure
+  <-> shallow margin <= 0 and deep margin > 0
+```
+
+This would turn the failed prefix theorem into a useful diagnostic surface.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" lean/dk_math/DkMath/Collatz/PetalBridge.lean  # no output
+git diff --check -- touched files
+```
````
`````
