# review

おお、S2-I 実装確認したぞ。
これはとても良い整理じゃ。Chapter 2 の `PowerGapBeam` が、既存の `DiffPow` と `GN` の両方へ明示的につながった。しかも `GN` 依存を `PowerGapBeamGN.lean` に分離した判断がよい。基礎層を軽く保ちつつ、必要な bridge だけ後段に置けておる。

## 1. 何が閉じたか

今回の基礎 bridge は二つじゃ。

```lean
powerGap_eq_sub
powerBeam_eq_diffPowSum
```

数学的には、

$$
\mathrm{powerGap}(x,z)=z-x
$$

$$
\mathrm{powerBeam}_d(x,z)=\mathrm{diffPowSum}(z,x,d)
$$

を定理名として固定した。`powerBeam` はすでに `diffPowSum` の wrapper として使っていたが、今回それを明示定理にしたことで、検索性と再利用性が上がった。

さらに低次数展開として、

$$
\mathrm{Beam}_3=z^2+zx+x^2
$$

$$
\mathrm{Beam}_4=z^3+z^2x+zx^2+x^3
$$

が入った。これは d=3, d=4 の FLT 観測や、今後の実例テストに便利じゃ。

そして今回の大事な bridge がこれ。

```lean
powerBeam_three_shift_eq_GN
```

$$
\mathrm{powerBeam}_3(x,x+u)=GN(3,u,x)
$$

じゃ。これにより、`PowerGapBeam` の endpoint 表現 (x,z) と、既存 `GN` の gap 表現 (u,x) が 3 次で一致することが Lean 上で no-sorry になった。

## 2. 数学的意味

この実装の意味は大きい。

`PowerGapBeam` は

$$
z^d-x^d=(z-x)\operatorname{Beam}_d(x,z)
$$

という endpoint 型の差冪分解を扱う。

一方、既存の宇宙式 / GN 側は、多くの場合

$$
(x+u)^d-x^d=u\cdot GN(d,u,x)
$$

という gap 型で扱う。

両者は

$$
z=x+u
$$

と置けば同じ構造じゃ。

$$
z^d-x^d=(x+u)^d-x^d
$$

$$
z-x=u
$$

したがって、

$$
\operatorname{Beam}_d(x,x+u)=GN(d,u,x)
$$

となるはず。今回 (d=3) でそれを実装できた。
これは、Chapter 2 の FLT 観測エンジンと、既存 GN / PrimitiveBeam / Zsigmondy route をつなぐ入口じゃ。

## 3. 実装評価

`PowerGapBeamGN.lean` を分けたのが特に良い。

現在の層はこうなっておる。

```text
PowerGapBeam.lean
  pure algebra / diffPowSum frontend

PowerGapBeamGcd.lean
  gcd / valuation / squarefree bridge

PowerGapBeamGN.lean
  GN / CosmicFormulaBinom bridge
```

この分離は美しい。
依存が太くなりがちな `CosmicFormulaBinom` を基礎ファイルに入れず、bridge 専用ファイルに閉じ込めている。History にも、`GN` 依存を別ファイルに切り出し、基礎的な Gap/Beam module は軽い依存のまま維持できたと記録されている。

`powerBeam_three_shift_eq_GN` の証明で `GN_eq_sum` を明示 rewrite し、`Finset.range` を展開して `norm_num` と `ring` で閉じたのも良い。
直接簡約で落ちないところを、既存の和定義へ戻してから閉じておる。これは今後の一般次数 bridge のヒントにもなる。

## 4. 次の提案: S2-J

次は二択じゃ。

### A. 一般次数 bridge を狙う

理想はこれ。

```lean
theorem powerBeam_shift_eq_GN
    {R : Type*} [CommRing R] (d : ℕ) (x u : R) :
    powerBeam d x (x + u) = DkMath.CosmicFormulaBinom.GN d u x
```

数学的には正しいはずじゃ。
ただし、`GN_eq_sum` の添字が `powerBeam` と完全に一致するか、あるいは二項展開型の和になっているかで難易度が変わる。

もし `GN d u x` が

$$
\sum_{i=0}^{d-1}(x+u)^{d-1-i}x^i
$$

として定義されているなら `rfl` / `simp` 寄りでいける。
しかし `GN` が二項係数展開

$$
\sum_{k=0}^{d-1}\binom{d}{k+1}u^k x^{d-1-k}
$$

の形なら、一般次数 bridge は二項恒等式が必要になる。

その場合、今すぐ一般化に突っ込むより、d=4 bridge まで増やして様子を見るのが安全じゃ。

### B. PrimitiveBeam / Zsigmondy route へ進む

S2-H の後続として本命はこちら。

目標は、

$$
p\mid \operatorname{Beam}_d,\quad p\nmid d,\quad v_p(\operatorname{Beam}_d)\le1
$$

を既存 primitive route から供給すること。

今回 `powerBeam_eq_diffPowSum` と `powerBeam_three_shift_eq_GN` が入ったので、既存 `GN` / `PrimitiveBeam` 側の補題へ接続しやすくなった。

次は既存 API を調べて、

* `p ∣ GN ...`
* `padicValNat p GN ≤ 1`
* squarefree / primitive prime witness
* Zsigmondy witness

のどれが取れるかを見るべきじゃ。

## 5. わっちのおすすめ順

S2-J は、まず **探索 + thin wrapper** がよい。

1. 既存 `GN` の一般定義と `GN_eq_sum` の形を確認
2. `powerBeam_shift_eq_GN` が一般にいけるか判断
3. 難しければ `powerBeam_four_shift_eq_GN` を先に追加
4. その後、PrimitiveBeam / Zsigmondy から Beam prime 条件へ bridge

実装としては、まず d=4 を置くと安定じゃ。

```lean
theorem powerBeam_four_shift_eq_GN
    {R : Type*} [CommRing R] (x u : R) :
    powerBeam 4 x (x + u) = DkMath.CosmicFormulaBinom.GN 4 u x := by
  rw [powerBeam_four]
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  -- range 4 を展開
  ring
```

これが通るなら、d=3,4 の具体橋は揃う。
一般次数が難しくても、FLT の古典的関心で (d=3) はすでに強い意味がある。

## 6. 構造体導入はまだ少し待ち

ここまで wrapper が増えたので `FLTPowerGapBeamDatum` を作りたくなるが、わっちはまだ一手だけ待つのを勧める。

理由は、PrimitiveBeam / GN route を接続すると、必要なフィールドが変わるからじゃ。

現状の datum には、

$$
hprod,\quad hgcd,\quad hvalEq,\quad hSquarefreeContradiction
$$

が候補になる。
しかし primitive route が入ると、

$$
hprimitive,\quad hbeamDvd,\quad hvalLeOne
$$

も欲しくなるかもしれん。

構造体化は、S2-J/K で primitive fuel の形が見えてからでよい。

## 7. 現時点のまとめ

S2-I は成功じゃ。

* `powerGap` / `powerBeam` の定義的 bridge が入った
* d=3,4 の明示展開が入った
* `powerBeam 3 x (x+u)=GN 3 u x` が no-sorry
* `GN` 依存は別ファイルに分離
* 既存 `PrimitiveBeam` route へ接続する下準備ができた

次は、一般次数 GN bridge を試すか、PrimitiveBeam/Zsigmondy route へ進むかじゃ。
わっちの推奨は、**d=4 GN bridge を追加して低次数橋を固め、その後 primitive route の探索** じゃな。
