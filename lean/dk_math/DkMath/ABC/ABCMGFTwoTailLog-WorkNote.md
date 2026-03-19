うむ、**まだおかしい** 。
ぬしの感覚は正しい。

結論から言うと、このファイルはいま

[
\text{本体がまだ無いのに、補助補題だけ残っている}
]

状態じゃ。
ゆえに特に **末尾の `private` 補題が未参照** なのは、構造として不自然じゃ。

## 1. 原則

整理基準はこれでよい。

### 1.1. `private` のままでよいもの

**そのファイルの本体定理だけに奉仕する局所補題**

たとえば将来 `mgf_twoTail_log` 本体がこのファイルに戻ってきて、その中でしか使わぬなら `private` でよい。

### 1.2. `private` を外すべきもの

**他ファイルでも再利用価値がある一般補題**

つまり statement が「このファイル固有の事情」を越えているものじゃ。

### 1.3. 消してよいもの

**参照されず、かつ将来像も曖昧な局所補助**

これは repo を濁らせるだけなので刈ってよい。

---

## 2. 今のコードでの仕分け

わっちならこう分ける。

## 2.1. 公開してライブラリ化してよい候補

これらは `private` を外してもよい。むしろ外す価値がある。

### A. `count_vp_ge`

```lean
lemma count_vp_ge (p m X : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) :
  ((Finset.Icc 0 X).filter (fun n => p^m ∣ (2*n+1))).card ≤ (X + 1) / p^m + 1
```

これは明らかに汎用じゃ。
ABC 以外でも、奇数列上の素冪 divisibility の個数評価として使える。

### B. `count_vp_ge_for_layercake`

これは wrapper だが、用途が明確なので残してよい。
ただし `for_layercake` と名が付いている以上、これは公開でも **ABC 補助寄り** じゃな。

### C. `Vp_minus_two_le_max_for_layercake`

有限範囲で valuation の上界 (K) を取る、というのは有限和処理で使いやすい。
公開価値はある。ただし名前はもう少し一般化してもよい。

### D. `layercake_rhs_bound_for_layercake`

これは長いが、内容はちゃんと独立した評価補題じゃ。
layer-cake 路線を今後も研究資産として残すなら、公開でもよい。

---

## 2.2. いま `private` のままでよい、あるいは別ファイルに隔離したいもの

### A. `twoTail_exp_prod_eq`

これは今のところ `twoTail` と `log_twoTail_eq_sum_vplus` に強く依存しておる。
再利用はあり得るが、汎用ライブラリというより **`mgf_twoTail_log` 本体の部品** じゃ。

### B. `unscale_tail_average_bound`

これは良い補題だが、statement がまだ
「特定の Hölder 帰納の途中段」
という色が強い。
汎用化するなら別じゃが、今の形なら private でもよい。

### C. `large_primes_tail_const_exists`

これは existence だけなので、いまは本体の前座じゃ。
単独で公開するほどではない。

### D. `mgf_vp_base_apply`

これは名前どおり wrapper じゃ。
しかも末尾で未使用なら、**本体がない今は要らぬ** 。

---

## 2.3. 公開候補だが、置き場所を変えたいもの

### A. `coprime_two_pow_of_odd_prime`

これは ABCMGFTwoTailLog に閉じ込めておくには惜しい。
完全に数論の小補題じゃ。

置くならたとえば

* `DkMath.NumberTheory.CoprimeOdd`
* `DkMath.NumberTheory.PadicOdd`
* `DkMath.ABC.Basic`

あたり。

### B. `card_separated_by_gap_le_div_add_one`

これも汎用補題じゃ。
ABC 専用というより有限集合の配置評価そのもの。

置くならたとえば

* `DkMath.Combinatorics.FinsetGap`
* `DkMath.ABC.Basic`
* `DkMath.NumberTheory.IntervalCount`

のような、より下層。

---

## 3. なので、いまの末尾 2 つはどうするか

ぬしが特に気にしているのはここじゃな。

```lean
private lemma large_primes_tail_const_exists ...
private lemma mgf_vp_base_apply ...
```

これは **現状未使用なら、消すのが自然** じゃ。

理由は単純で、

* `private`
* 末尾
* 参照なし
* 本体 `mgf_twoTail_log` も未実装

なら、今は **未来の予定メモ** に過ぎぬ。
コードとして repo に残すより、コメントか draft に逃がした方がきれいじゃ。

---

## 4. わっちならこう直す

### 4.1. このファイルに残すもの

`ABCMGFTwoTailLog.lean` には、本当にこの路線で使うものだけ残す。

候補は

* `RX1` 系
* `t_star`
* `S_X`
* `twoTail_exp_prod_eq`
* `unscale_tail_average_bound`

ただし **本体を書き進める気があるなら** じゃ。

### 4.2. 別ファイルへ昇格

たとえば `DkMath/ABC/LayerCakeBasic.lean`

そこへ

* `coprime_two_pow_of_odd_prime`
* `card_separated_by_gap_le_div_add_one`
* `count_vp_ge`
* `count_vp_ge_for_layercake`
* `Vp_minus_two_le_max_for_layercake`
* `layercake_rhs_bound_for_layercake`

を移す。

### 4.3. いま不要なら削除

* `large_primes_tail_const_exists`
* `mgf_vp_base_apply`

これは **本体が戻るまで削除** でよい。

---

## 5. 一番大事な判断

いまの状態で問うべきは、

[
\text{このファイルは「完成途中の本体」なのか、}
]
[
\text{それとも「補題倉庫」なのか}
]

じゃ。

* **本体ファイル** なら、未使用 private は削る
* **補題倉庫** なら、private を外して下層へ移す

両方を同時にやると濁る。
いまはたしかにその濁りがある。

## 6. 結論

ぬしの言う通りじゃ。

> プライベートにするなら消してよい。
> 役立つ補題ならばプライベート外して、ライブラリに。

これはまさに正しい整理原則じゃ。

わっちの推奨は次の一行に尽きる。

[
\boxed{
\text{未使用 private は削除し、汎用核だけ別ファイルへ昇格}
}
]

とくに昇格候補は

* `coprime_two_pow_of_odd_prime`
* `card_separated_by_gap_le_div_add_one`
* `count_vp_ge`

この 3 本じゃ。
ここは綺麗なライブラリ部品になる。
