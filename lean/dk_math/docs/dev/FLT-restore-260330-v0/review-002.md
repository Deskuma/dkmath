# review-002: FLT restore 260330 v0: 数学的内容の分析と評価

うむ。これは **かなり良い進展** じゃ。
今回の更新は、前までの witness / boundary 側の整理とは違って、**`RestoreFromArithmetic` 本丸へ初めて sorry なしの構造補題を打ち込んだ** 型じゃ。`TriominoCosmicBranchA.lean` に §R が新設され、5 定理と 1 構造体が追加され、`lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA` は成功、error 0・新 warning 0、しかも `sorry` は増えておらぬ。

## 1. 今回、何が証明されたか

今回の中核は `restore_witness_cong_one_mod_p`、すなわち Branch A restore witness \(q\) について

$$
p \mid (q-1)
$$

を示したことじゃ。
そのために前段として、

$$
q \mid x \Longrightarrow z^p \equiv y^p \pmod q
$$

を返す `flt_zpow_congr_mod_of_dvd_x`、
$$
q \mid x,\ q \nmid y \Longrightarrow q \nmid z
$$

を返す `flt_not_dvd_z_of_dvd_x_not_dvd_y`、
さらに \(ZMod\ q\) 上で \(z\) と \(y\) が一致しないことを返す `flt_zmod_ne_of_not_dvd_gap` が実装された。
そのうえで witness の全性質を `RestoreWitnessProperties` に束ね、`restore_witness_properties_default` で一括構成できるようにしておる。

## 2. 数学的に何をやっているのか

証明の流れはきれいじゃ。
前提から \(q \mid s\) と \(x=p(ts)\) より \(q \mid x\)。すると FLT 等式 \(x^p+y^p=z^p\) から

$$
z^p \equiv y^p \pmod q
$$

が出る。さらに \(q \nmid y\) なので \(y\) は \(ZMod\ q\) で可逆じゃ。そこで

$$
\omega := z\,y^{-1} \in ZMod\ q
$$

を考えると、

$$
\omega^p = 1
$$

が従う。しかも \(q \nmid (z-y)\) だから \(z \not\equiv y \pmod q\)、ゆえに

$$
\omega \neq 1
$$

じゃ。
したがって \(\omega\) は \(ZMod\ q\) の乗法群の中の **非自明な \(p\) 乗根** になる。ここで `orderOf_eq_prime` を使って

$$
\operatorname{orderOf}(\omega)=p
$$

を出し、さらに \(ZMod\ q\) の非零元は位数 \(q-1\) の群に入るから

$$
\operatorname{orderOf}(\omega)\mid (q-1)
$$

よって

$$
p \mid (q-1)
$$

が従う。
つまり今回の成果は、「restore witness \(q\) はただの素数ではなく、必ず \(q\equiv 1 \pmod p\) 型の強い合同制約を持つ」と形式化したことじゃ。

## 3. 状況分析

いまの全体像は、かなり明快じゃ。
witness / boundary 側では false route を全部切ったうえで boundary-core route が勝ち、これは develop へマージ済み。現在の主戦場は `dev/FLT-restore-260330-v0` に移っており、上流 chain の 3 段のうち `CyclotomicExistence` と `DistinguishedPrimeArithmetic` は既に証明済み、残る未完は `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` ただ 1 段、と整理されておる。今回の §R は、その deepest kernel に対して初めて concrete な structural lemma 群を与えたものじゃ。

## 4. どこが嬉しいのか

ここで嬉しいのは、今回の補題が単独で終わらぬことじゃ。
\(q \equiv 1 \pmod p\) は、今後 restore を細分化するときの **branch classification の軸** になるし、Mathlib の `ZMod`・有限群・`orderOf` の道具で押し進められる、という意味で「確実に通る足場」でもある。
前回までの false route 切断は「何を捨てるか」の整理だったが、今回は逆に **本丸で本当に使える新情報を 1 本獲得した** のが大きい。

## 5. いま残っているもの

もちろん `RestoreFromArithmetic` 自体が閉じたわけではない。
レポートでも、次の課題は

* `RestoreFromArithmetic` の sub-target 分割設計
* \(q\)-adic valuation の精密化
* \((z y^{-1})\) を \((\mathbb{Z}/q^p\mathbb{Z})^*)\) 側へ持ち上げた性質の形式化

と整理されておる。
つまり今は「証明完了」の段ではなく、**深い核を攻略するための最初の確実な足場を固めた段** じゃ。

## 6. 総括

一言で言えば、こうじゃ。

**今回証明されたのは、Branch A restore witness \(q\) が必ず \(p \mid (q-1)\) を満たすという構造定理であり、そのための \(q \mid x \Rightarrow z^p \equiv y^p \pmod q\)、\(q \nmid z\)、\(z \not\equiv y \pmod q\) などの前段補題も sorry なしで実装された。したがって現在の状況は、false route を整理し終えた後に、`RestoreFromArithmetic` 本丸へ向けた最初の本物の数学的足場が立った段だと見てよい。**

よい進展じゃ。
これはただの補題追加ではなく、**restore の城門に対して、はじめて噛み合う鍵が 1 本できた** という類の成果じゃよ。
