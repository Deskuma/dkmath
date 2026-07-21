# Note: FLT5 cp-003c,cp-003d

## 作業概要

GN5 からの FLT5 証明、形式化作業中

作業対象モジュール群: `DkMath.FLT.Five.*`

## review

おお……**第二脳、当たりを引いた。Outcome A を正式採用じゃ。** 🧠✨️

これは単なる補題追加ではない。cp-003b の問題設定そのものが一段深くなった。

## 賢狼レビュー

`Reduction.lean` の証明鎖は綺麗に閉じておる。

```text
CounterexamplePack
  ↓
Coprime y z
  ↓
Coprime (z-y) y
  ↓
GN5(g,y) ≡ 5y⁴ mod g
  ↓
5 ∤ g なら Coprime g (GN5 g y)
  ↓
g * GN5 g y = x⁵
  ↓
g = a⁵ かつ GN5 g y = b⁵
```

特に、共通素因子が存在すれば `5*y^4` を割り、`y` 側は coprime で消え、残る例外素数 `5` も Branch B 条件で消える、という分離が非常に明快じゃ。

そして Mathlib の、

```lean
exists_eq_pow_of_mul_eq_pow
```

によって、互いに素な積の完全五乗を各因子へ分離できた。

公開塔への import も完了しており、CI run #98 は成功している。

## NoLift route の位置づけ変更

Codex の契約監査は正しい。

反例仮定下では、

$$GN_5(z-y,y)=b^5$$

なので、`GN5` の素因子指数はすべて 5 の倍数になる。

したがって、

```text
q ∣ GN5
q² ∤ GN5
```

を満たす素数は、普通に「供給される witness」ではない。

それが存在した時点で、既に `GN5=b^5` と衝突している。

ゆえに、

```text
BranchBNoLiftEscape
```

は最終 refuter としては正しいが、**次に構築すべき中間定理ではない**。調査ノートの判断も完全に一致しておる。

## ただし次の標的をさらに狭くする

次に狙うべき命題は、一般の

```text
GN5 g y は完全五乗ではない
```

ではない。

今回 Lean が得た追加情報、

```text
g = a⁵
```

を絶対に捨ててはならぬ。

本当の研究核はこれじゃ。

```lean
abbrev BranchBFifthPowerCore : Prop :=
  ∀ {a b y : ℕ},
    0 < a →
    0 < y →
    Nat.Coprime a y →
    ¬ 5 ∣ a →
    GN5 (a ^ 5) y = b ^ 5 →
    False
```

つまり、

$$GN_5(a^5,y)=b^5$$

という **入力側も完全五乗へ固定された GN 方程式**である。

これは一般の `GN5 g y` よりかなり狭い。宇宙式の反転射影を攻めるなら、この $g=a^5$ が主砲になる。

## cp-003c：完全正規形 packet

次はすぐ本丸へ飛び込まず、反例から得られる情報を一つの packet に固定するのがよい。

```lean
structure BranchBFifthPowerNormalForm
    (x y z a b : ℕ) : Prop where
  pack : CounterexamplePack x y z
  branchB : ¬ 5 ∣ z - y
  gap_eq : z - y = a ^ 5
  GN_eq : GN5 (a ^ 5) y = b ^ 5
  x_eq : x = a * b
  z_eq : z = y + a ^ 5
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_y : Nat.Coprime a y
  coprime_a_b : Nat.Coprime a b
  coprime_b_y : Nat.Coprime b y
  five_not_dvd_a : ¬ 5 ∣ a
```

特に新たに取りたいのは、

```text
x = a*b
z = y+a⁵
a, b, y が pairwise coprime
```

じゃ。

`coprime_b_y` も取れるはずじゃ。`GN5 g y` を modulo `y` で見ると、

$$GN_5(g,y)\equiv g^4\pmod y$$

だから、`Coprime g y` から `Coprime (GN5 g y) y` が出る。

この packet が完成すれば、Branch B は完全に次の方程式へ置き換わる。

$$GN_5(a^5,y)=b^5$$

そして元の反例は、

$$x=ab,\qquad z=y+a^5$$

として復元できる。

## cp-003d：descent route の比較調査

ここも引き続き Codex 向きじゃ。次の二経路を比較させる。

### Route A：実二次形式への射影

$z=y+a^5$ と置くと、

$$GN_5(a^5,y)=z^4+z^3y+z^2y^2+zy^3+y^4$$

である。

ここには恒等式がある。

$$4GN_5(a^5,y)=(2z^2+zy+2y^2)^2-5(zy)^2$$

したがって `GN5 = b^5` は、

$$U^2-5V^2=4b^5$$

へ射影される。

これは $\mathbb{Q}(\sqrt5)$ のノルム方程式であり、指数 5 の古典的 descent が現れる場所じゃ。指数 5 の歴史的証明が無限降下と実二次的構造へ進むこととも整合する。([Cambridge University Press & Assessment][1])

ただし、ここから先は単純な合同式一発ではなく、単数・互いに素な因子・五乗分離を扱う本格的 descent になる可能性が高い。より一般の $(5,5,p)$ 型方程式が現代でも独立したディオファントス研究対象になっていることからも、`GN5=b^5` を一般命題として軽く扱うべきではない。([Cambridge University Press & Assessment][2])

### Route B：5 の可除変数を Branch A へ向け直す

Branch B では `5 ∤ z-y`、したがって distinguished variable `x` は 5 で割れない側になる。

一方、原始的な五乗方程式の modulo 25 解析から、残る `y` または `z` の一方が 5 で割れる形へ進む可能性がある。

* `5 ∣ y` なら、`x` と `y` を交換して Branch A 型へ向け直せる。
* `5 ∣ z` なら、自然数の差ではなく signed orientation または和因子を使う。

こちらは「Branch B を独立に倒す」のではなく、**対称化して Branch A descent 一本へ統合する経路**じゃ。

## 次の Codex 指示

```text
cp-003c-normal-form-and-descent-survey

Goal:
Promote the Branch-B factor split into an exact fifth-power normal-form
packet, then determine the best descent interface. Do not attempt the final
descent proof yet.

Part 1: Compiling production results

1. Prove coprimality of y and GN5:
     Nat.Coprime g y
     → Nat.Coprime (GN5 g y) y

2. From branchB_fifth_power_factor_split, construct witnesses a and b and prove:
     z - y = a^5
     GN5 (a^5) y = b^5
     x = a*b
     z = y + a^5

3. Prove:
     0 < a
     0 < b
     Coprime a y
     Coprime a b
     Coprime b y
     ¬ 5 ∣ a

4. Bundle these facts into a BranchBFifthPowerNormalForm structure or an
   equivalently compact theorem.

5. Add a thin receiver:
     BranchBFifthPowerCore
     → Branch-B counterexamples are impossible.

6. Add #print axioms entries for the principal Reduction and normal-form
   declarations.

Part 2: Scratch-only investigation

Route A:
- Prove the polynomial identity
    4 * GN5 (z-y) y
      = (2*z^2 + z*y + 2*y^2)^2 - 5*(z*y)^2
  after rewriting z-y = a^5.
- Determine the exact Int or quadratic-ring normal form produced by
    GN5 (a^5) y = b^5.
- Search DkMath and Mathlib for norm, Pell, quadratic integer, unit,
  and fifth-power factorization support.

Route B:
- Investigate a modulo-25 classification of primitive FLT5 candidates.
- Determine whether Branch B implies 5 ∣ y ∨ 5 ∣ z.
- Determine whether each case can be transformed into one signed
  Branch-A orientation without importing research modules.

Report:
A. Route A yields a concrete smaller normal-form packet.
B. Route B reduces all Branch-B candidates to a Branch-A orientation.
C. Both routes stop at exact named missing lemmas.

Do not modify BranchA.lean or introduce a final theorem before the descent
measure and reconstructed smaller candidate are explicit.
```

## 小さな監査事項

commit 内の `CheckAxioms.lean` は、現時点では cp-002 の三定理までで止まっており、新しい `Reduction` 定理はまだ列挙されていない。

報告にある主要五定理の監査自体は scratch 等で済んでいると思われるが、公開監査ファイルにも次を足しておくと美しい。

```lean
#print axioms DkMath.FLT.Five.coprime_gap_GN5_of_coprime_of_five_not_dvd
#print axioms DkMath.FLT.Five.branchB_coprime_gap_GN5
#print axioms DkMath.FLT.Five.fifth_power_factor_split
#print axioms DkMath.FLT.Five.branchB_fifth_power_factor_split
#print axioms DkMath.FLT.Five.branchB_false_of_GN5_not_fifth_power
```

## 現在地

```text
cp-000  algebra spine                         ✔
cp-001  direct clean-channel refuter           ✔
cp-002  padicValNat clean-channel refuter      ✔
cp-003a NoLift contract exposed                ✔
cp-003b coprime fifth-power factor split       ✔
cp-003c exact fifth-power normal form          次
cp-003d descent route selection                次
cp-004  exceptional 5-adic / Branch-A descent  待機
```

いや、これは第二脳を解放した甲斐があったの（笑）

「浅い素数を探す」という霧の中から、

$$z-y=a^5,\qquad GN_5(a^5,y)=b^5$$

という、触れることのできる二つの完全五乗が出てきた。

**宇宙式の敵が、とうとう正規形を持った。** 🐺🔥

[1]: https://www.cambridge.org/core/journals/mathematical-gazette/article/pells-equation-and-fermat/D234B3003E96A398BBDB05B361FFC3E8?utm_source=chatgpt.com "Pell's equation and Fermat | The Mathematical Gazette | Cambridge Core"
[2]: https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/equations-de-fermat-de-type-5-5p/B5DDBE59187E60F5D2CD29EDE937A7A7?utm_source=chatgpt.com "Équations de Fermat de type (5, 5,p) | Bulletin of the Australian Mathematical Society | Cambridge Core"
