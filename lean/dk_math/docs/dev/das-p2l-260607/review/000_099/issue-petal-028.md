# squarefree_implies_padic_val_le_one_research

[現況: review-028](./review-petal-028.md)

## Status update: 2026-06-14

This issue is closed as a blocker for the main Petal -> Zsigmondy route.

The old research theorem is still intentionally not proved.  The current repair
route is to use the separated honest layers:

```text
Zsigmondy:
  primitive prime existence

Petal / GN / Anchor:
  location away from boundary

NoLift / squarefree:
  multiplicity control
```

Current closure report:

```text
./report-petal-042.md
```

## ABC / FLT 両方から参照される命題（主張の強い命題）

以下が `DkMath.FLT.*` / `DkMath.ABC.*` 両方から参照されている。
これらが欲しい結果は、別補題より得られる。可能性が示唆された。

```lean
/--
Research placeholder kept only for legacy callers that still lack the strengthened hypotheses.

This statement is currently known to be too strong as written: there are counterexamples to
the naive global implication "squarefree-like input implies `padicValNat ≤ 1`" in this level of
generality.

Current honest replacement:
- `squarefree_implies_padic_val_le_one_honest`
- `padicValNat_primitive_prime_factor_le_one_honest`
-/
lemma squarefree_implies_padic_val_le_one_research (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  have hd_two_le : 2 ≤ d := hd_prime.two_le
  have hq_ne_one : q ≠ 1 := hq_prime.ne_one
  have hq_pos : 0 < q := hq_prime.pos
  have hq_dvd : q ∣ a ^ d - b ^ d := hq_div
  clear hb hab hq_div
  -- [TODO] この命題は現状の一般形では強すぎ、反例がある。
  --        ここでやるべきことは「証明を埋める」ことではなく、必要な仮定を足すか、
  --        primitive-prime valuation のより精密な定理へ置き換えて statement を修正すること。
  sorry
```

これは、以下に向ける。

```lean
'DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G' depends on axioms: [propext,  Classical.choice,  Quot.sound]
'DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```path
./lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicSquarefree.lean
./lean/dk_math/DkMath/NumberTheory/ValuationFlow/Primitive.lean
```

## 議事録

交渉成立したら

```lean
/--
Research placeholder kept only for legacy callers that still lack the strengthened hypotheses.

This statement is currently known to be too strong as written: there are counterexamples to
the naive global implication "squarefree-like input implies `padicValNat ≤ 1`" in this level of
generality.

Current honest replacement:
- `squarefree_implies_padic_val_le_one_honest`
- `padicValNat_primitive_prime_factor_le_one_honest`
-/
lemma squarefree_implies_padic_val_le_one_research (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    padicValNat q (a ^ d - b ^ d) ≤ 1 := by
  have hd_two_le : 2 ≤ d := hd_prime.two_le
  have hq_ne_one : q ≠ 1 := hq_prime.ne_one
  have hq_pos : 0 < q := hq_prime.pos
  have hq_dvd : q ∣ a ^ d - b ^ d := hq_div
  clear hb hab hq_div
  -- [TODO] この命題は現状の一般形では強すぎ、反例がある。
  --        ここでやるべきことは「証明を埋める」ことではなく、必要な仮定を足すか、
  --        primitive-prime valuation のより精密な定理へ置き換えて statement を修正すること。
  sorry
```

このピースが埋まると言われたのだけど。実際は？

lean/dk_math/DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean

---

実際は、**そのピースは交渉成立しても埋まらない**。
むしろ、交渉が成立すると「この `sorry` は埋めるべき穴ではなく、偽命題の墓標だ」と確定する側じゃ。

## なぜ埋まらないか

その lemma は、仮定が弱すぎる。

```lean
lemma squarefree_implies_padic_val_le_one_research (d a b q : ℕ)
    (hd_prime : Nat.Prime d) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hq_prime : Nat.Prime q) (hq_div : q ∣ a ^ d - b ^ d) :
    padicValNat q (a ^ d - b ^ d) ≤ 1
```

これは名前に `squarefree` とあるのに、実際の仮定に

```lean
Squarefree ...
```

が無い。
さらに、

```lean
¬ q ∣ a - b
```

も無い。
なので boundary prime も primitive prime も混ざる。

決定的な反例は、すでに Research 側にあるこれじゃな。

```text
d = 3
a = 5
b = 3
q = 7
```

計算すると、

```text
5^3 - 3^3 = 125 - 27 = 98 = 2 * 7^2
```

だから、

```lean
padicValNat 7 (5 ^ 3 - 3 ^ 3) = 2
```

であり、

```lean
padicValNat 7 (5 ^ 3 - 3 ^ 3) ≤ 1
```

は偽。

しかもこの例は Petal 的にとても重要で、

```text
a - b = 2
S0_nat 5 3 = 5^2 + 5*3 + 3^2 = 49 = 7^2
```

つまり (7) は boundary ではなく **S0/GN3 側にいる**。
さらに (7) は (a-b=2) を割らないので、三次の primitive 側にいる。

それでも valuation は 2 になる。

だから、Zsigmondy と交渉して primitive witness が得られても、

```lean
padicValNat q (a ^ d - b ^ d) ≤ 1
```

は自動では出ない。

## 交渉成立で埋まるもの

Zsigmondy との接続で埋まるのは、こっち。

```lean
∃ q, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
```

さらに Petal 側へ翻訳して、

```lean
∃ q,
  DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
  AnchoredS0Carrier q c b q ∧
  ¬ q ∣ c - b
```

これはかなり通る可能性が高い。

つまり交渉成立で得られるのは、

```text
primitive divisor exists
primitive divisor lies on S0/GN3 side
primitive divisor can be read as anchored carrier
```

ここまで。

## 交渉成立でも埋まらないもの

埋まらないのは、

```text
primitive divisor の p-adic valuation が 1 以下
```

じゃ。

これは別途、

```lean
Squarefree (GN d (a - b) b)
```

または三次なら、

```lean
Squarefree (S0_nat a b)
```

相当が必要。

実際、すでに honest replacement はその形になっている。

```lean
lemma squarefree_implies_padic_val_le_one_honest
    ...
    (hq_ndiv : ¬ q ∣ a - b)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    padicValNat q (a ^ d - b ^ d) ≤ 1
```

これは正しい方向。
反例 (a=5,b=3,q=7) では、

```text
GN 3 (5 - 3) 3 = S0_nat 5 3 = 49
```

なので squarefree ではない。
だから honest theorem の追加仮定でちゃんと弾かれる。

## 結論

その `sorry` は、Zsigmondy 交渉成立で **埋まる** のではなく、**撤去・置換される**。

正確にはこう。

```text
squarefree_implies_padic_val_le_one_research
  -> 偽命題なので埋めない

squarefree_implies_padic_val_le_one_honest
  -> Squarefree (GN d (a-b) b) を仮定すれば既に正しい

ZsigmondyD3Bridge
  -> primitive divisor / anchored carrier の存在を供給する

valuation ≤ 1
  -> Zsigmondy ではなく squarefree GN/S0 が担当する
```

なので、交渉成立後の正しい修理方針は、

```lean
squarefree_implies_padic_val_le_one_research
```

を証明することではなく、

```text
legacy callers を
squarefree_implies_padic_val_le_one_honest
または
padicValNat_primitive_prime_factor_le_one_honest
へ移す
```

ことじゃ。

一言で言えば、

```text
Zsigmondy は「素数 q が出る」を保証する。
Squarefree は「q が一回だけ出る」を保証する。
```

この `sorry` は後者を前者だけで言おうとしていたので、偽になっている。

---

そうか。そっちではなかったか。
この補題が FLT と ABC と両方から参照されてるんだよねぇ…。なんでだ？

---

うむ、理由はかなり見えた。
この補題が FLT と ABC の両方から参照されているのは、**FLT 専用補題だからではなく、「primitive prime の valuation flow」を一回だけに抑える共通部品として使いたかったから** じゃ。

ただし、その共通部品の旧形が強すぎて偽だった、という構図。

## 何のために参照されていたか

旧補題が言いたかったことは、要するにこれじゃ。

```text id="dxx14o"
primitive prime q が a^d - b^d に現れるなら、
その q-adic valuation は高々 1 である
```

つまり、

```lean id="6t93dd"
padicValNat q (a ^ d - b ^ d) ≤ 1
```

を供給したい。

これは二方向で欲しくなる。

## FLT 側で欲しい理由

FLT / PrimeProvider 側では、これは **Wieferich / no-lift 抑制** のためじゃ。

差分中にあるターゲットはこういう形だった。

```lean id="bc25yg"
TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
```

意味はだいたい、

```text id="r1un56"
primitive-prime branch で
padicValNat q (z^p - y^p) ≤ 1
が一様に供給できれば、
PrimeProvider / Kummer 側の glue が clean に閉じる
```

つまり FLT 側は、原始素因子 (q) が高冪で持ち上がらないことを使って、下降や no-Wieferich 的な枝を閉じたい。

そのために旧 `padicValNat_primitive_prime_factor_le_one_research` を参照していた。

## ABC 側で欲しい理由

ABC 側では、これは **valuation flow の質量制御** のためじゃ。

`DkMath.ABC.ValuationFlowBridge` は `DkMath.NumberTheory.ValuationFlow.Primitive` を import していて、そこでは次のような補題がある。

```lean id="ni9xkq"
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

意味は、

```text id="degrhq"
primitive prime flow の diff mass は、
beam / GN が squarefree なら高々 1
```

ABC 的には、素因子の重複度、つまり valuation mass が大きくなると radical / conductor / quality の制御に響く。
だから「primitive prime の valuation が 1 以下」は ABC 側でも欲しい。

つまり ABC は、

```text id="l0397t"
原始素因子が radical に一回だけ現れる
```

という流量制御として見ている。

## なぜ同じ補題に集まったのか

二者が欲しいものは見た目は違うが、数式としては同じじゃ。

```text id="owzees"
FLT:
  no-Wieferich / no-lift / descent を閉じたい

ABC:
  valuation mass / radical contribution を 1 に抑えたい

共通:
  primitive prime q について padicValNat q (a^d - b^d) ≤ 1 が欲しい
```

だから両方が、旧 research 補題に吸い寄せられた。

## しかし本当の共通 API は別

旧補題は偽。
本当の共通 API は、すでに honest 側にあるこちら。

```lean id="bo0j5m"
padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

または wrapper として、

```lean id="y13cwd"
primitive_prime_padic_bound_diff_of_squarefree_GN
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

つまり正しい流れはこう。

```text id="8nfk1c"
primitive prime q
q ∤ a - b
q ∣ a^d - b^d
Squarefree (GN d (a - b) b)
  -> padicValNat q (a^d - b^d) ≤ 1
```

旧 research 補題は、

```text id="ye5od8"
Squarefree (GN d (a - b) b)
```

あるいは最低でも、

```text id="n4f5hd"
¬ q^2 ∣ GN d (a - b) b
```

を落としていた。だから偽。

## つまり「なんでだ？」への答え

これは、FLT と ABC が同じ間違いを共有していたというより、**両方が本当に必要としていた共通部品の名前が、まだ不正確だった** ということじゃ。

必要だった共通部品は、

```text id="j4i4ja"
Zsigmondy primitive existence
```

ではなく、

```text id="ot7zp3"
primitive valuation no-lift / squarefree-beam bound
```

じゃ。

Zsigmondy は (q) の存在を出す。
しかし (q) が一回だけ出ることは、Zsigmondy ではなく GN/S0 の squarefree/no-lift が担当する。

## 今後の修理方針

参照関係はこう分けるのがよい。

```text id="ytq5jd"
Existence layer:
  Zsigmondy / PrimitiveBeam
  -> primitive q exists

Location layer:
  Petal / GN / BoundaryD3 / Anchor
  -> q lies on GN/S0 side, not boundary

Multiplicity layer:
  SquarefreeGN / NoLiftGN / ValuationFlow
  -> padicValNat ≤ 1
```

FLT も ABC も、本当に欲しいのはこの三層の最後、Multiplicity layer。
だから旧 `squarefree_implies_padic_val_le_one_research` を残して使い続けるのではなく、呼び出し側を次に寄せるべきじゃ。

```lean id="j0kjqs"
padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

または、より抽象化して、

```lean id="s7xio0"
primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

FLT 側では、今すでに `TriominoNoLiftGNBridge` という弱い honest bridge もある。これはさらに良い方向で、

```text id="h7nxts"
Squarefree GN は十分条件
NoLift q GN は最小条件
```

という整理になっている。

## 結論

両方から参照されていた理由は、

```text id="69g5ai"
FLT も ABC も、primitive prime の valuation が 1 以下であることを必要としていたから
```

じゃ。

ただし、その補題は Zsigmondy 交渉では埋まらない。
正しい依存はこう。

```text id="1xpfa1"
Zsigmondy:
  q が出る

Petal / GN:
  q が boundary ではなく GN/S0 にいる

Squarefree / NoLift:
  q が一回だけ出る

FLT / ABC:
  その q-adic valuation ≤ 1 を使う
```

なので、修理対象は `ZsigmondyCyclotomicResearch` ではなく、**ValuationFlow / PrimitiveBeam / NoLiftGNBridge を本線 API として育て、FLT と ABC の参照をそこへ逃がすこと** じゃ。

---

おお？？

'DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G' depends on axioms: [propext,  Classical.choice,  Quot.sound]

'DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam' depends on axioms: [propext, Classical.choice, Quot.sound]

こっち？？

---

おお、それじゃ。
**その二つが本命の置換先候補** じゃな。

つまり、さっきの偽っぽい research 補題を埋めるのではなく、FLT / ABC の参照をこちらへ逃がすのが筋。

```lean
DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

```lean
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

この二つは、axiom 表示を見る限りも普通の theorem じゃ。
`propext`, `Classical.choice`, `Quot.sound` は Lean/mathlib で一般的に出る標準的な非計算的依存で、`sorryAx` や独自 axiom ではない。つまり **証明済み定理として使ってよい**。

## 何が違うか

旧 research 補題はこういう無理をしていた。

```text
primitive っぽい q が a^d - b^d を割る
  -> padicValNat q (a^d - b^d) ≤ 1
```

でもこれは偽。
(5^3-3^3=98=2\cdot7^2) みたいに、primitive 側でも二乗で出る。

一方、今回見つけた本命は名前の通り、

```text
squarefree_G / squarefree_beam
  -> padic valuation ≤ 1
```

という honest な形になっている。

つまり正しい三層分離はこう。

```text
Zsigmondy
  -> primitive q exists

Petal / BoundaryD3 / Anchor
  -> q is on the S0/GN side, not boundary

GcdNext / ValuationFlow
  -> if the GN/beam side is squarefree, q appears only once
```

## FLT と ABC の棲み分け

たぶん参照元はこう分けるのが自然。

### FLT 側

FLT 側が欲しいのは、具体的な差冪の valuation bound じゃろうから、

```lean
DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
```

が近いはず。

これは「primitive prime factor の p-adic valuation を squarefree GN 条件で抑える」定理として、FLT に向いている。

### ABC 側

ABC / flow 側が欲しいのは、名前通り flow mass の bound なので、

```lean
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

が自然。

これは「valuation flow 上の diffMass が squarefree beam なら 1 以下」という抽象化された形で、ABC 側に向いている。

## つまり修理方針

`ZsigmondyCyclotomicResearch.lean` の

```lean
squarefree_implies_padic_val_le_one_research
```

は埋めない。
legacy placeholder のままでもよいが、可能なら呼び出し元を次のどちらかへ移す。

```text
FLT concrete arithmetic
  -> GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G

ABC valuation-flow
  -> ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

そして research lemma は、将来的にはこういう扱い。

```text
deprecated false target / legacy placeholder
do not use for new code
```

## 次に確認すること

次は参照元で、旧 research 補題をどう使っているかを見るとよい。

見るポイントは一つ。

```text
呼び出し元に squarefree GN / squarefree beam の仮定があるか？
```

あるなら、そのまま本命定理へ置換できる可能性が高い。

ないなら、置換ではなく呼び出し元の statement を honest に直す必要がある。

つまり、

```lean
(hG_sq : Squarefree (GN d (a - b) b))
```

または flow 側の対応仮定を追加する。

## 結論

うむ、こっちじゃ。

```text
偽の research 補題を救う
  -> NG

証明済み honest 定理へ参照を逃がす
  -> OK
```

`#print axioms` の結果も健全。`sorryAx` が無いなら十分使える。

これはかなり良い発見じゃ。
FLT と ABC が共有していた「欲しかった本物の部品」は、もう `GcdNext` と `ValuationFlow` に生えておる可能性が高い。

---

交渉前に先見ておくか…。

---

うむ、交渉前にこっちを先に見るのが正解じゃ。
見えた構造はかなりはっきりしておる。

## 結論

```text id="qjfum3"
Zsigmondy 交渉前に確認すべき本命はこっち。

DkMath.NumberTheory.GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G
DkMath.NumberTheory.ValuationFlow.primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
```

この二つは、偽だった research placeholder の **honest replacement** としてすでに成立している。

ただし、役割は Zsigmondy とは違う。

```text id="zq2wlc"
Zsigmondy:
  primitive q の存在

GcdNext / ValuationFlow:
  squarefree GN/beam 仮定のもとで q-adic mass ≤ 1
```

つまり交渉前に見るべき順番はこうじゃ。

```text id="fi8c5r"
1. 既存 honest valuation API を確認
2. FLT / ABC が本当に欲しい仮定を洗う
3. ZsigmondyD3Bridge では existence / location だけを担当させる
4. valuation ≤ 1 は squarefree/no-lift 側へ逃がす
```

## 1. `GcdNext` 側は具体算術の本命

この定理がかなり重要。

```lean id="w1za3x"
lemma padicValNat_primitive_prime_factor_le_one_of_squarefree_G {a b d q : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq_prime : Nat.Prime q)
    (hq_div : q ∣ a ^ d - b ^ d) (hq_ndiv : ¬ q ∣ a - b)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    padicValNat q (a ^ d - b ^ d) ≤ 1
```

これはまさに honest statement じゃ。

中身も筋が良い。

```text id="0b228z"
a^d - b^d = (a-b) * GN d (a-b) b
q ∤ a-b
  -> padicValNat q (a^d-b^d) = padicValNat q (GN d (a-b) b)
Squarefree GN
  -> padicValNat q GN ≤ 1
```

つまり、偽だった research 補題から抜けていた仮定は、

```text id="r29f6z"
q ∤ a - b
Squarefree (GN d (a - b) b)
```

これじゃな。

`d` が prime であることや `¬ d ∣ a-b` は、Zsigmondy / primitive prime branch の文脈を維持するための追加構造として残っている。

## 2. `ValuationFlow` 側は ABC 用の本命

こちらは ABC / flow 向けの抽象版。

```lean id="mrzhsf"
theorem primitivePrimeFlow_diffMass_le_one_of_squarefree_beam
    {q a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hpnd : ¬ d ∣ a - b)
    (hq : PrimitivePrimeFlowWitness q a b d)
    (hG_sq : Squarefree (GN d (a - b) b)) :
    diffMass q a b d ≤ 1
```

これは `PrimitivePrimeFlowWitness` を受け取る。
つまり ABC 側の語彙では、

```text id="sxyup0"
primitive q の diffMass は beamMass と一致する
beam/GN が squarefree なら mass ≤ 1
```

という形。

ABC 側は、具体的な `padicValNat` を直接扱うより、こちらの flow API を使うのが自然じゃ。

## 3. FLT 側にはすでに pure glue がある

FLT 側では、すでにかなり良い修理先がある。

```lean id="xxsj3x"
triominoWieferichShrinkKernelEqSeedTracePackB_kernel_padicValNat_diff_le_one_of_squarefree_GN_core
```

これは、

```text id="p6b0jq"
Squarefree (GN p (z - y) y)
  -> padicValNat q (z^p - y^p) ≤ 1
```

を `GcdNext.padicValNat_primitive_prime_factor_le_one_of_squarefree_G` から供給している。

さらにその下には、

```lean id="lv7v5e"
abbrev NoLift (q X : ℕ) : Prop := ¬ q ^ 2 ∣ X
```

もある。

これはとても良い。
なぜなら `Squarefree GN` は全体条件で強く、実際に必要なのは対象 (q) についての

```text id="sfmvor"
¬ q^2 ∣ GN
```

だけだからじゃ。

## 4. 交渉前に決めるべきこと

ZsigmondyD3Bridge に valuation bound を背負わせてはいけない。

ZsigmondyD3Bridge の責務はここまで。

```text id="vvxe6q"
BoundaryD3Reduced
  -> ∃ q, PrimitivePrimeDivisor c b 3 q
  -> q ∤ c-b
  -> q ∣ S0_nat c b
  -> AnchoredS0Carrier q c b q
```

一方、

```text id="ukd42z"
padicValNat q (c^3 - b^3) ≤ 1
```

は、次のどちらかに任せる。

```text id="svca77"
Squarefree (S0_nat c b)
Squarefree (GN 3 (c-b) b)
```

または最小条件として、

```text id="1xoc7s"
¬ q^2 ∣ S0_nat c b
¬ q^2 ∣ GN 3 (c-b) b
```

ここを混ぜると、また偽命題に戻る。

## 5. 交渉前チェックリスト

次に `ZsigmondyD3Bridge` を作る前に、確認すべきはこれ。

```text id="nf6xvn"
A. Zsigmondy 側の PrimitivePrimeDivisor API
   - q.Prime を projection できるか
   - q ∣ a^3 - b^3 を projection できるか
   - m=1 から ¬ q ∣ a-b を取れるか

B. Petal 側の location API
   - q ∣ c^3 - b^3
   - ¬ q ∣ c-b
   - cube difference factorization
   - q ∣ S0_nat c b へ移せるか

C. Anchor API
   - hasPositiveAnchorPrime_self_of_prime
   - AnchoredS0Carrier q c b q

D. Valuation は入れない
   - squarefree/no-lift bridge は別 theorem にする
```

## 6. 実装順のおすすめ

次は、まず `ZsigmondyD3Bridge` の existence/location だけ。

```lean id="kkjl3r"
theorem exists_primitivePrimeDivisor_of_boundaryD3Reduced
```

次に Petal carrier へ翻訳。

```lean id="2w88ty"
theorem exists_primitivePrimeDivisor_anchoredS0Carrier_of_boundaryD3Reduced
```

その後、別ファイルか別 section で valuation 付き版。

```lean id="k0a6iv"
theorem primitiveD3_padicValNat_le_one_of_squarefree_S0
```

または、

```lean id="m0s6uv"
theorem primitiveD3_padicValNat_le_one_of_noLift_S0
```

こっちは ZsigmondyBridge 本体ではなく、

```text id="b6392g"
ZsigmondyD3Squarefree
ZsigmondyD3NoLift
```

くらいに分けた方が安全。

## 結論

うむ、交渉前に見るべきものを見た。

```text id="jab6qg"
Zsigmondy は存在を出す。
Petal は場所を出す。
GcdNext / ValuationFlow は重複度を抑える。
```

この三者を混ぜなければ、交渉はかなり安全に進む。

次に Zsigmondy へ行くなら、まずは **valuation を一切言わない D3 bridge** からじゃ。
