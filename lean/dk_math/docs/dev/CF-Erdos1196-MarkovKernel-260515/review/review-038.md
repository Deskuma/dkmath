# review

うむ。DKMK-008H は、 **DKMK-007 の one-step route と DKMK-008 の path-family route を theorem-facing に重ね合わせた回** じゃ。
DKMK-008G で `oneStepDivisorAdjacentPathFamily` が入ったことで、one-step divisorStep は `AdjacentDivisorPathFamily` の特殊例として読めるようになった。今回 DKMK-008H では、それを selected / canonical の finite-step / two-step shadow wrapper に直接載せた。つまり **旧道と新道の合流標識が、公開 API として立った** わけじゃな。

## 1. 今回の核心

追加された theorem は selected / canonical で二本ずつ、合計四本じゃ。

selected route:

```lean
globalLogCapacitySubMarkovShadow_finiteStepTailOneStepPath_weightedHitMass_le
globalLogCapacitySubMarkovShadow_twoStepTailOneStepPath_weightedHitMass_le
```

canonical route:

```lean
canonicalExponentSlotMarkovShadow_finiteStepTailOneStepPath_weightedHitMass_le
canonicalExponentSlotMarkovShadow_twoStepTailOneStepPath_weightedHitMass_le
```

これらは、DKMK-008G の

```lean
oneStepDivisorAdjacentPathFamily
```

を直接使い、DKMK-008E/F の same-source multi-step theorem に渡している。

## 2. selected route の意味

selected route では、divisibility witness (hdiv) を手で渡さない。

代わりに、

```lean
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
```

と、

```lean
T.toDivisorTransitionKernel.index_dvd
```

から自動生成している。

つまり、(q\in IOf(s.1)) なら、

$$
q\in T.index(s.1)
$$

であり、kernel の `index_dvd` により、

$$
q\mid s.1
$$

が出る。これを `oneStepDivisorAdjacentPathFamily s.1 (IOf s.1) ...` に渡して、各 (q) の path

$$
s.1\to s.1/q
$$

を作っている。

これで selected route は、

```text
selected shadow
+ oneStepDivisorAdjacentPathFamily
+ finite-step / two-step mass
→ weightedHitMass bound
```

として一発で呼べる。

## 3. canonical route の意味

canonical route では、divisibility witness を

```lean
canonicalExponentSlotDivisorTransitionKernel.index_dvd
```

から自動供給している。

つまり、

$$
q\in canonicalExponentSlotLabels(s.1)
$$

なら、

$$
q\mid s.1
$$

が出る。これで canonical index 上の one-step family

$$
q\mapsto \bigl(s.1\to s.1/q\bigr)
$$

が作れる。

そのうえで canonical MarkovShadow を載せ、finite-step なら

$$
weightedHitMass(A)\le \left(\sum_{i\in steps}increment(i):\mathbb{R}\right)
$$

two-step なら

$$
weightedHitMass(A)\le (cHigh:\mathbb{R})
$$

を得る。

## 4. DKMK-008G からの前進

DKMK-008G では、

```text
hdiv : ∀ q ∈ I, q ∣ n
→ oneStepDivisorAdjacentPathFamily n I hdiv
```

までだった。

今回 DKMK-008H では、その `hdiv` を selected / canonical route から自動供給した。
これが重要じゃ。

つまり、利用者側はもう

```lean
q ∣ s.1
```

を個別に用意しなくてよい。

selected なら `hIOf + index_dvd`、canonical なら `canonicalExponentSlotDivisorTransitionKernel.index_dvd` によって、one-step path family が組み立つ。

## 5. DKMK-007 との対応

DKMK-007 の one-step route は、概念的にはこうだった。

```text
divisorStep:
  q ↦ {s.1 / q, s.1}
```

DKMK-008H の one-step path route はこうじゃ。

```text
oneStepDivisorAdjacentPathFamily:
  q ↦ [s.1, s.1 / q]
  nodeSet q = {s.1 / q, s.1}
```

DKMK-008G で node set が既存 divisorStep と同じ ({n/q,n}) として見える補題が入っていた。今回、それを selected / canonical shadow wrapper の公開 theorem まで引き上げた。

つまり、

```text
DKMK-007 one-step theorem
≈ DKMK-008 one-step path-family theorem
```

という対応が、API 上でも明確になった。

## 6. finite-step / two-step の二層

今回の四本は、mass 側で二層に分かれている。

finite-step 版は、DKMK-007M / DKMK-008E の一般形。

```text
finiteStepTailNatMassSpace
→ weightedHitMass ≤ total increment
```

two-step 版は、DKMK-007N / DKMK-008F の便利形。

```text
twoStepAsFiniteStepTailNatMassSpace
→ weightedHitMass ≤ cHigh
```

この二つが one-step path family にも直接載った。

これで、mass 側の到達成果が three ways に使える。

```text
external multi-step path family
same-source multi-step path family
one-step path family
```

特に one-step は旧 DKMK-007 route との照合用として重要じゃ。

## 7. DKMK-008A〜H の現在地

ここまでの流れはこうじゃ。

```text
008A:
  single AdjacentDivisorPath

008B:
  indexed AdjacentDivisorPathFamily

008C:
  external path family を selected / canonical shadow に接続

008D:
  same-source 条件で LogCapacitySourceMassBound を合成

008E:
  finite-step tail mass を same-source path family に載せる

008F:
  two-step tail mass を same-source path family に載せる

008G:
  one-step divisorStep を AdjacentDivisorPathFamily の特殊例として回収

008H:
  one-step path family を selected / canonical finite-step / two-step wrapper に直接載せる
```

これで DKMK-008 の前半はかなり綺麗に閉じてきた。

## 8. 何が残るか

History の次課題では、one-step wrapper と既存 divisorStep theorem の statement-level 対応を docs/report で整理し、必要なら path 自動生成を prime-power descent へ拡張する、と書かれている。

賢狼の見立てでも、次は二択じゃ。

第一は、DKMK-008I として docs/report 総括。

```text
DKMK-007 one-step divisorStep theorem
DKMK-008 one-step path-family theorem
```

の statement 対応表を作る。

第二は、さらに進めて prime-power descent の自動 path 生成へ行く。

例えば (q=p^k) に対して、

$$
n\to n/p\to n/p^2\to\cdots\to n/p^k
$$

のような path を生成する方向じゃ。
これはいよいよ multi-step の本命に近い。

## 9. 総合判定

DKMK-008H は **007 と 008 の照合を theorem-facing API にした成功フェーズ** じゃ。

到達形はこう。

```text
selected route:
  hIOf + index_dvd
  → oneStepDivisorAdjacentPathFamily
  → finite-step / two-step weightedHitMass bound

canonical route:
  canonical index_dvd
  → oneStepDivisorAdjacentPathFamily
  → finite-step / two-step weightedHitMass bound
```

これで DKMK-008 は、DKMK-007 を含む一般化としてかなり安定した。
ぬしよ、これは見事じゃ。旧道を捨てず、新道の特殊例として回収した。山道作りでは、こういう接続路が後で命綱になるのじゃ。
