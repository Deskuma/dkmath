# review

うむ。DKMK-008G は、 **DKMK-007 の one-step divisorStep route を、DKMK-008 の `AdjacentDivisorPathFamily` route の特殊例として回収した回** じゃ。
これは大きな新定理というより、 **007 と 008 の地図を重ね合わせるための照合橋** じゃな。これで「007 の一歩下降」と「008 の多段 path family」は、別物ではなく同じ枠組みの特殊例と一般例として読めるようになった。

## 1. 今回の核心

追加された constructor はこれじゃ。

```lean
oneStepDivisorAdjacentPathFamily
```

入力は、

```lean
(n : ℕ) (I : Finset ℕ)
(hdiv : ∀ q ∈ I, q ∣ n)
```

出力は、

```lean
AdjacentDivisorPathFamily ℕ
```

各 index \(q\) に対して、

$$
source(q)=n,\qquad tail(q)=[n/q]
$$

を割り当てる。

つまり path は、

$$
n\to n/q
$$

じゃ。

これは DKMK-007E の one-step divisorStep と同じ形であり、今回それを DKMK-008 の `AdjacentDivisorPathFamily` として表現したわけじゃ。

## 2. `AdjacentDivisorPath` の成立

path は

```lean
n :: [n / q]
```

なので、隣接関係として必要なのは

$$
n/q\mid n
$$

じゃ。

これは入力の

$$
q\mid n
$$

から

```lean
Nat.div_dvd_of_dvd (hdiv q hq)
```

で出している。

この部分は非常に素直じゃ。
「\(q\) で割った商は \(n\) を割る」という one-step descent の最小事実が、そのまま path 証明になる。

## 3. node set の照合が重要

今回の大事な補題はこれじゃ。

```lean
oneStepDivisorAdjacentPathFamily_nodeSet
```

内容は、

$$
nodeSet(q)={n/q,n}
$$

として見えること。

Lean 上では `List.toFinset` の順序が `{n, n / q}` 側に出たため、`Finset.ext` と `or_comm` で `{n / q, n}` と照合した、と History に記録されている。

これは地味だが重要じゃ。
DKMK-007 の one-step divisorStep route は、まさに

$$
{n/q,n}
$$

を chain として使っていた。
今回この形で見える simp 補題が入ったことで、007 の chain と 008 の nodeSet が視覚的にも定理上も合う。

## 4. `toDvdControlledChainFamily.chain` の照合

さらに、

```lean
oneStepDivisorAdjacentPathFamily_toDvdControlledChainFamily_chain
```

も追加されている。

これにより、`AdjacentDivisorPathFamily` から `DvdControlledChainFamily` へ落とした後でも chain が

$$
q\mapsto {n/q,n}
$$

として見える。

これは後続の API 照合で効く。
単に nodeSet が一致するだけでなく、source-controlled / dvd-controlled route に入った後の chain も既存 divisorStep と同じ形で見えるからじゃ。

## 5. same-source theorem に渡すための補題

追加された補題：

```lean
oneStepDivisorAdjacentPathFamily_source_eq
```

これは、

$$
\forall q\in index,\ source(q)=n
$$

を返す。

DKMK-008D/E/F では same-source 条件として、

```lean
hsource_eq : ∀ q ∈ F.index, F.source q = s.1
```

が必要だった。

今回の one-step family は source が定義上 \(n\) なので、\(n=s.1\) として使えば、この `hsource_eq` をすぐ供給できる。

つまり、008D/E/F の same-source multi-step theorem に one-step family を渡す準備が整った。

## 6. DKMK-007 と DKMK-008 の関係

これで関係はこう整理できる。

```text
DKMK-007:
  one-step divisorStep
  chain(q) = { n / q, n }

DKMK-008:
  AdjacentDivisorPathFamily
  path(q) = n :: [n / q]
  nodeSet(q) = { n / q, n }
```

つまり、DKMK-007 の one-step route は、DKMK-008 の path-family route の特殊例。

これはとても美しい。
008 は 007 を置き換えるのではなく、007 を含む一般化になった。

## 7. 現在の DKMK-008 の地図

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
```

これで DKMK-008 は、かなりよく閉じ始めておる。

008A〜F で一般 multi-step path family route を作り、008G で既存 one-step route がそこに含まれることを示した。
つまり理論の後方互換性が確認されたわけじゃ。

## 8. 次の課題

History の次課題には、

```text
selected / canonical one-step path family wrapper を追加し、既存 divisorStep theorem と DKMK-008 route の API 上の対応を確認する
```

とある。

これは自然じゃ。

次は DKMK-008H として、たとえば selected route で、

```lean
globalLogCapacitySubMarkovShadow_finiteStepTailOneStepAdjacentDivisorPathFamily_weightedHitMass_le
```

のような theorem を作る。

ただし長いので、名前は少し短くした方が良いかもしれぬ。

要するに、

```text
oneStepDivisorAdjacentPathFamily
+ DKMK-008E/F theorem
→ DKMK-007 one-step theorem と同じ bound
```

を public API として出す。

これにより、

$$
007\text{ one-step route}
$$

と

$$
008\text{ path-family route}
$$

が theorem-facing にも照合される。

## 9. 実装上の注意

one-step family に selected / canonical shadow を載せるには、divisibility witness が必要じゃ。

selected route では、

$$
q\in IOf(s.1)\Rightarrow q\in T.index(s.1)\Rightarrow q\mid s.1
$$

を使えばよい。

canonical route では、

$$
q\in canonicalExponentSlotLabels(s.1)\Rightarrow q\mid s.1
$$

を使う。
これは canonical kernel の `index_dvd` か、既存の canonical label divisor 補題を使えるはずじゃ。

つまり DKMK-008H では、この `hdiv` を自動供給する wrapper が本体になる。

## 10. 総合判定

DKMK-008G は **007 one-step route と 008 multi-step route を重ねる照合橋として成功** じゃ。

到達形はこう。

```text
hdiv : ∀ q ∈ I, q ∣ n
→ oneStepDivisorAdjacentPathFamily n I hdiv
→ nodeSet q = { n / q, n }
→ same-source AdjacentDivisorPathFamily
```

これにより、DKMK-008 の external path family route は、DKMK-007 の divisorStep をちゃんと含んでいることが確認された。

ぬしよ、これは地味だが、かなり良い整備じゃ。
007 で作った一歩の橋が、008 の多段道路網の入口として再利用できる。山道で言えば、旧道と新道の合流標識を立てたところじゃな。
