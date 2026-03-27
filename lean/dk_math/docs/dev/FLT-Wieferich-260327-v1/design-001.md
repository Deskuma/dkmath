# Wieferich witness をどこへ落とすか

うむ、スナップショット実体を見て整理すると、結論はかなりはっきりしておる。

ぬしの今回の焦点は、まさにこの文脈じゃな。すなわち「Branch A で既に (y^{p-1} \equiv 1 \pmod{p^2}) が取れているなら、それをどの契約へ落とすのが最短か」という話じゃ。
また全体の大枠として、このリポジトリは Zsigmondy / gcd / p-adic の橋渡し層から FLT 本体へ接続する設計になっておる。

## 1. 先に結論

**最短の接続案** はこれじゃ。

$$
\texttt{PrimeGe5BranchAWieferichOnYTarget}
;\to;
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
;\to;
\texttt{BranchARefuterTarget}
$$

そして最終的に

$$
\texttt{FLTPrimeGe5Target\_of\_branchA\_wieferich\_with\_normalizer\_impl}
$$

へ入れる。

つまり、新しく埋めるべき本命契約は

$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
$$

でよい。
いま既に witness 側

$$
\texttt{PrimeGe5BranchAWieferichOnYTarget}
$$

は満たせておるので、 **refuter だけ** 書けば、既存配線がそのまま使える、という見立てじゃ。

---

## 2. いちばん薄い adapter

最小入力は、ほんにこれだけで足りる。

```lean
PrimeGe5BranchAWieferichRefuterTarget :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    False
```

つまり必要入力は 3 本だけじゃ。

## 2.1. 最小入力

1. `hpack : PrimeGe5CounterexamplePack p x y z`
2. `hp_dvd_gap : p ∣ (z - y)`
3. `hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]`

これを書ければ、あとは既存 theorem で

```lean
primeGe5BranchARefuter_of_wieferich
```

または gap-invariant 側の

```lean
branchARefuter_of_wieferichTargets
```

で Branch A 全体 refuter に持ち上がる。

さらにそのまま

```lean
FLTPrimeGe5Target_of_branchA_wieferich_with_normalizer_impl
```

に渡せる。
工学的には、これが最短距離じゃ。

---

## 3. 候補 adapter 一覧

ここからは「どこへ落とすか」の候補を、薄い順に並べるぞい。

## 3.1. 候補 A. Wieferich refuter へ直接落とす

契約:
$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
$$

入力:
$$
(hpack,\ hp_dvd_gap,\ hWieferich)
$$

長所:

* 追加実装が最小
* 既存の Branch A mainline へ直結
* global provider / FLTPrimeGe5 まで配線済み

短所:

* shape / shrink / descent の既存 spine にはあまり乗らぬ
* 数学核を deeper kernel に落とす設計美は少し薄い

これは、 **最短案** じゃ。

---

## 3.2. 候補 B. 既存 descent refuter へ落とす

契約:
$$
\texttt{ExistingDescentRefuterTarget}
$$

入力:
$$
(hpack,\ hp_dvd_gap,\ hInput)
$$
ただし
$$
hInput : \texttt{BranchAShapeWitnessDescentInput}\ p\ x\ y\ z\ t
$$

この `hInput` の中身は

1. `tPos : 0 < t`
2. `powPredDvdGap : p^(p-1) ∣ (z-y)`
3. `gapShape : z-y = p^(p-1) * t^p`

じゃ。

長所:

* 既存 clean machinery と一番よく噛み合う
* `branchAShapeWitnessKernel_of_existingDescentRefuter` へそのまま入る
* その先の shrink / descent パイプも活きる

短所:

* Wieferich witness だけでは `t` がない
* 結局、shape witness の復元が別に要る

なので、ぬしが今もう持っておるのが「Wieferich witness のみ」なら、これは **再利用性は高いが最短ではない** 。

---

## 3.3. 候補 C. witness kernel へ落とす

契約:
$$
\texttt{BranchAShapeWitnessKernelTarget}
$$

入力:
$$
(hpack,\ hp_dvd_gap,\ ht)
$$
ただし
$$
ht : z-y = p^{p-1} t^p
$$

長所:

* shape-value から一段だけ奥
* 既存 theorem で normal form refuter に接続できる

短所:

* やはり Wieferich witness だけでは `ht` がない
* まず shape-value を回収せねばならぬ

---

## 3.4. 候補 D. shape-value refuter へ落とす

契約:
$$
\texttt{PrimeGe5BranchAShapeValueToRefuterTarget}
$$

入力:
$$
(hpack,\ hp_dvd_gap,\ \exists t,\ z-y = p^{p-1} t^p)
$$

長所:

* 既存 shape pipeline の自然な途中点
* factorization から value への橋は既に clean

短所:

* やはり witness 直受けではない
* いったん shape-value を復元してから使う必要がある

---

## 3.5. 候補 E. deepest clean kernel へ落とす

契約候補:
$$
\texttt{PrimeGe5BranchANormalFormRefuterTarget}
$$
あるいはさらに下の
$$
\texttt{PrimeGe5BranchANormalFormArithmeticKernelTarget}
$$

入力はかなり重い。具体的には

$$
z-y = p^{p-1} t^p,\qquad
GN\ p\ (z-y)\ y = p s^p,\qquad
x = p(ts)
$$

に加えて、`gcd = p` や `Nat.Coprime t s` などの局所条件まで要る。

長所:

* 数学的には最も clean
* 最終残穴として分離されている核に直接触れる

短所:

* Wieferich witness からは遠い
* adapter というより、別証明を建てる感覚になる

これは「美しい本丸」ではあるが、 **最短接続案ではない** 。

---

## 4. わっちの推奨

実務上は二段で考えるのがよい。

## 4.1. 今すぐ進む最短案

まず

```lean
theorem my_branchAWieferichRefuter :
    PrimeGe5BranchAWieferichRefuterTarget := by
  intro p x y z hpack hp_dvd_gap hWieferich
  ...
```

を埋める。

そのあと

```lean
have hA :
    BranchARefuterTarget :=
  branchARefuter_of_wieferichTargets
    primeGe5BranchAWieferichOnY_default
    my_branchAWieferichRefuter
```

あるいは BranchA 側でそのまま

```lean
exact primeGe5BranchARefuter_of_wieferich
  primeGe5BranchAWieferichOnY_default
  my_branchAWieferichRefuter
```

で閉じる。

これが最短。

---

## 4.2. clean machinery に寄せる中期案

上の `my_branchAWieferichRefuter` が書けたら、さらに

```lean
have hDesc : ExistingDescentRefuterTarget :=
  existingDescentRefuter_of_branchAWieferich
    my_branchAWieferichRefuter
```

としておくとよい。

これで既存の descent spine に戻せる。
つまり、

$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
\to
\texttt{ExistingDescentRefuterTarget}
\to
\texttt{BranchAShapeWitnessKernelTarget}
$$

という逆流も可能になる。
この形にしておくと、後で `ExistingDescentRefuterTarget` を clean kernel に差し替えるだけで、Wieferich route 側も一緒に clean 化される。

---

## 5. まとめ

要するに、整理はこうじゃ。

## 5.1. 既にあるもの

$$
\texttt{PrimeGe5BranchAWieferichOnYTarget}
$$
は取れている。

## 5.2. 最小で新たに埋めるべき契約

$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
$$

## 5.3. 最短接続

$$
\texttt{OnYTarget}
\to
\texttt{WieferichRefuterTarget}
\to
\texttt{BranchARefuterTarget}
\to
\texttt{FLTPrimeGe5Target}
$$

## 5.4. clean machinery 再利用の接続点

$$
\texttt{PrimeGe5BranchAWieferichRefuterTarget}
\to
\texttt{ExistingDescentRefuterTarget}
$$

これが、いまのコード構造に一番素直で、しかも後から clean kernel 差し替えにも耐える道じゃよ。
