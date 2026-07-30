# Note: 001: ABC GN valuation excess

## 結論

うむ。 **お主の読みは正しい。しかも現行 DkMath は、すでに半分以上その構造を実装しておる。**

ただし調査結果から、問いは少し言い換わる。

> GN5 を $GN_n$ へ一般化できるか？

ではない。

> **すでに一般化済みの $GN_n$ と `padicValNat` を、ABC の指数過剰量へ接続し、最後に元の $\mathrm{rad}(abc)$ へ戻せるか？**

これが本当の未実装部分じゃ。

今回、`main` の最新状態、commit `64305c707fa3a394a83301c45d2c878be5d905bb` を基準に調べた。

## 1. $GN_n$ 一般化はすでに完成している

一般 Tail は、

$$GN_n(x,u)=\mathrm{GTail}(n,1,x,u)$$

として実装済みじゃ。

さらに高次 Tail 全体として、

$$\mathrm{GTail}(n,r,x,u)$$

まで定義され、

$$
(x+u)^n = \sum_{j<r}\binom{n}{j}x^ju^{n-j} + x^r\mathrm{GTail}(n,r,x,u)
$$

が証明されている。

公開名 `GN` も、すでに $r=1$ の canonical specialization として固定されておる。

したがって任意の指数 $n$ に対し、

$$
(x+u)^n=u^n+x,GN_n(x,u)
$$

が利用できる。

つまり、 **GN5 の一般化は新規作業ではない** 。
ABC 側がまだ、この完成済み一般 GN を主語として組み直されていないだけじゃ。

## 2. 「padic は GN を見ている」は実装上も正しい

現行の `ValuationFlow.Basic` は、既に次のように定義されている。

$$
\mathrm{diffMass}_q(a,b,n) = v_q(a^n-b^n)
$$

$$
\mathrm{boundaryMass}_q(a,b) = v_q(a-b)
$$

$$
\mathrm{beamMass}_q(a,b,n) = v_q!\left(GN_n(a-b,b)\right)
$$

つまり `beamMass` は定義上、そのまま、

```lean
padicValNat q (GN d (a - b) b)
```

じゃ。

差冪分解、

$$
a^n-b^n=(a-b)GN_n(a-b,b)
$$

に `padicValNat` を作用させれば、

$$
v_q(a^n-b^n) = v_q(a-b) + v_q!\left(GN_n(a-b,b)\right)
$$

となる。

さらに $q$ が指数 $n$ の段で初めて現れる primitive prime なら、

$$
q\nmid a-b
$$

なので境界 valuation は消え、

$$
v_q(a^n-b^n) = v_q!\left(GN_n(a-b,b)\right)
$$

となる。この等式はすでに `primitive_prime_padic_eq_GN` として証明されている。

ゆえに、正確にはこうじゃ。

> `padicValNat` は差冪全体を観測しているが、primitive channel に制限すると、その観測値は完全に GN の観測値になる。

これは比喩ではなく、既存 theorem そのものじゃ。

## 3. 指数 $n$ は見えなくなるのではなく、二箇所へ圧縮される

お主のいう「指数部が padic によって見えなくなる」は、半分正しく、より正確には、

> **外側の指数記法が、valuation の係数と GN の内部構造へ圧縮される**

じゃ。

完全冪では、

$$
v_q(t^n)=n,v_q(t)
$$

となる。この定理も実装済みじゃ。

一方、差冪では指数 $n$ は、

1. $GN_n$ の二項係数・次数構造
2. 境界と GN が重なる例外素数

の二箇所に現れる。

現行コードでは、

$$
\gcd!\left(a-b,GN_n(a-b,b)\right)\mid n
$$

が証明済みじゃ。

したがって、素数 $q$ が境界と GN の両方を割るなら、

$$
q\mid n
$$

でなければならない。

逆に、

$$
q\nmid n
$$

ならば、境界と GN はその $q$-channel では混ざらない。

このため `UniqueFactorizationGN` では、すでに素数層を、

```text
exceptional layer      q ∣ n
non-exceptional layer  q ∤ n
```

へ分割する API が置かれている。

つまり指数 $n$ は消えておらぬ。

$$
\boxed{
n
\longmapsto
\begin{cases}
GN_n\text{ の内部次数構造}\
q\mid n\text{ という例外 prime layer}
\end{cases}
}
$$

へ姿を変えている。

## 4. ABC への GN 接続も、support 層までは存在する

ABC 側には既に、primitive prime family から差冪の radical 下界を出す bridge がある。

$$
2^{\#\text{channels}}
\le
\mathrm{rad}(a^n-b^n)
$$

型の定理まで実装されている。

Petal 側にも、

```text
selected GN prime labels
  → support product
  → supportMass (GN)
  → rad (GN)
```

という直接 bridge がある。

したがって現況は、

```text
GNₙ の一般定義                 完了
差冪 = 境界 × GNₙ              完了
primitive prime → GNₙ          完了
padic(diff) = padic(GNₙ)       完了
GNₙ prime support → ABC rad    完了
```

まで来ておる。

だが、ここから先が欠けている。

## 5. 本当に不足しているもの

ABC が数える radical は、各素数を一度しか数えない。

$$
\mathrm{rad}(m)=\prod_{q\mid m}q
$$

一方、数そのものは、

$$
m=\prod_{q\mid m}q^{v_q(m)}
$$

じゃ。

したがって GN における未観測量は、

$$
\mathrm{GNExcess}_n(x,u) = \sum_{q\mid GN_n(x,u)} \bigl(v_q(GN_n(x,u))-1\bigr)\log q
$$

となる。

これは、

$$
\log GN_n = \log\mathrm{rad}(GN_n) + \mathrm{GNExcess}_n
$$

における、radical が忘れた指数質量じゃ。

現行 bridge は prime support を radical へ送るところまでは完成しているが、 **この valuation excess 全体を制御していない** 。

既存の NoLift theorem は、選択した primitive prime $q$ に対して、

$$
q^2\nmid GN_n \Longrightarrow v_q(a^n-b^n)\le1
$$

と言う局所補題じゃ。

Squarefree GN なら全 channel を制御できるが、

$$
\mathrm{Squarefree}(GN_n)
$$

は一般には強すぎる仮定じゃ。

ゆえに本丸は、

> $q^2\mid GN_n(x,u)$ となる高持ち上がり prime を、指数素数 $q\mid n$ と、それ以外の Wieferich 型例外へ分離し、後者の総 valuation excess を抑える

ことになる。

## 6. $a+b=c$ から生じる GN power lift

任意の ABC Triple、

$$
a+b=c,\qquad \gcd(a,b)=1
$$

に対し、任意の $n$ について、

$$
c^n-b^n=a,GN_n(a,b)
$$

だから、新しい加法三つ組、

$$
a,GN_n(a,b)+b^n=c^n
$$

が得られる。

これは非常に自然な **GN power lift** じゃ。

しかも互いに素性も維持できる。

$$
\gcd!\left(aGN_n(a,b),b^n\right)=1
$$

$$
\gcd(b^n,c^n)=1
$$

$$
\gcd!\left(aGN_n(a,b),c^n\right)=1
$$

この canonical ABC Triple constructor は、今回調べた範囲では、まだ ABC 公開 API としては切り出されていない。

ここは新規実装価値が高い。

ただし、これだけでは元の ABC は閉じぬ。

なぜなら $GN_n$ に新しい素数が大量に現れると、持ち上げ後の radical は大きくなるが、それらは元の、

$$
\mathrm{rad}(abc)
$$

には含まれていないからじゃ。

つまり持ち上げは簡単でも、 **元の Triple への反転射影** が要る。

現行 `ValuationFlowBridge` にも、GN/diff radical から quality 側へ送る際、

```lean
htransport : ABC.rad c ≤ ABC.rad (a * b)
```

のような追加 transport 仮定が明示的に要求されている。

ここが現在の断線地点じゃ。

## 7. 確率 route を置換できるか

判定はこうなる。

### 前半は置換できる

確率や質量を使っていた、

```text
素因子 channel の出現
support の増加
valuation の流れ
```

は、GN の厳密因数分解で直接記述できる。

これは間違いなく楽で速い。

### 後半は、まだ一つの定理が必要

高持ち上がり集合、

$$
\mathcal H_n(a,b) = \{q\mid GN_n(a,b);\middle|;q^2\mid GN_n(a,b)\}
$$

について、

$$
\mathcal H_n = \mathcal H_n^{\mathrm{exp}} \cup \mathcal H_n^{\mathrm{Wieferich}}
$$

という分離を行い、

* $\mathcal H_n^{\mathrm{exp}}$：$q\mid n$ の有限例外
* $\mathcal H_n^{\mathrm{Wieferich}}$：$q\nmid n$ なのに高く持ち上がる例外

の後者を量的に抑えねばならぬ。

旧 Janson route は、この種の「稀な高密度事象」を確率で押さえようとしていた。しかし現在も Chernoff、独立性、第二モーメント、最終 Janson assembly が未完じゃ。

したがって最善の新構図は、

```text
GNₙ による決定論的分解
  ↓
q ∣ n / q ∤ n の分離
  ↓
primitive / support / rad は既存 theorem
  ↓
高持ち上がり GN prime だけを抽出
  ↓
必要なら、この例外集合だけに確率・密度評価を使う
```

じゃ。

確率を捨てるのではない。

**確率を最後の例外集合だけへ追放する。**

## 8. 次に作るべき実装面

新しい主線は、この四層がよい。

```text
DkMath/ABC/GNPowerLift.lean
DkMath/ABC/GNValuationSplit.lean
DkMath/ABC/GNHighLift.lean
DkMath/ABC/GNReturnBridge.lean
```

最初の checkpoint は次で十分じゃ。

```lean
def Triple.gnPowerLift (T : Triple) (n : ℕ) : Triple

theorem gnPowerLift_left_eq_boundary_mul_GN
theorem gnPowerLift_pairwise_coprime

theorem padic_diff_eq_boundary_add_GN
theorem primitive_padic_diff_eq_GN

theorem common_prime_boundary_GN_dvd_exponent
theorem nonExceptional_prime_not_dvd_boundary_and_GN
```

その後、

```lean
def GNHighLiftPrime (q n x u : ℕ) : Prop :=
  Nat.Prime q ∧ q ^ 2 ∣ GN n x u
```

を置き、指数例外と非例外高持ち上がりを分ける。

## 最終判定

$$
\boxed{
\text{padicValNat は GN を見ている}
}
$$

これは正しい。

さらに正確には、

$$
\boxed{
\text{padicValNat は指数 }n\text{ を、}
GN_n\text{ の内部 valuation と }q\mid n\text{ の例外層として見る}
}
$$

じゃ。

そして GN 一般化を ABC に取り込むことで、今の状況は確実に打破できる。少なくとも、未完成の巨大な確率機構を、

> **GN の高持ち上がり prime をどこまで抑えられるか**

という一つの明瞭な数論問題へ圧縮できる。

ただし現在の `abc_main` 自体は、まだ `abc_main_axiom` の直接呼び出しであり、最終証明には到達していない。

ゆえに賢狼の調査判定は、

> **着工価値は極めて高い。GN 一般化は完成済み。新規本丸は GN valuation excess の反転輸送である。**

じゃ。今回、GitHub 上の変更操作は行っておらぬ。
