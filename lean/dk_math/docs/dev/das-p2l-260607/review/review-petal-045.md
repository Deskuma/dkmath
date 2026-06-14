# Git diff / Report / Review

## Upd: Petal.BezoutBridge

gch: 34fadab576c16d5c7549ecb942e684f210997031

## Report

`Petal.BezoutBridge` を拡張して、Zsigmondy との一般 handshake を追加しました。

追加した主な接続は [BezoutBridge.lean](/lean/dk_math/DkMath/Petal/BezoutBridge.lean:91) です。

```lean
primitivePrimeFactor_not_dvd_boundary
padicValNat_bodyDiff_eq_GN_of_primitivePrimeFactor

primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor
zsigmondyPrimitivePrimeDivisor_not_dvd_boundary
zsigmondyPrimitivePrimeDivisor_dvd_GN
padicValNat_bodyDiff_eq_GN_of_zsigmondyPrimitivePrimeDivisor
anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor
```

これで流れが明確になりました。

```text
Zsigmondy.PrimitivePrimeDivisor
  -> PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
  -> boundary を避ける
  -> GN に載る
  -> body diff の p-adic height は GN 側で読める
  -> AnchoredGNCarrier
```

検証済みです。

```text
lake build DkMath.Petal.BezoutBridge
lake build DkMath.Petal
git diff --check -- lean/dk_math/DkMath/Petal/BezoutBridge.lean lean/dk_math/DkMath/Petal.lean
```

すべて成功。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は今回由来ではありません。

## Review

うむ。突合した結論から言うぞい。

**今回の差分は Lean 的にも数学的にも健全。merge 可。**
ただし、`DkMath.Zsigmondy` は古典的な **完全版 Zsigmondy 定理** そのものではなく、現状では **prime exponent 版の十分条件付き Zsigmondy-lite 公開 API** と見るのが正確じゃ。

## 1. 実際の Zsigmondy 定理との突合

古典的な Zsigmondy 定理は、おおよそ次を言う。

$$
a>b>0,\quad \gcd(a,b)=1,\quad n>1
$$

のとき、ほとんどの場合に

$$
a^n-b^n
$$

は **原始素因子** を持つ。ここで原始素因子とは、

$$
q\mid a^n-b^n
$$

かつ

$$
0<k<n \Rightarrow q\nmid a^k-b^k
$$

を満たす素数 (q) じゃ。例外は古典的には (n=2) 型の例外と ((a,b,n)=(2,1,6)) 型が主なもの。

一方、添付の `DkMath.Zsigmondy` が現在実装している公開定理は、主にこれじゃ。

```lean
theorem exists_primitivePrimeDivisor_prime_exp {a b d : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hab_lt : b < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hnd : ¬ d ∣ a - b) :
    ∃ q, PrimitivePrimeDivisor a b d q
```

つまり条件は、

$$
d\ \text{prime},\quad d\ge 3,\quad b<a,\quad 0<b,\quad \gcd(a,b)=1,\quad d\nmid a-b
$$

じゃ。

したがって突合結果はこう。

| 観点          | 古典 Zsigmondy          | DkMath.Zsigmondy 現状           |
| ----------- | --------------------- | ----------------------------- |
| 指数 (n)      | 一般 (n>1)              | 素数指数 (d\ge 3)                 |
| 例外処理        | 既知例外を除外               | `¬ d ∣ a-b` を仮定               |
| 原始性         | 全 lower exponent を避ける | `PrimitivePrimeDivisor` で実装済み |
| 存在定理        | ほぼ一般                  | 十分条件付き                        |
| 円分多項式経由の一般論 | 本筋                    | 足場あり、一般完成は未完                  |

要するに、DkMath 版は **完全 Zsigmondy ではなく、prime exponent route に必要な安全な部分定理** じゃな。

この切り分けは INDEX の地図とも一致しておる。`NumberTheory.ZsigmondyCyclotomic` は、冪差の分解、gcd 制御、primitive 抽出、円分多項式、p-adic 評価というブロックに分けて管理されており、特に primitive 抽出では `exists_primitive_prime_factor_basic` と `prime_exp_not_dvd_diff_imp_primitive` が中心とされている。

## 2. DkMath.Zsigmondy の実装内容

添付の `Zsigmondy.lean` の中核は、この定義じゃ。

```lean
def PrimitivePrimeDivisor (a b n q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ a ^ n - b ^ n ∧
  ∀ m : ℕ, 0 < m → m < n → ¬ q ∣ a ^ m - b ^ m
```

これは古典的な primitive prime divisor の定義とよく一致している。ここは良い。

その上で、`DkMath.Zsigmondy` は次の階段を作っている。

```text
exists_primitive_prime_factor_basic
  -> q ∣ a^d - b^d and q ∤ a-b

prime_exp_not_dvd_diff_imp_primitive
  -> q が全 lower exponent を避ける

exists_primitivePrimeDivisor_prime_exp
  -> PrimitivePrimeDivisor a b d q に梱包
```

つまり、下層の `GcdNext` ではまず

$$
q\mid a^d-b^d,\qquad q\nmid a-b
$$

を取り、それを prime exponent (d) の群論・位数 argument で

$$
0<k<d \Rightarrow q\nmid a^k-b^k
$$

へ昇格している。

ここがよい。
`¬ q ∣ a-b` だけでは本当の primitive ではないが、prime exponent なら群論で lower layer 全部を潰せる。DkMath はそこをちゃんと theorem 化している。

## 3. GN / Petal との整合

DkMath 側の GN 設計では、

$$
(x+u)^d-u^d=x,GN_d(x,u)
$$

が標準 GN の基本式であり、GN は境界因子を外した Beam / Tail 側の核として扱われる。 また、整数宇宙側の中心式としても同じ式が掲げられ、この可除情報が Petal、p-adic、primitive factor、Zsigmondy へ渡ると整理されている。

今回の差分はまさにそこを接続している。

```text
DkMath.Zsigmondy.PrimitivePrimeDivisor
  -> PrimitiveBeam.PrimitivePrimeFactorOfDiffPow
  -> boundary を避ける
  -> GN に載る
  -> padicValNat は GN 側で読める
  -> AnchoredGNCarrier
```

これは設計と一致しておる。特に、Erdős/ABC 系の実装計画でも primitive prime / GN / padicValNat を接続することが Phase C の到達目標として明記されており、今回の bridge はその Petal/Zsigmondy 版と見てよい。

## 4. 差分の各 theorem の検証

### 4.1. `primitivePrimeFactor_not_dvd_boundary`

```lean
theorem primitivePrimeFactor_not_dvd_boundary
    {q a b d : ℕ}
    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
    (hd1 : 1 < d) :
    ¬ q ∣ a - b
```

これは正しい。
理由は、境界 (a-b) は

$$
a^1-b^1
$$

だからじゃ。primitive witness は (0<1<d) の lower layer を割れない。よって (d>1) が必要。仮定 `hd1 : 1 < d` は適切。

### 4.2. `padicValNat_bodyDiff_eq_GN_of_primitivePrimeFactor`

```lean
padicValNat q (a ^ d - b ^ d) =
  padicValNat q (GN d (a - b) b)
```

これも正しい。
因数分解

$$
a^d-b^d=(a-b),GN_d(a-b,b)
$$

に対して、primitive 性から

$$
q\nmid a-b
$$

なので

$$
v_q(a-b)=0
$$

となり、

$$
v_q(a^d-b^d)=v_q(GN_d(a-b,b))
$$

が従う。

ここは Petal/valuation route の本命じゃ。

### 4.3. `primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor`

```lean
theorem primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor
    {q a b d : ℕ}
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q) :
    PrimitivePrimeFactorOfDiffPow q a b d
```

これは完全に自然な変換じゃ。
実質的には同型の Prop を、名前空間の違いに合わせて詰め替えているだけ。

この theorem が今回いちばん重要じゃな。
これにより、`DkMath.Zsigmondy` の公開 witness が、既存の `PrimitiveBeam` / `Petal` ルートへ入れるようになった。

### 4.4. `zsigmondyPrimitivePrimeDivisor_not_dvd_boundary`

正しい。
`PrimitivePrimeDivisor` から `PrimitivePrimeFactorOfDiffPow` へ変換し、先ほどの boundary 回避を使うだけ。

ただし、これも `hd1 : 1 < d` は必須じゃ。(d=1) では lower exponent (1) は存在しないので、boundary 回避は言えない。

### 4.5. `zsigmondyPrimitivePrimeDivisor_dvd_GN`

正しい。
必要条件は次。

```lean
(hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a)
```

`hab_lt` は `Nat` 減算と `pow_sub_pow_factor_cosmic_N` に必要。
`hd` は因数分解の非零指数条件。
`hd1` は boundary 回避条件。

Lean 的には `hd1` から `hd` は出せるが、下層 theorem が両方要求しているので、wrapper が両方受けるのは問題ない。

### 4.6. `padicValNat_bodyDiff_eq_GN_of_zsigmondyPrimitivePrimeDivisor`

正しい。
Zsigmondy witness を PrimitiveBeam witness に変換して、valuation 等式を使うだけ。

### 4.7. `anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor`

正しい。
これで Zsigmondy primitive divisor が Petal の `AnchoredGNCarrier` に入る。

数学的には、

$$
q\mid GN_d(a-b,b)
$$

かつ (q) 自身が prime anchor なので、

$$
AnchoredGNCarrier\ q\ d\ (a-b)\ b\ q
$$

として読める、ということじゃ。

## 5. 注意点・改善候補

Blocking issue ではないが、設計上の注意は 2 つある。

### 5.1. `DkMath.Zsigmondy` は完全版ではない

`DkMath.Zsigmondy` という名前は強い。
だが現状の存在定理は、

$$
d\ \text{prime},\quad d\ge 3,\quad d\nmid a-b
$$

を仮定する十分条件版じゃ。

したがって docs では、次のように明記した方が安全。

```text
DkMath.Zsigmondy は現時点では classical Zsigmondy theorem の完全形式化ではなく、
prime exponent route に必要な Zsigmondy-lite public API である。
```

特に `¬ d ∣ a-b` は古典 Zsigmondy の標準的な例外条件そのものではなく、DkMath の下層補題が要求する **安全な十分条件** と見るべきじゃ。

### 5.2. `Petal.BezoutBridge` が少し重くなる

今回、

```lean
import DkMath.Zsigmondy
```

が `Petal.BezoutBridge` に入った。

ビルドが通っているので循環依存はない。`DkMath.Zsigmondy` 側は Petal を import していないので、依存方向も破綻していない。

ただし設計美としては、将来 `Petal.BezoutBridge` を純粋な PrimitiveBeam bridge に保ちたいなら、Zsigmondy 部分を別ファイルに分ける案もある。

```text
DkMath.Petal.BezoutBridge
  primitive / gcd / GN の一般 bridge

DkMath.Petal.ZsigmondyBridge
  DkMath.Zsigmondy.PrimitivePrimeDivisor から Petal への handshake
```

今の規模なら分けなくてもよい。
ただ、Zsigmondy 側の theorem が増えるなら、分離した方が import 物語は綺麗になる。

## 6. 今回の数学的価値

今回の価値は、単に theorem が増えたことではない。

これまでは、

```text
Zsigmondy witness がある
```

と

```text
GN / Petal 面に primitive witness が載る
```

の間に、読み替えが必要だった。

今回、その橋が Lean theorem として固定された。

$$
\text{Zsigmondy primitive divisor}
$$

から

$$
\text{AnchoredGNCarrier}
$$

まで一気通貫で行ける。

これはかなり強い。
Zsigmondy の「新しい素因子」を、DkMath の語彙では

```text
境界ではなく GN kernel に現れる anchored carrier
```

として扱えるようになったわけじゃ。

## 7. 判定

**レビュー判定: approve。**

この差分は次の意味でよい。

```text
古典 Zsigmondy
  -> DkMath.Zsigmondy の prime-exponent witness
  -> PrimitiveBeam witness
  -> boundary/GN separation
  -> p-adic height transfer
  -> Petal anchored carrier
```

ただし、ドキュメントには一言だけ足すのがよい。

```text
Note:
This bridge consumes `DkMath.Zsigmondy.PrimitivePrimeDivisor`.
The current `DkMath.Zsigmondy` existence API is a prime-exponent,
sufficient-condition Zsigmondy-lite layer, not the full classical
Bang-Zsigmondy theorem with all exceptions removed.
```

これを書いておけば、過大主張にならぬ。
足場としては実に良い。Petal と Zsigmondy の握手が、ようやく Lean の theorem 名で呼べるようになったのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Petal/BezoutBridge.lean b/lean/dk_math/DkMath/Petal/BezoutBridge.lean
index a034c037..242244fb 100644
--- a/lean/dk_math/DkMath/Petal/BezoutBridge.lean
+++ b/lean/dk_math/DkMath/Petal/BezoutBridge.lean
@@ -7,6 +7,7 @@ Authors: D. and Wise Wolf.
 import DkMath.Petal.Anchor
 import DkMath.NumberTheory.PrimitiveBeam
 import DkMath.NumberTheory.UniqueFactorizationGN
+import DkMath.Zsigmondy
 
 #print "file: DkMath.Petal.BezoutBridge"
 
@@ -22,6 +23,8 @@ The mathematical core is already present in the lower layers:
   `a^d - b^d = (a - b) * GN d (a - b) b` to the `GN` side.
 * `UniqueFactorizationGN` controls the gcd between the visible boundary and the
   residual `GN` kernel.
+* `DkMath.Zsigmondy.PrimitivePrimeDivisor` is converted to the existing
+  `PrimitiveBeam` witness shape before entering the Petal/Anchor surface.
 
 This bridge does not introduce a new Bezout theorem.  Instead it records the
 interpretation needed by the Petal/Zsigmondy route:
@@ -87,6 +90,87 @@ theorem primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary
   primitive_prime_dvd_GN_body
     (q := q) (x := x) (u := u) (d := d) hq hd hd1
 
+/--
+Primitive witnesses avoid the visible boundary.
+
+This is the first half of the Bezout reading: the primitive prime cannot live
+on the `a - b` boundary because exponent `1` is a lower layer.
+-/
+theorem primitivePrimeFactor_not_dvd_boundary
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd1 : 1 < d) :
+    ¬ q ∣ a - b :=
+  primitive_prime_not_dvd_boundary hq hd1
+
+/--
+For a primitive witness, the `q`-adic height of the whole body difference is
+exactly the height seen on the residual `GN` kernel.
+-/
+theorem padicValNat_bodyDiff_eq_GN_of_primitivePrimeFactor
+    {q a b d : ℕ}
+    (hq : PrimitivePrimeFactorOfDiffPow q a b d)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    padicValNat q (a ^ d - b ^ d) =
+      padicValNat q (GN d (a - b) b) :=
+  primitive_prime_padic_eq_GN hq hd hd1 hab_lt
+
+/--
+Convert the public Zsigmondy primitive-divisor witness to the existing
+`PrimitiveBeam` primitive-prime-factor witness.
+
+This is the generic handshake between the Zsigmondy API and the Petal/GN
+location API.
+-/
+theorem primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q) :
+    PrimitivePrimeFactorOfDiffPow q a b d := by
+  refine
+    ⟨DkMath.Zsigmondy.PrimitivePrimeDivisor.prime hprim,
+      DkMath.Zsigmondy.PrimitivePrimeDivisor.dvd hprim, ?_⟩
+  intro k hk_pos hk_lt
+  exact DkMath.Zsigmondy.PrimitivePrimeDivisor.not_dvd_lower
+    hprim hk_pos hk_lt
+
+/--
+A Zsigmondy primitive divisor avoids the visible boundary.
+-/
+theorem zsigmondyPrimitivePrimeDivisor_not_dvd_boundary
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd1 : 1 < d) :
+    ¬ q ∣ a - b :=
+  primitivePrimeFactor_not_dvd_boundary
+    (primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor hprim)
+    hd1
+
+/--
+A Zsigmondy primitive divisor is observed on the residual `GN` kernel.
+-/
+theorem zsigmondyPrimitivePrimeDivisor_dvd_GN
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    q ∣ GN d (a - b) b :=
+  primitivePrimeFactor_dvd_GN_of_cosmicBoundary
+    (primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor hprim)
+    hd hd1 hab_lt
+
+/--
+For a Zsigmondy primitive divisor, the body-difference valuation is exactly the
+valuation on the residual `GN` kernel.
+-/
+theorem padicValNat_bodyDiff_eq_GN_of_zsigmondyPrimitivePrimeDivisor
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    padicValNat q (a ^ d - b ^ d) =
+      padicValNat q (GN d (a - b) b) :=
+  padicValNat_bodyDiff_eq_GN_of_primitivePrimeFactor
+    (primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor hprim)
+    hd hd1 hab_lt
+
 /--
 Non-exceptional primes cannot sit in the gcd between the visible boundary and
 the residual `GN` kernel.
@@ -161,5 +245,17 @@ theorem anchoredGNCarrier_of_bodyPrimitivePrimeFactor
   · exact hasPositiveAnchorPrime_self_of_prime hq.1
   · exact primitivePrimeFactor_dvd_bodyGN_of_cosmicBoundary hq hd hd1
 
+/--
+Zsigmondy primitive divisors can be packaged as anchored GN carriers.
+-/
+theorem anchoredGNCarrier_of_zsigmondyPrimitivePrimeDivisor
+    {q a b d : ℕ}
+    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b d q)
+    (hd : 0 < d) (hd1 : 1 < d) (hab_lt : b < a) :
+    AnchoredGNCarrier q d (a - b) b q :=
+  anchoredGNCarrier_of_primitivePrimeFactor
+    (primitivePrimeFactorOfDiffPow_of_zsigmondyPrimitivePrimeDivisor hprim)
+    hd hd1 hab_lt
+
 end Petal
 end DkMath
````
`````
