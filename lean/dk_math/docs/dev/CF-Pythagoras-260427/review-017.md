# review

おお、S2-L も通ったか。
これは重要じゃ。ついに **既存 `PrimitiveBeam` 側の GN 情報が、Chapter 2 の `PowerBeam` valuation engine に流入できる形** になった。ここまで来ると、S2 はかなり「接続された理論」になっておる。

## 1. 何が閉じたか

今回閉じたのは、主に三つじゃ。

まず、

$$
v_p(|GN(3,a-b,b)|)\le 1
$$

から

$$
v_p(|\operatorname{powerBeam}_3(b,a)|)\le 1
$$

へ移す

```lean
powerBeam_three_padicValNat_le_one_of_GN_le_one
```

が入った。

次に、

$$
Squarefree(|GN(3,a-b,b)|)
$$

から

$$
Squarefree(|\operatorname{powerBeam}_3(b,a)|)
$$

へ移す

```lean
powerBeam_three_squarefree_of_GN_squarefree
```

が入った。

そして一番大きいのが、

```lean
primitive_prime_dvd_powerBeam_three_natAbs
```

じゃ。これは Nat 側の

$$
q \mid GN(3,a-b,b)
$$

を、Int 側の

$$
q \mid |\operatorname{powerBeam}_3(b,a)|
$$

へ運ぶ wrapper になっておる。`PrimitiveBeam.primitive_prime_dvd_GN` の出力を、Chapter 2 側がそのまま使える `p ∣ (powerBeam 3 ...).natAbs` 型に変換できるようになったわけじゃ。

## 2. 数学的意味

ここでようやく、二つの流れが接続された。

これまで Chapter 2 側では、

$$
x^d+y^d=z^d
$$

から

$$
y^d=(z-x)\operatorname{powerBeam}_d(x,z)
$$

を得て、さらに Beam 側素因子の valuation 制約を作った。

一方、既存 `PrimitiveBeam` 側では、primitive prime が (GN) を割る、という情報があった。

今回の bridge により、少なくとも (d=3) では、

$$
q\mid GN(3,a-b,b)
$$

が

$$
q\mid \operatorname{powerBeam}_3(b,a)
$$

へ渡る。

つまり、

$$
\text{Primitive prime engine}
\to
GN
\to
PowerBeam
\to
valuation contradiction engine
$$

という流れができた。
これはかなり大きい。別々に育っていた道が、とうとう合流したのじゃ。

## 3. 実装評価

今回の実装で一番良いのは、Nat / Int の型差を wrapper で吸収した点じゃ。

`PrimitiveBeam` 側は Nat API、Chapter 2 の FLT / PowerBeam 側は Int + `natAbs` API。
このズレは放っておくと後続の証明を毎回重くする。

今回、

```lean
Nat.cast_sub
exact_mod_cast
Int.natCast_dvd
```

を使って、Nat `GN` の割り切りを Int `GN` の `natAbs` へ運んだ。History にも、直接 `rw` / `ring` では和の展開と `natAbs` の正規形が噛み合わず、cast 経由に修正したとある。

これは実装上かなり正しい判断じゃ。
今後はこの wrapper を使えば、後続は Nat/Int 変換を意識しなくてよい。

## 4. 注意点

`PrimitiveBeam` import により、依存先 `ZsigmondyCyclotomicResearch.lean` の既存 `sorry` warning が流入する点は注意じゃ。今回追加分由来ではないと記録されているので問題はないが、公開導線としては少し重い。

将来的には、

```text
PowerGapBeamGN.lean
  軽量 GN bridge

PowerGapBeamPrimitive.lean
  PrimitiveBeam import を含む重い bridge
```

のように分けてもよい。
今は作業速度を優先してよいが、公開 API を整える段階では分離候補じゃ。

## 5. 次の提案: S2-M

次は History にある通り、

> GN 側 squarefree / valuation 上界を S2-G/S2-H の contradiction API へ直接接続する d=3 wrapper

が自然じゃ。

つまり、今は部品としては揃った。

* `primitive_prime_dvd_powerBeam_three_natAbs`
* `powerBeam_three_padicValNat_le_one_of_GN_le_one`
* `powerBeam_three_squarefree_of_GN_squarefree`
* `flt_beam_prime_val_le_one_contradiction`
* `flt_beam_squarefree_prime_contradiction`

次はこれらを合成して、d=3 用の「一発 contradiction wrapper」を作る。

## 6. 具体的な候補

### 6.1. GN valuation 上界版

狙う定理はこうじゃ。

```lean
theorem flt_three_beam_GN_val_le_one_contradiction
    {p : ℕ} {x y z : ℤ}
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ 3 + y ^ 3 = z ^ 3)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ 3)
    (hbeam : p ∣ (powerBeam 3 x z).natAbs)
    (hbeam_ne : (powerBeam 3 x z).natAbs ≠ 0)
    (hGN_le_one :
      padicValNat p (DkMath.CosmicFormulaBinom.GN 3 (z - x) x).natAbs ≤ 1) :
    False := by
  apply flt_beam_prime_val_le_one_contradiction
  · norm_num
  · norm_num
  · exact hcop
  · exact hflt
  · exact hy_ne
  · exact hp
  · exact hpnd
  · exact hbeam
  · exact hbeam_ne
  · -- convert GN valuation upper bound to PowerBeam upper bound
```

最後は `powerBeam_three_padicValNat_le_one_of_GN_le_one` を、(a=z), (b=x) で使う。

### 6.2. GN squarefree 版

より自然なのはこちらかもしれぬ。

```lean
theorem flt_three_beam_GN_squarefree_contradiction
    {p : ℕ} {x y z : ℤ}
    (hcop : Int.gcd z x = 1)
    (hflt : x ^ 3 + y ^ 3 = z ^ 3)
    (hy_ne : y.natAbs ≠ 0)
    (hp : Nat.Prime p)
    (hpnd : ¬ p ∣ 3)
    (hbeam : p ∣ (powerBeam 3 x z).natAbs)
    (hbeam_ne : (powerBeam 3 x z).natAbs ≠ 0)
    (hGN_sq :
      Squarefree (DkMath.CosmicFormulaBinom.GN 3 (z - x) x).natAbs) :
    False := by
  apply flt_beam_squarefree_prime_contradiction
  · norm_num
  · norm_num
  · exact hcop
  · exact hflt
  · exact hy_ne
  · exact hp
  · exact hpnd
  · exact hbeam
  · exact hbeam_ne
  · exact powerBeam_three_squarefree_of_GN_squarefree hGN_sq
```

これはかなり軽く閉じるはずじゃ。

### 6.3. Nat primitive prime から直接 hbeam を供給する版

さらに一段進めるなら、Nat 版 primitive prime から `hbeam` を供給する。

ただし入力が Nat (a,b) で、FLT bridge が Int (x,y,z) なので、ここは少し設計が必要じゃ。

まずは、既にできた

```lean
primitive_prime_dvd_powerBeam_three_natAbs
```

を使えるように、FLT 変数を Nat 起源にする wrapper を作るのがよい。

たとえば、

```lean
theorem primitive_prime_dvd_powerBeam_three_from_nat_endpoints
    {q a b : ℕ}
    ...
```

はもうあるので、次はそれを contradiction wrapper へ渡すだけじゃ。

ただし、`hflt : (b : ℤ)^3 + y^3 = (a : ℤ)^3` のような形にするか、Nat FLT package から cast して渡すかを決める必要がある。

ここは少し待ってよい。

## 7. 優先順位

わっちのおすすめはこの順じゃ。

1. **GN squarefree 版 contradiction wrapper**
2. **GN valuation-le-one 版 contradiction wrapper**
3. **primitive prime divisibility を hbeam として供給する d=3 wrapper**
4. 必要なら `PowerGapBeamPrimitive.lean` へファイル分割

まず 1 と 2 は薄い wrapper なので、すぐ閉じられる可能性が高い。
3 は Nat/Int/FLT package の型設計が絡むので、その後でよい。

## 8. Chapter 2 の現在地

ここまでで Chapter 2 はかなり強くなった。

* 差冪分解
* FLT Gap/Beam bridge
* gcd 制御
* valuation 抽出
* squarefree contradiction
* GN ↔ PowerBeam bridge
* primitive prime divisibility の Nat→Int PowerBeam 移送

ここまで no-sorry で来たのは見事じゃ。

次の S2-M で、GN squarefree / valuation 上界から直接 `False` へ行く wrapper を置けば、Chapter 2 は **GN fuel 接続版 refuter** として一段まとまる。

わっちの見立てでは、その後に初めて `FLTPowerGapBeamDatum` 構造体を検討してよい。今はまだ wrapper で押し切れるぞ。
