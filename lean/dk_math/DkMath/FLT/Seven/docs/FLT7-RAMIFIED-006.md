# RAMIFIED-006

## RAMIFIED-005 総合判定

**Outcome A、全面採用です。** 🧙‍♀️✨️

PR head は報告どおり、

```text
534dacb4b8f8adadb102cff9adde31995c0889b8
```

へ更新されています。PR #65 は open / draft / mergeable、Lean CI run 403 も **success** です。

[PR にレビューを記録しました](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5101767230)

今回の実装は、前回の推論を正確に Lean theorem へ変換しています。

```text
B := residualRoot

B mod 7 = 1
B^7 mod 49 = 1

B mod 49 ∈ {1,8,15,22,29,36,43}

explicitUnit が七乗
  ↔ B = 1 mod 49
```

generic な六 unit residue も、canonical summit では `{19,31,48}` へ縮みました。

しかし、ここでさらに重要な道が見えました。

## 第一の新発見：terminal summit では $A$ も $7$-unit

記号を、

```text
A := gapRoot
B := residualRoot
```

とします。

common summit は、

$$\operatorname{distinguished}=7AB$$

を保持しています。

一方、元の terminal packet は、選択された endpoint factor を、

$$\operatorname{distinguished}=7\cdot\operatorname{carrierUnit}$$

とし、

$$7\nmid\operatorname{carrierUnit}$$

まで持っています。

Row-Y なら distinguished は $y$、Row-Z なら $z$ なので、両 branch で、

$$\operatorname{carrierUnit}=AB$$

です。

すでに、

$$7\nmid B$$

なので、

$$\boxed{7\nmid A}$$

も従います。

これは現在の generic `PrimitiveRamifiedSummitPacket` が忘れている、**terminal 起源固有の情報**です。

その結果、現在の一般式、

$$v_7(|v|)=5+7v_7(A)$$

は terminal summit では、

$$\boxed{v_7(|v|)=5}$$

へ固定されます。

さらに、

$$v_7(|c-e|)=6$$

$$v_7(|R-L|)=6$$

です。

つまり terminal ramified 世界では、深さは可変ではありません。

```text
root.snd       exact depth 5
endpoint gap   exact depth 6
cubic gap      exact depth 6
```

ここは最優先で packet 化すべきです。

## 第二の新発見：本当の整数方程式

次を置きます。

```text
v := root.snd

S := seventhPowerSndCore(root.fst, root.snd)

Q := ramifiedGapQuotient(7^5 A^7, endpointRight).snd
```

RAMIFIED-001 の exact equation は、

$$7vS=7^6A^7Q$$

です。

整数環で $7$ を消去すると、

$$\boxed{vS=7^5A^7Q}$$

を得ます。

RAMIFIED-003〜005 の unit class は、この整数分解を $7$-局所化した影です。

したがって、次は unit をさらに眺めるより、この式の**素因子住所**を作る方が強い。

## 左辺の二因子は互いに素

### $v$ と $S$

$S$ の定義は、

$$S=u^6+3u^5v-5u^4v^2-15u^3v^3-3u^2v^4+5uv^5+v^6$$

です。

mod $v$ では、

$$S\equiv u^6\pmod v$$

です。

root coordinates は primitive、

$$\gcd(u,v)=1$$

なので、直ちに、

$$\boxed{\gcd(|v|,|S|)=1}$$

となります。root coordinate coprimality はすでに証明済みです。

### $B$ と $S$

さらに、直接展開すると次の恒等式があります。

$$S=B\left(u^4+2u^3v-9u^2v^2-10uv^3+25v^4\right)-49v^6$$

ここで、

$$B=\operatorname{norm}(u,v)=u^2+uv+2v^2$$

です。

もし素数 $q$ が $B$ と $S$ の双方を割れば、

$$q\mid49v^6$$

となります。

しかし、

```text
gcd(B,v) = 1
7 ∤ B
```

なので不可能です。

したがって、

$$\boxed{\gcd(B,|S|)=1}$$

です。

これはかなり重要です。`residualRoot` と `sndCore` は、mod $7$ だけでなく**整数全体で素因子を共有しません**。

## 右辺の三因子も分離できる

terminal summit では、

$$7\nmid A,\qquad7\nmid Q$$

です。

また endpoint coprimality と、

$$c-e=7^6A^7$$

から、

$$\gcd(A,e)=1$$

です。

一方、

$$Q=-e^2-7eh-14h^2,\qquad h=7^5A^7$$

なので mod $A$ では、

$$Q\equiv-e^2\pmod A$$

です。

したがって、

$$\boxed{\gcd(A,|Q|)=1}$$

も得られます。

よって整数等式、

$$|v|\cdot|S|=7^5\cdot A^7\cdot|Q|$$

は、左右とも pairwise coprime な factor family です。

## ここに新しい 2×3 routing が生まれる

既存の `CoprimeTripleRouting` を利用し、

```text
left triple:
  |v|
  |S|
  1

right triple:
  7^5
  A^7
  |Q|
```

を routing できます。

第三の左因子が $1$ なので、実質は **2×3 routing board** です。

```text
                   7^5       A^7       |Q|
                 ┌────────┬────────┬────────┐
|v|              │ 7^5    │ Aᵥ^7   │ Qᵥ     │
                 ├────────┼────────┼────────┤
|S|              │ 1      │ Aₛ^7   │ Qₛ     │
                 └────────┴────────┴────────┘
```

ここから、

$$|v|=7^5A_v^7Q_v$$

$$|S|=A_s^7Q_s$$

$$A=A_vA_s$$

$$|Q|=Q_vQ_s$$

という exact split が得られます。

$Q_v$ は本質的には、

$$\boxed{Q_v=\gcd(|v|,|Q|)}$$

です。

これを **ramified compensation core** と呼べます。

## root-cubic gap の本当の形

RAMIFIED-001 の cubic difference は、

$$R-L=7vB$$

です。

上の factor split を代入すると、

$$|R-L|=7^6A_v^7Q_vB$$

となります。

したがって root-cubic gap が整数の ramified seventh-power shape、

$$|R-L|=7^6C^7$$

を持つための本当の条件は、

$$\boxed{Q_vB=W^7}$$

です。

これが、これまで「root-cubic gap shape receiver」と呼んでいたものの正体です。

つまり未解決 receiver は、曖昧な存在命題ではありません。

```text
compensationCore × residualRoot
  が完全七乗である
```

という一つの整数命題です。

## RAMIFIED-005 の六 branch の意味も変わる

$B$ が非自明 principal class、

$$B\in{8,15,22,29,36,43}\pmod{49}$$

であるとします。

もし $Q_vB$ が整数七乗なら、mod $49$ では $Q_v$ が $B$ の unit-class debt を正確に返済しなければなりません。

```text
B:
  非七乗 principal digit

Qᵥ:
  B の逆 principal digit を供給

QᵥB:
  七乗 class
```

したがって非自明 branch は、単なる「失敗」ではありません。

$$\boxed{\text{非自明 }B\text{ は必ず非自明 compensation core }Q_v\text{ を要求する}}$$

特に、

$$Q_v=1$$

なら、

$$Q_vB=B$$

なので、global seventh-power receiver は $B=1\pmod{49}$ branch でしか成立できません。

## compensation prime の性質

$Q_v>1$ なら、ある素数 $q$ が、

$$q\mid v,\qquad q\mid Q$$

を満たします。

この $q$ は、

* $q\ne7$
* $q\nmid B$
* $q$ は $T,L,R$ のどれも割らない
* したがって ramified endpoint/root product routing の外にいる
* 純粋に gap compensation channel にのみ現れる

という特殊な prime です。

さらに $q\mid Q$ は、

$$e^2+7eh+14h^2\equiv0\pmod q$$

を意味します。

$q\nmid h$ のとき $t=e/h$ と置けば、

$$t^2+7t+14\equiv0\pmod q$$

となり、判別式は、

$$\Delta=49-56=-7$$

です。

したがって、

$$\boxed{-7\text{ が }q\text{ 上で平方剰余}}$$

でなければなりません。

つまり compensation prime は無秩序ではなく、**判別式 $-7$ によって選別された split prime**です。

これは `TraceOneInt (-2)` の二次整数環そのものと一致しています。

## 切り開くべき次の道

次 checkpoint は、higher Hensel lifting より先にこちらです。

```text
FLT7-RAMIFIED-006
terminal second-coordinate compensation routing
```

### Phase A：terminal summit 強化

```lean
structure TerminalPrimitiveRamifiedSummitPacket where
  summit : PrimitiveRamifiedSummitPacket
  carrierUnit : ℕ

  carrier_eq :
    carrierUnit = summit.gapRoot * summit.residualRoot

  gap_residual_coprime :
    Nat.Coprime summit.gapRoot summit.residualRoot

  gapRoot_not_seven_dvd :
    ¬ 7 ∣ summit.gapRoot

  rootSnd_depth_eq_five :
    padicValNat 7 (Int.natAbs summit.root.snd) = 5

  endpointGap_depth_eq_six :
    padicValNat 7
      (Int.natAbs
        (summit.endpointLeft - summit.endpointRight)) = 6

  cubicGap_depth_eq_six :
    padicValNat 7
      (Int.natAbs
        (ramifiedRightCubic summit.root.fst summit.root.snd -
         ramifiedLeftCubic summit.root.fst summit.root.snd)) = 6
```

### Phase B：gcd ledger

```lean
rootSnd_sndCore_coprime
rootNorm_rootSnd_coprime
rootNorm_sndCore_coprime
gapRoot_endpointRight_coprime
gapRoot_gapQuotient_coprime
```

中心 polynomial identity：

```lean
theorem sndCore_eq_norm_mul_quartic_sub_49_mul_snd_pow_six :
  S =
    B * (u^4 + 2*u^3*v - 9*u^2*v^2 -
      10*u*v^3 + 25*v^4) -
    49*v^6
```

### Phase C：formal 2×3 routing

```lean
structure RamifiedSecondCoordinateRoutingPacket where
  summit : TerminalPrimitiveRamifiedSummitPacket
  routing : CoprimeTripleRouting
    (natAbs v) (natAbs S) 1
    (7^5) (A^7) (natAbs Q)
```

### Phase D：compensation receiver

```lean
def ramifiedCompensationCore : ℕ :=
  Nat.gcd (Int.natAbs v) (Int.natAbs Q)
```

最終 theorem：

```lean
theorem cubicGap_natAbs_eq :
  Int.natAbs (R - L) =
    7^6 * verticalGapRoot^7 *
      (ramifiedCompensationCore * residualRoot)
```

そして receiver：

```lean
def RamifiedCubicGapSeventhShapeReceiver : Prop :=
  ∃ w : ℕ,
    ramifiedCompensationCore * residualRoot = w^7
```

## Higher Kummer は並行路

`B=1 mod49` branch については、coherent unit tower が $\mathbb Z_7$ 上の七乗を持つことを証明できます。

ただし、

$$f(X)=X^7-U$$

の導関数は、

$$f'(X)=7X^6$$

で $7$-unit ではありません。

したがって普通の simple-root Hensel をそのまま使う道ではありません。

正しい構造は、

$$\mathbb Z_7^\times\cong\mu_6\times(1+7\mathbb Z_7)$$

と、

$$\left(\mathbb Z_7^\times\right)^7
=\mu_6\times(1+49\mathbb Z_7)$$

です。

RAMIFIED-005 の、

$$B=1\pmod{49}$$

は、この Kummer 条件そのものです。

これを証明すれば、

```text
B = 1 mod 49
  ↔ coherent unit tower は Z_7 上の七乗

B ≠ 1 mod 49
  ↔ 全高次層で永久に非七乗
```

まで閉じます。

しかしこれは局所定理です。整数降下を作るのは compensation routing 側です。

## 最終的な攻撃図

```text
RAMIFIED-005
  residualRoot B の一桁分類
            │
            ├───────────────┐
            │               │
            ▼               ▼
local Kummer route      integer factor route
B = 1 iff Z₇ seventh    vS = 7⁵A⁷Q
                            │
                            ▼
                     2×3 factor routing
                            │
                            ▼
                 compensation core Qᵥ
                            │
                            ▼
                  |R-L| = 7⁶Aᵥ⁷(QᵥB)
                            │
              ┌─────────────┴─────────────┐
              ▼                           ▼
          QᵥB = W⁷                   QᵥB ≠ W⁷
       exact global shape          explicit obstruction
```

$$\boxed{\text{次の魔核は }B\text{ 単体ではなく、}\gcd(|v|,|Q|)\cdot B}$$

RAMIFIED-005 により局所世界は完成しました。

次は、局所 unit debt を誰が支払っているのかを、整数の素因子住所として暴く段階です。これが現時点で最も太く、DkMath らしい突破路です。
