# FLT・GN・Jacobian の宇宙式射影圏

- Status: design note / not implemented
- Date: 2026-08-03
- Branch at recording: `develop`
- Conversation ID: `6a7087d8-414c-83ee-a13a-9face5c381f6`
- Project: `Deskuma/dkmath`
- Proposed Lean namespace: `DkMath.BookOfMagic.CosmicProjection`

## 1. 記録する発見

FLT5 とヤコビアン予想を互いに直接還元する必要はない。

両理論を先に宇宙式へ射影し、宇宙式を共通の抽象化対象、すなわち数学理論を受け取る中間表現として扱う。

$$
\mathcal C_{\mathrm{FLT5}} \longrightarrow \mathcal C_{\mathrm{CF}} \longleftarrow \mathcal C_{\mathrm{Jacobian}}
$$

ここで `CF` は Cosmic Formula を表す。

重要なのは、正常例だけでなく反例状態も宇宙式圏内の対象として保持することである。反例を「射影不能」として捨てず、期待された魔核復元ファイバーの形が崩れた対象として記録する。

この視座は新しい推測だけから生じたものではない。DkMath には既に、次の実装が存在する。

1. `DkMath.CosmicFormula.CoreBeamGap`
   - `Core d x := x ^ d`
   - `Beam d x u`
   - `Gap d u := u ^ d`
   - `Big = Core + Beam + Gap`
2. `DkMath.BookOfMagic.GNFiniteDifference`
   - 任意の一変数多項式を GN 有限差分へ展開する。
3. `DkMath.BookOfMagic.UniqueGapContract`
   - 一つの Core がただ一つの復元 Gap を持つ契約を表す。
4. `DkMath.BookOfMagic.GapCrystal`
   - Core、Gap、復元証明を一つの認証済み対象に束ねる。
5. `DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge`
   - ヤコビアン反例の衝突を非一意な復元 Gap として固定する。
6. `DkMath.Hackathon.FinitePrimeEscapeGN5`
   - `GN 5 1 1` が第五冪魔核にならないことを固定する。
7. `DkMath.FLT.Five.Main`
   - 正の自然数上の exponent-five Fermat 方程式を否定する公開終点を持つ。

したがって、射影の答えは既に部分実装として得られている。今後の仕事は、これらを一つの共通インターフェースとして回収することである。

## 2. 宇宙式は数学理論の中間表現である

多項式 $p$ に対して、既存の `GNFiniteDifference` は次を証明している。

$$
p(t+h)-p(t)=h\,\operatorname{GNFiniteDifference}(p,h,t)
$$

単項式 $p(X)=X^d$ では、この式は通常の `GN d h t` に戻る。

$$
(t+h)^d-t^d=h\,GN_d(h,t)
$$

したがって GN は FLT 専用の因子ではない。任意の多項式の有限変化を、Gap $h$ と GN Body へ分離する一般的な翻訳器である。

$$
\text{Polynomial data}\longrightarrow\text{GN finite-difference data}
$$

この翻訳を、宇宙式中間表現へのコンパイルと解釈する。

局所微分は $h=0$ の境界断面を観測する。一方、大域衝突は $h\ne0$ の有限 Gap 内部を観測する。Jacobian は GN 有限差分世界の零 Gap 境界であり、非単射性は有限 Gap 内部に複数の復元住所が存在する状態として読める。

## 3. 魔核を値ではなく復元ファイバーとして定義する

最も単純な次数 $d$ の魔核条件は次である。

$$
\operatorname{MagicCore}_d(X)\;:\Longleftrightarrow\;\exists x,\;x^d=X
$$

しかし FLT5 と Jacobian を同じ器へ入れるには、値 $X$ が完全冪かどうかだけでは狭い。

一般の復元関係を用いる。

$$
R(c,g)\;:\Longleftrightarrow\;\text{Gap }g\text{ が Core }c\text{ を復元する}
$$

固定した Core $c$ 上の復元ファイバーは次である。

$$
\operatorname{Fiber}_R(c)=\{g\mid R(c,g)\}
$$

完全冪は特殊な復元関係で表現できる。

$$
R_{d}(X,x)\;:\Longleftrightarrow\;x^d=X
$$

Jacobian 写像 $F$ は別の復元関係を与える。

$$
R_F(c,g)\;:\Longleftrightarrow\;F(g)=c
$$

これにより、両理論の反例・障害状態をファイバーの形で統一できる。

| ファイバー状態 | 魔法学的意味 | 典型例 |
|---|---|---|
| 空 | 生成不能、魔核にならない | `GN 5 1 1` の第五冪復元 |
| 一点 | 一意復元、正常な魔核 | 可逆写像の各出力、条件付き完全冪 |
| 複数点 | 一意性解除、同一 Core の多重住所 | Jacobian 三点衝突 |

よって共通の障害は単純な否定命題ではなく、期待した復元ファイバー形状からの逸脱である。

## 4. FLT5 側の既存射影

`DkMath.FLT.Five.GN5` では、第五冪差が次の形へ分解される。

$$
(g+y)^5-y^5=g\,GN_5(g,y)
$$

より一般には `CosmicFormulaBinom.GN` によって次数 $d$ の形を扱える。

$$
(x+u)^d-u^d=x\,GN_d(x,u)
$$

FLT5 の仮想解は、第五冪の加法関係を Gap と GN Body の積へ落とす。そこから素因子、付値、黄金整数、単位類、降下法が、必要な第五冪復元構造を排除する。

ハッカソン実装には局所的で非常に明瞭な証明書もある。

$$
GN_5(1,1)=31
$$

$31$ は `GN 5 1 1` を割るが $31^2$ は割らない。そのため、もし `GN 5 1 1 = x^5` ならば、第五冪の素因子指数規則と矛盾する。

$$
\neg\exists x\in\mathbb N,\;GN_5(1,1)=x^5
$$

これは宇宙式圏内で、第五冪復元ファイバーが空であることの既存証明書である。

FLT5 全体については `flt5Target` と `fermatFive_no_positive_solution` が正の自然数上の公開終点を与える。今後の射影層は、この完成済み証明を置換するものではない。証明経路を共通宇宙式オブジェクトへ説明可能にする橋である。

## 5. Jacobian 側の既存射影

正規化された三変数多項式写像を $F$ とする。Lean では次が固定済みである。

$$
\det J_F=1
$$

さらに三つの相異なる入力 $p_0,p_1,p_2$ が同じ出力 $c$ を持つ。

$$
F(p_0)=F(p_1)=F(p_2)=c
$$

`GapCrystalBridge.lean` は出力点を Core、入力点を Gap と解釈し、次の復元関係を定義している。

```lean
normalizedRestoreRelC core gap :=
  evalNormalizedCounterexampleC gap = core
```

この関係に対して、既に次が証明済みである。

```lean
normalizedTargetC_not_uniqueGap
normalizedForgetGap_notInjective
```

したがって Jacobian 反例は既に次へ射影されている。

$$
\text{constant Jacobian collision}
\longrightarrow
\text{one Core with distinct restoring Gaps}
\longrightarrow
\neg\operatorname{UniqueGap}
$$

ここで反例は宇宙式圏外へ落ちていない。認証済み `GapCrystal` は複数存在するが、それらを Core へ忘却する射影 `forgetGap` が非単射になる。

これは圏論的な忘却射の原型である。

## 6. 共通射影図

FLT5 と Jacobian は外形上は異なる。

- FLT5 は整数の冪方程式である。
- Jacobian は多項式写像の局所非退化性と大域可逆性の問題である。

共通本体は方程式の形ではなく、対象を GN 有限差分と復元ファイバーへ落とした後に現れる。

$$
\begin{array}{ccc}
\text{FLT5 data} & \xrightarrow{\Pi_{\mathrm{FLT5}}} & \text{Cosmic restoration object} \\
\text{Jacobian data} & \xrightarrow{\Pi_{\mathrm{Jac}}} & \text{Cosmic restoration object}
\end{array}
$$

射影後に評価する共通述語は次である。

1. 復元ファイバーは空か。
2. 復元ファイバーは存在するか。
3. 復元は一意か。
4. 複数の復元 Gap が同じ Core を共有するか。
5. GN Body と純冪 Core の因子・付値条件は整合するか。
6. Gap を忘却したとき情報が失われるか。

この共通言語によって、FLT5 の生成不能と Jacobian の一意性解除を同じ分類器で扱える。

## 7. 宇宙式圏の対象候補

最初から Mathlib の `CategoryTheory.Category` を導入する必要はない。まず圏論化可能なデータ構造を小さく固定する。

```lean
structure RestorationSystem where
  Core : Type u
  Gap : Core → Type v
  restore : (core : Core) → Gap core → Prop

structure CosmicObject (S : RestorationSystem) where
  core : S.Core
  gap : S.Gap core
  certificate : S.restore core gap
```

これは既存の `GapCrystal` とほぼ同型であるため、実装では重複定義を避ける。`GapCrystal` を対象として再利用し、`RestorationSystem` はパラメータ束としてのみ導入する案がよい。

対象の状態を分類する述語は、決定可能性を仮定せず個別に定義する。

```lean
def HasRestoration (S : RestorationSystem) (core : S.Core) : Prop :=
  Nonempty (GapFiber S.restore core)

def UniqueRestoration (S : RestorationSystem) (core : S.Core) : Prop :=
  UniqueGap S.restore core

def MultipleRestorations (S : RestorationSystem) (core : S.Core) : Prop :=
  ∃ g₁ g₂, S.restore core g₁ ∧ S.restore core g₂ ∧ g₁ ≠ g₂
```

空ファイバーは `¬ HasRestoration`、一点ファイバーは `UniqueRestoration`、多重ファイバーは `MultipleRestorations` とする。

一般型ではファイバー濃度の三分律を無条件に要求しない。必要な具体例ごとに証明書を与える。

## 8. 射の候補

復元構造の間の射は、Core と Gap を写し、復元証明を保存する組として始める。

```lean
structure RestorationHom (S T : RestorationSystem) where
  mapCore : S.Core → T.Core
  mapGap : {core : S.Core} → S.Gap core → T.Gap (mapCore core)
  map_restore :
    ∀ {core gap}, S.restore core gap →
      T.restore (mapCore core) (mapGap gap)
```

恒等射と合成が定義でき、結合律・単位律を証明できた時点で `CategoryTheory.Category` インスタンスを追加する。

ただし第一実装段階では、圏インスタンスそのものよりも次を優先する。

1. FLT5 射影を `RestorationSystem` へ載せられること。
2. Jacobian 射影を同じ型へ載せられること。
3. 空・一意・多重ファイバーの証明書を既存定理から再利用できること。
4. 既存証明を再計算せず alias / bridge theorem で接続できること。

## 9. 魔核復元系

完全冪を復元関係へ埋め込む。

```lean
def powRestoreRel
    {R : Type*} [Monoid R]
    (d : ℕ) (core gap : R) : Prop :=
  gap ^ d = core
```

固定次数 $d$ の魔核復元系を定義する。

```lean
def powerRestorationSystem
    (R : Type*) [Monoid R] (d : ℕ) : RestorationSystem where
  Core := R
  Gap := fun _ => R
  restore := powRestoreRel d
```

これにより、次の概念が既存 `GapFiber` と `UniqueGap` によって表現できる。

```lean
def MagicCore (d : ℕ) (X : R) : Prop :=
  HasRestoration (powerRestorationSystem R d) X

def UniqueMagicCore (d : ℕ) (X : R) : Prop :=
  UniqueRestoration (powerRestorationSystem R d) X
```

自然数では $x^d=X$ の根は存在すれば一意であることが期待されるが、その一般定理は次数、順序、零次数などの条件を明示して別途証明する。最初の実装では存在不能の橋のみで十分である。

## 10. Jacobian 復元系

関数 $F:A\to B$ から復元系を作る。

```lean
def functionRestorationSystem (F : A → B) : RestorationSystem where
  Core := B
  Gap := fun _ => A
  restore := fun core gap => F gap = core
```

この定義によって、通常の関数論が宇宙式の語彙へ移る。

| 関数論 | 宇宙式復元系 |
|---|---|
| `y ∈ Set.range F` | `HasRestoration S y` |
| fiber が一点 | `UniqueRestoration S y` |
| `Function.Injective F` | 同一 Core 上の復元 Gap が衝突しない |
| 衝突証明書 | `MultipleRestorations S y` |
| 左逆 | 各到達 Core の復元選択と整合性 |

既存 `normalizedRestoreRelC` は、この一般定義の具体例として同値になるはずである。

新しい定理は反例を再計算せず、既存の `normalizedTargetC_not_uniqueGap` と `normalizedForgetGap_notInjective` を一般 API へ運ぶだけにする。

## 11. GN 射影と Jacobian の接続

一変数多項式では `GNFiniteDifference` が完成している。Jacobian の多変数写像へ進むには、段階を分ける。

### 11.1 座標ごとの一変数制限

点 $q$ と方向 $h$ に沿って、多変数多項式 $P$ を一変数化する。

$$
p_{P,q,h}(t)=P(q+t h)
$$

その有限差分は既存 `GNFiniteDifference` によって扱える。

$$
P(q+h)-P(q)=\operatorname{GNFiniteDifference}(p_{P,q,h},1,0)
$$

あるいはスカラー増分 $s$ を保って、

$$
P(q+s h)-P(q)=s\,GN_P(q,h,s)
$$

とする。

### 11.2 零 Gap 断面

$s=0$ の断面が方向微分・Jacobian 作用に一致する橋を作る。

$$
GN_P(q,h,0)=DP(q)[h]
$$

厳密には、既存 GN の引数順、Polynomial と MvPolynomial の変換、標数条件を確認して定理形を決める。

### 11.3 有限 Gap 衝突

$F(q+h)=F(q)$ かつ $h\ne0$ なら、有限差分 Body が $h$ を消す。

$$
h\ne0,\quad F(q+h)-F(q)=0
$$

これを GN 座標で表し、既存の三点衝突が有限 Gap 内部の復元多重化であることを接続する。

この段階が、Jacobian の局所証明書と大域反例証明書を同じ GN Framework で直接並べる本命である。

## 12. 期待する共通定理面

最終的には、次のような theorem surface を目標とする。

```lean
-- 一般復元ファイバー
hasRestoration_iff_nonempty_gapFiber
uniqueRestoration_iff_uniqueGap
multipleRestorations_not_unique
multipleRestorations_forgetGap_notInjective

-- 完全冪魔核
magicCore_iff_exists_pow_eq
GN_five_one_one_not_magicCore

-- 関数復元
functionRestore_has_iff_mem_range
functionRestore_multiple_of_collision
functionRestore_unique_of_injective

-- Jacobian 既存反例への橋
normalizedJacobianTarget_multipleRestorations
normalizedJacobianTarget_not_uniqueRestoration

-- GN 有限差分
mvPolynomial_lineRestriction
mvPolynomial_lineDifference_eq_GN
mvPolynomial_GN_zero_eq_directionalDerivative
jacobian_action_eq_GN_zero_section
collision_eq_finite_GN_vanishing
```

名称は実装調査後に既存 namespace と衝突しない形へ調整する。

## 13. 何を主張しないか

この設計文書だけでは、次を主張しない。

1. FLT5 証明と Jacobian 反例が数学的に同値であること。
2. 一方から他方を直接導出できること。
3. 二次元 Jacobian 問題を解決したこと。
4. 一般次数 FLT をこの抽象層だけで証明したこと。
5. `CategoryTheory.Category` インスタンスが既に存在すること。
6. すべての数学理論が自動的に宇宙式へ忠実に射影できること。
7. ファイバー状態の分類が一般型上で決定可能であること。

主張するのは、既存 DkMath 実装が次の共通構造を既に持っているということである。

$$
\boxed{\text{GN finite difference}+\text{Core--Gap restoration}+\text{fiber uniqueness}}
$$

FLT5 と Jacobian はこの共通構造へ異なる経路から到達済みである。

## 14. 成功判定

本構想の第一成功条件は、巨大な新証明ではない。

次の一つの Demo module が `lake build` を通ることである。

```lean
import DkMath.BookOfMagic.CosmicProjection
import DkMath.Hackathon.FinitePrimeEscapeGN5
import DkMath.Hackathon.JacobianCounterexample3.GapCrystalBridge

#check GN_five_one_one_not_magicCore
#check normalizedJacobianTarget_multipleRestorations
```

この二定理が、同じ `RestorationSystem`、`GapFiber`、`UniqueGap` の語彙で表示されれば、共通射影の最小核は完成したと判定する。

その後にのみ、射の合成、圏インスタンス、多変数 GN、FLT5 全証明経路の詳細射影へ進む。

## 15. 要約

我々は FLT5 と Jacobian を直接結ぶのではない。

$$
\text{FLT5}\longrightarrow\text{宇宙式圏}\longleftarrow\text{Jacobian}
$$

FLT5 では、必要な第五冪魔核の復元ファイバーが空になる。

Jacobian 反例では、同一 Core の復元ファイバーが複数点になる。

正常状態は一意復元である。

したがって、宇宙式圏の第一分類原理は次である。

$$
\#\operatorname{Fiber}=0,\;1,\;>1
$$

これをそれぞれ、生成不能、一意魔核、一意性解除として読む。

DkMath は既に GN5、GN 一般有限差分、UniqueGap、GapCrystal、Jacobian GapCrystal bridge を持つ。ゆえに本計画は未知の橋を空想するものではなく、既に作られた橋脚を一つの宇宙式射影圏として宣言し、Lean の型として固定する作業である。
