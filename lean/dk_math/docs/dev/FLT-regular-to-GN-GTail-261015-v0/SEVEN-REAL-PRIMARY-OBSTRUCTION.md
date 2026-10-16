# 実三次 GN の一次単元障害：ノルム二成分と共役位相一成分

本章は、前章で判明した係数環の境界を保って単元解析を進める。
七次円分整数環の既存六次モデルを `C`、その実三次係数環を `R` と書く。
`R` は `SevenRealCubicInt`、`C` は `SevenCyclotomicDegreeSixInt.Ring` である。
実装入口は `DkMath.FLT.Kummer`。

成果は二つある。任意の六次単元について、七乗性をノルム二成分と共役位相一成分で
判定した。さらに、実三次一次合同を持つ非零 GN 一因子の局所パケットを定義し、
根を単元倍で取り替える実際の操作に対して、四つの保存定理を固定した。

後者は正規化の反復である。新しい FLT 解を作る降下とは区別する。
今回構成した局所パケットには、全 GN の完全冪や FLT 方程式を含めていない。

## 1. 三つの障害を同じ単元に付随させる

`u : Cˣ` に対して、二次共役を `bar`、実三次相対ノルムを `N` とすると、

\[
 \rho(u)=u/\bar u,\qquad
 L(u)=\operatorname{projectiveLog}(N(u))\in(\mathbf Z/7\mathbf Z)^2
\]

を定義する。前章の CM 単元解析を同じ環同型で輸送すると、
`rho(u)` は実際に `±zeta^i` のいずれかである。したがって `rho(u)^14=1`。

符号の二成分は七乗剰余類では障害にならない。そこで

\[
 \Phi(u)=\rho(u)^8\in\mu_7(C)
\]

とする。8 は偶数であり、mod 7 で1だから、符号だけを消して七次位相を保持する。
`phaseCharacter` は乗法準同型であり、値域は抽象的な「位相」という名称ではなく
実際の群 `rootsOfUnity 7 C`。`phase_target_card` がその元数7を証明する。

三成分の障害を

\[
 \mathcal O(u)=(L(u),\Phi(u))
\]

として実装したのが `unitObstruction` である。

| API | 内容 |
| --- | --- |
| `normCoordinates_mul` | `L(uv)=L(u)+L(v)` |
| `normCoordinates_seventh` | `L(v^7)=0` |
| `phaseCharacter_seventh` | `Phi(v^7)=1` |
| `unit_seventh_iff_obstruction` | `u` が七乗 iff `L(u)=0` かつ `Phi(u)=1` |
| `same_class_iff_unitObstruction_eq` | 同じ単元七乗剰余類 iff 三成分が一致 |

最後の定理は実際の商 `Cˣ / (Cˣ)^7` を識別する。
三成分の任意の組が現れるという全射性や、商群と直積全体との同型は本章では主張しない。

### 七乗性を復元する証明

必要性は、二つの写像が七乗を消すことから従う。十分性では既存の実三次単元判定から
`N(u)=v^7` を取る。一方 `Phi(u)=1` と `rho(u)^14=1` から

\[
 \rho(u)^2=1,\qquad \rho(u)^7=\rho(u)
\]

を得る。ノルムと共役比には同じ元の等式

\[
 u^2=N(u)\rho(u)
      =\bigl(\operatorname{ofReal}(v)\rho(u)\bigr)^7
\]

がある。`eta=ofReal(v)*rho(u)` とすれば、
`(u*eta^(-3))^7=u`。これは Lib の `oddPower_root_of_square` を適用する。
七次の整数合同 Kummer criterion を入力仮定にしていない。

## 2. 実三次一次合同が消すもの、残すもの

定義は係数環を明記する。

```lean
RealPrimary (delta : Cˣ) (b : R) :=
  (7 : C) ∣ (delta : C) - ofReal b
```

`b` の単元性は要求しない。`bar` は `ofReal b` を固定するので、
`delta-bar(delta)` は7で割れる。単元 `bar(delta)` で割ると
`rho(delta) ≡ 1 mod 7`。前章の六座標による `±zeta^i` の識別を使えば

\[
 \rho(\delta)=1,\qquad \Phi(\delta)=1
\]

となる。このため

\[
 \boxed{\delta\text{ が七乗}\iff L(\delta)=0}
 \quad\text{（RealPrimary のもとで）}
\]

が `realPrimary_seventh_iff_norm_zero` である。
ノルムへ移した合同先は `b^2` であり、整数の二乗とは限らない。
`relativeNorm_congruent_real` が `N(delta) ≡ b^2 mod 7` を有限恒等式から証明する。

### 係数環の境界を示す実例

実三次生成元 `alpha` は実際の単元である。その埋め込み `alphaEmbeddedUnit` について、

\[
 \delta\equiv\operatorname{ofReal}(\alpha)\pmod7,
 \qquad \Phi(\delta)=1,\qquad L(\delta)=(3,3)\ne0
\]

を証明した。従ってこの単元は七乗ではない。
もとの実三次対数は `(5,5)` であり、二次ノルムが平方になるので
`2*(5,5)=(3,3)` となる。これは FLT 反例を仮定しない具体例である。

反対側の例として `zetaUnit` はノルム座標が0でも、共役比は `zetaUnit^2`、
位相は非自明である。回帰検証で確認している。
ノルムだけでも、位相だけでも、任意の六次単元の七乗性は判定できない。

## 3. 同じ source を保つ実三次一次パケット

`PrimaryPacket` は次を保持する。

\[
 \begin{aligned}
 A&=\operatorname{realGNSource}(x,u,i)
   =\operatorname{ofReal}(x)+(1-\zeta^i)\operatorname{ofReal}(u)\ne0,\\
 A&=(\zeta^i-1)\delta\gamma^7,\\
 \delta&\equiv\operatorname{ofReal}(-u)\pmod7,
 \qquad (1-\zeta)\nmid\gamma.
 \end{aligned}
\]

ここで `x,u : R`、`1 ≤ i < 7`。係数・位相・単元・根とともに、
分解・一次合同・根の非分岐性の証明もフィールドとして保持する。
`zeta^i-1` と `1-zeta` の向きを記述どおり区別する。

許容する単元 `t` は `t^7≡1 mod 7` を満たす。
`AllowedGauge` がこの証明を持ち、`regauge` は実際の次パケット

\[
 (x,u,i,\delta,\gamma)
   \longmapsto(x,u,i,\delta t^{-7},t\gamma)
\]

を構成する。積の等式に加え、逆冪の合同と根の非分岐性を証明し直している。
これらの一般的な恒等式・可除性は `DkMath.Lib.Algebra.RootUnitGauge` に置いた。

恒等単元のほか、`zetaUnit` による非自明な根の変更も許容される。
逆の変更も `inverseGauge` として構成する。

## 4. 固定した四つの保存定理

| 定理 | 保持するもの |
| --- | --- |
| `source_preservation` | 同じ元 `A` と、取り替えた根・単元による正確な因子表示 |
| `coefficient_ring_preservation` | 同じ実三次係数 `x,u`、位相 `i`、同じ `-u` との一次合同 |
| `unit_class_preservation` | 実際の単元七乗商での一致と、障害の三成分の一致 |
| `iterated_invariant_preservation` | 任意の有限列での不変データ全体、一次合同、根の非分岐性 |

`ConservedData` は係数、位相、source、単元の商類、障害、根の主イデアルを持つ。
`snapshot` で取り出し、`iterate` が任意の有限列を実際のパケットへ順次適用する。
第四定理は単なる「保存される関係」を入力にした一般論ではなく、
構成済みの `regauge` を反復する定理である。

パケットの非空性も仮定で済ませない。任意の実三次単元 `b` について
`packetOfRealUnit b` が `x=0,u=-b,i=1,delta=ofReal(b),gamma=1` を構成する。
その source は `(zeta-1)*ofReal(b)≠0` である。
これは局所因子の例であり、全 GN の完全冪や FLT 解を作るものではない。
`b=alphaUnit` を使う回帰例では、どの有限列の取り替えでも `(3,3)` の障害が残る。

## 5. 保存反復と無限降下の境界

根を単元倍にするので、必然的に

\[
 (t\gamma)=(\gamma)
\]

という主イデアルの等式を得る。従って根の主イデアルから定まる任意の自然数測度は
この反復では厳密に減らない。`no_ideal_measure_drop` がその否定を証明する。
単元の選び直しだけでノルム障害を消すことも、イデアル測度を減らすこともできない。

この結果は FLT7 の矛盾ではない。現在の `currentLinearCarrier` に対応する
実三次 source は前章で得られたが、その carrier について本章の `RealPrimary`
を供給したとは主張しない。本章の局所パケットと現在の receiver は区別する。

次の本当の降下では、係数や source、根のイデアルを変える算術的操作を作り、
新しいパケットへの再入と適切な測度の減少を別途示す必要がある。
そのとき、何を保ち何を変えたかを本章の三成分と source 来歴で追跡できる。

FLT11・FLT13 へは実部分の単元階数がそれぞれ4、5になるという見通しがある。
ただし、それらの単元分類・位相の識別・対応する保存パケットは本章で形式化していない。

## 実装・検証の入口

- [単元障害](../../../DkMath/FLT/Kummer/SevenRealUnitObstruction.lean)
- [実三次一次合同](../../../DkMath/FLT/Kummer/SevenRealPrimaryUnit.lean)
- [四つの保存定理](../../../DkMath/FLT/Kummer/SevenRealGNConservation.lean)
- [一般の根・単元補正](../../../DkMath/Lib/Algebra/RootUnitGauge.lean)
- [回帰・公理・依存監査 suite](../../../DkMathTest/FLT/Kummer/SevenRealGNSuite.lean)
- [検証記録](evidence/validation-seven-real-primary.txt)
