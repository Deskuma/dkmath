# NOTE-020: 素数冪の自由加群構造と、非分裂な短完全列

日付: 2026-10-21。NOTE-020の独立した構造Coreとして、標数0の楕円曲線Eと素数pについて

\[
\boxed{E[p^k]\simeq_{\mathbb Z/p^k\mathbb Z}(\mathbb Z/p^k\mathbb Z)^2}
\]

を全てのk≥0で実装した。正指数では自由階数2も証明した。
また、同じ実際のE[p²]の中の位数p²の点の存在から、

\[
E[p^2]\not\simeq E[p]\times E[p]
\]

と、制限p倍写像E[p²]→E[p]が加法準同型の右逆を持たないことを証明した。
有限二項の直和は直積で表せるので、これはNOTE-020の直和非分解の主張に対応する。
**Weil対の幾何学的構成、円分行列式の無条件化、Tate加群の構成は今回の実装には含めない。**

## 1. モジュールと公開入口

| モジュール | 役割 |
| --- | --- |
| `DkMath.Lib.Algebra.TorsionPowerLifting` | 任意の可換加法群における、二つの生成元の冪の塔への持ち上げ帰納法 |
| `DkMath.Lib.NumberTheory.EllipticTorsionPrimePower` | 実際の点の持ち上げ、線形生成写像、全単射、基底・自由性・階数、塔の遷移と座標作用 |
| `DkMath.Lib.NumberTheory.EllipticTorsionNonSplit` | 位数p²の点、加法的sectionの不存在、二つのp-torsion群の直積との非同型 |
| `DkMath.FLT.FreyTorsionPrimePower` | 同じSourceの曲線への構造Coreの接続 |

本体4モジュール359行、教科書docstringを含む。名前付き公開宣言32個。
全新規Leanファイルでimport後の `#print "file: モジュール名"` を保持し、
`DkMath.Lib`・`DkMath.FLT`・ルート `DkMath` と、回帰・監査の `DkMathTest` に配線した。

## 2. Nakayamaを使わずに生成性を持ち上げる

一般の可換加法群Gについて、p倍で零になる全ての点がQ₀,Q₁の自然数係数の和で表せるとする。
またpᵏPᵢ=Qᵢとなる二点P₀,P₁を取る。
`lifted_pair_generates` は、p^{k+1}倍で零になる任意のxがP₀,P₁で生成されることを証明する。
この一般補題には素数性・有限性・局所環の仮定がない。

帰納段階では、まずxを最高段の核へ送る。

\[
p^{k+1}x=aQ_0+bQ_1.
\]

その分を元の点から引くと

\[
y=x-aP_0-bP_1,\qquad p^{k+1}y=0
\]

となる。一段低い核ではpP₀,pP₁が同じQ₀,Q₁の持ち上げなので、帰納仮定が適用できる。

\[
y=c(pP_0)+d(pP_1)
\quad\Longrightarrow\quad
x=(a+pc)P_0+(b+pd)P_1.
\]

指数0ではPᵢ=Qᵢなので、元の生成性そのものへ戻る。
これにより局所環の剰余加群・Jacobson根基・NakayamaのAPIを追加せず、既存の倍写像だけで生成性を運べた。

## 3. 同じ実際のE[p]の基底から自由加群同型へ

NOTE-016で次元2が確定し、NOTE-017で選択した `torsionBasis E p` を使う。
基底展開のZMod p係数を.valという自然数代表に読み替えると、一般群の生成補題の仮定を満たす。

NOTE-018の `multiplication_surjective` をpᵏ倍写像に適用し、各基底ベクトルの原像Pᵢを選ぶ。
この原像はp^{k+1}倍で零になるので、同じ実際のE[p^{k+1}]へ入る。
選択は非計算的であり、点の座標を数値計算したという意味ではない。

R=ZMod(p^{k+1})として、生成写像

\[
F:R^2\longrightarrow E[p^{k+1}],\qquad (a,b)\longmapsto aP_0+bP_1
\]

を線形写像として構成する。一般の持ち上げ補題がFの全射性を与える。
NOTE-019の位数公式によって両辺の位数はともに(p^{k+1})²なので、有限型上の全射は全単射になる。
ここで初めて `LinearEquiv.ofBijective` を使い、線形同型として固定する。
**位数が一致することだけから群の同型を導いたわけではない。**

公開した主なAPIは次の通り。

```lean
primePowerEquiv (k : ℕ) :
  Torsion E (p ^ k) ≃ₗ[ZMod (p ^ k)] (Fin 2 → ZMod (p ^ k))

primePowerBasis (k : ℕ) :
  Module.Basis (Fin 2) (ZMod (p ^ k)) (Torsion E (p ^ k))

primePower_free (k : ℕ) :
  Module.Free (ZMod (p ^ k)) (Torsion E (p ^ k))
```

正指数k+1では係数環が非自明なので、`primePower_finrank` は有限自由階数2を与える。
k=0ではp⁰=1であり、E[1]は零群、ZMod 1は零環である。
この場合も線形同型・二元基底の形式的なデータは存在するが、階数の一意性を同様には主張しない。
そのため階数定理は正指数に限定している。

## 4. 塔とガロア作用を保持する

`primePowerTransition E p k` は同じ実際の点をp倍する

\[
E[p^{k+1}]\twoheadrightarrow E[p^k]
\]

であり、既存の倍写像全射性から全射である。元のガロア作用とも可換する。
この写像自体は基底選択から独立である。

各段の線形同型に沿って元のガロア作用を運び、
`primePowerCoordinateRepresentation` と `primePowerCoordinate_equivariant` を公開した。
合成数のZMod(pᵏ)を体と見なさず、可換環上の表現として構成している。

ただし、各段で別々に選んだ基底が遷移写像に関して互換的であるとは証明していない。
同型先の標準座標空間に運ばれる作用も、一般には自明ではない。
各段の自由性、ガロア作用を運ぶ同変同型、塔全体の互換的基底は区別する。

## 5. 非分裂性は自由性と独立に証明する

非分裂性のモジュールは、素数冪自由加群の構成をimportしない。
NOTE-019の短完全列と、既存のE[p]の非零基底ベクトルだけを使う。

Q≠0をp倍写像で持ち上げると、P∈E[p²]でpP=Q≠0となる。
p²P=0と合わせて、`addOrderOf_eq_prime_pow` によりPの位数はちょうどp²である。

一方、E[p]×E[p]の全ての点はp倍で零になる。
加法同型は自然数倍を保つので、Pをその直積へ送る同型は存在しない。

さらに、加法準同型s:E[p]→E[p²]があれば

\[
p\,s(Q)=s(pQ)=s(0)=0.
\]

従って[p]∘sは零写像であり、非零のQにおいて恒等写像になれない。
これが `prime_square_no_additive_section` である。
「各段は自由」であることと「短完全列が分裂する」ことを混同しないための実際の構造的反例になっている。

## 6. 回帰と監査

実在するSource 2の(4,3,5)の曲線について、その同じ曲線のE[37²]・E[37³]を検査した。
仮想的なSource 37の存在には依存しない。

- E[37²]の構造同型、E[37³]の自由性と有限自由階数2。
- E[4]のZMod 4上の自由性、指数0の零群と座標同型。
- 実際の基底点の持ち上げと、座標(1,0)の逆像が第一持ち上げに一致すること。
- 最高段の基底を持ち上げる任意の二点の生成写像の全単射性。
- 塔の遷移の全射性・ガロア同変性、座標表現との同変性。
- 位数1369の点、同じ位数でもE[37²]とE[37]×E[37]が非同型であること。
- 37²の加法的sectionの不存在、素数2でも直積へ分解できないこと。

`Note020DependencyAudit` は公開32宣言・回帰16宣言の公理と、17本の型・opaque本体の依存経路を検査する。
構造同型には実際の基底・倍写像全射性・持ち上げ帰納法・生成写像の全射性・全指数位数公式を要求する。
非分裂性には非零基底点とp倍で消える性質の使用を要求する。
全ての検査経路でWeil対データ・外部未移植定理・FLT終点・旧条件付き位数provider等を禁止する。
一般群の生成補題では数論層の宣言も禁止する。許容公理はpropext・Classical.choice・Quot.soundだけである。

結果は [検証記録](evidence/validation-note020.txt)、ルートimportの確認コードは
[RootSmokeNOTE020.lean](evidence/RootSmokeNOTE020.lean) に保存した。

## 7. 残る境界

今回の構造Coreは、既存の幾何学的点群・基底・全射性・位数公式だけから導いた無条件の結果である。
Weil対を仮定した円分行列式の条件付き定理とは独立している。

Tate加群の逆極限、互換的な基底、そのZₚ上の自由性・階数はまだ構成していない。
NOTE-020がFLT本線で優先すべきとするWeil対の幾何学的存在も未実装であり、
NOTE-018の `WeilPairingData` を供給する関数体・付値・平行移動の理論は引き続き必要である。
Frey表現の既約性・Mazur型理論・Artin導手・FLTの終点も今回の結論には含めない。

今回、新たな外部ソースは移植せず、既存のDkMath CoreとMathlibの線形代数・有限濃度APIを組み合わせた。

## 8. 実行結果

- `lake build DkMath.Lib.Algebra.TorsionPowerLifting`: 成功（1246 jobs）。
- `lake build DkMath.Lib.NumberTheory.EllipticTorsionPrimePower`: 成功（2257 jobs）。
- `lake build DkMath.Lib.NumberTheory.EllipticTorsionPrimePower DkMath.Lib.NumberTheory.EllipticTorsionNonSplit`: 成功（2258 jobs）。
- `lake build DkMath.FLT.FreyTorsionPrimePower`: 成功（3182 jobs）。
- `lake build DkMathTest.FLT.FreyTorsionPrimePower`: 成功（3184 jobs）。
- `lake build DkMathTest.FLT.Note020DependencyAudit`: 成功（3185 jobs、32公開宣言・16回帰宣言・17経路）。
- `lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`: 成功（11594 jobs）。
- ルートsmoke、`lake env lean DkMathTest.lean`、マーカー照合、静的検査、`git diff --check`: 成功。

新規6モジュールには警告・エラーなし。別の既存モジュールには歴史的な警告が残るが、
今回の監査対象の公理はpropext・Classical.choice・Quot.soundだけである。
