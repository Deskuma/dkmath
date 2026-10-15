# GN から Kummer のイデアル構造へ — 実装解説

日付: 2026-10-15 (JST)

今回の到達点は **GN の整数ノルム表示、および非分岐側の Kummer 構造定理**。
正則素数に対する FLT 全体の再証明は未完成である。
単元の合同解析と分岐側の降下を、証明済みの結論に混ぜない。
添付研究ノートは数学的な構想・参照資料として読み、実装状態は本書と検証記録で区別する。

## 1. 読む入口

```lean
import DkMath.FLT.Kummer.GNStructure
```

従来の `import DkMath.FLT.Kummer` からも到達する。
新しい入口自身は旧 `CyclotomicPrincipalization` を import しない。
各証明の docstring は日本語で数学的意味・仮定・到達点を解説した。

| 読む順序 | 所有ファイル | 中心定理 |
| --- | --- | --- |
| 1 | `DkMath/Lib/Cosmic/GTail.lean` | `add_pow_eq_prefix_add_xpow_mul_GTail` |
| 2 | `DkMath/Lib/Cosmic/GTailCyclotomic.lean` | `GTail_one_eq_GTailCyclotomicShell` |
| 3 | `DkMath/Lib/Cosmic/GNPhaseFactorization.lean` | `GN_eq_nontrivial_phase_prod_range` |
| 4 | `DkMath/Lib/NumberTheory/CosmicCyclotomicNorm.lean` | `integral_norm_phaseFactor_eq_GTail` |
| 5 | `DkMath/Lib/NumberTheory/CosmicIdealBridge.lean` | `span_GTail_eq_prod_phase_span` |
| 6 | 同上 | `common_prime_contains_ramified` |
| 7 | 同上 | `phase_spans_pairwise_isCoprime` |
| 8 | 同上 | `GN_kummer_structure_of_unramified` |
| 9 | `DkMath/FLT/Kummer/GNStructure.lean` | `GN_kummer_structure_of_regular` |

`GN` は `DkMath.CosmicFormula.Defs` にある `GTail p 1` の略記。
別の多項式や別の GN を新設してはいない。

## 2. 多項式恒等式からノルムへ

任意の可換半環で

\[
(x+u)^d=x\,GTail(d,1,x,u)+u^d.
\]

原始 d 乗根 ζ を持つ整域では

\[
GTail(d,1,x,u)=\prod_{i=1}^{d-1}(x+(1-ζ^i)u).
\]

ここでは `x ≠ 0` を仮定しない。既存の `GapFocusing.Phase` の証明は
`R[X]` で形式変数 X を消去した後に評価するため、ゼロ差分でも正しい。
その実装を `Lib/Cosmic/GNPhaseFactorization.lean` へ移した。
旧 `Phase.lean` は互換 import となり、元の名前空間・定理名・型を保持する。

p が素数になると、非自明な p 乗根は全て原始根である。
`Gal(K/ℚ) ≃ (ZMod p)ˣ` によってノルムの添字を `1,…,p−1` と同一視できる。
新定理は、まず x,u∈ℚ について体ノルムを計算し、その後 x,u∈ℤ について
整数環のノルムに戻す:

\[
N_{\mathcal O_K/\mathbb Z}(x+(1-ζ)u)=GTail(p,1,x,u).
\]

Lean の左辺は `Algebra.norm ℤ`、右辺は **ℤ の等式**。
任意の p 次円分体 `K` と原始根に対して成立する。
モデルは `𝓞 K` であり、独自の `ℤ[ζ]` 型を作ったり、その環同型を新証明したりはしていない。
整数環に入る元は `hζ.toInteger` で明示する。

これは有限積を norm という名前で再定義したものではない。
Mathlib の線形代数的な `Algebra.norm` を `Algebra.norm_eq_prod_automorphisms` で展開して証明する。

ノルム同定とイデアル冪抽出は、同じ円分因子分解を共有する二つの経路である。
構造定理の証明はノルム等式からイデアル分解を逆算しない。
ノルムは共役方向の情報を積にまとめるので、ノルムが p 乗という情報だけでは
各因子イデアルの p 乗性は復元できない。因子ごとの互いに素性が必要になる。

## 3. なぜイデアルへ移すのか

主イデアル化は `(αβ)=(α)(β)` を満たすので、上の積はそのまま

\[
(GN_p(x,u))=\prod_{i=1}^{p-1}(x+(1-ζ^i)u)
\]

という **イデアルの積** へ移る。右辺の各括弧は `Ideal.span {…}`。
`x GN_p(x,u)=c^p` なら、添字 0 の因子 x を含めて

\[
\prod_{i=0}^{p-1}(x+(1-ζ^i)u)=(c)^p.
\]

元の一意分解は仮定していない。Dedekind 整域のイデアル分解を使うために
この世界へ移る。積が冪でも、互いに素性なしには個々の因子は冪にならない。

## 4. 共通素イデアルと分岐

`αᵢ=x+(1−ζⁱ)u` と書く。異なる i,j に対して

\[
α_i-α_j=(ζ^j-ζ^i)u.
\]

素数次数では `ζʲ−ζⁱ` は `ζ−1` と同伴である。
したがって共通素イデアル P は `ζ−1` または u を含む。

`IsCoprime x u` は Bezout の等式を意味する。P が u と αᵢ を含むなら x も含み、
Bezout の等式から 1∈P となって矛盾する。これが `common_prime_contains_ramified`。
ここまででは分岐を除外していない。

さらに `IsCoprime x (ζ−1)` を仮定すると、P が ζ−1 を含む場合も不可能になる。
実際 `ζ−1 ∣ ζⁱ−1` から x∈P が従う。
この議論が因子イデアルの対ごとの互いに素性を供給する。

整数環の FLT adapter では `ζ−1 ∣ p` を使い、整数上の
`IsCoprime (a+b) (p:ℤ)` からこの条件を導く。
整数の互いに素性は環準同型で写した Bezout 等式によって保存される。
一般の整域で「共通因子がない」という弱い条件と混同しない。

## 5. 類群から元へ戻す

互いに素なイデアルの積が `(c)^p` なら、各因子について `(αᵢ)=Iᵢ^p`。
c≠0 と p>0 から Iᵢ≠0 を示してから、類群を使う。

\[
[I_i]^p=1.
\]

`Nat.Coprime p (Fintype.card (ClassGroup R))` により p-torsion が消えるので
`[Iᵢ]=1`、従って `Iᵢ=(γᵢ)`。主イデアルの生成元の違いは単元なので

\[
α_i=ε_iγ_i^p,\qquad ε_i\in R^\times.
\]

Lean の結論には Iᵢ、Iᵢ≠⊥、主イデアルの p 乗等式、生成元 γᵢ、
`IsUnit εᵢ`、元の等式を全て残す。
正則性を PID 性へ強めていない。単元を消してもいない。
既存 `UnitPowerSector` はこの先の単元類の整理に使えるが、sector の供給・消去は別途必要。

## 6. FLT 座標での最終 API

奇数 p、整数 a,b,c について

\[
x=a+b,\quad u=-b,\quad (a+b)GN_p(a+b,-b)=a^p+b^p.
\]

円分因子は `x+(1−ζⁱ)u=a+ζⁱb` になる。
`GN_kummer_structure_of_regular` の仮定は次のとおり:

- p は素数かつ奇数、K は p 次円分体。
- c≠0、aᵖ+bᵖ=cᵖ。
- `IsCoprime a b`。
- `IsCoprime (a+b) (p:ℤ)`。
- p と K の類群の位数が互いに素。
- 0≤i<p（Lean では i:ℕ と i<p）。

結論は `a+ζⁱb=εγᵖ` とそのイデアル根・生成元の証明。
イデアル冪の存在、因子の対ごとの互いに素性、最終矛盾を入力に仮定してはいない。
非分岐条件は整数で検査可能な入力として残っている。
標準的 Case I の `p∤abc` からこの入力への専用 adapter は今回の API に含めていない。

## 7. 任意の GTail にもある、別の橋

切断位置 r≤d の prefix を Pᵣ とすると

\[
((x+u)^d-P_r)=(x)^r\,(GTail(d,r,x,u)).
\]

`span_tail_remainder` はこの等式を任意の可換環で証明する。
加法分割をイデアル和に移すのではなく、prefix を引いて因数分解した結果を移す。
これは全切断のイデアル接続であり、r>1 の円分ノルム表示を意味しない。

## 8. 既存 Kummer 資産の地図と再利用

| 既存資産 | 今回の関係・境界 |
| --- | --- |
| `Kummer/Basic`, `GapDivisibleBranch` | 従来の反例・降下の条件付き経路。新しい代数層は依存しない |
| `Kummer/CyclotomicPrincipalization` | 自然数反例を使ったノルム積・共通素イデアル解析が存在。新層は符号付き座標と一般整域へ整理 |
| `prod_units_zmod_eq_prod_range_erase_zero` | 添字変換の証明方針を neutral 層へ再利用。旧宣言は保持 |
| `IdealPowerFactor` | 互いに素なイデアル積から冪を抽出 |
| `PrincipalIdealPower` | 類群 torsion 消滅から生成元と単元を回収 |
| `ClassGroupTorsionBridge` | 類群位数条件から torsion 消滅を供給 |
| `UnitPowerSector` | 単元 modulo p 乗の後続 API。単元処理の完了ではない |
| `Kummer/RegularPrimeRoute` | 旧経路の合成入口。今回の独立した構造証明とは区別 |

文字列の棚卸しは [kummer-inventory.tsv](evidence/kummer-inventory.tsv) に保存した。
対象を現行の `DkMath/**/*.lean`、大文字小文字を区別する `Kummer` に固定すると
30 ファイル・321 出現（今回の追加を含む）。テスト・文書は含まない。
依頼文の 37 ファイル・410 件とは検索範囲・時点が異なり得るため、件数を証明範囲に換算しない。

旧 `CyclotomicPrincipalization.lean` の
`cyclotomicPrincipalizationNonFirstCasePeelDescentExistenceCore_of_classGroupPTorsionFree`
には現行ソースでも `sorry` がある。新しい定理はこの宣言に依存しない。
旧ルート全体を完成と数えることはできない。

## 9. ロードマップとの対応

| ID | 実装で得たもの | 残る境界 |
| --- | --- | --- |
| KGI-001 | 既存の殻対応と符号付き GN 恒等式を接続 | なし（この恒等式の範囲） |
| KGI-002 | 整数環ノルムと GN の等式 | 独自の ℤ[ζ] モデルは導入しない |
| KGI-003 | GN と全因子の主イデアル積 | なし（積の輸送の範囲） |
| KGI-004 | 原始性の下で共通素イデアルは ζ−1 を含む | 分岐側の正確な付値配分・剥離 |
| KGI-005 | 非分岐側のイデアル p 乗抽出 | 分岐側 |
| KGI-006 | 類数条件から単元倍 p 乗へ復元 | 単元 sector の具体的消去 |
| KGI-007 | 未完 | Kummer 補題、Case I の矛盾、Case II の無限降下 |
| KGI-008 | 全切断の剰余主イデアル等式 | 各切断のノルム・付値・support 分類 |
| KGI-009 | 未着手 | Carry/wheel。FLT の Kummer 証明と桁上がり定理は別物 |

## 10. 参照と検証

参照正本の現在の入口は、Case I と Case II を分けて合成している:
[FltRegular/FltRegular.lean](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/FltRegular.lean)。
類数との互いに素性による正則性の定義は
[RegularPrimes.lean](https://github.com/leanprover-community/flt-regular/blob/master/FltRegular/NumberTheory/RegularPrimes.lean)。
これらは構成と定義の照合資料であり、新しい外部依存として追加してはいない。

ビルド・公理監査・回帰例の実行結果は `evidence/validation.txt` に記録する。
新層の監査は `propext`, `Classical.choice`, `Quot.sound` 以外の依存を検出すると失敗する。
回帰例はゼロ差分、三次ノルム 13、負の座標、`9*GN₂(9,8)=15²` のイデアル抽出、r=0 の切断を扱う。
