# Kummer × GN・GTail × イデアル — 研究ノート要旨

実装後の到達点は [IMPLEMENTATION.md](IMPLEMENTATION.md) を参照。以下の研究要旨は実装前の記録として保持する。

三次の再形式化実験は [THREE-GN-DESCENT.md](THREE-GN-DESCENT.md) を参照。
環同型で GN・Kummer の三乗根を既存の同じ Eisenstein 剥離商に戻し、
既存の座標降下を再利用して、追加仮定のない FLT3 の別証明経路を構成する。

五次の続章は [FIVE-GN-DESCENT-AND-SEVEN.md](FIVE-GN-DESCENT-AND-SEVEN.md)。
相対ノルム、五次 Kummer 単元補題、同じ GoldenInt の β の五乗根を経て
既存の黄金比降下へ接続する。実装後の FLT7 への照合と研究考察も記録した。

**研究日：** 2026年10月15日  
**対象：** DkMath / CosmicFormula / FLT regular  
**参照正本：** https://github.com/leanprover-community/flt-regular

## 研究目的

Kummer の正則素数に対するフェルマーの最終定理の証明を学習し、その数学的構造を宇宙式の GN・GTail によって再解釈・形式化する。

目的は記号の置換ではない。宇宙式の多項式分解から出発し、円分因子、素イデアル、類群、単元、降下法が必要になる理由を明確にする。

## 中核となる発見

### 1. 桁上がりと GN

桁多項式を `Dₚ,ₙ(T) = Σ aᵢTⁱ` とすると、`Dₚ,ₙ(p) = n`、`Dₚ,ₙ(1) = Sₚ(n)`。

Legendre の階乗付値公式は、`p = (p−1)+1` による GN の重み付き総和として表現できる。

Kummer の桁上がり定理は、桁多項式の加法と正規化の差を計測する定理として解釈できる。

### 2. GN と円分ノルム

素数次数の GN は、円分体の共役因子の積と一致する。

`GNₚ(x,u) = N(x+(1−ζₚ)u)`

これが宇宙式と代数的整数論の中心的な接続点である。

### 3. FLT の Kummer 因子

奇素数 p に対する仮想反例 `aᵖ+bᵖ=cᵖ` に、`x=a+b`、`u=−b` を代入すると、

`(a+b)GNₚ(a+b,−b) = cᵖ`

が得られる。GN の円分分解は Kummer が扱う `a+ζₚʲb` の積そのものになる。

### 4. イデアルの役割

元の積を主イデアルの積へ輸送することで、円分整数環における素イデアル分解を利用できる。

イデアルの p 乗が得られても、元がそのまま p 乗とは限らない。

正則性は類群の p-torsion 障害を取り除き、単元倍の p 乗への復元を可能にする。ただし単元の処理は別途必要である。

## DkMath の既存資産

- `GTailCyclotomic`：GN と円分殻の対応
- `IdealPowerFactor`：互いに素なイデアルの冪の抽出
- `ClassGroupTorsionBridge`：類群の障害
- `PrincipalIdealPower`：単元倍の冪への復元
- `UnitPowerSector`：単元の剰余類
- `SevenRamifiedFusionCyclotomicSevenPID`：7次円分体の整数環の PID 性と類数1

これらの定理・構造のソースは確認済み。ただし今回、新たな Lean ビルドによる統合検証はしていない。また、Kummer パッケージには未完成部分が残る。

## 今後の研究課題

1. GN と円分ノルムの一致を Lean で固定する。
2. GN の因子を主イデアル積へ輸送する。
3. 円分因子の共通素イデアルと分岐素イデアルを分類する。
4. 正則性によるイデアル冪の抽出を接続する。
5. 単元の合同条件と Kummer の補題を接続する。
6. FLT の Case I / II を GN 起点で再構築する。
7. その後、任意の GTail 切断への一般化を検討する。

## 研究上の核心

**加法的な Big・Body・Gap の分解から得られる GN を、円分体における乗法的な素イデアル分解へどこまで忠実に輸送できるか。**

Kummer の証明を完成済みの地図とし、GN・GTail から同じ到達点を目指す。

その過程で、類群・単元・分岐を宇宙式の保存構造との関係で理解することが、この研究の目的である。

## 2026-10-15 Lean 実装の到達点

[実装解説](IMPLEMENTATION.md) に、GN → 円分ノルム → 主イデアル積 →
共通素イデアル → 類群 → 単元倍 p 乗、の証明を記録した。
入口は `DkMath.FLT.Kummer.GNRamified`（従来の `DkMath.FLT.Kummer` からも import）。
日本語 docstring 付きの主定理は `GN_kummer_structure_of_first_case`。
分岐側では `exists_ramified_phase_quotient_of_dvd_gap` が各非自明因子の正確な一段剥離を返す。

分岐側の [イデアル冪配分と主イデアル化](RAMIFIED-IDEAL-POWER.md) も実装した。
`GN_kummer_structure_of_ramified_case` が各非自明因子の `(ζ−1)εγᵖ` 表示を返す。

**Case I / 向きを固定した分岐側の構造定理まで。正則素数に対する FLT 全体の再証明は未完。**
単元の合同解析と分岐側の降下は残っている。
検証結果は [validation.txt](evidence/validation.txt) を参照。

今回の検証記録: [validation-ramified-ideal.txt](evidence/validation-ramified-ideal.txt)。

寄り道として、[幅1 GN の累積による Fermat の小定理](AKS-GN-UNIT-STEP.md) を
`AKSBridge` に追加。`GN p 1 n = 1 + p H_p(n)` と
`u^p = u + p E_p(u)` を保持し、GN 経由の合同式を独立に構成した。

[整数の分岐深度・ノルム復元・保存パケット](RAMIFIED-VALUATION-PACKET.md) を追加。
`GNRamifiedArithmetic` は `vₚ(a+b)+1=p*vₚ(c)` と、類数条件の下で
`GN p (a+b) (-b)=p*tᵖ`（p∤t）を返す。
検証記録: [validation-ramified-arithmetic.txt](evidence/validation-ramified-arithmetic.txt)。

さらに [整数根の剰余条件](RAMIFIED-ROOT-CONGRUENCE.md) を追加。
`ramified_integral_root_modEq_one` は `GN=p*tᵖ` と mod p² の先頭項から、
AKSBridge の GN 版 Fermat を使って `t≡1 mod p` を導く。

次章: [分岐剰余体と単元の一次正規化](RAMIFIED-UNIT-RESIDUE.md)。
`R/(ζ−1)≃𝔽_p`、剥離商 βᵢ≡−i*u、円分単元による γᵢ≡1 への正規化を実装。
FLT 座標では εᵢ≡i*b となり、同じ商・イデアル根を保持する。
検証記録: [validation-ramified-unit-residue.txt](evidence/validation-ramified-unit-residue.txt)。

次章: [正規化単元を mod λ² まで読む](RAMIFIED-QUADRATIC-CONGRUENCE.md)。
既存の付値から p²∣x と λ³∣x を供給し、同じ生成元のまま
`εᵢ≡i*b+choose i 2*λ*b mod λ²` を証明。p=3 も含む。
検証記録: [validation-ramified-quadratic.txt](evidence/validation-ramified-quadratic.txt)。

次章: [λ^p の合同から Kummer 単元補題へ](RAMIFIED-PRIMARY-UNIT-KUMMER-BRIDGE.md)。
`γᵢᵖ≡1`、`εᵢ≡b*Sᵢ mod λ^p` と、単元 δᵢ=εᵢ*Sᵢ⁻¹ の `δᵢ≡b mod p` を証明。
一般 p は明示的な単元補題を受け取る条件付き adapter、三次は Mathlib の実際の補題から
単元除去を検証済み。上流 flt-regular の実 import は未接続として区別する。
検証記録: [validation-ramified-primary.txt](evidence/validation-ramified-primary.txt)。
