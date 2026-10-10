# Step036 frontier — joint source generation

2026-10-11。既存 C と q43 の十二点だけを対象とする。

| Contract | Checked result | Boundary |
|---|---|---|
| coordinate split | 任意 x と行 e で x=iR(y)+iE(τ−t_e.val)iR(x.im) | x∈M は分解自体には不要 |
| joint prime generation | M(e,j)=A(e)⊔B(j) | 個別の A=M / B=M ではない |
| first address | M43=A0⊔B0 | 旧 M43 の定義を変更しない |
| individual extensions | A0<M00、B0<M00 を回帰 | join の等式と両立する |
| source powers | n:Fin 3 の各 source power→extension power→M power | 一方向、n.val=0,1,2 のみ |
| native mixed elements | iEα·iRF0∈M00³、iE(α²)·iRF0∈M00⁴ | 下限のみ、次の冪からの除外は示さない |
| orthogonal incidence | α 第一行、F0 第一列 | source 元の等式ではない |
| finite addresses | 十二点の distinctness / maximality を回帰 | 全 spectrum の分類ではない |

A と B を同じ C の ideal として加えることで、別々の source contract を共同で使える。
単一 source の拡大では欠けていた生成元の条件を、もう一方の拡大が供給する。
M² を A²⊔B² としてはいない。mixed product の所属は Ideal.mul_mem_mul と pow_add による。
Ideal.map_pow の等式は extension の冪について正しく、M の冪への移行は包含である。

## Original FLT7 frontier の再評価

GTailGlobalBalanceFirewall.fermat7Equation_iff_focused_scalar_balance と norm_balance は
additive focus の下で Fermat equation と exact scalar/norm balance を同値にする。
今回の join は local ideal equality であり、その exact balance の新しい入力ではない。
実際の数値組は non-Fermat のまま全 local join / mixed-support tests を満たす。

DescentClosureAudit.AwayDescentClosureProvider は nextX/Y/Z、nextPack、nextRoute、
carrier_match : nextRoute.carrier=Int.natAbs p.normal.root.snd を要求する。
今回の出力は Ideal C の等式・所属であり、これらの field や旧 signed carrier の再構成を
供給しない。これを provider が存在しない証明とも読まない。
次の研究では有限 grid の拡張より、元の仮想 primitive solution から何を新たに
非循環的に供給できるかを source-linked な契約として明示することが必要。

STOP036。global balance、canonical pairing from Fermat data、exact M-adic valuation、
全 spectrum、rank/domain/field/flatness、all-k tower、signed packet、class/unit extraction、
primitive provider、away descent、unconditional FLT7 closure は未構成。
