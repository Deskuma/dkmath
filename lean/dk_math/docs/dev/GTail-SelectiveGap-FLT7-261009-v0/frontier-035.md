# Step035 frontier — twelve local addresses

2026-10-11。C と E/R の二つの単射は Step034 のものをそのまま使用。

| Contract | Checked result | Boundary |
|---|---|---|
| Fin 2 × Fin 6 → Ideal C | M_injective、全十二個が maximal / prime | 全 spectrum の分類ではない |
| E contraction | row e の eisensteinResidueIdeal | j に依存しない |
| R contraction | column j の sixRootKernel 11 j | e に依存しない |
| old address | evGrid 0 0=eval43、M 0 0=M43 | 旧 owner は不変 |
| extension of P37 | map fromEisenstein P37 < M00 | 第二列の評価が ζ−11 を検出 |
| extension of K0 | map fromCyclotomic K0 < M00 | 第二行の評価が ω−37 を検出 |
| actual α | membership ↔ e=0 | 第一行の六点 |
| actual F0 | membership ↔ j=0 | 第一列の二点 |
| common membership | ↔ e=0 ∧ j=0 | 元の等式ではなく、両像は実際に異なる |
| Fermat tuple | ¬ Fermat7Equation 1166 1857 1858 | この例を仮想的な正の解に転用しない |

一つの E prime はこの grid 内で六つの C prime に、一つの R prime は二つに収縮する。
この有限 grid における multiplicity は証明済みだが、grid 外の prime を排除していない。
両 source address が与えられればこの grid 内の組は唯一になる。
その唯一性だけでは、元の focused Fermat data が source-linked な両 address を非循環的に
供給するか、signed carrier の一致や provider の field に何を供給するかは決まらない。

Ideal.map_pow は正しい既存 API。問題は拡大イデアルを M00 に置換することであり、
今回の二つの strict inequalities はその n=1 の同一視を否定する。
任意 n の深さ、rank 12、domain/field、12-way product=(43)、full spectrum、
class/unit principalization、signed packet、FLT7 descent は未構成。STOP035。
