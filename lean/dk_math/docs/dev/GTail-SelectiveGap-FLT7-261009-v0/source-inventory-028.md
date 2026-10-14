# Step028 — native second-digit source inventory

2026-10-10、branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
Base HEAD `126f7d2488fd405176a19e88bfb8fa2d71e8c388`。
review027/report027/inventory027 を確認。review は static inspection、独立 rebuild ではない。

| Owner / exact API | Carrier | Role |
|---|---|---|
| Step026 tailShellPoly / tailShellPoly_eval_nat | Polynomial A / natural GTail cast | Original seven-term shell, no replacement polynomial |
| Step027 gtailDerivativeInt_cast | ℤ → ZMod q | Explicit derivative base-change |
| Step027 gtail_shell_derivative_ne_zero | ZMod q | Canonical unit/support derivative guard |
| PolynomialHenselDigit.existsUnique_polynomial_powLift_digit | ℤ[X], ℤ, Fin q | Already proved finite next-digit theorem; instantiate k=2 |
| PolynomialHenselDigit.polynomial_powLift_iff | Integer evaluation / integer ediv | Optional k=2 linear criterion |
| Step025 gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail | Actual degree-six R / selected ideal K² | Bounded ideal-square receiver only |
| Step027 gtail_shift_gap_unit / ratio / derivative | Natural shift / ZMod q | Reuse with increment q*(q*d) |

Direct imports: Step027 and existing neutral PolynomialHenselDigit only。
Generic neutral owner、earlier GTail owners、facades は変更しない。
Generic owner の actual positive-depth and prime contracts / polynomial_shift_preserves_dvd / exists_polynomial_exact_depth_digit を確認。
Taylor quotient/induction の再実装はしない。native adapter のための exact evaluation/cast only。

Raw shifted evaluation bridge は任意 q,c,g,d（zero endpointsも含む）。
Integer x+(q:ℤ)²*d を cast(c+(g+q²*d)) に ring で変換、既存 eval_nat に接続。
q²|T → q|T は dvd_pow_self.trans。
q² natural support は exact_mod_cast で integer eval supportへ。
Derivative guard は ZMod.intCast_zmod_eq_zero_iff_dvd と Step027 cast/nonzero の組み合わせ。

Mathlib eval_add / derivative_map の exact sourceを確認。
ZMod.natCast_zmod_val は NeZero modulus premise付き。
Integer quotient / natural quotient は Int.natCast_ediv（Int.natCast_div alias）と Nat.cast_pow で接続可能。
ZMod(q³) の q² cancellation は行わない。

q³ scalar support と F_i∈K_i³ は未接続。今回の ideal receiver は K² に限定。
No q-adic completion, all-k ideal valuation, signed packets, principalization, unit-class lift or FLT descent。

## Final measured import cost

New source8937/local157、new test8938/local158。Step027比added local2（new ownerと既存PolynomialHenselDigit）、added Mathlib0。
Generic neutral closure1409/local1、neutral→FLT0。local union158のcycle0。
