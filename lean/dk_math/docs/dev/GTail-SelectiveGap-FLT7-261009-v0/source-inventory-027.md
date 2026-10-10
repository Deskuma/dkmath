# Step027 source inventory

2026-10-10. Base HEAD `9e29c43f0e62443dd9ce32601c72e052cc85ee65`、branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
review-026/report-026/source-inventory-026 を確認。review は static review、独立 rebuild ではない。

Owner は新 GTailCyclotomicTailTaylorLift、direct import は Step026 のみ。
actual shell は tailShellPoly。natural evaluation は Step023 の homogeneous sum に接続済み。
Derivative carrier はまず ℤ、続いて ZMod q。両者の equality は七項展開と cast の明示的証明で transport。
Taylor remainder は整数 polynomial の有限展開、checked quotient witness / ring で h² divisibility。
q,c,g,d arbitrary natural（q=0を含む）。ここに prime/unit/Tail-support premise はない。

Phase2 は T=q*(T/q) を Nat.mul_div_cancel' と exact_mod_cast で integers に持ち込む。
整数 Taylor witness で lifted T=q*(m+d*Dint+q*k)。mul_dvd_mul_iff_left（q≠0）と dvd_add_left により q² condition を q-divisibility にする。
ZMod.intCast_zmod_eq_zero_iff_dvd は最後の field-linear equation のみで使う。
ZMod(q²) の q を unit として消去する手順はない。

Existing neutral PolynomialHenselDigit を source確認。その polynomial_powLift_iff は任意正 depth、
existsUnique_polynomial_powLift_digit は一般 polynomial の next digit API。
今回の native GTail one-step contract と重なる classical mechanism だが、元 shell/cast/ratio の adapter は未接続。
旧 owner は編集・importしない。そこで使われている Mathlib exists_mul_sq_add_linear_part_eq_eval_add の source も確認。
新 owner は narrow degree-six integer remainder を直接 recheck、Taylor package の追加 import は不要。
Polynomial.derivative_mul/pow と eval/C APIs は Step026 の targeted derivative import 経由。
GN/Cosmic analytic derivative は finite-field digit iff の reusable endpoint ではない。

Correction は −(T/q)/D、D≠0 は Step026 actual cofactor equality と nonzero theorem。
整数 prime cancellation と finite-field inverse を区別する。後者で初めて derivative を除算。
No all-k induction, q-adic completion, packets, principalization, unit/class transfer or FLT descent.
