# findings-007 — centered image modulo five

## Scope / source reuse

instruction-007 と actual centeredSevenSextic definition、nestedAllocation_iff_centered、gate-004 family、gate-006 no-image を確認。開始時変更なし。対象は固定 gap D=7^27 と divisor r=1。

既存 centered modules の mod-five declarations を検索し、該当定理は見つからない。新しい source-coupling audit や receiver definition の変更は行わない。

## Proof plan

actual polynomial の mod 5 image を全 q の剰余5ケースで確認する。s≡1 mod5 のとき target≡3 を ModEq.pow / mul で導き、image と矛盾させる。cheap family は既存 k=5*j の specialization と arithmetic normalization で再利用する。

族の exact exclusion は r=1 のみ。full-sieve を全 j で排除するとは主張しない。589 の target が modular image に含まれることと、既存 adjacent-gap no-image の両立を検査する。

## Inventory and first attempt

Index build exit 0: 1,807 files / 29,276 declarations。centeredSevenSextic search は既存13件、mod-five image theorem なし。

初回 calibration exit 1: Nat.add_mod / mul_mod / pow_mod を simp に入れると nested modular reduction が再帰し maxRecDepth に到達した。数学的反例ではない。actual polynomial を ZMod 5 に cast して q mod 5 の5ケースを kernel reduction する方法へ変更する。全 s の target residue `448*s^49 ≡ 3*s (mod 5)` も private helper として同じ有限ケースで証明し、no-image に再利用する。

## Final verification

- Revised calibration exit0; focused production build exit0 (9092 jobs); final test exit0, no warning/error.
- Four exports have only standard propext / Classical.choice / Quot.sound, no sorryAx.
- Universal image inclusion and witnesses establish exact modular image {1,2,4}. General target helper covers all natural s.
- All k family passes both cheap filters and fails r=1 exact receiver. Tests establish injectivity and unboundedness.
- 589 target is in the mod-five image, while the existing adjacent-gap no-image still holds. The mechanisms are explicitly separated.
- Outcome A. Other divisors / full-sieve exclusion for all k remain outside the proved scope.
