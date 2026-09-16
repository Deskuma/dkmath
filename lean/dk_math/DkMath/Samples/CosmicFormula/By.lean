/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Samples.CosmicFormula.Defs

-- by? test

namespace DkMath.Sample
namespace CosmicFormula

/-- CosmicFormulaN 証明の展開デモンストレーション（意外と長かった） -/
theorem CosmicFormulaN_Demo_by?
  (x : ℕ) :
  N x + 1 = (P x + 1) ^ 2 := id
    (id
      (of_eq_true
        (Eq.trans
          (congr
            (congrArg Eq
              (Eq.trans
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.mul_congr
                    (Mathlib.Tactic.Ring.Common.atom_pf x rfl
                      (Eq.mpr
                        (id
                          (congrArg
                            (fun _a ↦ x ^ Nat.rawCast 1 * Nat.rawCast 1 = x ^ Nat.rawCast 1 * _a)
                            (Eq.symm rfl)))
                        (Eq.refl (x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                    (Mathlib.Tactic.Ring.Common.add_congr
                      (Mathlib.Tactic.Ring.Common.atom_pf x rfl
                        (Eq.mpr
                          (id
                            (congrArg
                              (fun _a ↦ x ^ Nat.rawCast 1 * Nat.rawCast 1 = x ^ Nat.rawCast 1 * _a)
                              (Eq.symm rfl)))
                          (Eq.refl (x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                      (Mathlib.Tactic.Ring.cast_pos
                        (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2)))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Nat.rawCast 2)
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_left x (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 2) (Eq.refl 2))))
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap x
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 2)))
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1))))
                          (Mathlib.Tactic.Ring.Common.mul_zero (x ^ Nat.rawCast 1 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                          (x ^ Nat.rawCast 1 * Nat.rawCast 2)
                          (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                            (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0))))
                      (Mathlib.Tactic.Ring.Common.zero_mul
                        (Nat.rawCast 2 + (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                        (x ^ Nat.rawCast 1 * Nat.rawCast 2 +
                          (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))))
                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 1)))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (x ^ Nat.rawCast 1 * Nat.rawCast 2 +
                        (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))))
                (Eq.trans
                  (Mathlib.Tactic.RingNF.add_assoc_rev (Nat.rawCast 1)
                    (x ^ Nat.rawCast 1 * Nat.rawCast 2) (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0))
                  (Eq.trans
                    (Mathlib.Tactic.RingNF.add_assoc_rev
                      (Nat.rawCast 1 + x ^ Nat.rawCast 1 * Nat.rawCast 2)
                      (x ^ Nat.rawCast 2 * Nat.rawCast 1) 0)
                    (Eq.trans
                      (congrFun'
                        (congrArg HAdd.hAdd
                          (congr
                            (congrArg HAdd.hAdd
                              (congr (congrArg HAdd.hAdd Mathlib.Tactic.RingNF.nat_rawCast_1)
                                (congrFun'
                                  (congrArg HMul.hMul
                                    (Eq.trans
                                      (congrArg (HPow.hPow x) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                      (pow_one x)))
                                  2)))
                            (Eq.trans
                              (congrArg (HMul.hMul (x ^ 2)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                              (mul_one (x ^ 2)))))
                        0)
                      (add_zero (1 + x * 2 + x ^ 2)))))))
            (Eq.trans
              (Mathlib.Tactic.Ring.Common.pow_congr
                (Mathlib.Tactic.Ring.Common.add_congr
                  (Mathlib.Tactic.Ring.Common.atom_pf x rfl
                    (Eq.mpr
                      (id
                        (congrArg
                          (fun _a ↦ x ^ Nat.rawCast 1 * Nat.rawCast 1 = x ^ Nat.rawCast 1 * _a)
                          (Eq.symm rfl)))
                      (Eq.refl (x ^ Nat.rawCast 1 * Nat.rawCast 1))))
                  (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 1)))
                  (Mathlib.Tactic.Ring.Common.add_pf_add_gt (Nat.rawCast 1)
                    (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                      (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                (Mathlib.Tactic.Ring.cast_pos (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 2)))
                (Mathlib.Tactic.Ring.Common.pow_add
                  (Mathlib.Tactic.Ring.Common.pow_nat (Mathlib.Tactic.Ring.Common.coeff_one 2 rfl)
                    (Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat
                      (Nat.rawCast 1 + (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) (Nat.rawCast 1)
                      { out := rfl })
                    (Mathlib.Tactic.Ring.Common.pow_bit0
                      (Mathlib.Tactic.Ring.Common.pow_one
                        (Nat.rawCast 1 + (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1)))
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_right x (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1))))
                            (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                              (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.add_mul
                          (Mathlib.Tactic.Ring.Common.mul_add
                            (Mathlib.Tactic.Ring.Common.mul_pf_left x (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1))))
                            (Mathlib.Tactic.Ring.Common.mul_add
                              (Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap x
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 2)))
                                (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                  (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                    (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1))))
                              (Mathlib.Tactic.Ring.Common.mul_zero
                                (x ^ Nat.rawCast 1 * Nat.rawCast 1))
                              (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                                (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))
                            (Mathlib.Tactic.Ring.Common.add_pf_add_lt
                              (x ^ Nat.rawCast 1 * Nat.rawCast 1)
                              (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                                (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0))))
                          (Mathlib.Tactic.Ring.Common.zero_mul
                            (Nat.rawCast 1 + (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (x ^ Nat.rawCast 1 * Nat.rawCast 1 +
                              (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0))))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                          (Mathlib.Tactic.Ring.Common.add_pf_add_overlap
                            (Mathlib.Tactic.Ring.Common.add_overlap_pf x (Nat.rawCast 1)
                              (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                                (Mathlib.Meta.NormNum.isNat_add (Eq.refl HAdd.hAdd)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                  (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 2))))
                            (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                              (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))))))
                  (Mathlib.Tactic.Ring.Common.pow_zero
                    (Nat.rawCast 1 + (x ^ Nat.rawCast 1 * Nat.rawCast 1 + 0)) rfl)
                  (Mathlib.Tactic.Ring.Common.add_mul
                    (Mathlib.Tactic.Ring.Common.mul_add
                      (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                        (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                          (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1)))
                      (Mathlib.Tactic.Ring.Common.mul_zero (Nat.rawCast 1))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_zero (Nat.rawCast 1 + 0)))
                    (Mathlib.Tactic.Ring.Common.add_mul
                      (Mathlib.Tactic.Ring.Common.mul_add
                        (Mathlib.Tactic.Ring.Common.mul_pf_left x (Nat.rawCast 1)
                          (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                            (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 2)
                              (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 2))))
                        (Mathlib.Tactic.Ring.Common.mul_zero (x ^ Nat.rawCast 1 * Nat.rawCast 2))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (x ^ Nat.rawCast 1 * Nat.rawCast 2 + 0)))
                      (Mathlib.Tactic.Ring.Common.add_mul
                        (Mathlib.Tactic.Ring.Common.mul_add
                          (Mathlib.Tactic.Ring.Common.mul_pf_left x (Nat.rawCast 2)
                            (Mathlib.Meta.NormNum.IsNat.to_raw_eq
                              (Mathlib.Meta.NormNum.isNat_mul (Eq.refl HMul.hMul)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1)
                                (Mathlib.Meta.NormNum.IsNat.of_raw ℕ 1) (Eq.refl 1))))
                          (Mathlib.Tactic.Ring.Common.mul_zero (x ^ Nat.rawCast 2 * Nat.rawCast 1))
                          (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                            (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))
                        (Mathlib.Tactic.Ring.Common.zero_mul (Nat.rawCast 1 + 0))
                        (Mathlib.Tactic.Ring.Common.add_pf_add_zero
                          (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))
                      (Mathlib.Tactic.Ring.Common.add_pf_add_lt (x ^ Nat.rawCast 1 * Nat.rawCast 2)
                        (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                          (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0))))
                    (Mathlib.Tactic.Ring.Common.add_pf_add_lt (Nat.rawCast 1)
                      (Mathlib.Tactic.Ring.Common.add_pf_zero_add
                        (x ^ Nat.rawCast 1 * Nat.rawCast 2 +
                          (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0)))))))
              (Eq.trans
                (Mathlib.Tactic.RingNF.add_assoc_rev (Nat.rawCast 1)
                  (x ^ Nat.rawCast 1 * Nat.rawCast 2) (x ^ Nat.rawCast 2 * Nat.rawCast 1 + 0))
                (Eq.trans
                  (Mathlib.Tactic.RingNF.add_assoc_rev
                    (Nat.rawCast 1 + x ^ Nat.rawCast 1 * Nat.rawCast 2)
                    (x ^ Nat.rawCast 2 * Nat.rawCast 1) 0)
                  (Eq.trans
                    (congrFun'
                      (congrArg HAdd.hAdd
                        (congr
                          (congrArg HAdd.hAdd
                            (congr (congrArg HAdd.hAdd Mathlib.Tactic.RingNF.nat_rawCast_1)
                              (congrFun'
                                (congrArg HMul.hMul
                                  (Eq.trans
                                    (congrArg (HPow.hPow x) Mathlib.Tactic.RingNF.nat_rawCast_1)
                                    (pow_one x)))
                                2)))
                          (Eq.trans
                            (congrArg (HMul.hMul (x ^ 2)) Mathlib.Tactic.RingNF.nat_rawCast_1)
                            (mul_one (x ^ 2)))))
                      0)
                    (add_zero (1 + x * 2 + x ^ 2)))))))
          (eq_self (1 + x * 2 + x ^ 2)))))

end CosmicFormula
end DkMath.Sample
