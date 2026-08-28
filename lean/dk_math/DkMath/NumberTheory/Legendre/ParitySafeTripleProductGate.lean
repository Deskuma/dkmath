/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafePairResidual

#print "file: DkMath.NumberTheory.Legendre.ParitySafeTripleProductGate"

/-!
## ParitySafeTripleProductGate

This module stops the parity-safe support lift at three distinct prime
directions.  The canonical prime of an L041 residual triple is placed behind
a strict cubic square-body gate, and the triple is then charged to the finite
wave of its three-prime product.  The exact wave occupancy is split at the
actual window width `2 * n`: near keys have a smaller canonical-prime gate,
while far keys have at most one seat.

These are finite shell, divisibility, and occupancy statements.  They do not
provide a universal bound for the residual ledger and do not prove Legendre's
conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

/-! ### PRIM-L042.1: canonical cube gate -/

/-- The active primes whose cubes fit strictly inside the square Body. -/
noncomputable def paritySafeTripleGatePrimes (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter (fun p => p ^ 3 < squareBody n)

@[simp] theorem mem_paritySafeTripleGatePrimes
    {n p : ℕ} :
    p ∈ paritySafeTripleGatePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧ p ^ 3 < squareBody n := by
  simp [paritySafeTripleGatePrimes]

set_option maxHeartbeats 800000 in
-- The canonical-support minimum and its finite membership packet need a larger
-- local elaboration budget; this does not change the theorem's statement.
/-- The shell-size packet for a canonical L041 residual triple. -/
theorem paritySafeCanonicalResidualTripleIncidence_shell_packet
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n) :
    paritySafeCanonicalSupportPrime n r < q ∧
      paritySafeCanonicalSupportPrime n r < s ∧
      q < s ∧
      paritySafeCanonicalSupportPrime n r * q * s ∣ n ^ 2 + r ∧
      paritySafeCanonicalSupportPrime n r * q * s ≤ n ^ 2 + r ∧
      n ^ 2 + r ≤ squareBody n ∧
      paritySafeCanonicalSupportPrime n r ^ 3 <
        paritySafeCanonicalSupportPrime n r * q * s ∧
      paritySafeCanonicalSupportPrime n r ^ 3 < squareBody n := by
  let p := paritySafeCanonicalSupportPrime n r
  have hpacket := paritySafeCanonicalResidualTripleIncidence_packet hinc
  rcases hpacket with ⟨hr, hp, hq, hs, hpqne, hpsne, hqsne, hdiv, hcop⟩
  have hinc' := Finset.mem_filter.mp hinc
  have hlt : q < s := hinc'.2.1
  have hcovered : r ∈ paritySafeCoveredCandidates n :=
    (Finset.mem_product.mp hinc'.1).1
  have hnonempty := (mem_paritySafeCoveredCandidates.mp hcovered).2
  have hqerase : q ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r) := hinc'.2.2.1
  have hserase : s ∈
      (squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r) := hinc'.2.2.2
  have hsupport :=
    squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate hr
  have hqoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    (paritySafeCanonicalSupportPrime_packet hcovered).2.2.1
    (Finset.erase_subset _ _ hqerase)
  have hsoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    (paritySafeCanonicalSupportPrime_packet hcovered).2.2.1
    (Finset.erase_subset _ _ hserase)
  rw [hsupport] at hqoff hsoff
  have hpmin : p = (paritySafeActiveSupport n r).min' hnonempty := by
    dsimp [p, paritySafeCanonicalSupportPrime]
    rw [dif_pos hnonempty]
  have hpqle : p ≤ q := by
    rw [hpmin]
    exact Finset.min'_le _ _ hqoff
  have hpsle : p ≤ s := by
    rw [hpmin]
    exact Finset.min'_le _ _ hsoff
  have hpq : p < q := by omega
  have hps : p < s := by omega
  have hpoint : n ^ 2 + r ≤ squareBody n :=
    squarePoint_le_squareBody_of_squareOffset
      (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr)
  have hpoint_pos : 0 < n ^ 2 + r := by
    have hoff := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr
    dsimp [SquareOffset] at hoff
    omega
  have hprodle : p * q * s ≤ n ^ 2 + r :=
    Nat.le_of_dvd hpoint_pos hdiv
  have hpqsmall : p * p < p * q :=
    Nat.mul_lt_mul_of_pos_left hpq (mem_squareAnchorOddActivePrimes.mp hp).1.pos
  have hpqsmall' : p * p * p < p * q * p :=
    Nat.mul_lt_mul_of_pos_right hpqsmall
      (mem_squareAnchorOddActivePrimes.mp hp).1.pos
  have hpsmall : p * q * p < p * q * s :=
    Nat.mul_lt_mul_of_pos_left hps
      (Nat.mul_pos (mem_squareAnchorOddActivePrimes.mp hp).1.pos
        (mem_squareAnchorOddActivePrimes.mp hq).1.pos)
  have hpcube : p ^ 3 < p * q * s := by
    calc
      p ^ 3 = p * p * p := by ring
      _ < p * q * p := hpqsmall'
      _ < p * q * s := hpsmall
  have hresult : p < q ∧ p < s ∧ q < s ∧ p * q * s ∣ n ^ 2 + r ∧
      p * q * s ≤ n ^ 2 + r ∧ n ^ 2 + r ≤ squareBody n ∧
      p ^ 3 < p * q * s ∧ p ^ 3 < squareBody n :=
    ⟨hpq, hps, hlt, hdiv, hprodle, hpoint, hpcube,
      hpcube.trans_le (hprodle.trans hpoint)⟩
  simpa [p] using hresult

theorem paritySafeCanonicalResidualTripleIncidence_mem_tripleGatePrimes
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n) :
    paritySafeCanonicalSupportPrime n r ∈ paritySafeTripleGatePrimes n := by
  have hpacket := paritySafeCanonicalResidualTripleIncidence_packet hinc
  rcases hpacket with ⟨hr, hp, hq, hs, hpq, hps, hqs, hdiv, hcop⟩
  have hshell := paritySafeCanonicalResidualTripleIncidence_shell_packet hinc
  rcases hshell with ⟨hpq', hps', hqs', hdiv', hprod', hbody', hcube', hbodycube'⟩
  exact mem_paritySafeTripleGatePrimes.mpr ⟨hp, hbodycube'⟩

/-! ### PRIM-L042.2: ordered triple keys and product waves -/

/-- The product modulus attached to a nested ordered triple key. -/
def paritySafeTripleProductModulus (key : ℕ × (ℕ × ℕ)) : ℕ :=
  key.1 * key.2.1 * key.2.2

/-- Canonical active ordered triple keys behind the cubic gate. -/
noncomputable def paritySafeTripleGateTriples (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeTripleGatePrimes n).product
      ((squareAnchorOddActivePrimes n).product (squareAnchorOddActivePrimes n)) |>.filter
    (fun key => key.1 < key.2.1 ∧ key.2.1 < key.2.2)

@[simp] theorem mem_paritySafeTripleGateTriples
    {n p q s : ℕ} :
    (p, (q, s)) ∈ paritySafeTripleGateTriples n ↔
      p ∈ paritySafeTripleGatePrimes n ∧
        q ∈ squareAnchorOddActivePrimes n ∧
        s ∈ squareAnchorOddActivePrimes n ∧
        p < q ∧ q < s := by
  simp [paritySafeTripleGateTriples, and_assoc, and_left_comm, and_comm]

theorem paritySafeCanonicalResidualTripleIncidence_mem_tripleGateTriples
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n) :
    (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeTripleGateTriples n := by
  have hpacket := paritySafeCanonicalResidualTripleIncidence_packet hinc
  rcases hpacket with ⟨hr, hp, hq, hs, hpq, hps, hqs, hdiv, hcop⟩
  have hshell := paritySafeCanonicalResidualTripleIncidence_shell_packet hinc
  rcases hshell with ⟨hpq', hps', hqs', hdiv', hprod', hbody', hcube', hbodycube'⟩
  exact mem_paritySafeTripleGateTriples.mpr ⟨
    paritySafeCanonicalResidualTripleIncidence_mem_tripleGatePrimes hinc,
    hq, hs, hpq', hqs'⟩

theorem paritySafeCanonicalResidualTripleIncidence_mem_productWave
    {n r q s : ℕ}
    (hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n) :
    r ∈ squareWaveOffsets n
      (paritySafeTripleProductModulus
        (paritySafeCanonicalSupportPrime n r, (q, s))) := by
  have hpacket := paritySafeCanonicalResidualTripleIncidence_packet hinc
  rcases hpacket with ⟨hr, hp, hq, hs, hpq, hps, hqs, hdiv, hcop⟩
  apply mem_squareWaveOffsets.mpr
  exact ⟨squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr,
    by simpa [paritySafeTripleProductModulus] using hdiv⟩

/-! ### PRIM-L042.3: finite product-wave upper ledger -/

/-- Upper incidences `(triple key, square seat)` for product waves. -/
noncomputable def paritySafeTripleProductWaveUpperIncidences (n : ℕ) :
    Finset ((ℕ × (ℕ × ℕ)) × ℕ) :=
  ((paritySafeTripleGateTriples n).product (squareOffsets n)).filter
    (fun hit => hit.2 ∈ squareWaveOffsets n
      (paritySafeTripleProductModulus hit.1))

/-- The finite upper budget obtained by summing the gated product waves. -/
noncomputable def paritySafeTripleProductWaveBudget (n : ℕ) : ℕ :=
  ∑ key ∈ paritySafeTripleGateTriples n,
    (squareWaveOffsets n (paritySafeTripleProductModulus key)).card

theorem paritySafeCanonicalResidualTripleIncidences_card_le_productWaveBudget
    (n : ℕ) :
    (paritySafeCanonicalResidualTripleIncidences n).card ≤
      paritySafeTripleProductWaveBudget n := by
  classical
  let f : ℕ × (ℕ × ℕ) → ((ℕ × (ℕ × ℕ)) × ℕ) := fun triple =>
    ((paritySafeCanonicalSupportPrime n triple.1, triple.2), triple.1)
  have hinj : Set.InjOn f
      (paritySafeCanonicalResidualTripleIncidences n : Set (ℕ × (ℕ × ℕ))) := by
    intro a ha b hb hab
    have hr : a.1 = b.1 := congrArg Prod.snd hab
    have hqs : a.2 = b.2 := by
      have := congrArg (fun z => z.1.2) hab
      exact this
    exact Prod.ext hr hqs
  have hcard :
      (paritySafeCanonicalResidualTripleIncidences n).card =
        ((paritySafeCanonicalResidualTripleIncidences n).image f).card := by
    exact (Finset.card_image_of_injOn hinj).symm
  have hsubset : (paritySafeCanonicalResidualTripleIncidences n).image f ⊆
      paritySafeTripleProductWaveUpperIncidences n := by
    intro hit hhit
    rcases Finset.mem_image.mp hhit with ⟨triple, htriple, rfl⟩
    have hkey := paritySafeCanonicalResidualTripleIncidence_mem_tripleGateTriples htriple
    have hwave := paritySafeCanonicalResidualTripleIncidence_mem_productWave htriple
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hkey,
      mem_squareOffsets.mpr (mem_squareWaveOffsets.mp hwave).1⟩, hwave⟩
  have hupper := Finset.card_le_card hsubset
  rw [← hcard] at hupper
  have hbudget : (paritySafeTripleProductWaveUpperIncidences n).card =
      paritySafeTripleProductWaveBudget n := by
    unfold paritySafeTripleProductWaveUpperIncidences
    calc
      (((paritySafeTripleGateTriples n).product (squareOffsets n)).filter
          (fun hit => hit.2 ∈ squareWaveOffsets n
            (paritySafeTripleProductModulus hit.1))).card =
          ∑ hit ∈ (paritySafeTripleGateTriples n).product (squareOffsets n),
            if hit.2 ∈ squareWaveOffsets n
                (paritySafeTripleProductModulus hit.1) then 1 else 0 := by simp
      _ = ∑ key ∈ paritySafeTripleGateTriples n,
          (squareWaveOffsets n (paritySafeTripleProductModulus key)).card := by
        calc
          _ = ∑ key ∈ paritySafeTripleGateTriples n,
              ∑ r ∈ squareOffsets n,
                if r ∈ squareWaveOffsets n
                    (paritySafeTripleProductModulus key) then 1 else 0 := by
            exact Finset.sum_product' (paritySafeTripleGateTriples n)
              (squareOffsets n) (fun key r => if r ∈ squareWaveOffsets n
                (paritySafeTripleProductModulus key) then 1 else 0)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro key hkey
            rw [Finset.sum_boole]
            apply congrArg Finset.card
            ext r
            simp only [Finset.mem_filter]
            constructor
            · exact And.right
            · intro hr
              exact ⟨mem_squareOffsets.mpr (mem_squareWaveOffsets.mp hr).1, hr⟩
      _ = paritySafeTripleProductWaveBudget n := rfl
  rw [hbudget] at hupper
  exact hupper

theorem paritySafeResidualPairMass_le_productWaveBudget
    (n : ℕ) :
    paritySafeResidualPairMass n ≤ paritySafeTripleProductWaveBudget n := by
  rw [← paritySafeCanonicalResidualTripleIncidences_card_eq_residual n]
  exact paritySafeCanonicalResidualTripleIncidences_card_le_productWaveBudget n

/-! ### PRIM-L042.4: exact wave arithmetic and near/far split -/

theorem paritySafeTripleProductWaveBudget_eq_div_add_carry
    (n : ℕ) :
    paritySafeTripleProductWaveBudget n =
      ∑ key ∈ paritySafeTripleGateTriples n,
        ((2 * n) / (paritySafeTripleProductModulus key) +
          squareWaveCarry n (paritySafeTripleProductModulus key)) := by
  unfold paritySafeTripleProductWaveBudget
  apply Finset.sum_congr rfl
  intro key hkey
  have hkey' := mem_paritySafeTripleGateTriples.mp hkey
  rcases hkey' with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hp' := (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
  have hq' := (mem_squareAnchorOddActivePrimes.mp hq).1.pos
  have hs' := (mem_squareAnchorOddActivePrimes.mp hs).1.pos
  simpa using (card_squareWaveOffsets_eq_div_add_carry (n := n)
    (m := paritySafeTripleProductModulus key) (by
      dsimp [paritySafeTripleProductModulus]
      exact Nat.mul_pos (Nat.mul_pos hp' hq') hs'))

noncomputable def paritySafeTripleGateNearTriples (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeTripleGateTriples n).filter
    (fun key => paritySafeTripleProductModulus key ≤ 2 * n)

noncomputable def paritySafeTripleGateFarTriples (n : ℕ) :
    Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeTripleGateTriples n).filter
    (fun key => 2 * n < paritySafeTripleProductModulus key)

theorem paritySafeTripleGateNearFar_disjoint (n : ℕ) :
    Disjoint (paritySafeTripleGateNearTriples n)
      (paritySafeTripleGateFarTriples n) := by
  rw [Finset.disjoint_left]
  intro key hnear hfar
  have hn := (Finset.mem_filter.mp hnear).2
  have hf := (Finset.mem_filter.mp hfar).2
  omega

theorem paritySafeTripleGateNearFar_union (n : ℕ) :
    paritySafeTripleGateNearTriples n ∪ paritySafeTripleGateFarTriples n =
      paritySafeTripleGateTriples n := by
  ext key
  by_cases h : key ∈ paritySafeTripleGateTriples n
  · simp [paritySafeTripleGateNearTriples, paritySafeTripleGateFarTriples, h]
    omega
  · simp [paritySafeTripleGateNearTriples, paritySafeTripleGateFarTriples, h]

theorem paritySafeTripleGateNearFar_budget_decomposition (n : ℕ) :
    paritySafeTripleProductWaveBudget n =
      (∑ key ∈ paritySafeTripleGateNearTriples n,
        (squareWaveOffsets n (paritySafeTripleProductModulus key)).card) +
      (∑ key ∈ paritySafeTripleGateFarTriples n,
        (squareWaveOffsets n (paritySafeTripleProductModulus key)).card) := by
  unfold paritySafeTripleProductWaveBudget
  rw [← Finset.sum_union]
  · rw [paritySafeTripleGateNearFar_union]
  · exact paritySafeTripleGateNearFar_disjoint n

theorem paritySafeTripleGateNear_canonical_cube_lt_two_mul
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateNearTriples n) :
    p ^ 3 < 2 * n := by
  have hnear := (Finset.mem_filter.mp hkey).2
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hprod : p ^ 3 < p * q * s := by
    have hps : p < s := lt_trans hpq hqs
    have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
    have hp_pos := (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
    have hq_pos := (mem_squareAnchorOddActivePrimes.mp hq).1.pos
    have hppq : p * p < p * q :=
      Nat.mul_lt_mul_of_pos_left hpq hp_pos
    have hppqp : p * p * p < p * q * p :=
      Nat.mul_lt_mul_of_pos_right hppq hp_pos
    have hpqps : p * q * p < p * q * s :=
      Nat.mul_lt_mul_of_pos_left hps (Nat.mul_pos hp_pos hq_pos)
    calc
      p ^ 3 = p * p * p := by ring
      _ < p * q * p := hppqp
      _ < p * q * s := hpqps
  exact hprod.trans_le hnear

theorem paritySafeTripleGateFar_wave_card_le_one
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n) :
    (squareWaveOffsets n (paritySafeTripleProductModulus (p, (q, s)))).card ≤ 1 := by
  have hfar := (Finset.mem_filter.mp hkey).2
  have hpos := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hkey).1
  rcases hpos with ⟨hp, hq, hs, hpq, hqs⟩
  apply card_squareWaveOffsets_le_one_of_two_mul_lt_modulus
  · have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
    exact Nat.mul_pos
      (Nat.mul_pos
        (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
        (mem_squareAnchorOddActivePrimes.mp hq).1.pos)
      (mem_squareAnchorOddActivePrimes.mp hs).1.pos
  · simpa [paritySafeTripleProductModulus] using hfar

/-! ### PRIM-L042.5: supplied `(16, 17)` witness -/

/--
The supplied seat `(n, r) = (16, 17)` has canonical triple `(3, 7, 13)`.
Its product lies in the far regime, the canonical prime passes the strict
cubic gate, and the associated product wave has exactly one occupied seat.
-/
theorem paritySafeTripleProductGate_witness_16_17 :
    17 ∈ squareAnchorOddPointCoprimeOffsets 16 ∧
      3 ∈ paritySafeTripleGatePrimes 16 ∧
      (3, (7, 13)) ∈ paritySafeTripleGateTriples 16 ∧
      17 ∈ squareWaveOffsets 16 (3 * 7 * 13) ∧
      3 ^ 3 < squareBody 16 ∧
      2 * 16 < 3 * 7 * 13 ∧
      (squareWaveOffsets 16 (3 * 7 * 13)).card = 1 := by
  have hL := paritySafeCanonicalResidualTriple_witness_16_17
  rcases hL with ⟨hcandidate, hsupport, hcanonical, hstar, hpair, hres,
    htriple, hdiv⟩
  have hkey := paritySafeCanonicalResidualTripleIncidence_mem_tripleGateTriples htriple
  rw [hcanonical] at hkey
  have hgate : 3 ∈ paritySafeTripleGatePrimes 16 :=
    (mem_paritySafeTripleGateTriples.mp hkey).1
  have hwave := paritySafeCanonicalResidualTripleIncidence_mem_productWave htriple
  rw [hcanonical] at hwave
  have hfar : 2 * 16 < 3 * 7 * 13 := by norm_num
  have hle : (squareWaveOffsets 16 (3 * 7 * 13)).card ≤ 1 :=
    card_squareWaveOffsets_le_one_of_two_mul_lt_modulus (by norm_num) hfar
  have hnonempty : (squareWaveOffsets 16 (3 * 7 * 13)).Nonempty :=
    ⟨17, hwave⟩
  have hcardpos : 0 < (squareWaveOffsets 16 (3 * 7 * 13)).card :=
    Finset.card_pos.mpr hnonempty
  exact ⟨hcandidate, hgate, hkey, hwave, by norm_num [squareBody], hfar,
    by omega⟩

end DkMath.NumberTheory.Legendre
