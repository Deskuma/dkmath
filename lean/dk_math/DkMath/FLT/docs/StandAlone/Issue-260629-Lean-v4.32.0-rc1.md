# Issue: Build error

Lean v4.29.0 → v4.32.0-rc1

**[SOLVED]** 2026/06/29 17:37

## Error status

### h_c_ne

```lean
lemma padicValNat_lower_bound_of_dvd_d3 {c q : ℕ}
    (hc_pos : 0 < c)
    (hq : Nat.Prime q)
    (hq_dvd_c : q ∣ c) :
    3 ≤ padicValNat q (c ^ 3) := by
  have h_c_ne : c ≠ 0 := Nat.ne_of_gt hc_pos
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h_val_c_ge_1 : 1 ≤ padicValNat q c := by
    have h_ne_zero : padicValNat q c ≠ 0 := by
      intro h
      have : ¬ q ∣ c := by
        rcases padicValNat.eq_zero_iff.mp h with hq1 | hc0 | hqndvd
        · exact (hq.ne_one hq1).elim
        · exact (h_c_ne hc0).elim
        · exact hqndvd
      exact this hq_dvd_c
    omega
  have h_val_pow : padicValNat q (c ^ 3) = 3 * padicValNat q c :=
    padicValNat.pow (n := 3) h_c_ne
  rw [h_val_pow]
  omega
```

```error
  have h_val_pow : padicValNat q (c ^ 3) = 3 * padicValNat q c :=
    padicValNat.pow (n := 3) h_c_ne

-> h_c_ne

Application type mismatch: The argument
  h_c_ne
has type
  c ≠ 0
of sort `Prop` but is expected to have type
  ℕ
of sort `Type` in the application
  padicValNat.pow h_c_ne
```

```infoview
c q : ℕ
hc_pos : 0 < c
hq : Nat.Prime q
hq_dvd_c : q ∣ c
h_c_ne : c ≠ 0
this : Fact (Nat.Prime q) := { out := hq }
h_val_c_ge_1 : 1 ≤ padicValNat q c
⊢ 3 ≤ padicValNat q (c ^ 3)
```

---

### simpa [hCore, s0] using

```lean
lemma exists_descend_measure_eq_zero_of_descentClassify_primitiveSized
    {c b q : ℕ}
    (hDescent : DescentClassifyImpossibleOnPrimitive c b)
    (hPrim : PrimitiveOnS0 c b q)
    (size : ℕ)
    (hsize : size ≤ q) :
    ∃ n : ℕ,
      (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        (GEisensteinDescentFrame.descend
          (primitiveSizedCandidateGEisensteinDescentFrame c b)
          (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize)
          n) = 0 := by
  let hCore : GEisensteinDescentCore c b :=
    GEisensteinDescentCore_of_descentClassify_primitiveSized hDescent
  let s0 : hCore.frame.State :=
    GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize
  simpa [hCore, s0] using
    GEisensteinDescentCore.exists_descend_measure_eq_zero_of_step_pred hCore s0
```

```error
-> simpa [hCore, s0] using

Type mismatch: After simplification, term
  GEisensteinDescentCore.exists_descend_measure_eq_zero_of_step_pred hCore s0
 has type
  ∃ n,
    (GEisensteinDescentCore_of_descentClassify_primitiveSized ⋯).frame.measure
        ((GEisensteinDescentCore_of_descentClassify_primitiveSized ⋯).frame.descend
          (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize) n) =
      0
but is expected to have type
  ∃ n,
    (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        ((primitiveSizedCandidateGEisensteinDescentFrame c b).descend
          (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize) n) =
      0
```

```infoview
c b q : ℕ
hDescent : DescentClassifyImpossibleOnPrimitive c b
hPrim : PrimitiveOnS0 c b q
size : ℕ
hsize : size ≤ q
hCore : GEisensteinDescentCore c b := GEisensteinDescentCore_of_descentClassify_primitiveSized ⋯
s0 : hCore.frame.State := GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize
⊢ ∃ n,
  (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
      ((primitiveSizedCandidateGEisensteinDescentFrame c b).descend
        (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize) n) =
    0
```

## Fix

### padicValNat_lower_bound_of_dvd_d3: h_val_pow

```lean
lemma padicValNat_lower_bound_of_dvd_d3 {c q : ℕ}
    (hc_pos : 0 < c)
    (hq : Nat.Prime q)
    (hq_dvd_c : q ∣ c) :
    3 ≤ padicValNat q (c ^ 3) := by
  have h_c_ne : c ≠ 0 := Nat.ne_of_gt hc_pos
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have h_val_c_ge_1 : 1 ≤ padicValNat q c := by
    exact one_le_padicValNat_of_dvd h_c_ne hq_dvd_c
  have h_val_pow : padicValNat q (c ^ 3) = 3 * padicValNat q c := by
    exact padicValNat.pow c 3  -- v4.32.0-rc1
  rw [h_val_pow]
  omega
```

### exists_descend_measure_eq_zero_of_descentClassify_primitiveSized

```lean
lemma exists_descend_measure_eq_zero_of_descentClassify_primitiveSized
    {c b q : ℕ}
    (_hDescent : DescentClassifyImpossibleOnPrimitive c b)
    (hPrim : PrimitiveOnS0 c b q)
    (size : ℕ)
    (hsize : size ≤ q) :
    ∃ n : ℕ,
      (primitiveSizedCandidateGEisensteinDescentFrame c b).measure
        (GEisensteinDescentFrame.descend
          (primitiveSizedCandidateGEisensteinDescentFrame c b)
          (GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize)
          n) = 0 := by
  let F := primitiveSizedCandidateGEisensteinDescentFrame c b
  let s0 : F.State :=
    GEisensteinPrimitiveSizedCandidate.ofPrimitiveWithSize hPrim size hsize
  refine ⟨F.measure s0, ?_⟩
  simpa [F, s0] using
    GEisensteinDescentFrame.measure_descend_eq_zero_of_step_pred
      F
      (primitiveSizedCandidate_frame_step_pred c b)
      s0
```
