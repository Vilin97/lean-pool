/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Padic

/-!
# The `2`-adic Hilbert symbol: units

Serre's explicit formula for the Hilbert symbol at `p = 2` writes `a = 2 ^ α u`,
`b = 2 ^ β v` with `u, v ∈ ℤ_[2]ˣ` and reads

`(a,b)_2 = (-1)^{ε(u) ε(v) + α ω(v) + β ω(u)}`,

where `ε(u) = 0` iff `u ≡ 1 (mod 4)` and `ω(u) = 0` iff `u ≡ ±1 (mod 8)`.

This file proves the *unit* case `α = β = 0`, in the intrinsic form

`(u,v)_2 = 1`  if `u ≡ 1 (mod 4)` or `v ≡ 1 (mod 4)`, and `(u,v)_2 = -1` otherwise.

The proof does not need any norm-group theory.  It uses the square-class structure of
`ℤ_[2]ˣ`: every unit is a square times one of `1, 5, -1, -5`, and on those four
representatives the symbol is decided either by an explicit rational point
(the `1` entries) or by reducing a putative solution modulo `4` (the `-1` entries).

Note that the "two units have symbol `1`" statement that holds for odd `p` is **false**
at `p = 2`: `(3,3)_2 = -1`.
-/

@[expose] public section

namespace HasseMinkowski

attribute [local instance] Classical.propDecidable

/-! ### Finite residue facts -/

-- Theorem: every unit of `ZMod 4` squares to `1`.
private lemma zmod4_isUnit_sq : ∀ w : ZMod 4, IsUnit w → w ^ 2 = (1 : ZMod 4) := by
  decide

-- Theorem: every unit of `ZMod 4` is `1` or `3`.
private lemma zmod4_isUnit_cases : ∀ w : ZMod 4, IsUnit w → w = 1 ∨ w = 3 := by
  decide

-- Theorem: there is no solution of `z² = 3 x² + 3 y²` in `ZMod 4` with one unit coordinate.
private lemma no_zmod4_sol : ∀ z x y : ZMod 4,
    (z ^ 2 = 1 ∨ x ^ 2 = 1 ∨ y ^ 2 = 1) → z ^ 2 - 3 * x ^ 2 - 3 * y ^ 2 = 0 → False := by
  decide

-- Theorem: every unit of `ZMod 8` squares to `1`.
private lemma zmod8_isUnit_sq : ∀ w : ZMod 8, IsUnit w → w ^ 2 = (1 : ZMod 8) := by
  decide

-- Theorem: every unit of `ZMod 8` is one of `1, 3, 5, 7`.
private lemma zmod8_isUnit_cases :
    ∀ w : ZMod 8, IsUnit w → w = 1 ∨ w = 3 ∨ w = 5 ∨ w = 7 := by
  decide

-- Theorem: `2 * x ≠ 1` in `ZMod 8`.
private lemma zmod8_two_mul_ne_one : ∀ x : ZMod 8, (2 : ZMod 8) * x ≠ 1 := by
  decide

-- Theorem: a unit of `ZMod 8` reducing to `1` modulo `4` is `1` or `5`.
private lemma zmod8_unit_mod4_eq_one : ∀ w : ZMod 8, IsUnit w →
    ZMod.cast w = (1 : ZMod 4) → w = 1 ∨ w = 5 := by
  decide

-- Theorem: `2` is not a unit of `ℤ_[2]`.
private lemma not_isUnit_two : ¬ IsUnit (2 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  change ‖((2 : ℕ) : ℤ_[2])‖ = 1 → False
  rw [PadicInt.norm_natCast_eq_one_iff]
  decide

-- Theorem: the odd numbers `3, 5, 7, 17` are units of `ℤ_[2]`.
private lemma isUnit_three : IsUnit (3 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  change ‖((3 : ℕ) : ℤ_[2])‖ = 1
  rw [PadicInt.norm_natCast_eq_one_iff]
  decide

private lemma isUnit_five : IsUnit (5 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  change ‖((5 : ℕ) : ℤ_[2])‖ = 1
  rw [PadicInt.norm_natCast_eq_one_iff]
  decide

private lemma isUnit_seven : IsUnit (7 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  change ‖((7 : ℕ) : ℤ_[2])‖ = 1
  rw [PadicInt.norm_natCast_eq_one_iff]
  decide

-- Theorem: reduction of a natural number modulo `8` is compatible with the coercion into
-- `ℤ_[2]`.
private lemma toZModPow_three_natCast (n : ℕ) :
    ((n : ℕ) : ℤ_[2]).toZModPow 3 = (n : ZMod 8) :=
  map_natCast (PadicInt.toZModPow 3) n

/-! ### Square units -/

-- Theorem: if a `2`-adic unit is a square, then its Hilbert symbol against any other unit
-- is `1`.
theorem hilbertSym_padic_two_units_of_isSquare {u v : ℤ_[2]ˣ}
    (hu : IsSquare (u : ℤ_[2])) :
    hilbertSym (u : ℚ_[2]) (v : ℚ_[2]) = 1 := by
  obtain ⟨s, hs⟩ := hu
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact u.ne_zero hs
  have hsq : ((u : ℤ_[2]) : ℚ_[2]) = ((s : ℚ_[2])) ^ 2 := by
    have h := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hs
    push_cast at h
    rw [pow_two]; exact h
  rw [show (u : ℚ_[2]) = (s : ℚ_[2]) ^ 2 from hsq]
  exact hilbertSym_sq_left (PadicInt.coe_ne_zero.mpr hs0)
    (PadicInt.coe_ne_zero.mpr v.ne_zero)

-- Theorem: a `2`-adic unit congruent to `1` modulo `8` is a square, so its Hilbert symbol
-- against any other unit is `1`.
theorem hilbertSym_padic_two_units_of_toZModPow_eq_one {u v : ℤ_[2]ˣ}
    (hu : (u : ℤ_[2]).toZModPow 3 = 1) :
    hilbertSym (u : ℚ_[2]) (v : ℚ_[2]) = 1 := by
  have hw : ¬ (2 : ℤ_[2]) ∣ (u : ℤ_[2]) := by
    intro hd
    exact not_isUnit_two
      (isUnit_iff_dvd_one.mpr (dvd_trans hd (isUnit_iff_dvd_one.mp u.isUnit)))
  have hmod : IsSquare ((u : ℤ_[2]).toZModPow 3) := by
    rw [hu]; exact IsSquare.one
  exact hilbertSym_padic_two_units_of_isSquare
    (PadicInt.isSquare_of_zmodPow hw hmod)

/-! ### Reducing rational solutions modulo `4`

The homogeneity of `z² - a x² - b y²` lets us rescale any nontrivial rational solution by
the inverse of a coordinate of maximal norm, producing an integral solution with a unit
coordinate.  This is the `p = 2` specialization of the generic rescaling
`exists_padicInt_solution_gen`.  Reducing that solution modulo `4` then contradicts
`no_zmod4_sol` whenever both coefficients are `3` mod `4`.
-/

-- Theorem: a nontrivial rational solution of `z² - c₁ x² - c₂ y² = 0` with integral
-- coefficients rescales to an integral solution with at least one unit coordinate.
private lemma exists_padicInt_solution_coeff {c₁ c₂ : ℤ_[2]} {x y z : ℚ_[2]}
    (hnontriv : (z, x, y) ≠ (0, 0, 0))
    (hsol : z ^ 2 - (c₁ : ℚ_[2]) * x ^ 2 - (c₂ : ℚ_[2]) * y ^ 2 = 0) :
    ∃ Z X Y : ℤ_[2], Z ^ 2 - c₁ * X ^ 2 - c₂ * Y ^ 2 = 0
      ∧ (IsUnit Z ∨ IsUnit X ∨ IsUnit Y) := by
  have hnontriv' : (x, y, z) ≠ (0, 0, 0) := by
    intro h
    apply hnontriv
    simp only [Prod.mk.injEq] at h ⊢
    tauto
  obtain ⟨Z, X, Y, hZeq, hunit⟩ :=
    exists_padicInt_solution_gen (p := 2) (c₁ := (c₁ : ℚ_[2])) (c₂ := (c₂ : ℚ_[2]))
      hnontriv' hsol
  refine ⟨Z, X, Y, ?_, hunit⟩
  apply PadicInt.ext
  push_cast
  exact hZeq

-- Theorem: if two `2`-adic units are both `3` modulo `4`, their Hilbert symbol is `-1`.
theorem hilbertSym_padic_two_units_eq_neg_one_of_mod4 {u v : ℤ_[2]ˣ}
    (hu : (u : ℤ_[2]).toZModPow 2 = 3) (hv : (v : ℤ_[2]).toZModPow 2 = 3) :
    hilbertSym (u : ℚ_[2]) (v : ℚ_[2]) = -1 := by
  have hu0 : (u : ℚ_[2]) ≠ 0 := fun h => u.ne_zero (PadicInt.coe_eq_zero.mp h)
  have hv0 : (v : ℚ_[2]) ≠ 0 := fun h => v.ne_zero (PadicInt.coe_eq_zero.mp h)
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - (u : ℚ_[2]) * x ^ 2 - (v : ℚ_[2]) * y ^ 2 = 0 := by
    rintro ⟨z, x, y, hnontriv, hsol⟩
    obtain ⟨Z, X, Y, hZeq, hunit⟩ :=
      exists_padicInt_solution_coeff (c₁ := (u : ℤ_[2])) (c₂ := (v : ℤ_[2])) hnontriv hsol
    have hmod := congrArg (PadicInt.toZModPow 2) hZeq
    simp only [map_sub, map_mul, map_pow, map_zero] at hmod
    rw [hu, hv] at hmod
    have hsqZ : IsUnit Z → (PadicInt.toZModPow 2 Z) ^ 2 = 1 := fun hZ =>
      zmod4_isUnit_sq _ (hZ.map (PadicInt.toZModPow 2))
    have hsqX : IsUnit X → (PadicInt.toZModPow 2 X) ^ 2 = 1 := fun hX =>
      zmod4_isUnit_sq _ (hX.map (PadicInt.toZModPow 2))
    have hsqY : IsUnit Y → (PadicInt.toZModPow 2 Y) ^ 2 = 1 := fun hY =>
      zmod4_isUnit_sq _ (hY.map (PadicInt.toZModPow 2))
    rcases hunit with hZ | hX | hY
    · exact no_zmod4_sol _ _ _ (Or.inl (hsqZ hZ)) hmod
    · exact no_zmod4_sol _ _ _ (Or.inr (Or.inl (hsqX hX))) hmod
    · exact no_zmod4_sol _ _ _ (Or.inr (Or.inr (hsqY hY))) hmod
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨hu0, hv0⟩), ite_eq_right hno]

/-! ### Reducing a unit to its residue class modulo `8`

Every unit `u` of `ℤ_[2]` is `r · s²` where `r ∈ {1, 3, 5, 7}` has the same residue as
`u` modulo `8` and `s` is another unit: indeed `u * r` is congruent to `r² ≡ 1` modulo
`8`, hence a square.  Because `hilbertSym` is unchanged when either argument is multiplied
by a nonzero square, this lets us compute the symbol on the four representatives. -/

-- Theorem: a unit whose mod-`8` residue agrees with `r` is `r` times a square.
private lemma exists_sq_mul_rep (u : ℤ_[2]ˣ) (r : ℤ_[2])
    (hr : r.toZModPow 3 = (u : ℤ_[2]).toZModPow 3) (hr0 : r ≠ 0) :
    ∃ s : ℚ_[2], (u : ℚ_[2]) = (r : ℚ_[2]) * s ^ 2 := by
  set m : ℤ_[2] := (u : ℤ_[2]) * r with hm
  have hm1 : m.toZModPow 3 = 1 := by
    rw [hm, map_mul, hr, ← pow_two]
    exact zmod8_isUnit_sq _ (u.isUnit.map (PadicInt.toZModPow 3))
  have hndvd : ¬ (2 : ℤ_[2]) ∣ m := by
    rintro ⟨k, hk⟩
    have h2k : m.toZModPow 3 = (2 : ZMod 8) * k.toZModPow 3 := by
      rw [hk, map_mul]
      congr 1
      simpa using toZModPow_three_natCast 2
    rw [hm1] at h2k
    exact zmod8_two_mul_ne_one _ h2k.symm
  obtain ⟨s, hs⟩ := PadicInt.isSquare_of_zmodPow hndvd (by rw [hm1]; exact IsSquare.one)
  have hrQ : (r : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hr0
  have hsu : (u : ℚ_[2]) * (r : ℚ_[2]) = (s : ℚ_[2]) * (s : ℚ_[2]) := by
    have h := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hs
    push_cast at h
    rw [hm] at h
    push_cast at h
    exact h
  refine ⟨(s : ℚ_[2]) * (r : ℚ_[2])⁻¹, ?_⟩
  have h1 : (r : ℚ_[2]) * ((r : ℚ_[2])⁻¹) ^ 2 = (r : ℚ_[2])⁻¹ := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hrQ, one_mul]
  have h2 : (r : ℚ_[2]) * ((s : ℚ_[2]) * (r : ℚ_[2])⁻¹) ^ 2
      = (s : ℚ_[2]) ^ 2 * ((r : ℚ_[2]) * ((r : ℚ_[2])⁻¹) ^ 2) := by ring
  rw [h2, h1, pow_two, ← hsu, mul_assoc, mul_inv_cancel₀ hrQ, mul_one]

-- Theorem: multiplying the first argument of the Hilbert symbol by a square is harmless.
private lemma hilbertSym_eq_rep_left (u : ℤ_[2]ˣ) (r : ℤ_[2]) (w : ℚ_[2])
    (hs : ∃ s : ℚ_[2], (u : ℚ_[2]) = (r : ℚ_[2]) * s ^ 2) :
    hilbertSym (u : ℚ_[2]) w = hilbertSym (r : ℚ_[2]) w := by
  obtain ⟨s, hs⟩ := hs
  have hs0 : s ≠ 0 := by
    intro h0
    have hzero : (u : ℚ_[2]) = 0 := by rw [hs, h0]; simp
    exact u.ne_zero (PadicInt.coe_eq_zero.mp hzero)
  rw [hs]
  simpa using hilbertSym_mul_square_eq (a := (r : ℚ_[2])) (a' := s)
    (b := w) (b' := (1 : ℚ_[2])) hs0 (by norm_num)

-- Theorem: multiplying the second argument of the Hilbert symbol by a square is harmless.
private lemma hilbertSym_eq_rep_right (w : ℚ_[2]) (v : ℤ_[2]ˣ) (r : ℤ_[2])
    (hs : ∃ s : ℚ_[2], (v : ℚ_[2]) = (r : ℚ_[2]) * s ^ 2) :
    hilbertSym w (v : ℚ_[2]) = hilbertSym w (r : ℚ_[2]) := by
  obtain ⟨s, hs⟩ := hs
  have hs0 : s ≠ 0 := by
    intro h0
    have hzero : (v : ℚ_[2]) = 0 := by rw [hs, h0]; simp
    exact v.ne_zero (PadicInt.coe_eq_zero.mp hzero)
  rw [hs]
  simpa using hilbertSym_mul_square_eq (a := w) (a' := (1 : ℚ_[2]))
    (b := (r : ℚ_[2])) (b' := s) (by norm_num) hs0

/-! ### The `4 × 4` table on the representatives

The positive entries are witnessed by explicit points: `(1,1,0)`, `(1,0,1)` and
`(5,2,1)` are rational, while `(√17,1,2)` and `(√33,1,2)` use that `17 ≡ 33 ≡ 1`
modulo `8` are squares in `ℤ_[2]`. -/

-- Theorem: `17` is a square in `ℚ_[2]`.
private lemma isSquare_seventeen : IsSquare (17 : ℚ_[2]) := by
  refine Padic.isSquare_of_dist_one_lt_pow ?_
  rw [dist_eq_norm]
  have h17 : (17 : ℚ_[2]) - 1 = ((2 : ℕ) : ℚ_[2]) ^ 4 := by norm_num
  rw [h17, Padic.norm_p_pow]
  norm_num

-- Theorem: `33` is a square in `ℚ_[2]`.
private lemma isSquare_thirtythree : IsSquare (33 : ℚ_[2]) := by
  refine Padic.isSquare_of_dist_one_lt_pow ?_
  rw [dist_eq_norm]
  have h33 : (33 : ℚ_[2]) - 1 = ((2 : ℕ) : ℚ_[2]) ^ 5 := by norm_num
  rw [h33, Padic.norm_p_pow]
  norm_num

-- Theorem: `(1, b)_2 = 1` for every nonzero `b`.
private lemma hilbertSym_one_left (w : ℚ_[2]) (hw : w ≠ 0) :
    hilbertSym (1 : ℚ_[2]) w = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) hw ⟨1, 1, 0, by simp, by norm_num⟩

-- Theorem: `(5, 1)_2 = 1`.
private lemma hilbertSym_five_one : hilbertSym (5 : ℚ_[2]) (1 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(1 : ℚ_[2]), 0, 1, by simp, by norm_num⟩

-- Theorem: `(5, 3)_2 = 1`, with `√17`.
private lemma hilbertSym_five_three : hilbertSym (5 : ℚ_[2]) (3 : ℚ_[2]) = 1 := by
  obtain ⟨w, hw⟩ := isSquare_seventeen
  refine hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨w, 1, 2, by simp, ?_⟩
  rw [show w ^ 2 = 17 by rw [pow_two]; exact hw.symm]
  norm_num

-- Theorem: `(5, 5)_2 = 1`, with the point `(5, 2, 1)`.
private lemma hilbertSym_five_five : hilbertSym (5 : ℚ_[2]) (5 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(5 : ℚ_[2]), 2, 1, by simp, by norm_num⟩

-- Theorem: `(5, 7)_2 = 1`, with `√33`.
private lemma hilbertSym_five_seven : hilbertSym (5 : ℚ_[2]) (7 : ℚ_[2]) = 1 := by
  obtain ⟨w, hw⟩ := isSquare_thirtythree
  refine hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨w, 1, 2, by simp, ?_⟩
  rw [show w ^ 2 = 33 by rw [pow_two]; exact hw.symm]
  norm_num

-- Theorem: `(5, v)_2 = 1` for every `2`-adic unit `v`.
private lemma hilbertSym_five_unit (v : ℤ_[2]ˣ) :
    hilbertSym (5 : ℚ_[2]) (v : ℚ_[2]) = 1 := by
  have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
  rcases zmod8_isUnit_cases ((v : ℤ_[2]).toZModPow 3)
      (v.isUnit.map (PadicInt.toZModPow 3)) with h | h | h | h
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 1 (by rw [h]; simp)
      (by norm_num)
    rw [hilbertSym_eq_rep_right (5 : ℚ_[2]) v 1 ⟨s, hs⟩]
    change hilbertSym (5 : ℚ_[2]) (1 : ℚ_[2]) = 1
    exact hilbertSym_five_one
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 3 (by rw [h]; simpa using toZModPow_three_natCast 3)
      isUnit_three.ne_zero
    rw [hilbertSym_eq_rep_right (5 : ℚ_[2]) v 3 ⟨s, hs⟩]
    change hilbertSym (5 : ℚ_[2]) (3 : ℚ_[2]) = 1
    exact hilbertSym_five_three
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 5 (by rw [h]; simpa using toZModPow_three_natCast 5)
      isUnit_five.ne_zero
    rw [hilbertSym_eq_rep_right (5 : ℚ_[2]) v 5 ⟨s, hs⟩]
    change hilbertSym (5 : ℚ_[2]) (5 : ℚ_[2]) = 1
    exact hilbertSym_five_five
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 7 (by rw [h]; simpa using toZModPow_three_natCast 7)
      isUnit_seven.ne_zero
    rw [hilbertSym_eq_rep_right (5 : ℚ_[2]) v 7 ⟨s, hs⟩]
    change hilbertSym (5 : ℚ_[2]) (7 : ℚ_[2]) = 1
    exact hilbertSym_five_seven

/-! ### The unit classification -/

-- Theorem: a `2`-adic unit congruent to `1` modulo `4` has Hilbert symbol `1` against
-- every other unit.
theorem hilbertSym_padic_two_units_eq_one_of_mod4 (u v : ℤ_[2]ˣ)
    (hu : (u : ℤ_[2]).toZModPow 2 = 1) :
    hilbertSym (u : ℚ_[2]) (v : ℚ_[2]) = 1 := by
  have hrel : ZMod.cast ((u : ℤ_[2]).toZModPow 3) = (u : ℤ_[2]).toZModPow 2 :=
    PadicInt.cast_toZModPow 2 3 (by norm_num) (u : ℤ_[2])
  have hcu : (u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 5 :=
    zmod8_unit_mod4_eq_one _ (u.isUnit.map (PadicInt.toZModPow 3)) (by rw [hrel, hu])
  rcases hcu with hcu | hcu
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep u 1 (by rw [hcu]; simp)
      (by norm_num)
    rw [hilbertSym_eq_rep_left u 1 (v : ℚ_[2]) ⟨s, hs⟩]
    change hilbertSym (1 : ℚ_[2]) (v : ℚ_[2]) = 1
    exact hilbertSym_one_left (v : ℚ_[2]) (PadicInt.coe_ne_zero.mpr v.ne_zero)
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep u 5 (by rw [hcu]; simpa using toZModPow_three_natCast 5)
      isUnit_five.ne_zero
    rw [hilbertSym_eq_rep_left u 5 (v : ℚ_[2]) ⟨s, hs⟩]
    change hilbertSym (5 : ℚ_[2]) (v : ℚ_[2]) = 1
    exact hilbertSym_five_unit v

-- Theorem: Serre's formula at `p = 2` for two units, in intrinsic form: the symbol is `-1`
-- exactly when both units are `3` modulo `4`.
theorem hilbertSym_padic_two_units (u v : ℤ_[2]ˣ) :
    hilbertSym (u : ℚ_[2]) (v : ℚ_[2])
      = if (u : ℤ_[2]).toZModPow 2 = 1 ∨ (v : ℤ_[2]).toZModPow 2 = 1
        then 1 else -1 := by
  by_cases hu : (u : ℤ_[2]).toZModPow 2 = 1
  · rw [ite_eq_left (Or.inl hu)]
    exact hilbertSym_padic_two_units_eq_one_of_mod4 u v hu
  · by_cases hv : (v : ℤ_[2]).toZModPow 2 = 1
    · rw [ite_eq_left (Or.inr hv), hilbertSym_comm]
      exact hilbertSym_padic_two_units_eq_one_of_mod4 v u hv
    · rw [ite_eq_right (by tauto)]
      refine hilbertSym_padic_two_units_eq_neg_one_of_mod4 (u := u) (v := v) ?_ ?_
      · rcases zmod4_isUnit_cases _ (u.isUnit.map (PadicInt.toZModPow 2)) with h | h
        · exact absurd h hu
        · exact h
      · rcases zmod4_isUnit_cases _ (v.isUnit.map (PadicInt.toZModPow 2)) with h | h
        · exact absurd h hv
        · exact h

/-! ### The `2`-adic unit decomposition -/

-- Theorem: `2` is nonzero as an element of `ℚ_[2]`.
private lemma two_padic_ne_zero : (2 : ℚ_[2]) ≠ 0 := by
  intro h
  have hnorm : ‖((2 : ℕ) : ℚ_[2])‖ = 0 := by
    rw [show ((2 : ℕ) : ℚ_[2]) = (2 : ℚ_[2]) by norm_num, h, norm_zero]
  rw [Padic.norm_p] at hnorm
  norm_num at hnorm

/-- The unit part of a nonzero `2`-adic number: `a = 2 ^ a.valuation * twoAdicUnit a ha`. -/
noncomputable def twoAdicUnit (a : ℚ_[2]) (ha : a ≠ 0) : ℤ_[2]ˣ :=
  padicUnit (p := 2) a ha

-- Theorem: the underlying `2`-adic number of `twoAdicUnit a ha` is `a * 2 ^ (-(a.valuation))`.
private lemma coe_twoAdicUnit (a : ℚ_[2]) (ha : a ≠ 0) :
    ((twoAdicUnit a ha : ℤ_[2]) : ℚ_[2]) = a * (2 : ℚ_[2]) ^ (-(a.valuation)) := by
  simpa only [twoAdicUnit, Nat.cast_ofNat] using coe_padicUnit (p := 2) a ha

-- Theorem: every nonzero `2`-adic number is `2 ^ a.valuation` times its unit part.
private lemma twoAdicUnit_spec (a : ℚ_[2]) (ha : a ≠ 0) :
    a = (2 : ℚ_[2]) ^ a.valuation * ((twoAdicUnit a ha : ℤ_[2]) : ℚ_[2]) := by
  simpa only [twoAdicUnit, Nat.cast_ofNat] using padicUnit_spec (p := 2) a ha

-- Theorem: the unit part of a nonzero `2`-adic number has norm `1`.
private lemma norm_twoAdicUnit (a : ℚ_[2]) (ha : a ≠ 0) :
    ‖((twoAdicUnit a ha : ℤ_[2]) : ℚ_[2])‖ = 1 := by
  simpa only [twoAdicUnit] using norm_padicUnit (p := 2) a ha

/-! ### The symbol of `2` against a unit

`(2, v)_2 = 1` iff `v ≡ ±1 (mod 8)`.  The two `-1` values are settled by reducing an
integral solution modulo `8` (there `z² - 2x² - 3y²` and `z² - 2x² - 5y²` have no zero with
a unit coordinate), and the two `1` values by explicit points: for `v ≡ 1` the unit `v` is
a square, while for `v ≡ 7` one has `-v = s²` and `(s, s, 1)` is a zero. -/

-- Theorem: `z² - 2 x² - 3 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_two_three : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 2 * x ^ 2 - 3 * y ^ 2 = 0 → False := by
  decide

-- Theorem: `z² - 2 x² - 5 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_two_five : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 2 * x ^ 2 - 5 * y ^ 2 = 0 → False := by
  decide

-- Theorem: if `z² - c₁ x² - c₂ y²` has no zero modulo `8` with a unit coordinate, then it has
-- no nontrivial rational zero.  This is the reduction modulo `8` shared by the negative cases.
private lemma not_isotropic_of_no_zmod8 {c₁ c₂ : ℕ}
    (h : ∀ z x y : ZMod 8, (IsUnit z ∨ IsUnit x ∨ IsUnit y) →
      z ^ 2 - (c₁ : ZMod 8) * x ^ 2 - (c₂ : ZMod 8) * y ^ 2 = 0 → False) :
    ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - (c₁ : ℚ_[2]) * x ^ 2 - (c₂ : ℚ_[2]) * y ^ 2 = 0 := by
  rintro ⟨z, x, y, hnontriv, hsol⟩
  obtain ⟨Z, X, Y, hZeq, hunit⟩ :=
    exists_padicInt_solution_coeff (c₁ := (c₁ : ℤ_[2])) (c₂ := (c₂ : ℤ_[2]))
      hnontriv (by push_cast; exact hsol)
  have hmod := congrArg (PadicInt.toZModPow 3) hZeq
  simp only [map_sub, map_mul, map_pow, map_zero] at hmod
  rw [toZModPow_three_natCast c₁, toZModPow_three_natCast c₂] at hmod
  refine h _ _ _ ?_ hmod
  rcases hunit with hZ | hX | hY
  · exact Or.inl (hZ.map (PadicInt.toZModPow 3))
  · exact Or.inr (Or.inl (hX.map (PadicInt.toZModPow 3)))
  · exact Or.inr (Or.inr (hY.map (PadicInt.toZModPow 3)))

-- Theorem: `(2, 3)_2 = -1`.
private theorem hilbertSym_two_three : hilbertSym (2 : ℚ_[2]) (3 : ℚ_[2]) = -1 := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_padic_ne_zero
  have h3 : (3 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 2 * x ^ 2 - 3 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 2) (c₂ := 3) no_zmod8_sol_two_three
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h2, h3⟩), ite_eq_right hno]

-- Theorem: `(2, 5)_2 = -1`.
private theorem hilbertSym_two_five : hilbertSym (2 : ℚ_[2]) (5 : ℚ_[2]) = -1 := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_padic_ne_zero
  have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 2 * x ^ 2 - 5 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 2) (c₂ := 5) no_zmod8_sol_two_five
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h2, h5⟩), ite_eq_right hno]

-- Theorem: Serre's formula at `p = 2` for a unit and the element `2`: the symbol is `1` when
-- `u ≡ ±1 (mod 8)` and `-1` otherwise.
theorem hilbertSym_padic_two_two_unit (u : ℤ_[2]ˣ) :
    hilbertSym (2 : ℚ_[2]) (u : ℚ_[2])
      = if (u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 7 then 1 else -1 := by
  rcases zmod8_isUnit_cases ((u : ℤ_[2]).toZModPow 3)
      (u.isUnit.map (PadicInt.toZModPow 3)) with h | h | h | h
  · rw [ite_eq_left (Or.inl h)]
    obtain ⟨s, hs⟩ := exists_sq_mul_rep u 1 (by rw [h]; simp) (by norm_num)
    rw [hilbertSym_eq_rep_right (2 : ℚ_[2]) u 1 ⟨s, hs⟩]
    change hilbertSym (2 : ℚ_[2]) (1 : ℚ_[2]) = 1
    exact hilbertSym_eq_one_of_sol (two_padic_ne_zero) (by norm_num)
      ⟨1, 0, 1, by simp, by norm_num⟩
  · rw [ite_eq_right (by rw [h]; decide)]
    obtain ⟨s, hs⟩ := exists_sq_mul_rep u 3 (by rw [h]; simpa using toZModPow_three_natCast 3)
      isUnit_three.ne_zero
    rw [hilbertSym_eq_rep_right (2 : ℚ_[2]) u 3 ⟨s, hs⟩]
    change hilbertSym (2 : ℚ_[2]) (3 : ℚ_[2]) = -1
    exact hilbertSym_two_three
  · rw [ite_eq_right (by rw [h]; decide)]
    obtain ⟨s, hs⟩ := exists_sq_mul_rep u 5 (by rw [h]; simpa using toZModPow_three_natCast 5)
      isUnit_five.ne_zero
    rw [hilbertSym_eq_rep_right (2 : ℚ_[2]) u 5 ⟨s, hs⟩]
    change hilbertSym (2 : ℚ_[2]) (5 : ℚ_[2]) = -1
    exact hilbertSym_two_five
  · rw [ite_eq_left (Or.inr h)]
    have hndvd : ¬ (2 : ℤ_[2]) ∣ (-(u : ℤ_[2])) := by
      intro hd
      exact not_isUnit_two (isUnit_iff_dvd_one.mpr
        (dvd_trans hd (isUnit_iff_dvd_one.mp u.isUnit.neg)))
    have hmod : IsSquare ((-(u : ℤ_[2])).toZModPow 3) := by
      rw [map_neg, h, show (-(7 : ZMod 8)) = 1 by decide]
      exact IsSquare.one
    obtain ⟨s, hs⟩ := PadicInt.isSquare_of_zmodPow hndvd hmod
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hs
      have hc : (u : ℚ_[2]) = 0 := by
        have h := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hs
        push_cast at h
        simpa using neg_eq_zero.mp h
      exact u.ne_zero (PadicInt.coe_eq_zero.mp hc)
    have hsq : (u : ℚ_[2]) = -((s : ℚ_[2]) ^ 2) := by
      have hc := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hs
      push_cast at hc
      rw [pow_two]
      linear_combination -1 * hc
    refine hilbertSym_eq_one_of_sol two_padic_ne_zero
      (PadicInt.coe_ne_zero.mpr u.ne_zero) ?_
    refine ⟨(s : ℚ_[2]), (s : ℚ_[2]), (1 : ℚ_[2]), ?_, ?_⟩
    · intro hc
      have hsQ : (s : ℚ_[2]) = 0 := by simpa using congrArg Prod.fst hc
      exact (PadicInt.coe_ne_zero.mpr hs0) hsQ
    · rw [hsq]; ring
/-! ### The `ε` and `ω` characters

Serre's exponent `ε(u)ε(v) + α ω(v) + β ω(u)` uses `ε(u) = 0` iff `u ≡ 1 (mod 4)` and
`ω(u) = 0` iff `u ≡ ±1 (mod 8)`.  Both are read off the residues `toZModPow 2` and
`toZModPow 3` of the unit. -/

-- Theorem: `parityPow (-1) n` is `1` when `n` is even.
private lemma parityPow_neg_one_of_even {n : ℤ} (h : Even n) : parityPow (-1) n = 1 := by
  rw [parityPow, ite_eq_left h]

-- Theorem: `parityPow (-1) n` is `-1` when `n` is odd.
private lemma parityPow_neg_one_of_odd {n : ℤ} (h : ¬ Even n) : parityPow (-1) n = -1 := by
  rw [parityPow, ite_eq_right h]

/-- Serre's `ε` character: `ε(u) = 0` iff `u ≡ 1 (mod 4)`. -/
noncomputable def eps (u : ℤ_[2]ˣ) : ℤ := if (u : ℤ_[2]).toZModPow 2 = 1 then 0 else 1

/-- Serre's `ω` character: `ω(u) = 0` iff `u ≡ ±1 (mod 8)`. -/
noncomputable def omg (u : ℤ_[2]ˣ) : ℤ :=
  if (u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 7 then 0 else 1

-- Theorem: `ε(u) = 0` when `u ≡ 1 (mod 4)`.
private lemma eps_eq_zero (u : ℤ_[2]ˣ) (h : (u : ℤ_[2]).toZModPow 2 = 1) : eps u = 0 := by
  rw [eps, ite_eq_left h]

-- Theorem: `ε(u) = 1` when `u ≢ 1 (mod 4)`.
private lemma eps_eq_one (u : ℤ_[2]ˣ) (h : (u : ℤ_[2]).toZModPow 2 ≠ 1) : eps u = 1 := by
  rw [eps, ite_eq_right h]

-- Theorem: `ω(u) = 0` when `u ≡ ±1 (mod 8)`.
private lemma omg_eq_zero (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 7) : omg u = 0 := by
  rw [omg, ite_eq_left h]

-- Theorem: `ω(u) = 1` when `u ≢ ±1 (mod 8)`.
private lemma omg_eq_one (u : ℤ_[2]ˣ)
    (h : ¬ ((u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 7)) : omg u = 1 := by
  rw [omg, ite_eq_right h]

-- Theorem: the residue of a unit modulo `4` is determined by its residue modulo `8`.
private lemma toZModPow_two_eq_of_three (u : ℤ_[2]ˣ) {c : ZMod 8}
    (h : (u : ℤ_[2]).toZModPow 3 = c) : (u : ℤ_[2]).toZModPow 2 = ZMod.cast c := by
  rw [← h]
  exact (PadicInt.cast_toZModPow 2 3 (by norm_num) (u : ℤ_[2])).symm

-- Theorem: Serre's formula at `p = 2` for the element `2` and a unit, in character form:
-- `(2, u)_2 = (-1)^{ω(u)}`.
theorem hilbertSym_two_unit_char (u : ℤ_[2]ˣ) :
    hilbertSym (2 : ℚ_[2]) (u : ℚ_[2]) = parityPow (-1) (omg u) := by
  rw [hilbertSym_padic_two_two_unit]
  by_cases h : (u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 7
  · rw [ite_eq_left h, omg, ite_eq_left h, parityPow_neg_one_of_even (show Even (0 : ℤ) by decide)]
  · rw [ite_eq_right h, omg, ite_eq_right h]
    exact parityPow_neg_one_of_odd (show ¬ Even (1 : ℤ) by decide)

/-! ### The mixed cases `(2r, w)`

Serre's formula at `p = 2` for `a = 2r` with `r` a unit and `b = w` a unit reads
`(2r, w)_2 = (-1)^{ε(r) ε(w) + ω(w)}`.  Reducing `r` and `w` to the residues `1, 3, 5, 7`
modulo `8` leaves a `4 × 4` table, whose `1` entries are witnessed by explicit rational
points and whose `-1` entries are settled by reducing an integral solution modulo `8`.
The `r = 1` row is `hilbertSym_two_unit_char`. -/

-- Theorem: `z² - 6 x² - 5 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_six_five : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 6 * x ^ 2 - 5 * y ^ 2 = 0 → False := by
  decide

-- Theorem: `z² - 6 x² - 7 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_six_seven : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 6 * x ^ 2 - 7 * y ^ 2 = 0 → False := by
  decide

-- Theorem: `z² - 10 x² - 3 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_ten_three : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 10 * x ^ 2 - 3 * y ^ 2 = 0 → False := by
  decide

-- Theorem: `z² - 10 x² - 5 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_ten_five : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 10 * x ^ 2 - 5 * y ^ 2 = 0 → False := by
  decide

-- Theorem: `z² - 14 x² - 5 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_fourteen_five : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 14 * x ^ 2 - 5 * y ^ 2 = 0 → False := by
  decide

-- Theorem: `z² - 14 x² - 7 y²` has no zero in `ZMod 8` with a unit coordinate.
private lemma no_zmod8_sol_fourteen_seven : ∀ z x y : ZMod 8,
    (IsUnit z ∨ IsUnit x ∨ IsUnit y) → z ^ 2 - 14 * x ^ 2 - 7 * y ^ 2 = 0 → False := by
  decide

/-! The characters `ε` and `ω` only see the residue of the unit modulo `4` respectively
modulo `8`; the next lemmas evaluate them on the four representatives. -/

-- Theorem: `ε(u) = 0` when `u ≡ 1 (mod 8)`.
private lemma eps_of_tzp3_eq_one (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 1) : eps u = 0 := by
  rw [eps, toZModPow_two_eq_of_three u h]
  decide

-- Theorem: `ε(u) = 1` when `u ≡ 3 (mod 8)`.
private lemma eps_of_tzp3_eq_three (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 3) : eps u = 1 := by
  rw [eps, toZModPow_two_eq_of_three u h]
  decide

-- Theorem: `ε(u) = 0` when `u ≡ 5 (mod 8)`.
private lemma eps_of_tzp3_eq_five (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 5) : eps u = 0 := by
  rw [eps, toZModPow_two_eq_of_three u h]
  decide

-- Theorem: `ε(u) = 1` when `u ≡ 7 (mod 8)`.
private lemma eps_of_tzp3_eq_seven (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 7) : eps u = 1 := by
  rw [eps, toZModPow_two_eq_of_three u h]
  decide

-- Theorem: `ω(u) = 0` when `u ≡ 1 (mod 8)`.
private lemma omg_of_tzp3_eq_one (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 1) : omg u = 0 := by
  rw [omg, ite_eq_left (Or.inl h)]

-- Theorem: `ω(u) = 1` when `u ≡ 3 (mod 8)`.
private lemma omg_of_tzp3_eq_three (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 3) : omg u = 1 := by
  rw [omg, ite_eq_right (by rw [h]; decide)]

-- Theorem: `ω(u) = 1` when `u ≡ 5 (mod 8)`.
private lemma omg_of_tzp3_eq_five (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 5) : omg u = 1 := by
  rw [omg, ite_eq_right (by rw [h]; decide)]

-- Theorem: `ω(u) = 0` when `u ≡ 7 (mod 8)`.
private lemma omg_of_tzp3_eq_seven (u : ℤ_[2]ˣ)
    (h : (u : ℤ_[2]).toZModPow 3 = 7) : omg u = 0 := by
  rw [omg, ite_eq_left (Or.inr h)]

-- Theorem: `(6, 1)_2 = 1`, with the point `(7, 2, 5)`.
private lemma hilbertSym_six_one : hilbertSym (6 : ℚ_[2]) (1 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(7 : ℚ_[2]), 2, 5, by simp, by norm_num⟩

-- Theorem: `(6, 3)_2 = 1`, with the point `(3, 1, 1)`.
private lemma hilbertSym_six_three : hilbertSym (6 : ℚ_[2]) (3 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(3 : ℚ_[2]), 1, 1, by simp, by norm_num⟩

-- Theorem: `(10, 1)_2 = 1`, with the point `(7, 2, 3)`.
private lemma hilbertSym_ten_one : hilbertSym (10 : ℚ_[2]) (1 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(7 : ℚ_[2]), 2, 3, by simp, by norm_num⟩

-- Theorem: `(10, 7)_2 = 1`, with `√17`.
private lemma hilbertSym_ten_seven : hilbertSym (10 : ℚ_[2]) (7 : ℚ_[2]) = 1 := by
  obtain ⟨w, hw⟩ := isSquare_seventeen
  refine hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨w, 1, 1, by simp, ?_⟩
  rw [show w ^ 2 = 17 by rw [pow_two]; exact hw.symm]
  norm_num

-- Theorem: `(14, 1)_2 = 1`, with the point `(23, 6, 5)`.
private lemma hilbertSym_fourteen_one : hilbertSym (14 : ℚ_[2]) (1 : ℚ_[2]) = 1 :=
  hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨(23 : ℚ_[2]), 6, 5, by simp, by norm_num⟩

-- Theorem: `(14, 3)_2 = 1`, with `√17`.
private lemma hilbertSym_fourteen_three : hilbertSym (14 : ℚ_[2]) (3 : ℚ_[2]) = 1 := by
  obtain ⟨w, hw⟩ := isSquare_seventeen
  refine hilbertSym_eq_one_of_sol (by norm_num) (by norm_num)
    ⟨w, 1, 1, by simp, ?_⟩
  rw [show w ^ 2 = 17 by rw [pow_two]; exact hw.symm]
  norm_num

-- Theorem: `(6, 5)_2 = -1`.
private theorem hilbertSym_six_five : hilbertSym (6 : ℚ_[2]) (5 : ℚ_[2]) = -1 := by
  have h6 : (6 : ℚ_[2]) ≠ 0 := by norm_num
  have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 6 * x ^ 2 - 5 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 6) (c₂ := 5) no_zmod8_sol_six_five
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h6, h5⟩), ite_eq_right hno]

-- Theorem: `(6, 7)_2 = -1`.
private theorem hilbertSym_six_seven : hilbertSym (6 : ℚ_[2]) (7 : ℚ_[2]) = -1 := by
  have h6 : (6 : ℚ_[2]) ≠ 0 := by norm_num
  have h7 : (7 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 6 * x ^ 2 - 7 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 6) (c₂ := 7) no_zmod8_sol_six_seven
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h6, h7⟩), ite_eq_right hno]

-- Theorem: `(10, 3)_2 = -1`.
private theorem hilbertSym_ten_three : hilbertSym (10 : ℚ_[2]) (3 : ℚ_[2]) = -1 := by
  have h10 : (10 : ℚ_[2]) ≠ 0 := by norm_num
  have h3 : (3 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 10 * x ^ 2 - 3 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 10) (c₂ := 3) no_zmod8_sol_ten_three
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h10, h3⟩), ite_eq_right hno]

-- Theorem: `(10, 5)_2 = -1`.
private theorem hilbertSym_ten_five : hilbertSym (10 : ℚ_[2]) (5 : ℚ_[2]) = -1 := by
  have h10 : (10 : ℚ_[2]) ≠ 0 := by norm_num
  have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 10 * x ^ 2 - 5 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 10) (c₂ := 5) no_zmod8_sol_ten_five
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h10, h5⟩), ite_eq_right hno]

-- Theorem: `(14, 5)_2 = -1`.
private theorem hilbertSym_fourteen_five : hilbertSym (14 : ℚ_[2]) (5 : ℚ_[2]) = -1 := by
  have h14 : (14 : ℚ_[2]) ≠ 0 := by norm_num
  have h5 : (5 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 14 * x ^ 2 - 5 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 14) (c₂ := 5) no_zmod8_sol_fourteen_five
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h14, h5⟩), ite_eq_right hno]

-- Theorem: `(14, 7)_2 = -1`.
private theorem hilbertSym_fourteen_seven : hilbertSym (14 : ℚ_[2]) (7 : ℚ_[2]) = -1 := by
  have h14 : (14 : ℚ_[2]) ≠ 0 := by norm_num
  have h7 : (7 : ℚ_[2]) ≠ 0 := by norm_num
  have hno : ¬ ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - 14 * x ^ 2 - 7 * y ^ 2 = 0 :=
    not_isotropic_of_no_zmod8 (c₁ := 14) (c₂ := 7) no_zmod8_sol_fourteen_seven
  unfold hilbertSym
  rw [ite_eq_right (by rw [not_or]; exact ⟨h14, h7⟩), ite_eq_right hno]

/-! Each row of the table is recorded against an arbitrary unit by reducing the second
argument.  The row `r = 1` is `hilbertSym_two_unit_char`, so only the rows `2r = 6, 10, 14`
are new. -/

-- Theorem: `(10, v)_2 = (-1)^{ω(v)}` for every `2`-adic unit `v`.
private lemma hilbertSym_ten_unit (v : ℤ_[2]ˣ) :
    hilbertSym (10 : ℚ_[2]) (v : ℚ_[2]) = parityPow (-1) (omg v) := by
  rcases zmod8_isUnit_cases ((v : ℤ_[2]).toZModPow 3)
      (v.isUnit.map (PadicInt.toZModPow 3)) with h | h | h | h
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 1 (by rw [h]; simp) (by norm_num)
    rw [hilbertSym_eq_rep_right (10 : ℚ_[2]) v 1 ⟨s, hs⟩]
    change hilbertSym (10 : ℚ_[2]) (1 : ℚ_[2]) = parityPow (-1) (omg v)
    rw [hilbertSym_ten_one, omg_of_tzp3_eq_one v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 3 (by rw [h]; simpa using toZModPow_three_natCast 3)
      isUnit_three.ne_zero
    rw [hilbertSym_eq_rep_right (10 : ℚ_[2]) v 3 ⟨s, hs⟩]
    change hilbertSym (10 : ℚ_[2]) (3 : ℚ_[2]) = parityPow (-1) (omg v)
    rw [hilbertSym_ten_three, omg_of_tzp3_eq_three v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 5 (by rw [h]; simpa using toZModPow_three_natCast 5)
      isUnit_five.ne_zero
    rw [hilbertSym_eq_rep_right (10 : ℚ_[2]) v 5 ⟨s, hs⟩]
    change hilbertSym (10 : ℚ_[2]) (5 : ℚ_[2]) = parityPow (-1) (omg v)
    rw [hilbertSym_ten_five, omg_of_tzp3_eq_five v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 7 (by rw [h]; simpa using toZModPow_three_natCast 7)
      isUnit_seven.ne_zero
    rw [hilbertSym_eq_rep_right (10 : ℚ_[2]) v 7 ⟨s, hs⟩]
    change hilbertSym (10 : ℚ_[2]) (7 : ℚ_[2]) = parityPow (-1) (omg v)
    rw [hilbertSym_ten_seven, omg_of_tzp3_eq_seven v h]
    decide

-- Theorem: `(6, v)_2 = (-1)^{ε(v) + ω(v)}` for every `2`-adic unit `v`.
private lemma hilbertSym_six_unit (v : ℤ_[2]ˣ) :
    hilbertSym (6 : ℚ_[2]) (v : ℚ_[2]) = parityPow (-1) (eps v + omg v) := by
  rcases zmod8_isUnit_cases ((v : ℤ_[2]).toZModPow 3)
      (v.isUnit.map (PadicInt.toZModPow 3)) with h | h | h | h
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 1 (by rw [h]; simp) (by norm_num)
    rw [hilbertSym_eq_rep_right (6 : ℚ_[2]) v 1 ⟨s, hs⟩]
    change hilbertSym (6 : ℚ_[2]) (1 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_six_one, eps_of_tzp3_eq_one v h, omg_of_tzp3_eq_one v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 3 (by rw [h]; simpa using toZModPow_three_natCast 3)
      isUnit_three.ne_zero
    rw [hilbertSym_eq_rep_right (6 : ℚ_[2]) v 3 ⟨s, hs⟩]
    change hilbertSym (6 : ℚ_[2]) (3 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_six_three, eps_of_tzp3_eq_three v h, omg_of_tzp3_eq_three v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 5 (by rw [h]; simpa using toZModPow_three_natCast 5)
      isUnit_five.ne_zero
    rw [hilbertSym_eq_rep_right (6 : ℚ_[2]) v 5 ⟨s, hs⟩]
    change hilbertSym (6 : ℚ_[2]) (5 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_six_five, eps_of_tzp3_eq_five v h, omg_of_tzp3_eq_five v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 7 (by rw [h]; simpa using toZModPow_three_natCast 7)
      isUnit_seven.ne_zero
    rw [hilbertSym_eq_rep_right (6 : ℚ_[2]) v 7 ⟨s, hs⟩]
    change hilbertSym (6 : ℚ_[2]) (7 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_six_seven, eps_of_tzp3_eq_seven v h, omg_of_tzp3_eq_seven v h]
    decide

-- Theorem: `(14, v)_2 = (-1)^{ε(v) + ω(v)}` for every `2`-adic unit `v`.
private lemma hilbertSym_fourteen_unit (v : ℤ_[2]ˣ) :
    hilbertSym (14 : ℚ_[2]) (v : ℚ_[2]) = parityPow (-1) (eps v + omg v) := by
  rcases zmod8_isUnit_cases ((v : ℤ_[2]).toZModPow 3)
      (v.isUnit.map (PadicInt.toZModPow 3)) with h | h | h | h
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 1 (by rw [h]; simp) (by norm_num)
    rw [hilbertSym_eq_rep_right (14 : ℚ_[2]) v 1 ⟨s, hs⟩]
    change hilbertSym (14 : ℚ_[2]) (1 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_fourteen_one, eps_of_tzp3_eq_one v h, omg_of_tzp3_eq_one v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 3 (by rw [h]; simpa using toZModPow_three_natCast 3)
      isUnit_three.ne_zero
    rw [hilbertSym_eq_rep_right (14 : ℚ_[2]) v 3 ⟨s, hs⟩]
    change hilbertSym (14 : ℚ_[2]) (3 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_fourteen_three, eps_of_tzp3_eq_three v h, omg_of_tzp3_eq_three v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 5 (by rw [h]; simpa using toZModPow_three_natCast 5)
      isUnit_five.ne_zero
    rw [hilbertSym_eq_rep_right (14 : ℚ_[2]) v 5 ⟨s, hs⟩]
    change hilbertSym (14 : ℚ_[2]) (5 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_fourteen_five, eps_of_tzp3_eq_five v h, omg_of_tzp3_eq_five v h]
    decide
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep v 7 (by rw [h]; simpa using toZModPow_three_natCast 7)
      isUnit_seven.ne_zero
    rw [hilbertSym_eq_rep_right (14 : ℚ_[2]) v 7 ⟨s, hs⟩]
    change hilbertSym (14 : ℚ_[2]) (7 : ℚ_[2]) = parityPow (-1) (eps v + omg v)
    rw [hilbertSym_fourteen_seven, eps_of_tzp3_eq_seven v h, omg_of_tzp3_eq_seven v h]
    decide

-- Theorem: multiplying the first argument `2 * r` of the Hilbert symbol by a square is
-- harmless.
private lemma hilbertSym_two_mul_rep_left (r : ℤ_[2]ˣ) (a : ℤ_[2]) (w : ℚ_[2])
    (hs : ∃ s : ℚ_[2], (r : ℚ_[2]) = (a : ℚ_[2]) * s ^ 2) :
    hilbertSym (2 * (r : ℚ_[2])) w = hilbertSym (2 * (a : ℚ_[2])) w := by
  obtain ⟨s, hs⟩ := hs
  have hs0 : s ≠ 0 := by
    intro h0
    have hzero : (r : ℚ_[2]) = 0 := by rw [hs, h0]; simp
    exact r.ne_zero (PadicInt.coe_eq_zero.mp hzero)
  rw [hs, show 2 * ((a : ℚ_[2]) * s ^ 2) = (2 * (a : ℚ_[2])) * s ^ 2 by ring]
  simpa using hilbertSym_mul_square_eq (a := 2 * (a : ℚ_[2])) (a' := s)
    (b := w) (b' := (1 : ℚ_[2])) hs0 (by norm_num)

-- Theorem: Serre's formula at `p = 2` for `2 · r` against a unit.
theorem hilbertSym_two_mul_unit (r w : ℤ_[2]ˣ) :
    hilbertSym (2 * (r : ℚ_[2])) (w : ℚ_[2])
      = parityPow (-1) (eps r * eps w + omg w) := by
  rcases zmod8_isUnit_cases ((r : ℤ_[2]).toZModPow 3)
      (r.isUnit.map (PadicInt.toZModPow 3)) with h | h | h | h
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep r 1 (by rw [h]; simp) (by norm_num)
    rw [hilbertSym_two_mul_rep_left r 1 (w : ℚ_[2]) ⟨s, hs⟩]
    rw [show (2 : ℚ_[2]) * ((1 : ℤ_[2]) : ℚ_[2]) = 2 by norm_num,
      hilbertSym_two_unit_char w, eps_of_tzp3_eq_one r h]
    simp [zero_mul, zero_add]
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep r 3
      (by rw [h]; simpa using toZModPow_three_natCast 3) isUnit_three.ne_zero
    rw [hilbertSym_two_mul_rep_left r 3 (w : ℚ_[2]) ⟨s, hs⟩]
    rw [show (2 : ℚ_[2]) * ((3 : ℤ_[2]) : ℚ_[2]) = 6 by
        change (2 : ℚ_[2]) * (3 : ℚ_[2]) = (6 : ℚ_[2]); norm_num,
      hilbertSym_six_unit w, eps_of_tzp3_eq_three r h]
    simp
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep r 5
      (by rw [h]; simpa using toZModPow_three_natCast 5) isUnit_five.ne_zero
    rw [hilbertSym_two_mul_rep_left r 5 (w : ℚ_[2]) ⟨s, hs⟩]
    rw [show (2 : ℚ_[2]) * ((5 : ℤ_[2]) : ℚ_[2]) = 10 by
        change (2 : ℚ_[2]) * (5 : ℚ_[2]) = (10 : ℚ_[2]); norm_num,
      hilbertSym_ten_unit w, eps_of_tzp3_eq_five r h]
    simp [zero_mul, zero_add]
  · obtain ⟨s, hs⟩ := exists_sq_mul_rep r 7
      (by rw [h]; simpa using toZModPow_three_natCast 7) isUnit_seven.ne_zero
    rw [hilbertSym_two_mul_rep_left r 7 (w : ℚ_[2]) ⟨s, hs⟩]
    rw [show (2 : ℚ_[2]) * ((7 : ℤ_[2]) : ℚ_[2]) = 14 by
        change (2 : ℚ_[2]) * (7 : ℚ_[2]) = (14 : ℚ_[2]); norm_num,
      hilbertSym_fourteen_unit w, eps_of_tzp3_eq_seven r h]
    simp

/-! ### The identity `(a,b) = (a,-ab)` and the case `α = β = 1`

Completing the square turns a zero of `z² - a x² - b y²` into a zero of `z² - a x² + a b y²`
and conversely, so the two quadratic forms have nontrivial zeros simultaneously and the two
symbols agree.  This reduces `(2u, 2v)` to `(2u, -uv)`, which is the `α = 1, β = 0` case
proved above. -/

-- Theorem: a nontrivial zero of `z² - a x² - b y²` gives one of `z² - a x² + a b y²`.
private lemma sol_add_neg_mul {a b : ℚ_[2]}
    (h : ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) :
    ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 + a * b * y ^ 2 = 0 := by
  obtain ⟨z, x, y, hne, heq⟩ := h
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      rintro rfl
      have hz2 : z ^ 2 = 0 := by simpa [hy] using heq
      have hz : z = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using hz2)
      exact hne (by simp [hy, hz])
    have hs : a = (z / x) ^ 2 := by
      have hzax : z ^ 2 = a * x ^ 2 := by
        have h' : z ^ 2 - a * x ^ 2 = 0 := by simpa [hy] using heq
        exact sub_eq_zero.mp h'
      rw [div_pow, hzax]
      field_simp
    exact ⟨z / x, 1, 0, by simp, by rw [hs]; ring⟩
  · refine ⟨a * (x / y), z / y, 1, by simp, ?_⟩
    field_simp
    linear_combination (-a) * heq

-- Theorem: a nontrivial zero of `z² - a x² + a b y²` gives one of `z² - a x² - b y²`.
private lemma sol_neg_mul_add {a b : ℚ_[2]} (ha : a ≠ 0)
    (h : ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 + a * b * y ^ 2 = 0) :
    ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  obtain ⟨z, x, y, hne, heq⟩ := h
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      rintro rfl
      have hz2 : z ^ 2 = 0 := by simpa [hy] using heq
      have hz : z = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using hz2)
      exact hne (by simp [hy, hz])
    have hs : a = (z / x) ^ 2 := by
      have hzax : z ^ 2 = a * x ^ 2 := by
        have h' : z ^ 2 - a * x ^ 2 = 0 := by simpa [hy] using heq
        exact sub_eq_zero.mp h'
      rw [div_pow, hzax]
      field_simp
    exact ⟨z / x, 1, 0, by simp, by rw [hs]; ring⟩
  · refine ⟨x / y, z / y / a, 1, by simp, ?_⟩
    field_simp
    linear_combination (-1) * heq

-- Theorem: `(a,b)_2 = (a,-ab)_2` for nonzero `a, b`.
private lemma hilbertSym_self_neg_mul (a b : ℚ_[2]) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = hilbertSym a (-(a * b)) := by
  have hab : -(a * b) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero ha hb)
  have hP : (∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
        ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0)
      ↔ (∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
        ∧ z ^ 2 - a * x ^ 2 - (-(a * b)) * y ^ 2 = 0) := by
    constructor
    · intro h
      obtain ⟨Z, X, Y, hne, heq⟩ := sol_add_neg_mul h
      exact ⟨Z, X, Y, hne, by linear_combination heq⟩
    · intro h
      have h' : ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
          ∧ z ^ 2 - a * x ^ 2 + a * b * y ^ 2 = 0 := by
        obtain ⟨Z, X, Y, hne, heq⟩ := h
        exact ⟨Z, X, Y, hne, by linear_combination heq⟩
      exact sol_neg_mul_add ha h'
  have hL : hilbertSym a b = (if ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 then 1 else -1) := by
    unfold hilbertSym
    rw [ite_eq_right (by rw [not_or]; exact ⟨ha, hb⟩)]
  have hR : hilbertSym a (-(a * b)) = (if ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 - (-(a * b)) * y ^ 2 = 0 then 1 else -1) := by
    unfold hilbertSym
    rw [ite_eq_right (by rw [not_or]; exact ⟨ha, hab⟩)]
  rw [hL, hR]
  by_cases h : ∃ z x y : ℚ_[2], (z, x, y) ≠ (0, 0, 0)
      ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
  · rw [ite_eq_left h, ite_eq_left (hP.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hP.mpr h'))]

/-! ### The `α = β = 1` exponent identity

The characters `ε` and `ω` factor through the residue modulo `8`, so the exponent identity
behind `(2u, 2v) = (2u, -uv)` is a finite computation on `ZMod 8`. -/

/-- `ε` read off the residue modulo `8`. -/
private def epsR (c : ZMod 8) : ℤ := if c = 1 ∨ c = 5 then 0 else 1

/-- `ω` read off the residue modulo `8`. -/
private def omgR (c : ZMod 8) : ℤ := if c = 1 ∨ c = 7 then 0 else 1

-- Theorem: `ε` factors through the residue modulo `8`.
private lemma eps_eq_epsR (u : ℤ_[2]ˣ) : eps u = epsR ((u : ℤ_[2]).toZModPow 3) := by
  have h2 : (u : ℤ_[2]).toZModPow 2 = ZMod.cast ((u : ℤ_[2]).toZModPow 3) :=
    toZModPow_two_eq_of_three u rfl
  rw [eps, epsR]
  by_cases h : (u : ℤ_[2]).toZModPow 3 = 1 ∨ (u : ℤ_[2]).toZModPow 3 = 5
  · have hc1 : (u : ℤ_[2]).toZModPow 2 = 1 := by
      rcases h with h | h
      · rw [h2, h]; decide
      · rw [h2, h]; decide
    rw [ite_eq_left hc1, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right ?_]
    intro hc
    exact h (zmod8_unit_mod4_eq_one _ (u.isUnit.map (PadicInt.toZModPow 3))
      (by rw [← h2]; exact hc))

-- Theorem: `ω` factors through the residue modulo `8`.
private lemma omg_eq_omgR (u : ℤ_[2]ˣ) : omg u = omgR ((u : ℤ_[2]).toZModPow 3) := rfl

-- Theorem: the exponent identity, checked on all residues modulo `8`.
private lemma parityPow_neg_mul_aux :
    ∀ c d : ZMod 8, IsUnit c → IsUnit d →
      parityPow (-1) (epsR c * epsR (-(c * d)) + omgR (-(c * d)))
        = parityPow (-1) (epsR c * epsR d + omgR d + omgR c) := by
  decide

-- Theorem: the exponent identity behind `(2u, 2v) = (2u, -uv)`.
private lemma parityPow_neg_mul (u v : ℤ_[2]ˣ) :
    parityPow (-1) (eps u * eps (-(u * v)) + omg (-(u * v)))
      = parityPow (-1) (eps u * eps v + omg v + omg u) := by
  rw [eps_eq_epsR u, eps_eq_epsR (-(u * v)), omg_eq_omgR (-(u * v)),
    eps_eq_epsR v, omg_eq_omgR v, omg_eq_omgR u]
  generalize hc : ((u : ℤ_[2]).toZModPow 3) = c
  generalize hd : ((v : ℤ_[2]).toZModPow 3) = d
  have hneg : (((-(u * v) : ℤ_[2]ˣ) : ℤ_[2]).toZModPow 3) = -(c * d) := by
    rw [← hc, ← hd]
    simp [map_mul, map_neg]
  rw [hneg]
  exact parityPow_neg_mul_aux c d
    (hc ▸ u.isUnit.map (PadicInt.toZModPow 3))
    (hd ▸ v.isUnit.map (PadicInt.toZModPow 3))

-- Theorem: Serre's formula at `p = 2` for two elements of valuation `1`.
theorem hilbertSym_two_mul_two_mul (u v : ℤ_[2]ˣ) :
    hilbertSym (2 * (u : ℚ_[2])) (2 * (v : ℚ_[2]))
      = parityPow (-1) (eps u * eps v + omg v + omg u) := by
  have hu : (2 * (u : ℚ_[2])) ≠ 0 :=
    mul_ne_zero two_padic_ne_zero (PadicInt.coe_ne_zero.mpr u.ne_zero)
  have hv : (2 * (v : ℚ_[2])) ≠ 0 :=
    mul_ne_zero two_padic_ne_zero (PadicInt.coe_ne_zero.mpr v.ne_zero)
  rw [hilbertSym_self_neg_mul (2 * (u : ℚ_[2])) (2 * (v : ℚ_[2])) hu hv]
  have hcoe : ((-(u * v) : ℤ_[2]ˣ) : ℚ_[2]) = -((u : ℚ_[2]) * (v : ℚ_[2])) := by
    simp [Units.val_neg, Units.val_mul]
  have harg : -((2 * (u : ℚ_[2])) * (2 * (v : ℚ_[2])))
      = ((-(u * v) : ℤ_[2]ˣ) : ℚ_[2]) * (2 : ℚ_[2]) ^ 2 := by
    rw [hcoe]; ring
  rw [harg]
  rw [show hilbertSym (2 * (u : ℚ_[2]))
        (((-(u * v) : ℤ_[2]ˣ) : ℚ_[2]) * (2 : ℚ_[2]) ^ 2)
      = hilbertSym (2 * (u : ℚ_[2])) ((-(u * v) : ℤ_[2]ˣ) : ℚ_[2]) by
    simpa using hilbertSym_mul_square_eq (a := 2 * (u : ℚ_[2])) (a' := (1 : ℚ_[2]))
      (b := ((-(u * v) : ℤ_[2]ˣ) : ℚ_[2])) (b' := (2 : ℚ_[2]))
      (by norm_num) (by norm_num)]
  rw [hilbertSym_two_mul_unit u (-(u * v)), parityPow_neg_mul u v]

/-! ### Assembling the closed formula

Reducing the two valuations modulo `2` turns `(a,b)_2` into one of the four base cases
already proved above.  The only remaining bookkeeping is that the exponent in Serre's
formula uses the *full* valuations; since one summand `valuation * ω(unit)` is odd exactly
when both factors are odd, it differs from the reduced exponent by an even integer, and
`parityPow (-1)` only sees parity. -/

-- Theorem: `parityPow (-1)` is additive in the exponent.
private lemma parityPow_neg_one_add (m n : ℤ) :
    parityPow (-1) (m + n) = parityPow (-1) m * parityPow (-1) n := by
  rcases Int.even_or_odd m with hm | hm <;> rcases Int.even_or_odd n with hn | hn
  · rw [parityPow_neg_one_of_even (hm.add hn), parityPow_neg_one_of_even hm,
      parityPow_neg_one_of_even hn, one_mul]
  · rw [parityPow_neg_one_of_odd (Int.not_even_iff_odd.mpr (hm.add_odd hn)),
      parityPow_neg_one_of_even hm, parityPow_neg_one_of_odd (Int.not_even_iff_odd.mpr hn),
      one_mul]
  · rw [parityPow_neg_one_of_odd (Int.not_even_iff_odd.mpr (hm.add_even hn)),
      parityPow_neg_one_of_odd (Int.not_even_iff_odd.mpr hm), parityPow_neg_one_of_even hn,
      mul_one]
  · rw [parityPow_neg_one_of_even (hm.add_odd hn),
      parityPow_neg_one_of_odd (Int.not_even_iff_odd.mpr hm),
      parityPow_neg_one_of_odd (Int.not_even_iff_odd.mpr hn), ← pow_two]
    norm_num

-- Theorem: `parityPow (-1)` depends only on the parity of the exponent.
private lemma parityPow_neg_one_congr {m n : ℤ} (h : Even (m - n)) :
    parityPow (-1) m = parityPow (-1) n := by
  have hm : m = (m - n) + n := by ring
  rw [hm, parityPow_neg_one_add, parityPow_neg_one_of_even h, one_mul]

-- Theorem: if `m` is odd, then `m * x - x` is even.
private lemma even_sub_mul_of_odd {m : ℤ} (hm : ¬ Even m) (x : ℤ) :
    Even (m * x - x) := by
  obtain ⟨k, hk⟩ := Int.not_even_iff_odd.mp hm
  exact ⟨k * x, by rw [hk]; ring⟩

-- Theorem: if `m` is even, then `m * x` is even.
private lemma even_mul_of_even {m : ℤ} (hm : Even m) (x : ℤ) : Even (m * x) :=
  hm.mul_right x

-- Theorem: reduction of the valuation modulo `2` for `p = 2` (absorbing
-- `(2^{α/2})²` into a square).
private lemma hilbertSym_reduce_two (a b : ℚ_[2]) (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b
      = hilbertSym ((2 : ℚ_[2]) ^ (a.valuation % 2)
            * ((twoAdicUnit a ha : ℤ_[2]) : ℚ_[2]))
          ((2 : ℚ_[2]) ^ (b.valuation % 2)
            * ((twoAdicUnit b hb : ℤ_[2]) : ℚ_[2])) := by
  simpa only [twoAdicUnit, Nat.cast_ofNat] using hilbertSym_reduce (p := 2) a b ha hb

-- Theorem: the unit--unit case agrees with `parityPow (-1) (eps u * eps v)`.
private lemma hilbertSym_two_units_eq_parity (u v : ℤ_[2]ˣ) :
    hilbertSym (u : ℚ_[2]) (v : ℚ_[2]) = parityPow (-1) (eps u * eps v) := by
  rw [hilbertSym_padic_two_units]
  by_cases hu : (u : ℤ_[2]).toZModPow 2 = 1
  · rw [ite_eq_left (Or.inl hu), eps_eq_zero u hu, zero_mul,
      parityPow_neg_one_of_even (show Even (0 : ℤ) by decide)]
  · by_cases hv : (v : ℤ_[2]).toZModPow 2 = 1
    · rw [ite_eq_left (Or.inr hv), eps_eq_one u hu, eps_eq_zero v hv, mul_zero,
        parityPow_neg_one_of_even (show Even (0 : ℤ) by decide)]
    · rw [ite_eq_right (by tauto), eps_eq_one u hu, eps_eq_one v hv, mul_one,
        parityPow_neg_one_of_odd (show ¬ Even (1 : ℤ) by decide)]

-- Theorem: the exponent agrees with the reduced one when both valuations are even.
private lemma parity_two_00 {a b : ℚ_[2]} (u v : ℤ_[2]ˣ)
    (hαe : Even a.valuation) (hβe : Even b.valuation) :
    parityPow (-1) (eps u * eps v + a.valuation * omg v + b.valuation * omg u)
      = parityPow (-1) (eps u * eps v) := by
  refine parityPow_neg_one_congr ?_
  have hd : eps u * eps v + a.valuation * omg v + b.valuation * omg u
      - eps u * eps v = a.valuation * omg v + b.valuation * omg u := by ring
  rw [hd]
  exact (even_mul_of_even hαe (omg v)).add (even_mul_of_even hβe (omg u))

-- Theorem: the exponent agrees with the reduced one when `α` is odd and `β` is even.
private lemma parity_two_10 {a b : ℚ_[2]} (u v : ℤ_[2]ˣ)
    (hαo : ¬ Even a.valuation) (hβe : Even b.valuation) :
    parityPow (-1) (eps u * eps v + a.valuation * omg v + b.valuation * omg u)
      = parityPow (-1) (eps u * eps v + omg v) := by
  refine parityPow_neg_one_congr ?_
  have hd : eps u * eps v + a.valuation * omg v + b.valuation * omg u
      - (eps u * eps v + omg v) = (a.valuation * omg v - omg v)
        + b.valuation * omg u := by ring
  rw [hd]
  exact (even_sub_mul_of_odd hαo (omg v)).add (even_mul_of_even hβe (omg u))

-- Theorem: the exponent agrees with the reduced one when `α` is even and `β` is odd.
private lemma parity_two_01 {a b : ℚ_[2]} (u v : ℤ_[2]ˣ)
    (hαe : Even a.valuation) (hβo : ¬ Even b.valuation) :
    parityPow (-1) (eps u * eps v + a.valuation * omg v + b.valuation * omg u)
      = parityPow (-1) (eps u * eps v + omg u) := by
  refine parityPow_neg_one_congr ?_
  have hd : eps u * eps v + a.valuation * omg v + b.valuation * omg u
      - (eps u * eps v + omg u) = a.valuation * omg v
        + (b.valuation * omg u - omg u) := by ring
  rw [hd]
  exact (even_mul_of_even hαe (omg v)).add (even_sub_mul_of_odd hβo (omg u))

-- Theorem: the exponent agrees with the reduced one when both valuations are odd.
private lemma parity_two_11 {a b : ℚ_[2]} (u v : ℤ_[2]ˣ)
    (hαo : ¬ Even a.valuation) (hβo : ¬ Even b.valuation) :
    parityPow (-1) (eps u * eps v + a.valuation * omg v + b.valuation * omg u)
      = parityPow (-1) (eps u * eps v + omg v + omg u) := by
  refine parityPow_neg_one_congr ?_
  have hd : eps u * eps v + a.valuation * omg v + b.valuation * omg u
      - (eps u * eps v + omg v + omg u) = (a.valuation * omg v - omg v)
        + (b.valuation * omg u - omg u) := by ring
  rw [hd]
  exact (even_sub_mul_of_odd hαo (omg v)).add (even_sub_mul_of_odd hβo (omg u))

-- Theorem: Serre's formula for the Hilbert symbol at p = 2.
theorem hilbertSym_padic_two_eq {a b : ℚ_[2]} (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b
      = parityPow (-1) (eps (twoAdicUnit a ha) * eps (twoAdicUnit b hb)
          + a.valuation * omg (twoAdicUnit b hb) + b.valuation * omg (twoAdicUnit a ha)) := by
  rw [hilbertSym_reduce_two a b ha hb]
  obtain hα0 | hα1 := Int.emod_two_eq_zero_or_one a.valuation
  · have hαe : Even a.valuation := Int.even_iff.mpr hα0
    obtain hβ0 | hβ1 := Int.emod_two_eq_zero_or_one b.valuation
    · -- both valuations even
      have hβe : Even b.valuation := Int.even_iff.mpr hβ0
      rw [hα0, hβ0]
      simp only [zpow_zero, one_mul]
      change hilbertSym (twoAdicUnit a ha : ℚ_[2]) (twoAdicUnit b hb : ℚ_[2])
        = parityPow (-1) (eps (twoAdicUnit a ha) * eps (twoAdicUnit b hb)
            + a.valuation * omg (twoAdicUnit b hb) + b.valuation * omg (twoAdicUnit a ha))
      rw [hilbertSym_two_units_eq_parity,
        parity_two_00 (a := a) (b := b) (twoAdicUnit a ha) (twoAdicUnit b hb) hαe hβe]
    · -- `α` even, `β` odd
      have hβo : ¬ Even b.valuation := Int.not_even_iff.mpr hβ1
      rw [hα0, hβ1]
      simp only [zpow_zero, zpow_one, one_mul]
      change hilbertSym (twoAdicUnit a ha : ℚ_[2]) (2 * (twoAdicUnit b hb : ℚ_[2]))
        = parityPow (-1) (eps (twoAdicUnit a ha) * eps (twoAdicUnit b hb)
            + a.valuation * omg (twoAdicUnit b hb) + b.valuation * omg (twoAdicUnit a ha))
      rw [hilbertSym_comm, hilbertSym_two_mul_unit,
        mul_comm (eps (twoAdicUnit b hb)) (eps (twoAdicUnit a ha)),
        parity_two_01 (a := a) (b := b) (twoAdicUnit a ha) (twoAdicUnit b hb) hαe hβo]
  · have hαo : ¬ Even a.valuation := Int.not_even_iff.mpr hα1
    obtain hβ0 | hβ1 := Int.emod_two_eq_zero_or_one b.valuation
    · -- `α` odd, `β` even
      have hβe : Even b.valuation := Int.even_iff.mpr hβ0
      rw [hα1, hβ0]
      simp only [zpow_one, zpow_zero, one_mul]
      change hilbertSym (2 * (twoAdicUnit a ha : ℚ_[2])) (twoAdicUnit b hb : ℚ_[2])
        = parityPow (-1) (eps (twoAdicUnit a ha) * eps (twoAdicUnit b hb)
            + a.valuation * omg (twoAdicUnit b hb) + b.valuation * omg (twoAdicUnit a ha))
      rw [hilbertSym_two_mul_unit,
        parity_two_10 (a := a) (b := b) (twoAdicUnit a ha) (twoAdicUnit b hb) hαo hβe]
    · -- both valuations odd
      have hβo : ¬ Even b.valuation := Int.not_even_iff.mpr hβ1
      rw [hα1, hβ1]
      simp only [zpow_one]
      change hilbertSym (2 * (twoAdicUnit a ha : ℚ_[2]))
          (2 * (twoAdicUnit b hb : ℚ_[2]))
        = parityPow (-1) (eps (twoAdicUnit a ha) * eps (twoAdicUnit b hb)
            + a.valuation * omg (twoAdicUnit b hb) + b.valuation * omg (twoAdicUnit a ha))
      rw [hilbertSym_two_mul_two_mul,
        parity_two_11 (a := a) (b := b) (twoAdicUnit a ha) (twoAdicUnit b hb) hαo hβo]

/-! ### Multiplicativity in the first argument

The closed formula of `hilbertSym_padic_two_eq` is a product of signs whose exponent is
built from the two valuations and the two unit characters `ε`, `ω`.  Multiplicativity in
`a` therefore reduces to the two character identities `ε(uv) ≡ ε(u) + ε(v)` and
`ω(uv) ≡ ω(u) + ω(v)` modulo `2` (checked on the four units of `ZMod 8`), together with
`valuation (a * a') = valuation a + valuation a'` and multiplicativity of the unit part. -/

-- Theorem: multiplication of units is compatible with `twoAdicUnit` at `p = 2`.
private lemma twoAdicUnit_mul (a a' : ℚ_[2]) (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (twoAdicUnit (a * a') (mul_ne_zero ha ha') : ℤ_[2])
      = (twoAdicUnit a ha : ℤ_[2]) * (twoAdicUnit a' ha' : ℤ_[2]) := by
  simpa only [twoAdicUnit] using padicUnit_mul (p := 2) a a' ha ha'

-- Theorem: `ε(u * v) - ε(u) - ε(v)` is even, checked on the units of `ZMod 8`.
private lemma even_eps_mul_sub_aux :
    ∀ c d : ZMod 8, IsUnit c → IsUnit d →
      Even (epsR (c * d) - epsR c - epsR d) := by
  decide

-- Theorem: `ω(u * v) - ω(u) - ω(v)` is even, checked on the units of `ZMod 8`.
private lemma even_omg_mul_sub_aux :
    ∀ c d : ZMod 8, IsUnit c → IsUnit d →
      Even (omgR (c * d) - omgR c - omgR d) := by
  decide

-- Theorem: `ε` is additive modulo `2` on `ℤ_[2]ˣ`.
private lemma even_eps_mul_sub (u v : ℤ_[2]ˣ) :
    Even (eps (u * v) - eps u - eps v) := by
  have h : (((u * v : ℤ_[2]ˣ) : ℤ_[2]).toZModPow 3)
      = ((u : ℤ_[2]).toZModPow 3) * ((v : ℤ_[2]).toZModPow 3) := by
    simp [Units.val_mul, map_mul]
  rw [eps_eq_epsR (u * v), eps_eq_epsR u, eps_eq_epsR v, h]
  exact even_eps_mul_sub_aux _ _ (u.isUnit.map (PadicInt.toZModPow 3))
    (v.isUnit.map (PadicInt.toZModPow 3))

-- Theorem: `ω` is additive modulo `2` on `ℤ_[2]ˣ`.
private lemma even_omg_mul_sub (u v : ℤ_[2]ˣ) :
    Even (omg (u * v) - omg u - omg v) := by
  have h : (((u * v : ℤ_[2]ˣ) : ℤ_[2]).toZModPow 3)
      = ((u : ℤ_[2]).toZModPow 3) * ((v : ℤ_[2]).toZModPow 3) := by
    simp [Units.val_mul, map_mul]
  rw [omg_eq_omgR (u * v), omg_eq_omgR u, omg_eq_omgR v, h]
  exact even_omg_mul_sub_aux _ _ (u.isUnit.map (PadicInt.toZModPow 3))
    (v.isUnit.map (PadicInt.toZModPow 3))

-- Theorem: the Hilbert symbol on `ℚ_[2]` is multiplicative in the first argument.
theorem hilbertSym_padic_two_mul_left (a a' b : ℚ_[2]) :
    hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [hilbertSym_zero_left]
  rcases eq_or_ne a' 0 with rfl | ha'
  · simp [hilbertSym_zero_left]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [hilbertSym_zero_right]
  have hu : twoAdicUnit (a * a') (mul_ne_zero ha ha')
      = twoAdicUnit a ha * twoAdicUnit a' ha' :=
    Units.ext (twoAdicUnit_mul a a' ha ha')
  rw [hilbertSym_padic_two_eq (mul_ne_zero ha ha') hb,
    hilbertSym_padic_two_eq ha hb, hilbertSym_padic_two_eq ha' hb,
    Padic.valuation_mul ha ha', hu]
  rw [← parityPow_neg_one_add]
  refine parityPow_neg_one_congr ?_
  have hD1 := even_eps_mul_sub (twoAdicUnit a ha) (twoAdicUnit a' ha')
  have hD2 := even_omg_mul_sub (twoAdicUnit a ha) (twoAdicUnit a' ha')
  have hkey :
      eps (twoAdicUnit a ha * twoAdicUnit a' ha') * eps (twoAdicUnit b hb)
          + (a.valuation + a'.valuation) * omg (twoAdicUnit b hb)
          + b.valuation * omg (twoAdicUnit a ha * twoAdicUnit a' ha')
        - (eps (twoAdicUnit a ha) * eps (twoAdicUnit b hb)
            + a.valuation * omg (twoAdicUnit b hb)
            + b.valuation * omg (twoAdicUnit a ha)
          + (eps (twoAdicUnit a' ha') * eps (twoAdicUnit b hb)
            + a'.valuation * omg (twoAdicUnit b hb)
            + b.valuation * omg (twoAdicUnit a' ha')))
        = (eps (twoAdicUnit a ha * twoAdicUnit a' ha')
              - eps (twoAdicUnit a ha) - eps (twoAdicUnit a' ha'))
            * eps (twoAdicUnit b hb)
          + (omg (twoAdicUnit a ha * twoAdicUnit a' ha')
              - omg (twoAdicUnit a ha) - omg (twoAdicUnit a' ha'))
            * b.valuation := by
    ring
  rw [hkey]
  exact (even_mul_of_even hD1 (eps (twoAdicUnit b hb))).add
    (even_mul_of_even hD2 b.valuation)

instance instHasBilinHilbertSym : HasBilinHilbertSym ℚ_[2] :=
  ⟨fun {a a' b} => hilbertSym_padic_two_mul_left a a' b⟩

end HasseMinkowski
