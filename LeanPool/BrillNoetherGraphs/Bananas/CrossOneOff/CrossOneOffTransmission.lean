/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.CrossOneOffResidueDelta

/-!
# Transmission rows forced by cross-one-off rank differences

This small interface turns an exact value `rankDelta = 1` into the
corresponding row of a transmission permutation.  The geometric calculations
are kept in the preceding modules; this file is deliberately purely formal.
-/

namespace Bananas

open Utilities

/-- Comparing two forced rows a period apart.  This is the elementary
affinity constraint used to rule out candidate short periods. -/
theorem IsKAffine.row_difference
    {k : ℕ} {τ : ℤ → ℤ} (hAffine : IsKAffine k τ)
    {a a' b : ℤ} (hRow : τ b = a) (hRowShift : τ (b + k) = a') :
    a' = a + k := by
  rw [hAffine b, hRow] at hRowShift
  exact hRowShift.symm

/-- A forced pair of rows contradicts a putative affine period whenever their
values do not differ by that period. -/
theorem IsKAffine.not_period_of_forced_rows
    {k : ℕ} {τ : ℤ → ℤ} (hAffine : IsKAffine k τ)
    {a a' b : ℤ} (hRow : τ b = a) (hRowShift : τ (b + k) = a')
    (hNe : a' ≠ a + k) : False := by
  exact hNe (hAffine.row_difference hRow hRowShift)

/-- A rank-difference equal to one forces the indicated transmission row. -/
theorem transmission_value_of_rankDelta_eq_one
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hτ : IsTransmissionPermutation M D τ) {a b : ℤ}
    (hDelta : rankDelta M (D + a • one_chip M.u - b • one_chip M.v) = 1) :
    τ b = a := by
  have hValue := hτ.2 a b
  rw [hDelta] at hValue
  simpa using hValue

/-- Linear equivalence transports a computed second rank difference into a
forced transmission row. -/
theorem transmission_value_of_linearEquiv_rankDelta_eq_one
    {M : TwiceMarked} {D E : CFDiv M.graph} {τ : ℤ → ℤ}
    (hτ : IsTransmissionPermutation M D τ) {a b : ℤ}
    (hDE : linear_equiv M.graph (D + a • one_chip M.u - b • one_chip M.v) E)
    (hDelta : rankDelta M E = 1) :
    τ b = a := by
  apply transmission_value_of_rankDelta_eq_one hτ
  rw [rankDelta_eq_of_linearEquiv hDE]
  exact hDelta

/-- Corrected Lemma 4.30(3), now as a forced transmission row.  This is the
positive-residue case `b = m n_β + r`; its candidate is
`g + 2m - b + 2`. -/
theorem transmission_crossOneOff_positive_residue
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (b m r c : ℕ) (τ : ℤ → ℤ)
    (hg : 2 ≤ g) (hαβ : α ≠ β) (hb : b = m * B.length β + r)
    (hrLo : 1 ≤ r) (hrHi : r + 1 < B.length β)
    (hCandidate : b ≤ g + 2 * m + 2)
    (ha : g + 2 * m + 2 - b ≤ B.length α)
    (hpLo : 2 ≤ g + 2 * m + 2 - b)
    (hpHi : g + 2 * m + 2 - b < B.length α)
    (hc : c ≤ g - 2) (hbm : b ≤ g + m) (hcEq : c = g + m - b)
    (hτ : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (g • one_chip (rightEndpoint B)) τ) :
    τ (b : ℤ) = (g + 2 * m + 2 - b : ℕ) := by
  let M := mark B.graph
    (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
    (strandVertex B β ⟨B.length β - 1, by omega⟩)
  let D : CFDiv B.graph := g • one_chip (rightEndpoint B)
  let p : B.PathPosition α := ⟨g + 2 * m + 2 - b, by omega⟩
  let q : B.PathPosition β := ⟨r, by omega⟩
  have hFiring := crossOneOff_firing_positive_residue B α β b m r hb hrLo hrHi
    hCandidate ha
  have hDelta := rankDelta_crossOneOff_two_interior_eq_one B α β p q c hg hαβ
    (by simpa [p] using hpLo) (by simpa [p] using hpHi)
    (by simpa [q] using hrLo) (by simpa [q] using hrHi) hc
  have hE : linear_equiv B.graph
      (D + ((g + 2 * m + 2 - b : ℕ) : ℤ) •
          one_chip (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) •
          one_chip (strandVertex B β ⟨B.length β - 1, by omega⟩))
      ((c : ℤ) • (one_chip (leftEndpoint B) + one_chip (rightEndpoint B)) +
        one_chip (strandVertex B α p) + one_chip (strandVertex B β q)) := by
    have hcEqZ : (c : ℤ) = (g : ℤ) + (m : ℤ) - (b : ℤ) := by
      exact_mod_cast hcEq
    rw [hcEqZ]
    simpa only [D, p, q, Nat.cast_smul_eq_nsmul] using hFiring
  exact transmission_value_of_linearEquiv_rankDelta_eq_one hτ hE (by
    simpa [M, p, q] using hDelta)

/-- Corrected Lemma 4.30(1), as a forced row at a positive multiple of the
second marked-strand length. -/
theorem transmission_crossOneOff_multiple
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (b m c : ℕ) (τ : ℤ → ℤ)
    (hg : 2 ≤ g) (hαβ : α ≠ β) (hb : b = m * B.length β)
    (hm : 1 ≤ m) (ha : m + 1 < B.length α)
    (hβLength : 2 ≤ B.length β) (hc : c ≤ g - 1)
    (hbm : b ≤ g + m) (hcEq : c = g + m - b)
    (hτ : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (g • one_chip (rightEndpoint B)) τ) :
    τ (b : ℤ) = (m + 1 : ℕ) := by
  let M := mark B.graph
    (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
    (strandVertex B β ⟨B.length β - 1, by omega⟩)
  let D : CFDiv B.graph := g • one_chip (rightEndpoint B)
  let p : B.PathPosition α := ⟨m + 1, by omega⟩
  have hFiring := crossOneOff_firing_multiple B α β b m hb (by omega)
  have hDelta := rankDelta_crossOneOff_multiple_normalForm_eq_one B α β p c
    hg hαβ (by simpa [p] using hm) (by simpa [p] using ha)
    hβLength hc
  have hE : linear_equiv B.graph
      (D + ((m + 1 : ℕ) : ℤ) •
          one_chip (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) •
          one_chip (strandVertex B β ⟨B.length β - 1, by omega⟩))
      ((c : ℤ) • one_chip (rightEndpoint B) + one_chip (strandVertex B α p)) := by
    have hcEqZ : (c : ℤ) = (g : ℤ) + (m : ℤ) - (b : ℤ) := by
      exact_mod_cast hcEq
    rw [hcEqZ]
    simpa only [D, p, Nat.cast_smul_eq_nsmul, add_comm] using hFiring
  exact transmission_value_of_linearEquiv_rankDelta_eq_one hτ hE (by
    simpa [M, p] using hDelta)

/-- Corrected Lemma 4.30(2), as a forced row in the complementary-residue
case `b + 1 = m n_β`.  The strict normal-form bound excludes exactly the
length-two boundary whose rank difference is zero. -/
theorem transmission_crossOneOff_complement_residue
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (b m c : ℕ) (τ : ℤ → ℤ)
    (hg : 2 ≤ g) (hαβ : α ≠ β) (hm : 1 ≤ m)
    (hb : b + 1 = m * B.length β) (ha : g + m < B.length α)
    (hβLength : 2 ≤ B.length β) (hc : c < g - 1)
    (hcm : m * (B.length β - 1) ≤ g)
    (hcEq : c = g - m * (B.length β - 1))
    (hτ : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (g • one_chip (rightEndpoint B)) τ) :
    τ (b : ℤ) = (g + m : ℕ) := by
  let M := mark B.graph
    (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
    (strandVertex B β ⟨B.length β - 1, by omega⟩)
  let D : CFDiv B.graph := g • one_chip (rightEndpoint B)
  let p : B.PathPosition α := ⟨g + m, by omega⟩
  let q : B.PathPosition β := ⟨B.length β - 1, by omega⟩
  have hFiring := crossOneOff_firing_complement_residue B α β b m hm hb (by omega)
  have hDelta := rankDelta_crossOneOff_complement_normalForm_eq_one B α β p c
    hg hαβ (by simpa [p] using (show 2 ≤ g + m by omega))
    (by simpa [p] using ha) hβLength hc
  have hE : linear_equiv B.graph
      (D + ((g + m : ℕ) : ℤ) •
          one_chip (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩) -
        (b : ℤ) •
          one_chip (strandVertex B β ⟨B.length β - 1, by omega⟩))
      (((g : ℤ) - 1) • one_chip (leftEndpoint B) +
        (c : ℤ) • one_chip (rightEndpoint B) +
        one_chip (strandVertex B α p) + one_chip (strandVertex B β q)) := by
    have hcEqZ : (c : ℤ) = (g : ℤ) - (m : ℤ) * ((B.length β : ℤ) - 1) := by
      rw [hcEq, Nat.cast_sub hcm, Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ B.length β)]
      norm_num
    rw [hcEqZ]
    simpa only [D, p, q, Nat.cast_smul_eq_nsmul] using hFiring
  exact transmission_value_of_linearEquiv_rankDelta_eq_one hτ hE (by
    simpa [M, p, q] using hDelta)

end Bananas
