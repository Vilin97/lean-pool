/-
Copyright (c) 2026 Colin Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colin Jones
-/

import Mathlib.Tactic

noncomputable def pbc_real (position box_length : ℝ) : ℝ :=  position - box_length * round (position / box_length)

noncomputable def squaredminImageDistance_real ( posA posB box_length : Fin 3 → ℝ) : ℝ :=
  let dx := pbc_real (posB (0:Fin 3) - posA (0: Fin 3)) (box_length (0: Fin 3))
  let dy := pbc_real (posB (1:Fin 3) - posA (1: Fin 3)) (box_length (1: Fin 3))
  let dz := pbc_real (posB (2:Fin 3) - posA (2: Fin 3)) (box_length (2: Fin 3))
  dx^2 + dy^2 + dz^2 


noncomputable def minImageDistance_real ( posA posB box_length : Fin 3 → ℝ) : ℝ :=
  (squaredminImageDistance_real  posA posB box_length).sqrt


theorem minImageDistance_real_self (pos box_length : Fin 3 → ℝ) : 
  minImageDistance_real pos pos box_length = 0 := by
  unfold minImageDistance_real squaredminImageDistance_real
  have h0 : pbc_real (pos (0:Fin 3) - pos (0: Fin 3)) (box_length (0: Fin 3)) = 0 := by
    simp [pbc_real, sub_self, zero_div, round_zero, mul_zero, sub_zero]
  have h1 : pbc_real (pos (1:Fin 3) - pos (1:Fin 3)) (box_length (1:Fin 3)) = 0 := by
    simp [pbc_real, sub_self, zero_div, round_zero, mul_zero, sub_zero]
  have h2 : pbc_real (pos (2:Fin 3) - pos (2:Fin 3)) (box_length (2:Fin 3)) = 0 := by
    simp [pbc_real, sub_self, zero_div, round_zero, mul_zero, sub_zero]
  rw [h0, h1, h2]
  simp

theorem minImageDistance_real_nonneg ( posA posB box_length : Fin 3 → ℝ) :
  0 ≤ minImageDistance_real  posA posB box_length := by
  unfold minImageDistance_real
  apply Real.sqrt_nonneg

/-- Alternate way of defining the minimum image distance function -/
noncomputable def minImageDist (box_length posA posB : Fin n → ℝ) : ℝ :=
  let dist := fun i => pbc_real (posB i - posA i) (box_length i)
  (Finset.univ.sum (fun i => (dist i) ^ 2)).sqrt


/-! Basic Math Theorems on `round` function. -/
variable [LinearOrderedField α] [FloorRing α]

theorem round_sub_one_le_x (x : α) : round x - 1 ≤ x := by
  rw [round_eq x]
  have h1 : ↑⌊x + 1/2⌋ ≤ x + 1/2 := Int.floor_le (x + 1/2)
  have h2 : ↑⌊x + 1/2⌋ - 1 ≤ (x + 1/2) - 1 := by linarith
  have h3 : (x + 1/2) - 1 = x - 1/2 := by ring
  rw [h3] at h2
  have h4 : x - 1/2 ≤ x := by linarith
  exact le_trans h2 h4

theorem abs_diff_round_le_half (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq]
  have h1 : x - 1/2 < ↑⌊x + 1/2⌋ := by
    have h1a : x + 1/2 < ↑⌊x + 1/2⌋ + 1 := by apply Int.lt_floor_add_one
    linarith
  have h2 : ↑⌊x + 1/2⌋ ≤ x + 1/2 := Int.floor_le (x + 1/2)
  have h3 : -(1/2) ≤ x - ↑⌊x + 1/2⌋ ∧ x - ↑⌊x + 1/2⌋ ≤ 1/2 := by
    constructor
    · linarith
    · linarith
  exact abs_le.mpr h3

theorem abs_pbc_le (x L : ℝ) (hL : 0 < L) : |pbc_real x L| ≤ L / 2 := by
  dsimp only [pbc_real]
  have : |(x / L) - round (x / L)| ≤ 1 / 2 := abs_diff_round_le_half (x / L)
  calc
    |x - L * round (x / L)| = |L * ((x / L) - round (x / L))| := by field_simp
    _ = |L| * |(x / L) - round (x / L)| := by rw [abs_mul]
    _ = L * |(x / L) - round (x / L)| := by rw [abs_of_pos hL]
    _ ≤ L * (1 / 2) := mul_le_mul_of_nonneg_left this (by linarith)
    _ = L / 2 := by ring


-- # The Periodic Boundary Conditions guarantee periodic behavior
theorem pbc_periodic (x L : ℝ) (k : ℤ) (hL : L ≠ 0) : pbc_real (x - k * L) L = pbc_real x L := by
  dsimp only [pbc_real]
  have : round ((x - k * L) / L) = round (x / L - k) := by
    congr
    field_simp [mul_comm]
  rw [this, round_sub_intCast, Int.cast_sub, mul_sub]
  ring


--# The minImageDistance is bounded above by the diagonal of the simulation cell.
theorem minImageDistance_bounded
    (box_length posA posB : Fin n → ℝ) (hbox : ∀ i, 0 < box_length i) :
    minImageDist box_length posA posB
    ≤ (Finset.univ.sum fun i => (box_length i / 2) ^ 2).sqrt := by
  dsimp only [minImageDist]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  have bound : |pbc_real (posB i - posA i) (box_length i)| ≤ box_length i / 2 := 
    abs_pbc_le (posB i - posA i) (box_length i) (hbox i)
  calc
    (pbc_real (posB i - posA i) (box_length i))^2
        = |pbc_real (posB i - posA i) (box_length i)|^2 := by rw [sq_abs]
    _ ≤ (box_length i / 2)^2 := by
      apply pow_le_pow_left₀ 
      · exact abs_nonneg (pbc_real (posB i - posA i) (box_length i))
      · bound


--# The minimum image distance is invariant under periodic translations.
theorem minImageDistance_real_periodic
    (box_length posA posB : Fin n → ℝ) (k : Fin n → ℤ)
    (hbox : ∀ i, box_length i ≠ 0) :
    minImageDist box_length posA posB =
    minImageDist box_length (fun i => posA i + (k i : ℝ) * box_length i) posB := by
  dsimp [minImageDist]
  have h_dist : ∀ i,
      pbc_real (posB i - (posA i + (k i : ℝ) * box_length i)) (box_length i)
        = pbc_real (posB i - posA i) (box_length i) := by
    intro i
    rw [sub_add_eq_sub_sub]
    exact pbc_periodic (posB i - posA i) (box_length i) (k i) (hbox i)
  simp_rw [h_dist]


--# The minimum image distance between any two points is non-negative
theorem minImageDist_nonneg (box_length posA posB : Fin n → ℝ) :
  0 ≤ minImageDist box_length posA posB := by
  unfold minImageDist
  apply Real.sqrt_nonneg


--# The minimum image distance between two identical points is zero.
theorem minImageDist_self (box_length pos : Fin n → ℝ) :
  minImageDist box_length pos pos = 0 := by
  unfold minImageDist
  have h_dist : ∀ i, pbc_real (pos i - pos i) (box_length i) = 0 := by
    intro i
    simp [pbc_real]
  simp_rw [h_dist]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, Real.sqrt_zero]

lemma apply_pbc_sub (a b L : ℝ) :
  pbc_real (a - b) L = (a - b) - L * round ((a - b) / L) := by rfl


lemma apply_pbc_nested (a b L : ℝ) (hL : L ≠ 0) :
  pbc_real (pbc_real a L - pbc_real b L) L = (a - b) - L * round ((a - b) / L) := by
  calc
    pbc_real (pbc_real a L - pbc_real b L) L
        = pbc_real ((a - L * round (a / L)) - (b - L * round (b / L))) L := by rfl
    _ = pbc_real ((a - b) - L * (round (a / L) - round (b / L))) L := by ring_nf
    _ = (a - b) - L * (round (a / L) - round (b / L))
        - L * round (((a - b) - L * (round (a / L) - round (b / L))) / L) := by rw [pbc_real]
    _ = (a - b) - L * (round (a / L) - round (b / L))
        - L * round ((a - b) / L - (round (a / L) - round (b / L))) := by
      have h_div : ((a - b) - L * (round (a / L) - round (b / L))) / L =
                    (a - b) / L - (round (a / L) - round (b / L)) := by field_simp [hL]
      rw [h_div]
    _ = (a - b) - L * round ((a - b) / L) := by
        rw [← Int.cast_sub, round_sub_intCast, sub_sub, ← mul_add, ← Int.cast_add, add_sub_cancel]


--# Theorem to show that applying PBC to each position individually gives the same squared distance
/-
This theorem asserts that the minimum image distance between two positions posA and posB in a periodic box
can be calculated equivalently in two ways:
By directly computing the minimum image distance for the box size, or
By first applying periodic boundary conditions (PBC) to both positions and then computing the minimum image
distance. In other words, the order of applying PBC—either before or during the computation of distances—
does not affect the final result.
-/

theorem squaredminImageDistance_theorem (box_length posA posB : Fin 3 → ℝ) (hL : ∀ i, box_length i ≠ 0) :
  squaredminImageDistance_real box_length posA posB =
  squaredminImageDistance_real box_length
    (λ i => pbc_real (posA i) (box_length i))
    (λ i => pbc_real (posB i) (box_length i)) := by
  unfold squaredminImageDistance_real
  have h0 : pbc_real (pbc_real (posB ⟨0, by decide⟩) (box_length ⟨0, by decide⟩) -
                       pbc_real (posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩)) (box_length ⟨0, by decide⟩) =
            pbc_real (posB ⟨0, by decide⟩ - posA ⟨0, by decide⟩) (box_length ⟨0, by decide⟩) := by
    apply apply_pbc_nested
    exact hL ⟨0, by decide⟩
  have h1 : pbc_real (pbc_real (posB ⟨1, by decide⟩) (box_length ⟨1, by decide⟩) -
                       pbc_real (posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩)) (box_length ⟨1, by decide⟩) =
            pbc_real (posB ⟨1, by decide⟩ - posA ⟨1, by decide⟩) (box_length ⟨1, by decide⟩) := by
    apply apply_pbc_nested
    exact hL ⟨1, by decide⟩
  have h2 : pbc_real (pbc_real (posB ⟨2, by decide⟩) (box_length ⟨2, by decide⟩) -
                       pbc_real (posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩)) (box_length ⟨2, by decide⟩) =
            pbc_real (posB ⟨2, by decide⟩ - posA ⟨2, by decide⟩) (box_length ⟨2, by decide⟩) := by
    apply apply_pbc_nested
    exact hL ⟨2, by decide⟩
  simp only [Function.const_apply]
